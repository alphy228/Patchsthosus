#!/usr/bin/env python3
"""
mod_to_datapatch.py — Convert pure JSON / HJSON / JSON5 Mindustry mods into
DataPatch asset .zip archives (importable via Map Editor -> Data / Assets ->
Import Zip and loadable via mindustry.mod.DataManager), with a multi-layer
engine-accurate bypass pipeline for Mindustry's single-page 500x500
`data-patch-reserved-env` environment sprite atlas limit.

Key Capabilities:
  1. Full Arc Jval-compatible HJSON / JSON5 / JSON parser (no external deps;
     requires only Pillow for PNG inspection/cropping/atlas visualization).
  2. Complete Mod -> DataPatch normalization:
     - Folder canonicalization (`status` -> `statuses`, `weathers` -> `weather`,
       skipping DataPatch-unsupported `planets`/`sectors`).
     - Automatic conversion of vanilla content override files into DataPatch
       `patches/00-vanilla-overrides.json`.
     - Rewriting `<mod>-` prefixes to `dp-` across content JSON, sprite/part
       region names, and `bundles/*.properties` localization keys (while
       avoiding double `dp-dp-` prefixes on `weapons[*].name`).
     - Rewriting custom audio stems (`sounds/`, `music/`) to `dp-<name>` across
       sound/music fields and `RandomSound` arrays.
     - Stripping DataPatch-disallowed `research` trees and filtering custom mod
       planets out of `shownPlanets` so custom items/blocks/units neither crash
       `ContentParser` nor become unbuildable on Serpulo/Erekir/custom maps.
     - Deduplicating colliding asset basenames per `DataAssetType`.
  3. 7-Layer `500x500` Environment Atlas (`data-patch-reserved-env`) Bypass:
     - Layer 1 (Unhittable Privileged Buildings): Converts non-functional,
       non-destructible, non-floor/overlay environment blocks (`StaticWall`,
       `StaticTree`, `TallBlock`, `TreeBlock`, `Prop`, `SeaBush`, `Seaweed`,
       `WobbleProp`) into unhittable privileged `MemoryBlock` buildings
       (`privileged: true`, `memoryCapacity: 0`, `targetable: false`,
       `underBullets: true`, `breakable: false`, `rebuildable: false`,
       `drawTeamOverlay: false`, `drawCached: true`, `drawDynamic: false`,
       `forceDark` preserved) and moves their sprites to `patchAtlas` (4096x4096).
     - Layer 2 (Functional/Destructible Evacuation): Moves sprites stored under
       `sprites/blocks/environment/` that belong to `CacheLayer.normal`
       functional/destructible blocks (`PowerTurret`, `StorageBlock`, `Duct`,
       etc.) out to `sprites/blocks/env-functional/`.
     - Layer 3 (`cacheLayer: "normal"` StaticWall Bypass): Keeps functional
       `StaticWall`s (`itemDrop` for `BeamDrill`, `attributes` for `WallCrafter`,
       `wallOre` compatibility) as genuine `StaticWall` instances while setting
       `"cacheLayer": "normal"`, routing their rendering through `BlockRenderer`
       & `EditorSpriteCache` (`patchAtlas` 4096x4096) instead of `FloorRenderer`.
     - Layer 4 (`-edge` Bug Shield + Orphan/UI Evacuation): Sets
       `"drawEdgeOut": false` on custom `Floor`s lacking environment `-edge`
       sprites (preventing `DataManager.regenerateContentSprites` from placing
       generated `-edge` sprites onto `patchAtlas` and causing magenta
       `env-error` borders), and evacuates orphan/typo/UI/preview sprites out
       of `blocks/environment/`.
     - Layer 5 (Symmetric Center Alpha-Cropping + Exact Guillotine Sort):
       Symmetrically center-crops transparent borders on center-drawn
       `SteamVent`, `OverlayFloor`, and `OreBlock` sprites, and searches
       insertion orders against an exact port of Arc's
       `PixmapPacker.GuillotineStrategy(pageWidth, pageHeight, padding=2)`,
       encoding the winning order into `sprites/blocks/environment/r0000/...`
       so `MapAssetsDialog`'s lexicographic path sort feeds `DataImagePacker`
       optimally.
     - Layer 6 (Progressive Minimum-Loss Variant Consolidation): If the packed
       environment atlas still exceeds 1 page, consolidates `96x96` `SteamVent`
       secondary variants (`2 -> 1`) and then trims excess variants from the
       highest-variant `Floor`/`OverlayFloor` blocks one sprite at a time,
       stopping the instant `pages == 1`.
     - Layer 7 (`TextureRegion.scale` Sub-Resolution Client Patch): Downsamples
       large `SteamVent` / `Floor` PNGs by 2x and emits matching
       `"block.dp-<name>.variantRegions.<i>.scale": 2.0` rules into
       `patches/zz-env-scale-client.json` so `FloorRenderBatch` renders full
       world dimensions at ~1/4th the atlas pixel area (used as ultimate
       fallback in `auto` mode, or primary zero-variant-loss bypass in
       `scale-first` mode).
"""

from __future__ import annotations

import argparse
import base64
import copy
import dataclasses
import hashlib
import io
import json
import os
import random
import re
import sys
import zipfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from PIL import Image, ImageChops, ImageDraw


# ============================================================================
# 1. Arc Jval-Compatible HJSON / JSON5 / JSON Parser
# ============================================================================

class HjsonParseError(ValueError):
    pass


class HjsonParser:
    """Parses Mindustry JSON / HJSON / JSON5 files identically to Arc's Jval."""

    def __init__(self, text: str, filename: str = "<string>"):
        # Strip UTF-8 BOM if present
        if text.startswith("\ufeff"):
            text = text[1:]
        self.s = text.replace("\r\n", "\n").replace("\r", "\n")
        self.n = len(self.s)
        self.i = 0
        self.filename = filename

    def parse(self) -> Any:
        self._skip_ws_and_comments()
        if self.i >= self.n:
            return {}
        ch = self.s[self.i]
        if ch == "{":
            val = self._parse_object(braced=True)
        elif ch == "[":
            val = self._parse_array()
        else:
            # Root-braceless HJSON object (very common in Mindustry mods!)
            val = self._parse_object(braced=False)
        self._skip_ws_and_comments()
        return val

    def _skip_ws_and_comments(self) -> None:
        s, n = self.s, self.n
        while self.i < n:
            c = s[self.i]
            if c in " \t\n\f\v":
                self.i += 1
            elif c == "#":
                # Line comment
                nl = s.find("\n", self.i)
                self.i = n if nl == -1 else nl + 1
            elif c == "/" and self.i + 1 < n:
                nxt = s[self.i + 1]
                if nxt == "/":
                    nl = s.find("\n", self.i + 2)
                    self.i = n if nl == -1 else nl + 1
                elif nxt == "*":
                    end = s.find("*/", self.i + 2)
                    if end == -1:
                        self.i = n
                    else:
                        self.i = end + 2
                else:
                    break
            else:
                break

    def _skip_inline_ws_and_comments(self) -> None:
        s, n = self.s, self.n
        while self.i < n:
            c = s[self.i]
            if c in " \t":
                self.i += 1
            elif c == "/" and self.i + 1 < n and s[self.i + 1] == "*":
                end = s.find("*/", self.i + 2)
                self.i = n if end == -1 else end + 2
            else:
                break

    def _parse_object(self, braced: bool) -> Dict[str, Any]:
        obj: Dict[str, Any] = {}
        if braced:
            self.i += 1  # consume '{'
        while True:
            self._skip_ws_and_comments()
            if self.i >= self.n:
                if braced:
                    # Tolerate EOF on slightly malformed mod files if needed
                    break
                break
            c = self.s[self.i]
            if braced and c == "}":
                self.i += 1
                break
            if c == ",":
                self.i += 1
                continue

            key = self._parse_key()
            self._skip_ws_and_comments()
            if self.i < self.n and self.s[self.i] in (":", "="):
                self.i += 1
            elif self.i < self.n and self.s[self.i] in ("{", "["):
                # HJSON allows `key { ... }` without colon
                pass
            else:
                raise HjsonParseError(
                    f"{self.filename}: expected ':' after key {key!r} at pos {self.i}"
                )

            val = self._parse_value(is_array=False)
            obj[key] = val

            self._skip_inline_ws_and_comments()
            if self.i < self.n and self.s[self.i] == ",":
                self.i += 1
        return obj

    def _parse_key(self) -> str:
        c = self.s[self.i]
        if c in ('"', "'"):
            return self._parse_quoted_string(c)
        start = self.i
        while self.i < self.n:
            ch = self.s[self.i]
            if ch in ":,={}[] \t\n":
                break
            if ch == "#" or (ch == "/" and self.i + 1 < self.n and self.s[self.i + 1] in ("/", "*")):
                break
            self.i += 1
        key = self.s[start:self.i].strip()
        if not key:
            raise HjsonParseError(
                f"{self.filename}: empty key at pos {self.i} near {self.s[self.i:self.i+30]!r}"
            )
        return key

    def _parse_array(self) -> List[Any]:
        arr: List[Any] = []
        self.i += 1  # consume '['
        while True:
            self._skip_ws_and_comments()
            if self.i >= self.n:
                break
            c = self.s[self.i]
            if c == "]":
                self.i += 1
                break
            if c == ",":
                self.i += 1
                continue
            arr.append(self._parse_value(is_array=True))
            self._skip_inline_ws_and_comments()
            if self.i < self.n and self.s[self.i] == ",":
                self.i += 1
        return arr

    def _parse_value(self, is_array: bool = False) -> Any:
        self._skip_ws_and_comments()
        if self.i >= self.n:
            return ""
        c = self.s[self.i]
        if c == "{":
            return self._parse_object(braced=True)
        if c == "[":
            return self._parse_array()
        if c == "'" and self.s[self.i:self.i + 3] == "'''":
            return self._parse_multiline_string()
        if c in ('"', "'"):
            return self._parse_quoted_string(c)
        return self._parse_quoteless_or_literal(is_array=is_array)

    def _parse_multiline_string(self) -> str:
        # Calculation of indentation follows HJSON spec / Arc Jval
        # Determine column of opening '''
        line_start = self.s.rfind("\n", 0, self.i) + 1
        indent = self.i - line_start
        self.i += 3  # skip '''
        # Skip optional spaces and single leading newline right after '''
        while self.i < self.n and self.s[self.i] in " \t":
            self.i += 1
        if self.i < self.n and self.s[self.i] == "\n":
            self.i += 1
        end = self.s.find("'''", self.i)
        if end == -1:
            raw = self.s[self.i:]
            self.i = self.n
        else:
            raw = self.s[self.i:end]
            self.i = end + 3

        lines = raw.split("\n")
        processed: List[str] = []
        for idx, ln in enumerate(lines):
            # Strip up to `indent` leading spaces/tabs
            k = 0
            while k < len(ln) and k < indent and ln[k] in " \t":
                k += 1
            processed.append(ln[k:])
        # If last line was only whitespace before closing ''', drop trailing newline
        if processed and processed[-1].strip() == "":
            processed.pop()
        return "\n".join(processed)

    def _parse_quoted_string(self, quote: str) -> str:
        self.i += 1  # consume opening quote
        out: List[str] = []
        s, n = self.s, self.n
        while self.i < n:
            c = s[self.i]
            if c == quote:
                self.i += 1
                return "".join(out)
            if c == "\\":
                self.i += 1
                if self.i >= n:
                    break
                esc = s[self.i]
                self.i += 1
                if esc == "n":
                    out.append("\n")
                elif esc == "r":
                    out.append("\r")
                elif esc == "t":
                    out.append("\t")
                elif esc == "b":
                    out.append("\b")
                elif esc == "f":
                    out.append("\f")
                elif esc == "u" and self.i + 4 <= n:
                    hex4 = s[self.i:self.i + 4]
                    try:
                        out.append(chr(int(hex4, 16)))
                        self.i += 4
                    except ValueError:
                        out.append("\\u")
                elif esc == "#":
                    # ContentParser escapes '#' as '\#' in .json files
                    out.append("#")
                else:
                    out.append(esc)
            else:
                out.append(c)
                self.i += 1
        return "".join(out)

    @staticmethod
    def _try_literal_or_number(raw: str) -> Tuple[bool, Any]:
        if raw == "true":
            return True, True
        if raw == "false":
            return True, False
        if raw == "null":
            return True, None
        if re.fullmatch(r"-?(?:0|[1-9]\d*)(?:\.\d+)?(?:[eE][+-]?\d+)?", raw):
            if "." in raw or "e" in raw or "E" in raw:
                return True, float(raw)
            return True, int(raw)
        return False, raw

    def _parse_quoteless_or_literal(self, is_array: bool = False) -> Any:
        """Exact port of Arc Jval.Hparser.readQuotelessString."""
        start = self.i
        s, n = self.s, self.n
        while self.i < n:
            c = s[self.i]
            is_comment = (
                (c == "#" and not (self.i == start and re.match(r"#[0-9a-fA-F]{6}", s[self.i:self.i + 7])))
                or (c == "/" and self.i + 1 < n and s[self.i + 1] in ("/", "*"))
            )
            is_eol = (
                c == "\n"
                or (c == "," and is_array)
                or c in "}]"
                or is_comment
            )
            if is_eol or c == ",":
                cand = s[start:self.i].strip()
                ok, val = self._try_literal_or_number(cand)
                if ok:
                    return val
                if is_eol:
                    # Strip single trailing comma on unquoted object string value
                    end = self.i
                    if end > start and s[end - 1] == ",":
                        end -= 1
                    raw = s[start:end].strip()
                    if re.fullmatch(r"#[0-9a-fA-F]{6}(?:[0-9a-fA-F]{2})?", raw):
                        return raw[1:]
                    return raw
            self.i += 1

        end = self.i
        if end > start and s[end - 1] == ",":
            end -= 1
        raw = s[start:end].strip()
        ok, val = self._try_literal_or_number(raw)
        if ok:
            return val
        if re.fullmatch(r"#[0-9a-fA-F]{6}(?:[0-9a-fA-F]{2})?", raw):
            return raw[1:]
        return raw


def parse_hjson_file(path: Path) -> Any:
    text = path.read_text(encoding="utf-8", errors="replace")
    return HjsonParser(text, str(path)).parse()


# ============================================================================
# 2. Exact Port of Arc's PixmapPacker (GuillotineStrategy)
# ============================================================================

@dataclass
class PackedRect:
    name: str
    x: int
    y: int
    width: int
    height: int


class _GuillotineNode:
    __slots__ = ("x", "y", "w", "h", "left", "right", "full")

    def __init__(self, x: int, y: int, w: int, h: int):
        self.x = x
        self.y = y
        self.w = w
        self.h = h
        self.left: Optional[_GuillotineNode] = None
        self.right: Optional[_GuillotineNode] = None
        self.full: bool = False


class _GuillotinePage:
    def __init__(self, page_width: int, page_height: int, padding: int):
        self.rects: List[PackedRect] = []
        self.root = _GuillotineNode(
            padding,
            padding,
            page_width - padding * 2,
            page_height - padding * 2,
        )


class ArcGuillotinePacker:
    """
    100% line-for-line faithful port of `arc.graphics.g2d.PixmapPacker` with
    `GuillotineStrategy`, matching `new PixmapPacker(w, h, 2, true)`.
    """

    def __init__(self, page_width: int = 500, page_height: int = 500, padding: int = 2):
        self.page_width = page_width
        self.page_height = page_height
        self.padding = padding
        self.pages: List[_GuillotinePage] = []

    def pack(self, name: str, width: int, height: int) -> Tuple[int, PackedRect]:
        if width > self.page_width or height > self.page_height:
            raise ValueError(
                f"Page size ({self.page_width}x{self.page_height}) too small for '{name}' ({width}x{height})"
            )
        if not self.pages:
            self.pages.append(_GuillotinePage(self.page_width, self.page_height, self.padding))

        page_idx = len(self.pages) - 1
        page = self.pages[page_idx]
        rw = width + self.padding
        rh = height + self.padding

        node = self._insert(page.root, rw, rh)
        if node is None:
            page = _GuillotinePage(self.page_width, self.page_height, self.padding)
            self.pages.append(page)
            page_idx = len(self.pages) - 1
            node = self._insert(page.root, rw, rh)
        if node is None:
            raise ValueError(
                f"Failed to pack '{name}' ({rw}x{rh} padded) into root ({page.root.w}x{page.root.h})"
            )
        node.full = True
        pr = PackedRect(name=name, x=node.x, y=node.y, width=node.w - self.padding, height=node.h - self.padding)
        page.rects.append(pr)
        return page_idx, pr

    def _insert(self, node: _GuillotineNode, rw: int, rh: int) -> Optional[_GuillotineNode]:
        if not node.full and node.left is not None and node.right is not None:
            res = self._insert(node.left, rw, rh)
            if res is None:
                res = self._insert(node.right, rw, rh)
            return res
        if node.full:
            return None
        if node.w == rw and node.h == rh:
            return node
        if node.w < rw or node.h < rh:
            return None

        dw = node.w - rw
        dh = node.h - rh
        if dw > dh:
            node.left = _GuillotineNode(node.x, node.y, rw, node.h)
            node.right = _GuillotineNode(node.x + rw, node.y, node.w - rw, node.h)
        else:
            node.left = _GuillotineNode(node.x, node.y, node.w, rh)
            node.right = _GuillotineNode(node.x, node.y + rh, node.w, node.h - rh)
        return self._insert(node.left, rw, rh)


def simulate_env_pack(
    items: List[Tuple[str, int, int]],
    limit: int = 500,
    padding: int = 2,
) -> ArcGuillotinePacker:
    packer = ArcGuillotinePacker(limit, limit, padding)
    for name, w, h in items:
        packer.pack(name, w, h)
    return packer


def find_optimal_guillotine_order(
    items: List[Tuple[str, int, int]],
    limit: int = 500,
    padding: int = 2,
) -> Tuple[List[Tuple[str, int, int]], ArcGuillotinePacker]:
    """
    Searches deterministic Guillotine sort heuristics (and local perturbations
    if needed) to minimize `(len(pages), page1_overflow_area)`.
    """
    if not items:
        return [], ArcGuillotinePacker(limit, limit, padding)

    heuristics = [
        lambda x: (-max(x[1], x[2]), -(x[1] * x[2]), x[0]),
        lambda x: (-(x[1] * x[2]), -max(x[1], x[2]), x[0]),
        lambda x: (-x[2], -x[1], x[0]),
        lambda x: (-x[1], -x[2], x[0]),
        lambda x: (-(x[1] + x[2]), -(x[1] * x[2]), x[0]),
        lambda x: (-min(x[1], x[2]), -max(x[1], x[2]), x[0]),
        lambda x: (x[0],),  # original alphabetical baseline
    ]

    best_order = list(items)
    best_packer = simulate_env_pack(best_order, limit, padding)
    best_score = (
        len(best_packer.pages),
        sum(len(p.rects) for p in best_packer.pages[1:]),
    )

    for key_fn in heuristics:
        cand = sorted(items, key=key_fn)
        pk = simulate_env_pack(cand, limit, padding)
        score = (len(pk.pages), sum(len(p.rects) for p in pk.pages[1:]))
        if score < best_score:
            best_order, best_packer, best_score = cand, pk, score
        if best_score[0] == 1:
            return best_order, best_packer

    # If 2 pages with tiny overflow, try deterministic seeded swaps
    if best_score[0] == 2 and best_score[1] <= 12 and len(items) > 4:
        rng = random.Random(42)
        cur = list(best_order)
        for _ in range(120):
            cand = list(cur)
            a, b = rng.sample(range(len(cand)), 2)
            cand[a], cand[b] = cand[b], cand[a]
            pk = simulate_env_pack(cand, limit, padding)
            score = (len(pk.pages), sum(len(p.rects) for p in pk.pages[1:]))
            if score < best_score:
                best_order, best_packer, best_score = cand, pk, score
                cur = cand
                if best_score[0] == 1:
                    break

    return best_order, best_packer


# ============================================================================
# 3. Mindustry Engine Constants & Classification Tables
# ============================================================================

# Folder mapping -> exact Mindustry ContentType.folderName accepted by MapAssetsDialog
CONTENT_FOLDER_MAP: Dict[str, Tuple[str, str]] = {
    "items": ("item", "items"),
    "item": ("item", "items"),
    "blocks": ("block", "blocks"),
    "block": ("block", "blocks"),
    "liquids": ("liquid", "liquids"),
    "liquid": ("liquid", "liquids"),
    "statuses": ("status", "statuses"),
    "status": ("status", "statuses"),
    "units": ("unit", "units"),
    "unit": ("unit", "units"),
    "weather": ("weather", "weather"),
    "weathers": ("weather", "weather"),
}

UNSUPPORTED_CONTENT_FOLDERS: Set[str] = {
    "planets", "planet", "sectors", "sector", "bullets", "bullet",
    "teams", "team", "unitcommands", "unitstances",
}

VANILLA_PLANETS: Set[str] = {"serpulo", "erekir", "sun", "tantros", "gier", "notva", "verilus"}

# Vanilla content names commonly overridden in mods (checked when `type` is absent)
VANILLA_ITEMS: Set[str] = {
    "copper", "lead", "metaglass", "graphite", "sand", "coal", "titanium",
    "thorium", "scrap", "silicon", "plastanium", "phase-fabric", "surge-alloy",
    "spore-pod", "blast-compound", "pyratite", "beryllium", "tungsten",
    "oxide", "carbide", "fissile-matter", "dormant-cyst",
}
VANILLA_LIQUIDS: Set[str] = {
    "water", "slag", "oil", "cryofluid", "arkycite", "gallium",
    "neoplasm", "ozone", "hydrogen", "nitrogen", "cyanogen",
}
VANILLA_STATUSES: Set[str] = {
    "none", "burning", "freezing", "unmoving", "slow", "wet", "muddy",
    "melting", "sapped", "tarred", "overdrive", "overclock", "shielded",
    "shocked", "blasted", "corroded", "boss", "spore-slowed", "disarmed",
    "electrified", "invincible",
}
VANILLA_SOUNDS: Set[str] = {
    "none", "unset", "artillery", "back", "bang", "beam", "bigshot", "bioLoop",
    "blaster", "bolt", "boom", "break", "build", "buttonClick", "cannon",
    "chatMessage", "click", "combustion", "conveyor", "corexplode", "cutter",
    "door", "drill", "drillCharge", "drillImpact", "dullExplosion", "electricHum",
    "explosion", "explosionbig", "extractLoop", "fire", "flame", "flame2",
    "flux", "glow", "grinding", "hum", "largeCannon", "largeExplosion", "laser",
    "laserbeam", "laserbig", "laserblast", "lasercharge", "lasercharge2",
    "lasershoot", "machine", " malignShoot", "mediumCannon", " melting",
    "message", "mineDeploy", "minebeam", "missile", "missileLarge", "missileLaunch",
    "missileSmall", "missileTrail", "mud", "noammo", "pew", "place", "plantBreak",
    "plasmaboom", "plasmadrop", "pulse", "pulseBlast", "railgun", "rain",
    "release", "respawn", "rockBreak", "sap", "shield", "shockBullet", "shoot",
    "shootAlt", "shootAltLong", "shootArc", "shootBig", "shootFlame",
    "shootFlamePlasma", "shootLaser", "shootLocus", "shootMalign", "shootMeltdown",
    "shootNavanax", "shootQuad", "shootRetusa", "shoot Scatter", "shootSmite",
    "shootSnap", "shootSpectre", "shootSublimate", "shootTank", "smelter",
    "spark", "spellLoop", "splash", "spray", "steam", "stepMud", "stepWater",
    " swish", "techloop", "thruster", "titanExplosion", "torch", "tractorbeam",
    "unlock", "wave", "wind", "wind2", "wind3", "windhowl",
    # v8 renamed/added loop & shoot sounds:
    "loopAmbient", "loopBio", "loopCircuit", "loopCombustion", "loopConveyor",
    "loopCultivator", "loopCutter", "loopDifferential", "loopDrill", "loopElectricHum",
    "loopExtract", "loopFire", "loopFlux", "loopGlow", "loopGrind", "loopHum",
    "loopLaser", "loopMachine", "loopMachine2", "loopMachineSpin", "loopMalign",
    "loopMineBeam", "loopPulse", "loopRegen", "loopShield", "loopSmelter",
    "loopSpray", "loopSteam", "loopTech", "loopThoriumReactor", "loopThruster",
    "blockExplode1", "blockExplode2", "blockExplode3", "blockExplodeElectric",
    "blockExplodeElectricBig", "blockExplodeFlammable", "blockExplodeWall",
}
VANILLA_MUSICS: Set[str] = {
    "launch", "land", "menu", "editor", "game1", "game2", "game3", "game4",
    "game5", "game6", "game7", "game8", "game9", "fine", "boss1", "boss2",
}

# Environment block hierarchies (from mindustry.world.blocks.environment.*)
FLOOR_OVERLAY_TYPES: Set[str] = {
    "Floor", "ShallowLiquid", "EmptyFloor", "SteamVent", "OverlayFloor", "OreBlock",
}
CONVERTIBLE_ENV_BLOCK_TYPES: Set[str] = {
    "StaticWall", "StaticTree", "Prop", "TallBlock", "TreeBlock",
    "SeaBush", "Seaweed", "WobbleProp",
}

# Constructor defaults of convertible environment classes that differ from MemoryBlock
ENV_CLASS_DEFAULTS: Dict[str, Dict[str, Any]] = {
    "StaticWall": {
        "solid": True,
        "variants": 2,
        "placeableLiquid": True,
        "allowRectanglePlacement": True,
        "instantBuild": True,
        "ignoreBuildDarkness": True,
        "fillsTile": True,
        "obstructsLight": True,
        "forceDark": True,
    },
    "StaticTree": {
        "solid": True,
        "variants": 0,
        "placeableLiquid": True,
        "allowRectanglePlacement": True,
        "instantBuild": True,
        "ignoreBuildDarkness": True,
        "fillsTile": True,
        "obstructsLight": True,
        "forceDark": True,
    },
    "TallBlock": {
        "solid": True,
        "variants": 0,
        "clipSize": 90,
        "fillsTile": False,
        "obstructsLight": True,
        "forceDark": False,
    },
    "TreeBlock": {
        "solid": True,
        "variants": 0,
        "clipSize": 90,
        "fillsTile": False,
        "obstructsLight": True,
        "forceDark": False,
    },
    "Prop": {
        "solid": False,
        "variants": 0,
        "fillsTile": False,
        "obstructsLight": True,
        "forceDark": False,
    },
    "SeaBush": {
        "solid": False,
        "variants": 0,
        "fillsTile": False,
        "obstructsLight": False,
        "forceDark": False,
    },
    "Seaweed": {
        "solid": False,
        "variants": 0,
        "fillsTile": False,
        "obstructsLight": False,
        "forceDark": False,
    },
    "WobbleProp": {
        "solid": False,
        "variants": 0,
        "fillsTile": False,
        "obstructsLight": True,
        "forceDark": False,
    },
}

# Fields existing ONLY on environment subclasses (must be stripped when changing `type` to `MemoryBlock`)
ENV_SUBCLASS_ONLY_FIELDS: Set[str] = {
    # Prop / TallBlock / TreeBlock
    "layer", "shadowOffset", "shadowLayer", "rotationRand", "shadowAlpha", "shadow",
    # StaticWall
    "large", "autotile", "autotileMidVariants",
    # SeaBush
    "botRegion", "centerRegion", "lobesMin", "lobesMax", "botAngle", "origin",
    "sclMin", "sclMax", "magMin", "magMax", "timeRange", "spread",
    # WobbleProp
    "wscl", "wmag", "wtscl", "wmag2",
    # Occasional author typos in env blocks (e.g., `attribute` instead of `attributes` on TreeBlock)
    "attribute",
}

AUDIO_FIELD_NAMES: Set[str] = {
    "sound", "shootSound", "chargeSound", "loopSound", "ambientSound",
    "destroySound", "breakSound", "placeSound", "walkSound", "hitSound",
    "despawnSound", "lightningSound", "deflectSound", "activeSound",
    " healSound", "healSound", "mineSound", "drillSound", "flameSound",
}


# ============================================================================
# 4. Data Structures & Conversion Report
# ============================================================================

@dataclass
class SpriteRecord:
    stem: str
    orig_rel_path: str  # relative to `sprites/`, forward slashes
    abs_path: Path
    width: int
    height: int
    png_bytes: bytes
    rgba_md5: str
    dest_rel_path: str = ""  # final path relative to `sprites/`
    cropped: bool = False
    downscaled_factor: int = 1
    excluded: bool = False


@dataclass
class ContentRecord:
    ctype: str          # 'item', 'block', 'liquid', 'status', 'unit', 'weather'
    folder_name: str    # 'items', 'blocks', 'liquids', 'statuses', 'units', 'weather'
    stem: str           # filename without extension
    rel_subpath: str    # subpath inside `content/<folder_name>/`
    data: Dict[str, Any]
    orig_type: str      # original `type` (or inferred default)
    converted_to_building: bool = False
    cache_layer_bypassed: bool = False


@dataclass
class ConversionStats:
    mod_name: str = ""
    total_content_in: int = 0
    total_content_out: int = 0
    skipped_planet_sector_files: int = 0
    vanilla_overrides_patched: int = 0
    synthesized_icons: int = 0
    synthesized_outlines: int = 0
    synthesized_treads: int = 0
    converted_env_buildings: List[Tuple[str, str]] = field(default_factory=list)
    functional_static_walls_bypassed: List[str] = field(default_factory=list)
    evacuated_functional_sprites: int = 0
    evacuated_building_sprites: int = 0
    evacuated_staticwall_sprites: int = 0
    evacuated_orphan_ui_sprites: int = 0
    deduped_rgba_env_sprites: int = 0
    deduped_rgba_env_blocks: List[Tuple[str, int, int]] = field(default_factory=list)
    center_cropped_sprites: int = 0
    center_crop_bytes_px_saved: int = 0
    mt_size_buckets: int = 0
    trimmed_vent_variants: List[Tuple[str, int, int]] = field(default_factory=list)
    trimmed_floor_variants: List[Tuple[str, int, int]] = field(default_factory=list)
    scaled_env_blocks: List[Tuple[str, int]] = field(default_factory=list)
    deduplicated_assets: List[Tuple[str, str]] = field(default_factory=list)
    raw_env_sprite_count: int = 0
    raw_env_padded_area: int = 0
    raw_env_pages: int = 0
    final_env_sprite_count: int = 0
    final_env_padded_area: int = 0
    final_env_pages: int = 0
    env_limit: int = 500
    building_privilege: str = "privileged"


# ============================================================================
# 5. Core Converter Implementation
# ============================================================================

class ModToDataPatchConverter:
    def __init__(
        self,
        mod_dir: Path,
        out_zip: Path,
        env_limit: int = 500,
        hard_bypass_mode: str = "auto",  # "auto" | "scale-first" | "buildings-only"
        convert_buildings: bool = True,
        building_privilege: str = "privileged",  # "privileged" | "unprivileged"
        atlas_preview_path: Optional[Path] = None,
    ):
        self.mod_dir = mod_dir.resolve()
        self.out_zip = out_zip.resolve()
        self.env_limit = env_limit
        self.hard_bypass_mode = hard_bypass_mode
        self.convert_buildings = convert_buildings
        self.building_privilege = building_privilege
        self.atlas_preview_path = atlas_preview_path.resolve() if atlas_preview_path else None

        self.stats = ConversionStats(env_limit=env_limit, building_privilege=building_privilege)
        self.mod_name = self._detect_mod_name()
        self.stats.mod_name = self.mod_name

        self.custom_planets: Set[str] = set()
        self.sound_stems: Set[str] = set()
        self.music_stems: Set[str] = set()
        self.sprites_by_stem: Dict[str, SpriteRecord] = {}
        self.content_records: List[ContentRecord] = []
        self.vanilla_patches: Dict[str, Any] = {}
        self.client_scale_patches: Dict[str, Any] = {}

    # ------------------------------------------------------------------
    # Step 1: Mod Metadata, Audio Stems, Sprites Discovery
    # ------------------------------------------------------------------

    def _detect_mod_name(self) -> str:
        for fname in ("mod.hjson", "mod.json", "plugin.hjson", "plugin.json"):
            p = self.mod_dir / fname
            if p.is_file():
                meta = parse_hjson_file(p)
                if isinstance(meta, dict) and "name" in meta:
                    raw = str(meta["name"]).strip()
                    return raw.lower().replace(" ", "-").replace("_", "-")
        return self.mod_dir.name.lower().replace(" ", "-")

    def _collect_audio_and_sprites(self) -> None:
        # Sounds
        sounds_dir = self.mod_dir / "sounds"
        if sounds_dir.is_dir():
            for p in sorted(sounds_dir.rglob("*")):
                if p.is_file() and p.suffix.lower() in (".ogg", ".mp3"):
                    self.sound_stems.add(p.stem)

        # Music
        music_dir = self.mod_dir / "music"
        if music_dir.is_dir():
            for p in sorted(music_dir.rglob("*")):
                if p.is_file() and p.suffix.lower() in (".ogg", ".mp3"):
                    self.music_stems.add(p.stem)

        # Sprites (note: `sprites-override` is skipped by default unless unique,
        # because overriding vanilla UI/team regions like `error` or `logo` in
        # DataPatch only creates unused `dp-error` / `dp-logo` regions).
        sprites_dir = self.mod_dir / "sprites"
        if sprites_dir.is_dir():
            raw_env_items: List[Tuple[str, int, int]] = []
            for p in sorted(sprites_dir.rglob("*")):
                if not p.is_file() or p.suffix.lower() != ".png":
                    continue
                rel = p.relative_to(sprites_dir).as_posix()
                stem = p.stem
                # Strip explicit `<mod>-` prefix on sprite filename if present
                if stem.startswith(self.mod_name + "-"):
                    stem = stem[len(self.mod_name) + 1:]
                    rel = str(Path(rel).with_name(stem + ".png")).replace("\\", "/")

                raw_bytes = p.read_bytes()
                with Image.open(io.BytesIO(raw_bytes)) as im:
                    im_rgba = im.convert("RGBA")
                    w, h = im_rgba.size
                    md5 = hashlib.md5(im_rgba.tobytes()).hexdigest()

                if "blocks/environment/" in rel:
                    self.stats.raw_env_sprite_count += 1
                    self.stats.raw_env_padded_area += (w + 2) * (h + 2)
                    raw_env_items.append((stem, w, h))

                if stem in self.sprites_by_stem:
                    # Duplicate basename across folders! MapAssetsDialog rejects
                    # duplicate `name` within DataAssetType.image. Prefer non-environment
                    # path when identical or keep first deterministic hit.
                    existing = self.sprites_by_stem[stem]
                    self.stats.deduplicated_assets.append(("sprites", f"{rel} (kept {existing.orig_rel_path})"))
                    if "blocks/environment/" in existing.orig_rel_path and "blocks/environment/" not in rel:
                        # Prefer the path outside `blocks/environment/` automatically!
                        existing.orig_rel_path = rel
                        existing.dest_rel_path = rel
                    continue

                self.sprites_by_stem[stem] = SpriteRecord(
                    stem=stem,
                    orig_rel_path=rel,
                    abs_path=p,
                    width=w,
                    height=h,
                    png_bytes=raw_bytes,
                    rgba_md5=md5,
                    dest_rel_path=rel,
                )

            if raw_env_items:
                raw_pk = simulate_env_pack(raw_env_items, self.env_limit, padding=2)
                self.stats.raw_env_pages = len(raw_pk.pages)

    # ------------------------------------------------------------------
    # Step 2: Parse & Normalize Content Files
    # ------------------------------------------------------------------

    def _collect_and_parse_content(self) -> None:
        content_root = self.mod_dir / "content"
        if not content_root.is_dir():
            return

        # Pass 1: discover custom planet names from `content/planets/`
        for sub in content_root.iterdir():
            if sub.is_dir() and sub.name.lower() in ("planets", "planet"):
                for f in sorted(sub.rglob("*")):
                    if f.is_file() and f.suffix.lower() in (".hjson", ".json", ".json5"):
                        self.custom_planets.add(f.stem)
                        self.stats.skipped_planet_sector_files += 1
            elif sub.is_dir() and sub.name.lower() in UNSUPPORTED_CONTENT_FOLDERS:
                for f in sorted(sub.rglob("*")):
                    if f.is_file() and f.suffix.lower() in (".hjson", ".json", ".json5"):
                        self.stats.skipped_planet_sector_files += 1

        # Pass 2: parse supported content folders
        seen_content_stems: Set[str] = set()
        for sub in sorted(content_root.iterdir(), key=lambda x: x.name):
            if not sub.is_dir():
                continue
            key = sub.name.lower()
            if key in UNSUPPORTED_CONTENT_FOLDERS:
                continue
            if key not in CONTENT_FOLDER_MAP:
                continue
            ctype, canonical_folder = CONTENT_FOLDER_MAP[key]

            for f in sorted(sub.rglob("*")):
                if not f.is_file() or f.suffix.lower() not in (".hjson", ".json", ".json5"):
                    continue
                self.stats.total_content_in += 1
                parsed = parse_hjson_file(f)
                if not isinstance(parsed, dict):
                    continue

                stem = f.stem
                rel_sub = f.relative_to(sub).with_suffix(".json").as_posix()

                # Detect vanilla override files (no `type`/`template` + matches vanilla item/liquid/status)
                if self._is_vanilla_override(ctype, stem, parsed):
                    cleaned = self._sanitize_content_tree(parsed, ctype=ctype, is_patch=True)
                    if cleaned:
                        self.vanilla_patches[f"{ctype}.{stem}"] = cleaned
                        self.stats.vanilla_overrides_patched += 1
                    continue

                if stem in seen_content_stems:
                    self.stats.deduplicated_assets.append(("content", f"{canonical_folder}/{rel_sub}"))
                    continue
                seen_content_stems.add(stem)

                orig_type = str(parsed.get("type", self._default_type_for(ctype))).strip()
                # Capitalize short class name like ContentParser.resolve()
                if orig_type and orig_type[0].islower() and ctype != "unit":
                    orig_type = orig_type[0].upper() + orig_type[1:]

                sanitized = self._sanitize_content_tree(parsed, ctype=ctype, is_patch=False)
                self.content_records.append(
                    ContentRecord(
                        ctype=ctype,
                        folder_name=canonical_folder,
                        stem=stem,
                        rel_subpath=rel_sub,
                        data=sanitized,
                        orig_type=orig_type,
                    )
                )

    def _default_type_for(self, ctype: str) -> str:
        return {
            "block": "Block",
            "item": "Item",
            "liquid": "Liquid",
            "status": "StatusEffect",
            "unit": "UnitType",
            "weather": "Weather",
        }.get(ctype, "Content")

    def _is_vanilla_override(self, ctype: str, stem: str, data: Dict[str, Any]) -> bool:
        if "type" in data or "template" in data:
            return False
        if ctype == "item" and stem in VANILLA_ITEMS:
            return True
        if ctype == "liquid" and stem in VANILLA_LIQUIDS:
            return True
        if ctype == "status" and stem in VANILLA_STATUSES:
            return True
        return False

    def _sanitize_content_tree(self, node: Any, ctype: str, is_patch: bool, parent_key: str = "", in_weapon: bool = False) -> Any:
        """
        Recursively rewrites mod-specific constructs into DataPatch-safe JSON:
          - Removes `research` (disallowed when `allowPatching = false`)
          - Filters unknown mod planets from `shownPlanets`
          - Removes invalid `planet` field on non-Sector/Planet content
          - Rewrites `<mod>-<x>` -> `dp-<x>` (stripping `<mod>-` on `weapon.name`
            because `ContentParser` prepends `currentMod.name + "-"` = `"dp-"`)
          - Rewrites custom sound/music stems -> `dp-<stem_underscored>`
        """
        if isinstance(node, dict):
            out: Dict[str, Any] = {}
            for k, v in node.items():
                if not is_patch and k == "research":
                    continue
                if k == "planet" and ctype in ("block", "item", "liquid", "status", "unit", "weather"):
                    continue
                if k == "shownPlanets":
                    planets = v if isinstance(v, list) else [v]
                    valid = [str(p) for p in planets if str(p) in VANILLA_PLANETS and str(p) not in self.custom_planets]
                    if valid:
                        out[k] = valid
                    # If empty, omit `shownPlanets` completely so content is buildable on all planets!
                    continue

                child_in_weapon = in_weapon or (parent_key == "weapons")
                if child_in_weapon and k == "name" and isinstance(v, str):
                    # Weapon parser automatically prefixes `dp-`!
                    wname = v
                    if wname.startswith(self.mod_name + "-"):
                        wname = wname[len(self.mod_name) + 1:]
                    elif wname.startswith("dp-"):
                        wname = wname[3:]
                    out[k] = wname
                    continue

                if k == "basePrefix" and isinstance(v, str):
                    if v == self.mod_name + "-":
                        out[k] = ""
                    else:
                        out[k] = self._rewrite_mod_prefix(v)
                    continue

                if k in AUDIO_FIELD_NAMES:
                    out[k] = self._rewrite_audio_ref(v)
                    continue

                out[k] = self._sanitize_content_tree(
                    v, ctype=ctype, is_patch=is_patch, parent_key=k, in_weapon=child_in_weapon
                )
            return out

        if isinstance(node, list):
            return [
                self._sanitize_content_tree(item, ctype=ctype, is_patch=is_patch, parent_key=parent_key, in_weapon=in_weapon)
                for item in node
            ]

        if isinstance(node, str):
            return self._rewrite_mod_prefix(node)

        return node

    def _rewrite_mod_prefix(self, s: str) -> str:
        prefix = self.mod_name + "-"
        if prefix not in s:
            return s
        # Replace token-boundary `<mod>-` with `dp-` (handles `asthosus-foo`,
        # `asthosus-foo/20`, `[asthosus-foo]`, etc.)
        return re.sub(rf"(?<![A-Za-z0-9_-]){re.escape(self.mod_name)}-", "dp-", s)

    def _rewrite_audio_ref(self, val: Any) -> Any:
        if isinstance(val, list):
            return [self._rewrite_audio_ref(x) for x in val]
        if not isinstance(val, str):
            return val
        s = val.strip()
        if s in VANILLA_SOUNDS or s in VANILLA_MUSICS or s.startswith("dp-"):
            return s
        if s.startswith(self.mod_name + "-"):
            s = s[len(self.mod_name) + 1:]
        if s in self.sound_stems or s in self.music_stems:
            return "dp-" + s.replace(" ", "_")
        return val

    # ------------------------------------------------------------------
    # Step 3: 7-Layer 500x500 Environment Atlas Bypass Pipeline
    # ------------------------------------------------------------------

    def _count_existing_variant_sprites(self, stem: str) -> int:
        v = 0
        while f"{stem}{v + 1}" in self.sprites_by_stem:
            v += 1
        return v

    def _is_functional_or_destructible_env_block(self, rec: ContentRecord) -> Tuple[bool, str]:
        """
        Determines whether an environment block is functional or destructible:
          - Explicit `destructible: true` or `update: true` -> destructible/functional
          - Non-empty `itemDrop` (e.g. ore-bearing StaticWall for BeamDrill) -> functional
          - Non-empty `attributes` dict (e.g. attribute wall for WallCrafter) -> functional
        """
        d = rec.data
        if d.get("destructible") is True:
            return True, "destructible"
        if d.get("update") is True:
            return True, "update"
        if d.get("itemDrop") not in (None, "", "air"):
            return True, "itemDrop"
        attrs = d.get("attributes")
        if isinstance(attrs, dict) and any(float(v) != 0.0 for v in attrs.values() if isinstance(v, (int, float))):
            return True, "attributes"
        return False, ""

    def _convert_env_block_to_privileged_building(self, rec: ContentRecord) -> None:
        """
        Layer 1: Converts a non-functional, non-destructible, non-floor/overlay
        environment block into an unhittable, unbreakable, non-derelictable
        privileged `MemoryBlock` building (`memoryCapacity: 0`).
        """
        orig_type = rec.orig_type
        defaults = ENV_CLASS_DEFAULTS.get(orig_type, ENV_CLASS_DEFAULTS["Prop"])
        d = rec.data

        # Determine effective variant count accurately
        disk_variants = self._count_existing_variant_sprites(rec.stem)
        if "variants" in d:
            decl_v = int(d["variants"])
        else:
            decl_v = int(defaults["variants"])

        if decl_v > 0 and disk_variants > 0:
            eff_variants = min(decl_v, disk_variants)
        elif decl_v > 0 and disk_variants == 0 and rec.stem in self.sprites_by_stem:
            eff_variants = 0
        elif decl_v == 0 and rec.stem not in self.sprites_by_stem and disk_variants > 0:
            eff_variants = disk_variants
        else:
            eff_variants = decl_v

        solid = bool(d.get("solid", defaults["solid"]))
        fills_tile = bool(d.get("fillsTile", defaults["fillsTile"]))
        obstructs_light = bool(d.get("obstructsLight", defaults["obstructsLight"]))
        force_dark = bool(d.get("forceDark", defaults["forceDark"]))

        # Strip subclass-only fields that don't exist on `MemoryBlock` / `Block`
        for bad_key in list(d.keys()):
            if bad_key in ENV_SUBCLASS_ONLY_FIELDS:
                del d[bad_key]

        # Note on `customShadow`: TallBlock/TreeBlock set `customShadow = true`,
        # which expects `<name>-shadow1..N` or `<name>-shadow`. Keep `customShadow`
        # ONLY if valid shadow sprites actually exist; otherwise let standard tile
        # shadows apply cleanly without missing region lookups.
        if orig_type in ("TallBlock", "TreeBlock") or d.get("customShadow") is True:
            if eff_variants > 0:
                has_all_shadows = all(
                    f"{rec.stem}-shadow{i}" in self.sprites_by_stem
                    for i in range(1, eff_variants + 1)
                )
            else:
                has_all_shadows = f"{rec.stem}-shadow" in self.sprites_by_stem
            d["customShadow"] = bool(has_all_shadows)

        # Apply unhittable MemoryBlock configuration (`privileged` by default, or `unprivileged` via CLI)
        is_priv = self.building_privilege == "privileged"
        d["type"] = "MemoryBlock"
        d["privileged"] = is_priv
        d["memoryCapacity"] = 0
        d["destructible"] = True
        d["targetable"] = False
        d["underBullets"] = True
        d["breakable"] = False
        d["unitMoveBreakable"] = False
        d["alwaysReplace"] = False
        d["replaceable"] = False
        d["rebuildable"] = False
        d["drawTeamOverlay"] = False
        d["drawDisabled"] = False
        d["enableDrawStatus"] = False
        d["canOverdrive"] = False
        d["outlineIcon"] = False
        d["drawCached"] = True
        d["drawDynamic"] = False
        if not is_priv:
            d["health"] = 2147483647
            d["armor"] = 1000000000
            d["absorbLasers"] = False
        d["solid"] = solid
        d["variants"] = eff_variants
        d["fillsTile"] = fills_tile
        d["obstructsLight"] = obstructs_light
        d["forceDark"] = force_dark
        d.setdefault("buildVisibility", "editorOnly")

        if "clipSize" not in d and "clipSize" in defaults:
            d["clipSize"] = defaults["clipSize"]
        for opt_k in ("placeableLiquid", "allowRectanglePlacement", "instantBuild", "ignoreBuildDarkness"):
            if opt_k in defaults and opt_k not in d:
                d[opt_k] = defaults[opt_k]

        rec.converted_to_building = True
        self.stats.converted_env_buildings.append((rec.stem, orig_type))

    def _apply_environment_atlas_bypasses(self) -> None:
        block_records: Dict[str, ContentRecord] = {
            r.stem: r for r in self.content_records if r.ctype == "block"
        }

        # ---- Layer 1 & Layer 3 on Block Definitions ----
        for rec in block_records.values():
            if rec.orig_type in CONVERTIBLE_ENV_BLOCK_TYPES:
                is_func, _reason = self._is_functional_or_destructible_env_block(rec)
                if not is_func and self.convert_buildings:
                    self._convert_env_block_to_privileged_building(rec)
                elif rec.orig_type in ("StaticWall", "StaticTree") and self.hard_bypass_mode != "buildings-only":
                    # Layer 3: Functional StaticWall (`itemDrop` / `attributes`)!
                    # Keep `type: StaticWall` so BeamDrill, WallCrafter, wallOre, and
                    # collideTerrain work 100% natively, while setting `cacheLayer: normal`
                    # so BlockRenderer & EditorSpriteCache draw it from 4096x4096 patchAtlas!
                    rec.data["cacheLayer"] = "normal"
                    rec.cache_layer_bypassed = True
                    self.stats.functional_static_walls_bypassed.append(rec.stem)

            elif rec.orig_type == "Floor" and self.hard_bypass_mode != "buildings-only":
                # Layer 4a: Prevent Mindustry's upstream `regenerateContentSprites` bug where
                # `Floor.createIcons` writes `generated/<hash>/<floor>-edge.png` onto `patchAtlas`,
                # causing `FloorRenderBatch` to draw magenta `env-error` borders around every floor!
                edge_sp = self.sprites_by_stem.get(f"{rec.stem}-edge")
                has_env_edge = edge_sp is not None and "blocks/environment/" in edge_sp.orig_rel_path
                if not has_env_edge and "drawEdgeOut" not in rec.data:
                    rec.data["drawEdgeOut"] = False

        # ---- Map Every Sprite Currently in `blocks/environment/` to Its Owner Block ----
        # Determine exact set of sprite stems that MUST stay on `FloorRenderer.texture` (`data-patch-reserved-env`)
        required_env_stems: Dict[str, Tuple[ContentRecord, str]] = {}  # sprite_stem -> (owner_rec, role)

        for rec in block_records.values():
            if rec.converted_to_building or rec.cache_layer_bypassed:
                continue
            btype = rec.orig_type
            # ONLY Floor/Overlay subclasses OR StaticWall/StaticTree still on CacheLayer.walls
            # ever enter FloorRenderer.FloorRenderBatch!
            needs_floor_atlas = (
                btype in FLOOR_OVERLAY_TYPES
                or (
                    btype in ("StaticWall", "StaticTree")
                    and str(rec.data.get("cacheLayer", "walls")) == "walls"
                )
            )
            if not needs_floor_atlas:
                continue

            for sp_stem in self._expected_env_sprite_stems(rec):
                if sp_stem in self.sprites_by_stem:
                    required_env_stems[sp_stem] = (rec, btype)

        # ---- Evacuate Non-FloorRenderer Sprites Out of `blocks/environment/` ----
        block_stems_desc = sorted(block_records.keys(), key=len, reverse=True)

        for sp in self.sprites_by_stem.values():
            if "blocks/environment/" not in sp.dest_rel_path:
                continue
            if sp.stem in required_env_stems:
                continue

            # Classify why this sprite is being evacuated for detailed reporting
            owner: Optional[ContentRecord] = None
            for bstem in block_stems_desc:
                if (
                    sp.stem == bstem
                    or sp.stem.startswith(bstem + "-")
                    or (sp.stem.startswith(bstem) and sp.stem[len(bstem):].isdigit())
                ):
                    owner = block_records[bstem]
                    break

            if self.hard_bypass_mode == "buildings-only":
                # In strict buildings-only baseline mode, only evacuate converted buildings
                if owner is not None and owner.converted_to_building:
                    sp.dest_rel_path = f"blocks/env-buildings/{sp.stem}.png"
                    self.stats.evacuated_building_sprites += 1
                continue

            if owner is not None and owner.converted_to_building:
                sp.dest_rel_path = f"blocks/env-buildings/{sp.stem}.png"
                self.stats.evacuated_building_sprites += 1
            elif owner is not None and owner.cache_layer_bypassed:
                sp.dest_rel_path = f"blocks/env-walls/{sp.stem}.png"
                self.stats.evacuated_staticwall_sprites += 1
            elif owner is not None and owner.orig_type not in FLOOR_OVERLAY_TYPES:
                # Layer 2: Functional / destructible / CacheLayer.normal block sprite!
                sp.dest_rel_path = f"blocks/env-functional/{sp.stem}.png"
                self.stats.evacuated_functional_sprites += 1
            else:
                # Layer 4b: Orphaned / typo / -preview / -ui / -full sprite!
                sp.dest_rel_path = f"blocks/env-orphans/{sp.stem}.png"
                self.stats.evacuated_orphan_ui_sprites += 1

        if self.hard_bypass_mode == "buildings-only":
            self._finalize_env_pack_order(interleave_barriers=False)
            return

        # ---- Layer 5a: Lossless RGBA-Identical Variant Deduplication ----
        # Mods often duplicate `<floor>1..5.png` as `<floor>7..11.png` or `<vent>1.png` as `<vent>2.png`.
        # Trimming byte-identical trailing RGBA variants saves thousands of `500x500` pixels with ZERO art loss!
        self._deduplicate_identical_env_variants(block_records)

        # ---- Layer 5b: Symmetric Center-Anchored Alpha Cropping on SteamVent / OverlayFloor / OreBlock ----
        for sp_stem, (owner_rec, btype) in list(required_env_stems.items()):
            if btype in ("SteamVent", "OverlayFloor", "OreBlock"):
                sp = self.sprites_by_stem[sp_stem]
                if "blocks/environment/" in sp.dest_rel_path:
                    self._symmetric_center_crop(sp)

        # Check if Layers 1-5 already fit inside a single `env_limit x env_limit` page!
        _, pk = self._pack_current_env_sprites()
        if len(pk.pages) <= 1:
            self._finalize_env_pack_order(interleave_barriers=True)
            return

        # ---- Layer 6 & Layer 7: Escalating Hard Compression Until `pages <= 1` ----
        if self.hard_bypass_mode == "scale-first":
            self._apply_scale_downsampling_until_fit(block_records)
            _, pk = self._pack_current_env_sprites()
            if len(pk.pages) > 1:
                self._trim_vent_variants_until_fit(block_records)
                self._trim_floor_variants_until_fit(block_records)
        else:
            # Default "auto": preserve 100% crisp 1:1 native pixel art first by
            # consolidating redundant SteamVent variants (2 -> 1) and excess Floor
            # variants; use `TextureRegion.scale` downsampling if still > 1 page!
            self._trim_vent_variants_until_fit(block_records)
            _, pk = self._pack_current_env_sprites()
            if len(pk.pages) > 1:
                self._trim_floor_variants_until_fit(block_records)
            _, pk = self._pack_current_env_sprites()
            if len(pk.pages) > 1:
                self._apply_scale_downsampling_until_fit(block_records)

        self._finalize_env_pack_order(interleave_barriers=True)

    def _deduplicate_identical_env_variants(self, block_records: Dict[str, ContentRecord]) -> None:
        """
        Detects trailing `<stem>k.png` environment variants whose RGBA pixels are
        100% byte-for-byte identical to an earlier variant `<stem>1..(k-1).png`
        (e.g. `arcana-vent2 == arcana-vent1`, `coarse-dirt7..11 == coarse-dirt1..5`)
        and relocates those duplicate PNGs out of `blocks/environment/` into `patchAtlas`
        with zero loss of unique artwork.
        """
        for rec in sorted(block_records.values(), key=lambda r: r.stem):
            if rec.converted_to_building or rec.cache_layer_bypassed:
                continue
            if rec.orig_type not in FLOOR_OVERLAY_TYPES or rec.data.get("autotile"):
                continue
            default_v = 2 if rec.orig_type == "SteamVent" else 3
            v_count = int(rec.data.get("variants", default_v))
            if v_count <= 1:
                continue
            sps = [self.sprites_by_stem.get(f"{rec.stem}{i}") for i in range(1, v_count + 1)]
            if any(sp is None for sp in sps):
                continue

            # Find longest prefix ending at `new_v` where all trailing `new_v+1..v_count`
            # already appear in `1..new_v` by exact RGBA hash!
            new_v = v_count
            while new_v > 1:
                cand_sp = sps[new_v - 1]
                assert cand_sp is not None
                earlier_hashes = {sps[j].rgba_md5 for j in range(new_v - 1) if sps[j] is not None}
                if cand_sp.rgba_md5 in earlier_hashes:
                    new_v -= 1
                else:
                    break

            if new_v < v_count:
                rec.data["variants"] = new_v
                for drop_idx in range(new_v + 1, v_count + 1):
                    dsp = self.sprites_by_stem.get(f"{rec.stem}{drop_idx}")
                    if dsp and "blocks/environment/" in dsp.dest_rel_path:
                        dsp.dest_rel_path = f"blocks/env-dedup/{dsp.stem}.png"
                        self.stats.deduped_rgba_env_sprites += 1
                self.stats.deduped_rgba_env_blocks.append((rec.stem, v_count, new_v))

    def _expected_env_sprite_stems(self, rec: ContentRecord) -> List[str]:
        """Returns exact atlas region stems loaded by `Floor` / `SteamVent` / `OverlayFloor` / `OreBlock` / `StaticWall`."""
        d = rec.data
        btype = rec.orig_type
        stems: List[str] = []

        default_variants = 2 if btype in ("SteamVent", "StaticWall") else (0 if btype == "StaticTree" else 3)
        variants = int(d.get("variants", default_variants))
        if d.get("autotile") is True and btype in FLOOR_OVERLAY_TYPES:
            variants = 0

        if variants > 0:
            for i in range(1, variants + 1):
                stems.append(f"{rec.stem}{i}")
        else:
            stems.append(rec.stem)

        # Tiling variants on Floor (`<name>-tile1..N`)
        tiling_v = int(d.get("tilingVariants", 0))
        for i in range(1, tiling_v + 1):
            stems.append(f"{rec.stem}-tile{i}")

        # Autotile regions (`<name>-0..46` + mid variants)
        if d.get("autotile") is True:
            for i in range(47):
                stems.append(f"{rec.stem}-{i}")
            mid_v = int(d.get("autotileMidVariants", 1))
            for i in range(1, mid_v):
                stems.append(f"{rec.stem}-mid-{i + 1}")

        # Explicit `-edge` or `-large`
        if btype in FLOOR_OVERLAY_TYPES and f"{rec.stem}-edge" in self.sprites_by_stem:
            stems.append(f"{rec.stem}-edge")
        if btype == "StaticWall" and f"{rec.stem}-large" in self.sprites_by_stem:
            stems.append(f"{rec.stem}-large")

        return stems

    def _symmetric_center_crop(self, sp: SpriteRecord) -> None:
        """
        Symmetrically crops transparent margins around the exact geometric center
        `(w/2, h/2)` of a sprite drawn via `Draw.rect(region, cx, cy)`.
        Because `Draw.rect` centers `region` at `(cx, cy)` with world dimensions
        `region.width * Draw.scl` by `region.height * Draw.scl`, symmetric even-pixel
        cropping around the center leaves every non-transparent pixel at the EXACT
        same subpixel world coordinate with zero resampling!
        """
        with Image.open(io.BytesIO(sp.png_bytes)) as im:
            rgba = im.convert("RGBA")
            w, h = rgba.size
            bbox = rgba.split()[3].getbbox()
            if not bbox:
                return
            cx, cy = w / 2.0, h / 2.0
            half_w = int(-(-max(cx - bbox[0], bbox[2] - cx) // 1))  # ceil
            half_h = int(-(-max(cy - bbox[1], bbox[3] - cy) // 1))
            # Keep even dimensions so `(w - cw) / 2` is an exact integer pixel offset!
            cw = min(w, max(2, half_w * 2))
            ch = min(h, max(2, half_h * 2))
            if (w - cw) % 2 != 0:
                cw = min(w, cw + 1)
            if (h - ch) % 2 != 0:
                ch = min(h, ch + 1)
            if cw >= w and ch >= h:
                return

            left = (w - cw) // 2
            top = (h - ch) // 2
            cropped = rgba.crop((left, top, left + cw, top + ch))
            buf = io.BytesIO()
            cropped.save(buf, format="PNG", optimize=True)

            old_area = (w + 2) * (h + 2)
            new_area = (cw + 2) * (ch + 2)
            sp.png_bytes = buf.getvalue()
            sp.width = cw
            sp.height = ch
            sp.cropped = True
            self.stats.center_cropped_sprites += 1
            self.stats.center_crop_bytes_px_saved += (old_area - new_area)

    def _current_env_sprites(self) -> List[SpriteRecord]:
        return [
            sp for sp in self.sprites_by_stem.values()
            if not sp.excluded and "blocks/environment/" in sp.dest_rel_path
        ]

    def _pack_current_env_sprites(self) -> Tuple[List[Tuple[str, int, int]], ArcGuillotinePacker]:
        items = [(sp.stem, sp.width, sp.height) for sp in self._current_env_sprites()]
        return find_optimal_guillotine_order(items, self.env_limit, padding=2)

    def _trim_vent_variants_until_fit(self, block_records: Dict[str, ContentRecord]) -> None:
        """
        Layer 6a: Consolidates multi-variant large `SteamVent`s from `variants: N` -> `1`
        (largest sprite area first), checking the exact Guillotine packer after EACH vent
        so we stop the instant the environment atlas fits on 1 page!
        """
        vents = [
            r for r in block_records.values()
            if r.orig_type == "SteamVent" and int(r.data.get("variants", 2)) > 1
        ]
        # Sort largest vent sprites first (96x96 vents save ~9,600 px^2 each; 32x32 geysers only ~1,156 px^2)
        def vent_sort_key(r: ContentRecord) -> Tuple[int, str]:
            sp1 = self.sprites_by_stem.get(f"{r.stem}1")
            area = (sp1.width * sp1.height) if sp1 else 0
            return (-area, r.stem)

        for vent in sorted(vents, key=vent_sort_key):
            _, pk = self._pack_current_env_sprites()
            if len(pk.pages) <= 1:
                return
            old_v = int(vent.data.get("variants", 2))
            while int(vent.data.get("variants", old_v)) > 1:
                cur_v = int(vent.data.get("variants", old_v))
                drop_sp = self.sprites_by_stem.get(f"{vent.stem}{cur_v}")
                vent.data["variants"] = cur_v - 1
                if drop_sp and "blocks/environment/" in drop_sp.dest_rel_path:
                    drop_sp.dest_rel_path = f"blocks/env-trimmed/{drop_sp.stem}.png"
                _, pk = self._pack_current_env_sprites()
                if len(pk.pages) <= 1:
                    break
            new_v = int(vent.data["variants"])
            if new_v != old_v:
                self.stats.trimmed_vent_variants.append((vent.stem, old_v, new_v))

    def _trim_floor_variants_until_fit(self, block_records: Dict[str, ContentRecord]) -> None:
        """
        Layer 6b: Greedily trims excess variants one sprite at a time from whichever
        `Floor` / `OverlayFloor` / `OreBlock` currently has the HIGHEST variant count
        (e.g. `coarse-dirt` 11 -> 10 -> 9..., `arcane-tendrils` 9 -> 8..., etc.),
        halting at the exact single variant removal where `pages == 1`!
        """
        candidates = [
            r for r in block_records.values()
            if r.orig_type in ("Floor", "ShallowLiquid", "OverlayFloor", "OreBlock")
            and not r.data.get("autotile")
        ]
        orig_variants: Dict[str, int] = {
            r.stem: int(r.data.get("variants", 3)) for r in candidates
        }

        while True:
            _, pk = self._pack_current_env_sprites()
            if len(pk.pages) <= 1:
                break
            # Pick candidate with highest current variant count (> 1), tie-breaking by largest sprite area
            reducibles = [r for r in candidates if int(r.data.get("variants", 3)) > 1]
            if not reducibles:
                break
            reducibles.sort(
                key=lambda r: (
                    -int(r.data.get("variants", 3)),
                    -(self.sprites_by_stem[f"{r.stem}1"].width * self.sprites_by_stem[f"{r.stem}1"].height)
                    if f"{r.stem}1" in self.sprites_by_stem else 0,
                    r.stem,
                )
            )
            target = reducibles[0]
            cur_v = int(target.data.get("variants", 3))
            drop_sp = self.sprites_by_stem.get(f"{target.stem}{cur_v}")
            target.data["variants"] = cur_v - 1
            if drop_sp and "blocks/environment/" in drop_sp.dest_rel_path:
                drop_sp.dest_rel_path = f"blocks/env-trimmed/{drop_sp.stem}.png"

        for r in candidates:
            new_v = int(r.data.get("variants", orig_variants[r.stem]))
            if new_v != orig_variants[r.stem]:
                self.stats.trimmed_floor_variants.append((r.stem, orig_variants[r.stem], new_v))

    def _apply_scale_downsampling_until_fit(self, block_records: Dict[str, ContentRecord]) -> None:
        """
        Layer 7: Downsamples multi-tile `SteamVent` (and if still needed, `OverlayFloor` /
        `Floor`) PNGs by 2x and emits `TextureRegion.scale = 2.0` client DataPatches so
        `FloorRenderBatch` (`region.width * Draw.scl * region.scale`) renders them at
        exact full world size while consuming ~73% less `500x500` atlas space!
        """
        # Order: large SteamVents first, then OverlayFloors, then Floors
        priority_order = [
            r for r in sorted(block_records.values(), key=lambda x: x.stem)
            if r.orig_type in ("SteamVent", "OverlayFloor", "Floor", "ShallowLiquid")
            and not r.converted_to_building
        ]
        priority_order.sort(
            key=lambda r: (
                0 if r.orig_type == "SteamVent" else (1 if r.orig_type == "OverlayFloor" else 2),
                r.stem,
            )
        )

        for rec in priority_order:
            _, pk = self._pack_current_env_sprites()
            if len(pk.pages) <= 1:
                return

            default_v = 2 if rec.orig_type == "SteamVent" else 3
            v_count = int(rec.data.get("variants", default_v))
            sp_stems = [f"{rec.stem}{i}" for i in range(1, v_count + 1)] if v_count > 0 else [rec.stem]
            env_sps = [
                self.sprites_by_stem[s] for s in sp_stems
                if s in self.sprites_by_stem and "blocks/environment/" in self.sprites_by_stem[s].dest_rel_path
            ]
            if not env_sps or any(sp.width < 32 or sp.height < 32 or sp.downscaled_factor > 1 for sp in env_sps):
                continue

            for idx, sp in enumerate(env_sps):
                nw, nh = max(1, sp.width // 2), max(1, sp.height // 2)
                with Image.open(io.BytesIO(sp.png_bytes)) as im:
                    resized = im.convert("RGBA").resize((nw, nh), Image.Resampling.BOX)
                    buf = io.BytesIO()
                    resized.save(buf, format="PNG", optimize=True)
                sp.png_bytes = buf.getvalue()
                sp.width, sp.height = nw, nh
                sp.downscaled_factor = 2
                if v_count > 0:
                    self.client_scale_patches[f"block.dp-{rec.stem}.variantRegions.{idx}.scale"] = 2.0
                if idx == 0:
                    self.client_scale_patches[f"block.dp-{rec.stem}.region.scale"] = 2.0

            self.stats.scaled_env_blocks.append((rec.stem, 2))

    def _finalize_env_pack_order(self, interleave_barriers: bool = True) -> None:
        ordered_items, final_pk = self._pack_current_env_sprites()
        self.stats.final_env_sprite_count = len(ordered_items)
        self.stats.final_env_padded_area = sum((w + 2) * (h + 2) for _, w, h in ordered_items)
        self.stats.final_env_pages = len(final_pk.pages)

        if not interleave_barriers or not ordered_items:
            for rank, (stem, _w, _h) in enumerate(ordered_items):
                sp = self.sprites_by_stem[stem]
                sp.dest_rel_path = f"blocks/environment/r{rank:04d}/{sp.stem}.png"
            if self.atlas_preview_path is not None:
                self._render_atlas_preview(final_pk, self.atlas_preview_path)
            return

        # Multithreaded `Vars.mainExecutor` Barrier Interleaving:
        # `DataImagePacker.pack` submits `toPack` (sorted by `image.path`) to an
        # asynchronous thread pool (`Vars.mainExecutor`) and routes an image to
        # `envPacker` iff `image.path.contains("blocks/environment/")`.
        # Because small 32x32 PNGs finish `Pixmaps.antialias` ~9x faster than 96x96
        # PNGs, contiguous env paths race across threads and fragment Guillotine splits!
        # Grouping env sprites into uniform `(w, h)` buckets (`s00/blocks/environment/`,
        # `s02/blocks/environment/`, ...) and interleaving heavy `patchAtlas` sprites
        # (`s01-barrier/`, `s03-barrier/`, ...) between buckets makes every bucket
        # 100% permutation-invariant internally AND barrier-isolated across threads!
        buckets: List[List[Tuple[str, int, int]]] = []
        for item in ordered_items:
            if not buckets or (buckets[-1][0][1], buckets[-1][0][2]) != (item[1], item[2]):
                buckets.append([item])
            else:
                buckets[-1].append(item)

        self.stats.mt_size_buckets = len(buckets)
        for b_idx, bucket in enumerate(buckets):
            stage_prefix = f"s{2 * b_idx:03d}"
            for rank, (stem, _w, _h) in enumerate(bucket):
                sp = self.sprites_by_stem[stem]
                sp.dest_rel_path = f"{stage_prefix}/blocks/environment/r{rank:04d}/{sp.stem}.png"

        # Distribute all non-environment `patchAtlas` sprites across the `(len(buckets) - 1)`
        # inter-bucket barriers, prioritizing largest pixel-area sprites into the earliest
        # barriers (right after 96x96 SteamVents) for maximum CPU decode barrier duration!
        # Keep exact filename (`{sp.stem}.png`) in a rank subdirectory so `image.name == sp.stem`!
        num_gaps = max(0, len(buckets) - 1)
        if num_gaps > 0:
            non_env_sps = [
                sp for sp in self.sprites_by_stem.values()
                if not sp.excluded and "blocks/environment/" not in sp.dest_rel_path
            ]
            non_env_sps.sort(key=lambda sp: (-(sp.width * sp.height), sp.stem))
            for idx, sp in enumerate(non_env_sps):
                gap_idx = idx % num_gaps
                barrier_prefix = f"s{2 * gap_idx + 1:03d}-barrier"
                sp.dest_rel_path = f"{barrier_prefix}/r{idx:04d}/{sp.stem}.png"

        if self.atlas_preview_path is not None:
            self._render_atlas_preview(final_pk, self.atlas_preview_path)

    def _render_atlas_preview(self, packer: ArcGuillotinePacker, out_path: Path) -> None:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        canvas = Image.new("RGBA", (self.env_limit, self.env_limit), (18, 20, 28, 255))
        draw = ImageDraw.Draw(canvas)
        # Draw usable root boundary (padding=2)
        draw.rectangle(
            [2, 2, self.env_limit - 3, self.env_limit - 3],
            outline=(70, 85, 115, 255),
            width=1,
        )
        if packer.pages:
            page0 = packer.pages[0]
            for pr in page0.rects:
                sp = self.sprites_by_stem.get(pr.name)
                if sp is not None:
                    with Image.open(io.BytesIO(sp.png_bytes)) as sp_im:
                        rgba = sp_im.convert("RGBA")
                        canvas.alpha_composite(rgba, (pr.x, pr.y))
                draw.rectangle(
                    [pr.x, pr.y, pr.x + pr.width - 1, pr.y + pr.height - 1],
                    outline=(0, 255, 180, 90),
                    width=1,
                )
        canvas.save(out_path, format="PNG")

    # ------------------------------------------------------------------
    # Step 4: Bundle Rewriting & Final Zip Assembly
    # ------------------------------------------------------------------

    def _rewrite_bundle_text(self, text: str) -> str:
        """
        Rewrites `<ctype>.<modname>-<id>.<prop>` -> `<ctype>.dp-<id>.<prop>` in
        Java `.properties` files while preserving comments and custom keys.
        """
        lines_out: List[str] = []
        pattern = re.compile(
            rf"^(\s*(?:block|item|liquid|unit|status|weather)\.){re.escape(self.mod_name)}-([A-Za-z0-9_-]+)(\.[A-Za-z0-9_.-]+\s*[=:])"
        )
        for line in text.splitlines():
            # Skip planet/sector bundle keys only? Keeping them is harmless in Core.bundle,
            # while rewriting supported content keys makes all localized names/descriptions work!
            rewritten = pattern.sub(r"\1dp-\2\3", line)
            lines_out.append(rewritten)
        return "\n".join(lines_out) + ("\n" if text.endswith("\n") else "")

    _VANILLA_HELPER_PNGS_B64: Dict[str, str] = {
        "block-1": "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAq0lEQVR42t3XUQqAIAwGYE8cHaFjRM8doOeeuplRYJQwdbLtHz0MfAj9yE1nmJc1bvsBizCMU0QibgAS8QBQiA8gR1xjiWABEkI64AAKEawWpxBdAOp3mgBqWa0KaC0tFQC3vkUBtUU4CDagdfLe77oAnG0SB3Cz/H8A+BaYJyG8DF0cRC6OYheXkYvrWL0hgbdk1o0pCZBElN4dRYBG5AhzQI6AAN4IGCAhTrs4Z350exVBAAAAAElFTkSuQmCC",
        "block-2": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAABaUlEQVR42u2bMQ7CMAxFe2LEETgGYuYAzEzcrAgkUKmqJiH+jpP/hwxdUvfVseMfZzpfrvPt/qAd0+F4mpkhvAEwQ/gCYIXwA2ALwuu551EMYAmh94/PgbAJ4ANhpFHsASOO7BiQmgD1N6zmLXl3NgArY1NByWpeUwBWxuamJqRHFQOwMrY0P6M8qhmAVnk+1BLwhhAyCHpBMM8ClmkQDQGSBlFr1DvGuAKwqti6BGBdtnYFAFW7dwEALWCEBuCl4oQE4C1lhQJQ+xGeEMwBWBnvBSEEAI+5YFthdJlr4UlQRajGYIRXldYD1eVwa5WnJJZAFKF/DEWm1lp74QBaKz5NAXgUVgKgJRAcQPdBkD4NaiOkrbCKIZXDEkQkiUkUlSyugxEdjelwVMfj1A0S1C0y1E1S9G1y9I2S9K2yapZma5envzChKzMDQti7ErgLYAQIqXuRSQCjjTUEOgBrCJQAlhBoAXwgPAERy1arBo/qKgAAAABJRU5ErkJggg==",
        "block-3": "iVBORw0KGgoAAAANSUhEUgAAAGAAAABgCAYAAADimHc4AAACM0lEQVR42u3dMVIEIRBG4Tmx5RH2GJaxBzDeyJutZWBiMotA/w/mBVQZWQNfLfQMTXO8vX88Pu9ftlA7Xl5vDxHCACIAAEQAAIgAABABACACAEAEAMBfhJ+/bedtKMAvgm0OggBhhMPBzyJ0AZz986rOpQcxAvDsHFc1KOm5vBSgZZWvHJR0RFMCQB18KkIMgDgfJ6aiCEBqUSSElXGAVHhHCSujAKkYmxTbxwBmhnK00LJlHEoARkUQlHm8p2/lACM7S4lkevpY+iI2o7OzEGY+T+mLWEVnRyMkn2dpAFpbAmD3LcRtANJwVaEyDoDw6xn5qWErgAqE6o99KADCGlLRh8sAzNqjECC8iF4aoGceHjV/X3oR7t10SeEv9SY8e9OFMvgxAMLmPeUZo5lxZISqZ4unJhIRKp8JkRu66o4YPjdUAAEEEGAjgJXSUlDnA2ak9BHTDGckJww7H0A+yFGxeYQ4H1DxcSuZZvif/iOSc6mDP2NABdgdwCkoPAW5CAMWYcNQQBjqi5ifIvwUIYAAAgjglqRbkm7Km5ZiWoqJWaYmmppocq7p6aane0DDI0oCeEgPfk6Yekz1MgAe1LZUwb6lCizWYbma/cvVWLApWLDJkmXhkmUW7YMV7bNspYVbLdxq6WKLd1u82/L1MAAvcPAKkz2vMPESH8AlPl5jBbjGylb0MU6E8FWGIkAARHi+tdzH3ARga29nCAKEEQQIIwgQRhAgjCBAGEGAMIIAYYRvf97v+gIEuBUAAAAASUVORK5CYII=",
        "block-4": "iVBORw0KGgoAAAANSUhEUgAAAIAAAACACAYAAADDPmHLAAADj0lEQVR42u3dS07sMBCF4awYsQSWgRj3AhgzYmcgBkgI0aLbrsepnH+Q2dWV4/MRdZxy+Xh+uXy8vr1zmV7Hw+PTBwjMAYAAACAAAAgAAAIAgAAAIAAACAAAAgCAAADLCL7+LVfcJQHgVgQENgfB3QD+Q0BQsxAsAbiGgIDmIVgG8BvB6oBXbnpCMBFhViDYAvCNYHegK//HhL/K7LmRB3DPQDKfHp2P5My5iUBwKIR/7UanvG1E31clgkMlfAD0IDhUw5/y+F8dqwqCQzX8ST8AV8eqgOBQDn/SK+DqWLsRhADIDJ+Fndw3jG0AhK+HoAwA4WsikAZA0Jf29ZM2AMrfxaOujnscAcAh/K57lQfgFH7HPUsDcAy/+t5lATiHXzkHkusAhF8zF5IrgYRfg0BmKfjW0jDX8DPmRupbgNpCyKRFm+5xSQGYuLKoOOaRACYvK6uNfRyAM3xTULqH9oKQ7omLmOysMu+dcY0qCFEKv2qzRiaCkQUhSuFHAehAMLYgRCn8SADVCE71LaAr/GgAlQhGAlALPwOACgK53wBZlS6VBSmdCHZ/CLa+BShOakdVTsVm0HELQZPC70Rw2pXAaeF3IbAFoBh+BwIAiIVf3dQBAILhV3U9AYBw+FFjAkDCgoby518AJANQrwEAQCKACYUgAEgCcNYmUQA4eZMoAGz+Yp7eJAoA5s0jAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACwFAwAPgYBgM/BAKAgBACUhAGAolDeAigLZ2MIG0NYCGJrGCuBbA5lezjbw08PgAYRAwHQIsa4RQxNooybRNEmzrxNHI0iaRRJq1jnVrE0izZvFk27eNrFc2AEB0ZwZAxHxnBoFIdGcWwcx8ZxcKTzwZEcHWt8dCyHRxsfHs3x8cbHx3feOOEP+BbgjkB140kpAFcEyhtPygG4IVDfeNICwAVBxz2OAeDUBKJzcUkaAAjin26yBSEgqA9fpiAEBD3hSxSEZFbDTAqzIvxUAB0IztgkSiX8JQCVCM7aJEol/GUAVQhcm0RVhb8FIAMBAGrD3wYQiSCzzFvt8V/ZbCIdQASCijJvtR+AnTuQwgHsIMh6vZrwCrgzNz/nXQJAVdEo1+XPeZcAAIL68HcRhAMAQX34OwhSAICgPvxVBGkAuPquexAAwBwBAMwRAMAcAQDMEQDAHAEAzBEAwBwBAMwRAMAcAQDMEXwC5kPNtXKk0ooAAAAASUVORK5CYII=",
        "reinforced-block-2": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAAAXNSR0IArs4c6QAAAzNJREFUeJzdmzuO20AMhiljjyI3BnyRpEzr2nAV7BH2CItUi9RpUyYXMbCNfZdNszTG43n8HD5k569sWRLJT9TMUJQn6ujt56+P3j6IDvvdJNk/ym7zRysnUGeWsFv9wdoJxJkl7BY3ejnRc2YJu6t8w/fnF1cniMqBegdfs3FF5MvXbx9ERPN6S5vN7O3P5YpEBF+yS5QA4OBZURCWEkOYiG6DZ7UgvL+fIUNaiJ52DvvdNNWCZy0JIQLyzSCY63w6Vh1BDaOBjByjzbAuAKJ4CFHBE4EAiNoQUCHHa21I1R0DcuVjQrTDuUJugVRpJiwdvIUPTQDzelvcbnE7WKrlS8/PbgaUINTALKlSoMhFekJOPq+3dD4dL59HJL1XR6dOtoMeDwEg0l31kYFqs5ld1w8s8SAolWaUjqhFXAFYBOANwQ2ApeOeENxvASt5QTAHcD4d3dYJHhBMAfBUyZ8fAQL0PABRGnx+fMnpHI7XOqF3Xuh5gGafUiaMrtpSIcCQfZqPxFK16gJEnAm9QK0yATnPYb+bVkREf//87nZs0EBbx0c9D0CDJ0puAW8IkqW0BoIkeKJsDEAgjGikjvAqt/Pu0M0gaA1BU0RZQ4BaY0R+mbCkav3Ih1kKe6kIQPqg9BFU6z/eALAOXjNzWC97SxCuAHhd+REIXtVfDuECQLMaRCSBoAkemTlSCCsi/+BZaF0R0YFiCFBnqBe8NMWRugJ5P8GirhjqC4zsk6oELN/WywSruqKZARaBaVXKBMvS2XQh5NExyjPBenkMN0ZQpV0kK3lkFstlKXyPvcOa3GoBSwieQF2LIQvHvbPJvRrUBBBxK4neERodjEYC0bThJUtpaBbIGx6RAUmUBo6214f6Ap7T0qhKV129FO41PO5FmvcYVYPgPUBgH0arSPVKUDom9KBpzsXfJYNg6ENRbZ8RtSHJBDUAbfdYs6/Fe4wqAB7BS4/RQoC7w6jhkiMaeb2fQPT5hwn+8j/2AlglCFd/mWFFQ+AWXITdFELxT1OsKAh5/zEKwo/Xlyu7xYahtzO15usSdqtdYC9nep3naLuhzqBt90i7XYesnJG+cxBl9x8FHvnCWAiSUAAAAABJRU5ErkJggg==",
        "reinforced-block-3": "iVBORw0KGgoAAAANSUhEUgAAAGAAAABgCAYAAADimHc4AAADyklEQVR4nO2bS27cMBBEfb546XsEOYKPEWTte9pwgAkmg5HUVV39k2igFwZGVPV7ImXCnJcX4uf3n4/P6GJynS1zWSPqhiZmLm9E1dDEzG0a8TY0MXO7RtiGqvPKJFQ3Mb0W/AZFwf/x+vb589d7efizFAz/VlYJ35/zVDaQirwwfKsEbzPZEirzwvCPJEyD3yE3DH9LwlT4HfLD8B8lTIffRgIC/17CUZAJ8JmscgkR8K2NIYAYqCoByOdDBTA39kpghTHjq/oKEaCC6G2SuVfGw8FKMP/1s1WqfQJzDVKKTBESDgUcwVfuE6Lge8aPlkALyNwnVJdHQoiAzH1Cl2IlpAtQ7hMqAHskpAnYk4A0UA2dydViCdqSoAxeBZ+R4Jk1LgH3EjwhusFHwHrv4RZgEcQ0a3npIcWOHy05VIBln/CsWTV87/gjBVj2CZNqlADLPmFinULAZAljBJxRQqslCP0TdboEK+QUAew+wSohUgozNvqEhwpglymrBCS4B2QUfOZe5n/IeN8VzPUoEOS6KPjobKNORaglsOur97oo+EiVC0DBqus0AjxLUCf42RLow1nK9b9CggVOtAT6eCIKTjlWFnzre0cCn5VgbThizGj4VgGMBPqIOgvq7AKQcXfhR0noAh+FVQIfXYpUArLgI9DUMypEgAXeWQVI1/4lYAlYApaAJWAJWAKWgCVgCRgkwNLsWQWgEuQCrM2qx8uAbxWAjFcCHxGQIQF5YiPGlS09ETNgqgDJuwCFr34HTF2CUPhPJbDwreA6wUfARcH/T4IXvkJCNnwLwGj4/ySoBLASquDvgcyC30LA0XWsKMt11U+/WcAePNV7wHINCn/vuuj13yqqxeFc5F6K2Xn7PUoCIqr8eDoz2zwSHn9XS0BnSukXNDqUUgKzVJV9RalTKSSw74qSL+l1rCgJS4BQwhgBZ5QwagliJUTLs47/CM7DoFQAAjN6BqHj3+B5+w8XYPlctOSoh8MCtlSA57PV8D25kPdDmIBoYZUSGKCpAhSzpho6k4vZJ5QI6AhYIegIaJqAq0l47Kl8CYqSEC3Ok2lPwt71bgFZEqJnjyLTMwke+GYBXglso6p7qXNZrrfAhwSwEpRNMjkzHw4UPiwAleCFfz8Ok1PRE9oXAp8SYJVw1BQDNaqQrEr4fwWwh7MsoSdIUPYBLz/e44nTJUTkt0qQHdCdKiEy95EE6RH1iRIy8m5J2IVfKWHaDLDeA4bvkbBqWwIEf0nQFgV/SWgAv5OEK2Ru29CVMrdr6IqZ2zR05czlDV0l8xdC9Nw1T0GC6AAAAABJRU5ErkJggg==",
        "source-bottom": "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAADNJREFUWIXtzjEBADAIxMCn8toR/1qKDJaLgVzd1z+Lnc05AAAAAAAAAAAAAAAAAABAkgy9CwInLKEs8AAAAABJRU5ErkJggg==",
        "cross-full": "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAItJREFUWIVjYBjpgBHG8PIO/k9Pi7dtXcvIwMDAwERPS7GBUQeMOmDUAQPuABZSNaio6sLZd25fptgBJIUAsuXY+DR3ADZAqSOokgYocQRJDsAX5+Q6guQQoLYjyIoCajqC7DRAjSxIkQOo5QiKcwG6I0h1FMklITGOIAUMeF0w6oBRB4w6YMAdMAoAggUextt5PKkAAAAASUVORK5CYII=",
        "liquid-router-bottom": "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAADNJREFUWIXtzkEBADAIxLBjIpGAfwdMBp/UQFPdsznsXc4BAAAAAAAAAAAAAAAAAACS5ANiHQJR9qkxXQAAAABJRU5ErkJggg==",
        "liquid-container-bottom": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAAAXNSR0IArs4c6QAAAJhJREFUeJzt0FEVABAAwECEFEH/BsS4D7sEe5t7nzs+tnSA1gAdoDVAB2gN0AFaA3SA1gAdoDVAB2gN0AFaA3SA1gAdoDVAB2gN0AFaA3SA1gAdoDVAB2gN0AFaA3SA1gAdoDVAB2gN0AFaA3SA1gAdoDVAB2gN0AFaA3SA1gAdoDVAB2gN0AHaAxcLApGXdP76AAAAAElFTkSuQmCC",
        "liquid-tank-bottom": "iVBORw0KGgoAAAANSUhEUgAAAGAAAABgCAYAAADimHc4AAAAAXNSR0IArs4c6QAAAOxJREFUeJzt0TENACAAwDBAJBLw7wBk9GBVsGRz73NHmKUDftcArAFYA7AGYA3AGoA1AGsA1gCsAVgDsAZgDcAagDUAawDWAKwBWAOwBmANwBqANQBrANYArAFYA7AGYA3AGoA1AGsA1gCsAVgDsAZgDcAagDUAawDWAKwBWAOwBmANwBqANQBrANYArAFYA7AGYA3AGoA1AGsA1gCsAVgDsAZgDcAagDUAawDWAKwBWAOwBmANwBqANQBrANYArAFYA7AGYA3AGoA1AGsA1gCsAVgDsAZgDcAagDUAawDWAKwBWAOwBmANwBqAPRk/AtGzdGPkAAAAAElFTkSuQmCC",
    }

    @staticmethod
    def _parse_hex_rgba(hex_str: str, default_rgb: Tuple[int, int, int] = (64, 64, 73)) -> Tuple[int, int, int, int]:
        s = str(hex_str or "").strip().lstrip("#")
        try:
            if len(s) == 6:
                return (int(s[0:2], 16), int(s[2:4], 16), int(s[4:6], 16), 255)
            if len(s) == 8:
                return (int(s[0:2], 16), int(s[2:4], 16), int(s[4:6], 16), int(s[6:8], 16))
        except ValueError:
            pass
        return (default_rgb[0], default_rgb[1], default_rgb[2], 255)

    @classmethod
    def _outline_rgba(cls, im: Image.Image, hex_color: str = "404049", radius: int = 4) -> Image.Image:
        """Exact port of Arc's `Pixmaps.outline(pixmap, color, radius)`."""
        rgba = im.convert("RGBA")
        if radius <= 0:
            return rgba
        ocr, ocg, ocb, _ = cls._parse_hex_rgba(hex_color)
        w, h = rgba.size
        src = rgba.load()
        out = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        dst = out.load()
        offsets = [
            (dx, dy)
            for dy in range(-radius, radius + 1)
            for dx in range(-radius, radius + 1)
            if dx * dx + dy * dy <= radius * radius + 0.01
        ]
        for y in range(h):
            for x in range(w):
                r, g, b, a = src[x, y]
                if a == 255:
                    dst[x, y] = (r, g, b, 255)
                    continue
                maxa = 0
                for dx, dy in offsets:
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < w and 0 <= ny < h:
                        na = src[nx, ny][3]
                        if na > maxa:
                            maxa = na
                            if maxa == 255:
                                break
                if maxa == 0:
                    dst[x, y] = (0, 0, 0, 0)
                elif a == 0:
                    dst[x, y] = (ocr, ocg, ocb, maxa)
                else:
                    fa = a / 255.0
                    ba = (maxa / 255.0) * (1.0 - fa)
                    oa = fa + ba
                    nr = int(round((r * fa + ocr * ba) / oa))
                    ng = int(round((g * fa + ocg * ba) / oa))
                    nb = int(round((b * fa + ocb * ba) / oa))
                    dst[x, y] = (nr, ng, nb, int(round(oa * 255)))
        return out

    @classmethod
    def _tint_rgba(cls, im: Image.Image, hex_color: str) -> Image.Image:
        rgba = im.convert("RGBA")
        c = cls._parse_hex_rgba(hex_color, (86, 86, 86))
        return ImageChops.multiply(rgba, Image.new("RGBA", rgba.size, c))

    @staticmethod
    def _has_interior_cutout(top_im: Image.Image) -> bool:
        """
        Returns True if `top_im` contains transparent interior pixels (e.g. a
        chevron direction window on a Duct / Conduit) not connected to the
        top (`y=0`) or bottom (`y=h-1`) exterior border.
        """
        rgba = top_im.convert("RGBA")
        w, h = rgba.size
        px = rgba.load()
        visited: Set[Tuple[int, int]] = set()
        stack: List[Tuple[int, int]] = []
        for x in range(w):
            if px[x, 0][3] == 0:
                visited.add((x, 0))
                stack.append((x, 0))
            if px[x, h - 1][3] == 0 and (x, h - 1) not in visited:
                visited.add((x, h - 1))
                stack.append((x, h - 1))
        while stack:
            cx, cy = stack.pop()
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                nx, ny = cx + dx, cy + dy
                if 0 <= nx < w and 0 <= ny < h and (nx, ny) not in visited and px[nx, ny][3] == 0:
                    visited.add((nx, ny))
                    stack.append((nx, ny))
        for y in range(h):
            for x in range(w):
                if px[x, y][3] == 0 and (x, y) not in visited:
                    return True
        return False

    @staticmethod
    def _is_nonempty_rgba(im: Image.Image) -> bool:
        alpha = im.convert("RGBA").getchannel("A")
        lo, hi = alpha.getextrema()
        return hi > 0

    def _emit_generated_sprite(self, stem: str, canvas: Image.Image, stat_kind: str = "icon") -> None:
        rgba = canvas.convert("RGBA")
        buf = io.BytesIO()
        rgba.save(buf, format="PNG", optimize=True)
        out_bytes = buf.getvalue()
        rel_out = f"generated-icons/{stem}.png"
        self.sprites_by_stem[stem] = SpriteRecord(
            stem=stem,
            orig_rel_path=rel_out,
            abs_path=self.mod_dir / "sprites" / rel_out,
            width=rgba.width,
            height=rgba.height,
            png_bytes=out_bytes,
            rgba_md5=hashlib.md5(rgba.tobytes()).hexdigest(),
            dest_rel_path=rel_out,
        )
        if stat_kind == "icon":
            self.stats.synthesized_icons += 1
        elif stat_kind == "outline":
            self.stats.synthesized_outlines += 1
        elif stat_kind == "tread":
            self.stats.synthesized_treads += 1

    def _synthesize_icons_outlines_and_treads(self) -> None:
        """
        Replicates the sprite generation steps normally performed by
        `Block.createIcons(MultiPacker)` and `UnitType.createIcons(MultiPacker)`
        (which Mindustry's `DataManager.load` skips at runtime):
          1. Generates missing `<part>-outline.png` sprites for `RegionPart`s on
             turrets/blocks/units/weapons, turret body `<name>-outline.png`,
             crawler `<unit>-segment-outline<i>.png`, and tank animated
             `<unit>-treads<r>-<i>.png` slices.
          2. Synthesizes crisp multi-layer `<block>-full.png` (and `<block>.png`
             where absent on Conduits/Ducts) icons for Conduits (`Aqueduct`,
             `Viaduct`), Ducts (`Strataduct`, `Ferrinite Pipeline`,
             `Transverse Pipeline`, `Hive Vein`), Sorters (`Pipeline Sorter`,
             `Inverted Pipeline Sorter`), Turrets (`Comedite`, `Shaft`,
             `Cavalier`, `Instauro`, etc.), LiquidRouters, and multi-layer
             Crafters/Generators/Drills/Payload blocks.
        All generated PNGs are placed under `sprites/generated-icons/` so they
        pack onto the 4096x4096 `patchAtlas` and consume 0 px of the 500x500
        `data-patch-reserved-env` reserve.
        """
        vanilla_cache: Dict[str, Image.Image] = {}

        def get_vanilla_im(name: str) -> Optional[Image.Image]:
            if name in vanilla_cache:
                return vanilla_cache[name]
            b64 = self._VANILLA_HELPER_PNGS_B64.get(name)
            if not b64:
                return None
            im = Image.open(io.BytesIO(base64.b64decode(b64))).convert("RGBA")
            vanilla_cache[name] = im
            return im

        def open_sp(sp: SpriteRecord) -> Image.Image:
            with Image.open(io.BytesIO(sp.png_bytes)) as im:
                return im.convert("RGBA")

        def composite_layers(layers: List[Image.Image]) -> Image.Image:
            max_w = max(im.width for im in layers)
            max_h = max(im.height for im in layers)
            canvas = Image.new("RGBA", (max_w, max_h), (0, 0, 0, 0))
            for im in layers:
                ox = (max_w - im.width) // 2
                oy = (max_h - im.height) // 2
                canvas.alpha_composite(im.convert("RGBA"), (ox, oy))
            return canvas

        def normalize_sprite_stem(raw: str) -> str:
            s = raw.strip()
            if s.startswith("dp-"):
                return s[3:]
            if s.startswith(self.mod_name + "-"):
                return s[len(self.mod_name) + 1:]
            return s

        def emit_outline_if_missing(stem: str, color_hex: str, radius: int) -> None:
            out_stem = f"{stem}-outline"
            if stem in self.sprites_by_stem and out_stem not in self.sprites_by_stem:
                src_im = open_sp(self.sprites_by_stem[stem])
                if self._is_nonempty_rgba(src_im):
                    self._emit_generated_sprite(
                        out_stem,
                        self._outline_rgba(src_im, color_hex, radius),
                        stat_kind="outline",
                    )

        def process_region_parts(parts_node: Any, owner_stem: str, turret_shading: bool, color_hex: str, radius: int) -> bool:
            """Returns True if at least one DrawPart entry was present."""
            if isinstance(parts_node, dict):
                plist = [parts_node]
            elif isinstance(parts_node, list):
                plist = parts_node
            else:
                return False
            had_any = False
            for p in plist:
                if not isinstance(p, dict):
                    continue
                had_any = True
                ptype = p.get("type", "RegionPart")
                if ptype == "RegionPart" or ("type" not in p and ("suffix" in p or "name" in p)):
                    draw_reg = bool(p.get("drawRegion", True))
                    default_outline = not ("blending" in p and "color" in p and "outline" not in p)
                    outline = bool(p.get("outline", default_outline))
                    mirror = bool(p.get("mirror", False))
                    raw_name = p.get("name")
                    suffix = str(p.get("suffix", ""))
                    real = normalize_sprite_stem(raw_name) if isinstance(raw_name, str) and raw_name else f"{owner_stem}{suffix}"
                    if draw_reg and outline:
                        targets = [f"{real}-r", f"{real}-l"] if (mirror and turret_shading) else [real]
                        for t in targets:
                            emit_outline_if_missing(t, color_hex, radius)
                if "children" in p:
                    process_region_parts(p["children"], owner_stem, turret_shading, color_hex, radius)
            return had_any

        # --------------------------------------------------------------
        # Pass 1: RegionPart / Turret / Unit Outlines & Tank Treads
        # --------------------------------------------------------------
        for rec in self.content_records:
            if rec.ctype == "block":
                color_hex = str(rec.data.get("outlineColor", "404049"))
                radius = int(rec.data.get("outlineRadius", 4))
                dr = rec.data.get("drawer")
                if isinstance(dr, dict) and dr.get("type") == "DrawMulti":
                    drawers = dr.get("drawers", [])
                elif isinstance(dr, dict):
                    drawers = [dr]
                elif isinstance(dr, list):
                    drawers = dr
                else:
                    drawers = []
                for d in drawers:
                    if isinstance(d, dict) and d.get("type") == "DrawTurret":
                        has_parts = process_region_parts(d.get("parts"), rec.stem, True, color_hex, radius)
                        ap = d.get("ammoParts")
                        if isinstance(ap, dict):
                            for v in ap.values():
                                if process_region_parts(v, rec.stem, True, color_hex, radius):
                                    has_parts = True
                        if has_parts:
                            emit_outline_if_missing(rec.stem, color_hex, radius)

            elif rec.ctype == "unit":
                color_hex = str(rec.data.get("outlineColor", "565666"))
                radius = int(rec.data.get("outlineRadius", 3))
                outlines_enabled = bool(rec.data.get("outlines", True))

                process_region_parts(rec.data.get("parts"), rec.stem, False, color_hex, radius)
                weapons = rec.data.get("weapons")
                if isinstance(weapons, list):
                    for w in weapons:
                        if not isinstance(w, dict):
                            continue
                        raw_wname = w.get("name")
                        wstem = normalize_sprite_stem(raw_wname) if isinstance(raw_wname, str) and raw_wname else rec.stem
                        process_region_parts(w.get("parts"), wstem, False, color_hex, radius)
                        if outlines_enabled and isinstance(raw_wname, str) and raw_wname:
                            wparts = w.get("parts") if isinstance(w.get("parts"), list) else []
                            has_under = any(isinstance(wp, dict) and wp.get("under") for wp in wparts)
                            if (not bool(w.get("top", True))) or has_under:
                                emit_outline_if_missing(wstem, color_hex, radius)

                if outlines_enabled:
                    if bool(rec.data.get("alwaysCreateOutline", False)):
                        emit_outline_if_missing(rec.stem, color_hex, radius)
                    segments = int(rec.data.get("segments", 0))
                    for i in range(segments):
                        seg_stem = f"{rec.stem}-segment{i}"
                        seg_out = f"{rec.stem}-segment-outline{i}"
                        if seg_stem in self.sprites_by_stem and seg_out not in self.sprites_by_stem:
                            seg_im = open_sp(self.sprites_by_stem[seg_stem])
                            if self._is_nonempty_rgba(seg_im):
                                self._emit_generated_sprite(
                                    seg_out,
                                    self._outline_rgba(seg_im, color_hex, radius),
                                    stat_kind="outline",
                                )

                # Tank animated 1px tread slices (`UnitType.createIcons` lines 1267..1294)
                tread_sp = self.sprites_by_stem.get(f"{rec.stem}-treads")
                tread_rects = rec.data.get("treadRects")
                if tread_sp is not None and isinstance(tread_rects, list) and tread_rects:
                    pix = open_sp(tread_sp)
                    tread_frames = int(rec.data.get("treadFrames", 18))
                    pull_offset = int(rec.data.get("treadPullOffset", 0))
                    for r_idx, trect in enumerate(tread_rects):
                        if not isinstance(trect, dict):
                            continue
                        sx = int(float(trect.get("x", 0)) + pix.width / 2.0)
                        sy = int(float(trect.get("y", 0)) + pix.height / 2.0)
                        sh = int(float(trect.get("height", 0)))
                        if sh <= 0 or sx < 0 or sx >= pix.width:
                            continue
                        slice_px = [
                            pix.getpixel((sx, min(max(sy + y, 0), pix.height - 1)))
                            for y in range(sh)
                        ]
                        for f_idx in range(tread_frames):
                            tread_stem = f"{rec.stem}-treads{r_idx}-{f_idx}"
                            if tread_stem in self.sprites_by_stem:
                                continue
                            frame_im = Image.new("RGBA", (1, sh), (0, 0, 0, 0))
                            for y in range(sh):
                                idx = y + f_idx
                                if idx >= sh:
                                    idx = ((idx - sh + pull_offset) % sh + sh) % sh
                                frame_im.putpixel((0, y), slice_px[idx])
                            self._emit_generated_sprite(tread_stem, frame_im, stat_kind="tread")

        # --------------------------------------------------------------
        # Pass 2: Multi-Layer Block `-full.png` (and missing base `.png`)
        # --------------------------------------------------------------
        env_skip_types = {
            "Floor", "OverlayFloor", "OreBlock", "SteamVent", "TallBlock",
            "TreeBlock", "StaticTree", "Prop", "SeaBush", "Seaweed",
            "WobbleProp", "StaticWall", " ShallowLiquid",
        }
        top_composite_types = {
            "WallCrafter", "BurstDrill", "DirectionalUnloader",
            "UnitCargoUnloadPoint", "UnitAssembler", "UnitAssemblerModule",
            "PayloadDeconstructor", "Constructor", "PayloadConveyor",
            "PayloadRouter", "PayloadMassDriver", "ShieldWall",
        }

        for rec in self.content_records:
            if rec.ctype != "block" or rec.converted_to_building:
                continue
            bname = rec.stem
            btype = rec.orig_type
            if btype in env_skip_types:
                continue
            if f"{bname}-full" in self.sprites_by_stem or f"block-{bname}-full" in self.sprites_by_stem:
                continue

            dr = rec.data.get("drawer")
            has_draw_turret = (
                (isinstance(dr, dict) and dr.get("type") == "DrawTurret")
                or (isinstance(dr, dict) and dr.get("type") == "DrawMulti" and any(isinstance(x, dict) and x.get("type") == "DrawTurret" for x in dr.get("drawers", [])))
                or (isinstance(dr, list) and any(isinstance(x, dict) and x.get("type") == "DrawTurret" for x in dr))
            )

            layers: List[Image.Image] = []
            also_emit_base = False

            # 1. Conduit / ArmoredConduit (`Aqueduct`, `Viaduct`, etc.)
            if btype in ("Conduit", "ArmoredConduit"):
                top_sp = (
                    self.sprites_by_stem.get(f"{bname}-top-0")
                    or self.sprites_by_stem.get(f"{bname}-top")
                    or self.sprites_by_stem.get(f"{bname}-cap")
                )
                if top_sp is not None:
                    top_im = open_sp(top_sp)
                    bot_color = str(rec.data.get("botColor", "565656"))
                    if self._has_interior_cutout(top_im):
                        bot_sp = self.sprites_by_stem.get(f"{bname}-bottom-0")
                        raw_bot = open_sp(bot_sp) if bot_sp is not None else get_vanilla_im("source-bottom")
                        if raw_bot is not None:
                            layers.append(self._tint_rgba(raw_bot, bot_color))
                    layers.append(top_im)
                    also_emit_base = bname not in self.sprites_by_stem

            # 2. Duct / ArmoredDuct (`Strataduct`, `Ferrinite Pipeline`, `Transverse Pipeline`, `Hive Vein`)
            elif btype in ("Duct", "ArmoredDuct"):
                top_sp = (
                    self.sprites_by_stem.get(f"{bname}-top-0")
                    or self.sprites_by_stem.get(f"{bname}-top")
                    or self.sprites_by_stem.get(f"{bname}-cap")
                )
                if top_sp is not None:
                    top_im = open_sp(top_sp)
                    if self._has_interior_cutout(top_im):
                        bot_sp = self.sprites_by_stem.get(f"{bname}-bottom-0")
                        raw_bot = open_sp(bot_sp) if bot_sp is not None else get_vanilla_im("source-bottom")
                        if raw_bot is not None:
                            layers.append(raw_bot)
                    layers.append(top_im)
                    also_emit_base = bname not in self.sprites_by_stem

            # 3. Sorter (`Pipeline Sorter`, `Inverted Pipeline Sorter`)
            elif btype == "Sorter":
                if bname in self.sprites_by_stem:
                    center_sp = self.sprites_by_stem.get(f"{bname}-cross-full")
                    center_im = open_sp(center_sp) if center_sp is not None else get_vanilla_im("source-bottom")
                    if center_im is not None:
                        layers.append(center_im)
                    layers.append(open_sp(self.sprites_by_stem[bname]))

            # 4. Turrets (`Comedite`, `Shaft`, `Cavalier`, `Instauro`, `Barite Slinger`, etc.)
            elif btype.endswith("Turret") or has_draw_turret:
                size = int(rec.data.get("size", 1))
                base_prefix = ""
                if isinstance(dr, dict) and isinstance(dr.get("basePrefix"), str):
                    base_prefix = normalize_sprite_stem(dr["basePrefix"])
                elif isinstance(dr, dict) and dr.get("type") == "DrawMulti":
                    for sub in dr.get("drawers", []):
                        if isinstance(sub, dict) and isinstance(sub.get("basePrefix"), str):
                            base_prefix = normalize_sprite_stem(sub["basePrefix"])
                            break
                elif isinstance(dr, list):
                    for sub in dr:
                        if isinstance(sub, dict) and isinstance(sub.get("basePrefix"), str):
                            base_prefix = normalize_sprite_stem(sub["basePrefix"])
                            break

                base_sp = (
                    self.sprites_by_stem.get(f"{bname}-base")
                    or self.sprites_by_stem.get(f"{base_prefix}block-{size}")
                )
                base_im = (
                    open_sp(base_sp)
                    if base_sp is not None
                    else (get_vanilla_im(f"{base_prefix}block-{size}") or get_vanilla_im(f"block-{size}"))
                )
                if base_im is not None:
                    layers.append(base_im)

                body_sp = self.sprites_by_stem.get(f"{bname}-preview")
                if body_sp is None and bname in self.sprites_by_stem:
                    cand_im = open_sp(self.sprites_by_stem[bname])
                    if self._is_nonempty_rgba(cand_im):
                        body_sp = self.sprites_by_stem[bname]

                if body_sp is not None:
                    body_im = open_sp(body_sp)
                    if bool(rec.data.get("outlineIcon", True)):
                        ocol = str(rec.data.get("outlineColor", "404049"))
                        orad = int(rec.data.get("outlineRadius", 4))
                        body_im = self._outline_rgba(body_im, ocol, orad)
                    layers.append(body_im)

                if f"{bname}-top" in self.sprites_by_stem:
                    layers.append(open_sp(self.sprites_by_stem[f"{bname}-top"]))

            # 5. LiquidRouter (`Aqueduct Router`, `Liquid Vat`, `Liquid Silo`)
            elif btype == "LiquidRouter":
                if bname in self.sprites_by_stem:
                    size = int(rec.data.get("size", 1))
                    bot_sp = self.sprites_by_stem.get(f"{bname}-bottom")
                    v_fallback = {1: "liquid-router-bottom", 2: "liquid-container-bottom", 3: "liquid-tank-bottom"}.get(size, "")
                    bot_im = open_sp(bot_sp) if bot_sp is not None else get_vanilla_im(v_fallback)
                    if bot_im is not None:
                        layers.append(bot_im)
                    layers.append(open_sp(self.sprites_by_stem[bname]))

            # 6. Multi-drawer Crafters / Generators / Drills / Payload / Unloaders
            else:
                drawer_seq: List[Any] = []
                if isinstance(dr, dict) and dr.get("type") == "DrawMulti" and isinstance(dr.get("drawers"), list):
                    drawer_seq = dr["drawers"]
                elif isinstance(dr, list):
                    drawer_seq = dr

                if drawer_seq:
                    for sub in drawer_seq:
                        if sub == "DrawDefault" or (isinstance(sub, dict) and sub.get("type", "DrawDefault") == "DrawDefault"):
                            if bname in self.sprites_by_stem:
                                layers.append(open_sp(self.sprites_by_stem[bname]))
                        elif isinstance(sub, dict) and sub.get("type") == "DrawRegion":
                            rname = sub.get("name")
                            suff = str(sub.get("suffix", ""))
                            target = normalize_sprite_stem(rname) if isinstance(rname, str) and rname else f"{bname}{suff}"
                            if target in self.sprites_by_stem:
                                layers.append(open_sp(self.sprites_by_stem[target]))
                    if len(layers) <= 1:
                        layers = []

                if not layers and bname in self.sprites_by_stem:
                    has_bot = f"{bname}-bottom" in self.sprites_by_stem
                    has_top = f"{bname}-top" in self.sprites_by_stem and btype in top_composite_types
                    if has_bot or has_top:
                        if has_bot:
                            layers.append(open_sp(self.sprites_by_stem[f"{bname}-bottom"]))
                        layers.append(open_sp(self.sprites_by_stem[bname]))
                        if btype in ("UnitAssembler", "UnitAssemblerModule") and f"{bname}-side1" in self.sprites_by_stem:
                            layers.append(open_sp(self.sprites_by_stem[f"{bname}-side1"]))
                        if f"{bname}-top" in self.sprites_by_stem and (has_top or has_bot):
                            layers.append(open_sp(self.sprites_by_stem[f"{bname}-top"]))

                if not layers and bname not in self.sprites_by_stem and f"{bname}1" not in self.sprites_by_stem:
                    for suffix in ("-ui", "-icon", "-base", "-top", "-bottom"):
                        cand = self.sprites_by_stem.get(f"{bname}{suffix}")
                        if cand is not None:
                            layers = [open_sp(cand)]
                            break

            if not layers:
                continue

            comp_im = composite_layers(layers)
            self._emit_generated_sprite(f"{bname}-full", comp_im, stat_kind="icon")
            if also_emit_base and bname not in self.sprites_by_stem:
                self._emit_generated_sprite(bname, comp_im, stat_kind="icon")

    def convert(self) -> ConversionStats:
        self._collect_audio_and_sprites()
        self._collect_and_parse_content()
        self._synthesize_icons_outlines_and_treads()
        self._apply_environment_atlas_bypasses()

        self.out_zip.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(self.out_zip, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
            # 1. Patches (`patches/`)
            if self.vanilla_patches:
                patch_obj = {"name": f"{self.mod_name}-vanilla-overrides", **self.vanilla_patches}
                zf.writestr(
                    "patches/00-vanilla-overrides.json",
                    json.dumps(patch_obj, indent=2, ensure_ascii=False),
                )
            if self.client_scale_patches:
                scale_obj = {"name": f"{self.mod_name}-env-atlas-scale", **self.client_scale_patches}
                zf.writestr(
                    "patches/zz-env-scale-client.json",
                    json.dumps(scale_obj, indent=2, ensure_ascii=False),
                )

            # Also include any existing `patches/` files from the source mod
            src_patches = self.mod_dir / "patches"
            if src_patches.is_dir():
                seen_p: Set[str] = {"00-vanilla-overrides", "zz-env-scale-client"}
                for p in sorted(src_patches.rglob("*")):
                    if p.is_file() and p.suffix.lower() in (".json", ".hjson", ".json5"):
                        if p.stem in seen_p:
                            continue
                        seen_p.add(p.stem)
                        pdata = parse_hjson_file(p)
                        pdata = self._sanitize_content_tree(pdata, ctype="patch", is_patch=True)
                        rel = p.relative_to(src_patches).with_suffix(".json").as_posix()
                        zf.writestr(f"patches/{rel}", json.dumps(pdata, indent=2, ensure_ascii=False))

            # 2. Content (`content/<ctype.folderName>/`)
            for rec in self.content_records:
                zpath = f"content/{rec.folder_name}/{rec.rel_subpath}"
                zf.writestr(zpath, json.dumps(rec.data, indent=2, ensure_ascii=False))
                self.stats.total_content_out += 1

            # 3. Bundles (`bundles/*.properties`)
            bundles_dir = self.mod_dir / "bundles"
            if bundles_dir.is_dir():
                seen_b: Set[str] = set()
                for p in sorted(bundles_dir.rglob("*.properties")):
                    if not p.is_file():
                        continue
                    if p.stem in seen_b:
                        self.stats.deduplicated_assets.append(("bundles", p.name))
                        continue
                    seen_b.add(p.stem)
                    raw_txt = p.read_text(encoding="utf-8", errors="replace")
                    rel = p.relative_to(bundles_dir).as_posix()
                    zf.writestr(f"bundles/{rel}", self._rewrite_bundle_text(raw_txt))

            # 4. Sprites (`sprites/**/*.png`) sorted by destination path
            for sp in sorted(self.sprites_by_stem.values(), key=lambda x: x.dest_rel_path):
                if sp.excluded:
                    continue
                zf.writestr(f"sprites/{sp.dest_rel_path}", sp.png_bytes)

            # 5. Sounds & Music (`sounds/`, `music/`)
            for folder_name in ("sounds", "music"):
                adir = self.mod_dir / folder_name
                if not adir.is_dir():
                    continue
                seen_a: Set[str] = set()
                for p in sorted(adir.rglob("*")):
                    if not p.is_file() or p.suffix.lower() not in (".ogg", ".mp3"):
                        continue
                    if p.stem in seen_a:
                        self.stats.deduplicated_assets.append((folder_name, p.name))
                        continue
                    seen_a.add(p.stem)
                    rel = p.relative_to(adir).as_posix()
                    zf.writestr(f"{folder_name}/{rel}", p.read_bytes())

        return self.stats


# ============================================================================
# 6. CLI Entrypoint & Summary Formatter
# ============================================================================

def format_report(stats: ConversionStats, out_zip: Path) -> str:
    usable_area = (stats.env_limit - 4) * (stats.env_limit - 4)
    raw_pct = (stats.raw_env_padded_area / usable_area * 100.0) if usable_area else 0.0
    fin_pct = (stats.final_env_padded_area / usable_area * 100.0) if usable_area else 0.0
    size_mb = out_zip.stat().st_size / (1024 * 1024) if out_zip.exists() else 0.0

    lines = [
        f"======================================================================",
        f" Mindustry Mod -> DataPatch Asset Zip Report ({stats.mod_name})",
        f"======================================================================",
        f" Output Zip                 : {out_zip} ({size_mb:.2f} MB)",
        f" Content Files Converted    : {stats.total_content_out} (from {stats.total_content_in} loadable files; {stats.skipped_planet_sector_files} planet/sector files skipped)",
        f" Vanilla Overrides -> Patch : {stats.vanilla_overrides_patched}",
        f" Synthesized Block Icons    : {stats.synthesized_icons}",
        f" Synthesized Part Outlines  : {stats.synthesized_outlines}",
        f" Synthesized Tank Treads    : {stats.synthesized_treads}",
        f" Duplicate Assets Merged    : {len(stats.deduplicated_assets)}",
        f"----------------------------------------------------------------------",
        f" Environment Atlas (`data-patch-reserved-env`, limit {stats.env_limit}x{stats.env_limit}, pad=2):",
        f"   BEFORE Bypasses          : {stats.raw_env_sprite_count:3d} sprites | {stats.raw_env_padded_area:9,d} px^2 ({raw_pct:6.1f}% of {usable_area:,d}) -> {stats.raw_env_pages} Guillotine pages {'[OVERFLOW!]' if stats.raw_env_pages > 1 else '[OK]'}",
        f"   AFTER  Bypasses          : {stats.final_env_sprite_count:3d} sprites | {stats.final_env_padded_area:9,d} px^2 ({fin_pct:6.1f}% of {usable_area:,d}) -> {stats.final_env_pages} Guillotine page  {'[FITS 1 PAGE!]' if stats.final_env_pages <= 1 else '[OVERFLOW!]'}",
        f"----------------------------------------------------------------------",
        f" Breakdown of Applied Bypasses:",
        f"   [Layer 1] Env Blocks -> Unhittable ({stats.building_privilege}) MemoryBlock Buildings : {len(stats.converted_env_buildings)} blocks ({stats.evacuated_building_sprites} sprites -> patchAtlas)",
        f"   [Layer 2] Misplaced Functional/Destructible Block Sprites Evacuated : {stats.evacuated_functional_sprites} sprites -> patchAtlas",
        f"   [Layer 3] Functional StaticWalls (`cacheLayer: normal`) Bypassed    : {len(stats.functional_static_walls_bypassed)} walls ({stats.evacuated_staticwall_sprites} sprites -> patchAtlas)",
        f"   [Layer 4] Orphan / UI / Preview Env Sprites Evacuated + Edge Shield : {stats.evacuated_orphan_ui_sprites} sprites -> patchAtlas",
        f"   [Layer 5] Exact RGBA-Duplicate Env Variants Deduplicated (Lossless) : {stats.deduped_rgba_env_sprites} sprites ({len(stats.deduped_rgba_env_blocks)} blocks)",
        f"   [Layer 6] Symmetric Center-Cropped + MT Thread-Pool Barrier Buckets : {stats.center_cropped_sprites} cropped ({stats.center_crop_bytes_px_saved:,d} px^2 saved), {stats.mt_size_buckets} MT buckets",
        f"   [Layer 7] Progressive Variant Consolidations                        : {len(stats.trimmed_vent_variants)} SteamVents, {len(stats.trimmed_floor_variants)} Floors/Overlays",
        f"   [Layer 8] Sub-Resolution `TextureRegion.scale` Patched Blocks       : {len(stats.scaled_env_blocks)} blocks",
        f"======================================================================",
    ]
    if stats.deduped_rgba_env_blocks:
        d_str = ", ".join(f"{n} ({a}->{b})" for n, a, b in stats.deduped_rgba_env_blocks)
        lines.append(f" Deduplicated RGBA Env  : {d_str}")
    if stats.trimmed_vent_variants:
        v_str = ", ".join(f"{n} ({a}->{b})" for n, a, b in stats.trimmed_vent_variants)
        lines.append(f" Consolidated SteamVents: {v_str}")
    if stats.trimmed_floor_variants:
        f_str = ", ".join(f"{n} ({a}->{b})" for n, a, b in stats.trimmed_floor_variants)
        lines.append(f" Consolidated Floors    : {f_str}")
    if stats.scaled_env_blocks:
        s_str = ", ".join(f"{n} ({k}x)" for n, k in stats.scaled_env_blocks)
        lines.append(f" Scale-Patched Blocks   : {s_str}")
    return "\n".join(lines)


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Convert a pure JSON/HJSON/JSON5 Mindustry mod directory or zip into a DataPatch asset .zip."
    )
    ap.add_argument("input_mod", help="Path to source mod directory (or .zip archive)")
    ap.add_argument("output_zip", help="Path to output DataPatch asset .zip")
    ap.add_argument(
        "--env-limit",
        type=int,
        default=500,
        help="Target width/height of `data-patch-reserved-env` in pixels (default: 500; v160+ master uses 700).",
    )
    ap.add_argument(
        "--mode",
        choices=["auto", "scale-first", "buildings-only"],
        default="auto",
        help=(
            "Hard bypass strategy after building conversion: "
            "'auto' = lossless evacuations + RGBA dedup + center crop + progressive variant trim + scale fallback; "
            "'scale-first' = keep 100%% of unique variants using 2x TextureRegion.scale client patches first; "
            "'buildings-only' = apply ONLY Layer 1 building conversion (for comparison)."
        ),
    )
    ap.add_argument(
        "--building-privilege",
        choices=["privileged", "unprivileged"],
        default="privileged",
        help=(
            "Privilege mode for converted MemoryBlock env buildings: "
            "'privileged' (default: `privileged: true`, 100%% bullet pass-through & zero damage via MemoryBuild) or "
            "'unprivileged' (`privileged: false` with max health/armor + `underBullets: true`)."
        ),
    )
    ap.add_argument(
        "--no-building-conversion",
        action="store_true",
        help="Disable Layer 1 conversion of decorative env blocks into unhittable MemoryBlock buildings.",
    )
    ap.add_argument(
        "--atlas-preview",
        type=Path,
        default=None,
        help="Optional output PNG path visualizing the packed `data-patch-reserved-env` page.",
    )
    args = ap.parse_args(argv)

    in_path = Path(args.input_mod)
    temp_extract: Optional[Path] = None
    try:
        if in_path.is_file() and in_path.suffix.lower() == ".zip":
            import tempfile
            temp_extract = Path(tempfile.mkdtemp(prefix="mod_to_dp_"))
            with zipfile.ZipFile(in_path, "r") as zf:
                zf.extractall(temp_extract)
            # Unwrap single top-level directory inside zip if present
            entries = [e for e in temp_extract.iterdir() if not e.name.startswith(".")]
            mod_root = entries[0] if len(entries) == 1 and entries[0].is_dir() else temp_extract
        elif in_path.is_dir():
            mod_root = in_path
        else:
            print(f"Error: input mod path not found: {in_path}", file=sys.stderr)
            return 1

        out_zip = Path(args.output_zip)
        converter = ModToDataPatchConverter(
            mod_dir=mod_root,
            out_zip=out_zip,
            env_limit=args.env_limit,
            hard_bypass_mode=args.mode,
            convert_buildings=not args.no_building_conversion,
            building_privilege=args.building_privilege,
            atlas_preview_path=args.atlas_preview,
        )
        stats = converter.convert()
        print(format_report(stats, out_zip))
        return 0 if stats.final_env_pages <= 1 else 2
    finally:
        if temp_extract is not None:
            import shutil
            shutil.rmtree(temp_extract, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
