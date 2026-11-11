#!/usr/bin/env python3
"""Generate a Mindustry World Processor MLOG script (`test_all_dp_world_processor.mlog`)
from a DataPatch `.zip` archive that places ALL `dp-*` blocks (floors, overlays/ores,
walls/props, functional buildings) and spawns ALL `dp-*` units on an empty test map
(recommended map size: 200x200+).
"""

from __future__ import annotations

import argparse
import json
import zipfile
from pathlib import Path

FLOOR_TYPES = {"Floor", "ShallowLiquid", "SteamVent", "EmptyFloor"}
OVERLAY_TYPES = {"OverlayFloor", "OreBlock"}
MISSILE_TYPES = {"missile"}


def generate_mlog(datapatch_zip: Path, out_mlog: Path, map_width: int = 200, include_missiles: bool = False) -> tuple[int, int, int, int, int]:
    floors: list[str] = []
    overlays: list[str] = []
    blocks: list[tuple[int, str, bool]] = []
    units: list[tuple[float, str, bool]] = []

    with zipfile.ZipFile(datapatch_zip, "r") as zf:
        for name in sorted(zf.namelist()):
            if name.startswith("content/blocks/") and name.endswith(".json"):
                stem = Path(name).stem
                dp_name = f"@dp-{stem}"
                data = json.loads(zf.read(name).decode("utf-8"))
                btype = str(data.get("type", ""))
                size = int(data.get("size", 1) or 1)
                if btype in OVERLAY_TYPES:
                    overlays.append(dp_name)
                elif btype in FLOOR_TYPES:
                    floors.append(dp_name)
                else:
                    is_static_env = btype in {"StaticWall", "StaticTree", "TreeBlock", "Prop", "TallBlock", "SeaBush", "Seaweed"}
                    blocks.append((size, dp_name, not is_static_env))
            elif name.startswith("content/units/") and name.endswith(".json"):
                stem = Path(name).stem
                dp_name = f"@dp-{stem}"
                data = json.loads(zf.read(name).decode("utf-8"))
                utype = str(data.get("type", "")).lower()
                template = str(data.get("template", "")).lower()
                if not include_missiles and (utype in MISSILE_TYPES or "missile" in template):
                    continue
                if bool(data.get("internal", False)):
                    continue
                hitsize = float(data.get("hitSize", 10.0) or 10.0)
                is_naval = utype == "naval"
                units.append((hitsize, dp_name, is_naval))

    floors.sort()
    overlays.sort()
    blocks.sort(key=lambda t: (t[0], t[1]))
    units.sort(key=lambda t: (t[0], t[1]))

    lines: list[str] = [
        "# ============================================================================",
        "# Patchsthosus — World Processor Script: Place ALL dp-* Blocks & Spawn ALL dp-* Units",
        "# Paste into a World Processor (or Generation -> World Logic) on a 200x200+ empty map.",
        "# Runs once automatically (`initialized` guard) and stops.",
        "# ============================================================================",
        "jump done equal initialized 1",
        "set initialized 1",
        "setrule unitCap 2000",
    ]

    margin = 8
    cur_x = margin
    cur_y = margin

    # 1. Floors
    for fl in floors:
        if cur_x + 2 >= map_width - margin:
            cur_x = margin
            cur_y += 2
        lines.append(f"setblock floor {fl} {cur_x} {cur_y}")
        cur_x += 2

    if floors:
        cur_x = margin
        cur_y += 4

    # 2. Overlays / Ores
    for ov in overlays:
        if cur_x + 2 >= map_width - margin:
            cur_x = margin
            cur_y += 2
        lines.append(f"setblock ore {ov} {cur_x} {cur_y}")
        cur_x += 2

    if overlays:
        cur_x = margin
        cur_y += 4

    # 3. Walls, Props & Functional Buildings
    row_max_sz = 1
    for sz, blk, has_team in blocks:
        if cur_x + sz + 1 >= map_width - margin:
            cur_x = margin
            cur_y += row_max_sz + 2
            row_max_sz = 1
        cx = cur_x + (sz - 1) // 2
        cy = cur_y + (sz - 1) // 2
        team_tok = "@sharded" if has_team else "@derelict"
        lines.append(f"setblock block {blk} {cx} {cy} {team_tok} 0")
        row_max_sz = max(row_max_sz, sz)
        cur_x += sz + 2

    # 4. Units
    cur_x = margin + 2
    cur_y += row_max_sz + 8
    row_step_y = 6
    for hitsize, uname, is_naval in units:
        cell = max(4, int((hitsize / 8.0) + 2.999))
        if cur_x + cell >= map_width - margin:
            cur_x = margin + 2
            cur_y += row_step_y
            row_step_y = 6
        ux = cur_x + cell // 2
        uy = cur_y + cell // 2
        if is_naval:
            lines.append(f"setblock floor @deep-water {ux} {uy}")
        lines.append(f"spawn {uname} {ux} {uy} 90 @sharded outUnit")
        row_step_y = max(row_step_y, cell + 2)
        cur_x += cell + 1

    lines.append("done:")
    lines.append("stop")

    instr_count = sum(1 for ln in lines if ln and not ln.startswith("#") and not ln.endswith(":"))
    out_mlog.parent.mkdir(parents=True, exist_ok=True)
    out_mlog.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return len(floors), len(overlays), len(blocks), len(units), instr_count


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("datapatch_zip", type=Path, help="Input DataPatch .zip archive")
    ap.add_argument("out_mlog", type=Path, help="Output .mlog file path")
    ap.add_argument("--map-width", type=int, default=200, help="Target empty test map width in tiles (default: 200)")
    ap.add_argument("--include-missiles", action="store_true", help="Also spawn MissileUnitType units")
    args = ap.parse_args()

    fl, ov, bl, un, ic = generate_mlog(args.datapatch_zip, args.out_mlog, args.map_width, args.include_missiles)
    print(f"Generated {args.out_mlog}: {fl} floors, {ov} overlays, {bl} blocks, {un} units ({ic}/1000 MLOG instructions)")


if __name__ == "__main__":
    main()
