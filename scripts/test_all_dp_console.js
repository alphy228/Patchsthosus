// ============================================================================
// Patchsthosus — Place ALL `dp-*` Blocks & Spawn ALL `dp-*` Units Test Script
// ============================================================================
// Works in BOTH:
//   1. Mindustry Client JS Console (`F8` on an empty Sandbox / Custom map with
//      DataPatch assets loaded, or while connected as host), OR
//   2. Mindustry Dedicated Server console (`js Vars.mods.scripts.runConsole(...)`
//      or paste single-line; or simply run `patchsthosus-test` if the plugin is installed).
//
// Automatically discovers every loaded `dp-*` Floor, Overlay/Ore, Wall/Prop/Building,
// and Unit from `Vars.content`, arranges them in neat grids on the active map, sets
// a high unit cap, puts deepwater pools under naval units, and prints a summary.
// ============================================================================

(function() {
    var TEAM = Team.sharded;
    var INCLUDE_MISSILES = false; // Set true to also spawn temporary MissileUnitType projectiles
    var MARGIN = 6;

    if (!Vars.world || !Vars.world.tiles) {
        print("[Patchsthosus Test] Load or host an empty test map first (200x200+ recommended)!");
        return "No map loaded.";
    }

    var mapW = Vars.world.width();
    var mapH = Vars.world.height();

    if (Vars.state && Vars.state.rules) {
        Vars.state.rules.unitCap = Math.max(Vars.state.rules.unitCap, 2000);
        Vars.state.rules.unitCapVariable = false;
        Vars.state.rules.infiniteResources = true;
    }

    var dpFloors = [];
    var dpOverlays = [];
    var dpBlocks = [];

    var allBlocks = Vars.content.blocks();
    for (var i = 0; i < allBlocks.size; i++) {
        var b = allBlocks.get(i);
        if (!b || !b.name.startsWith("dp-") || b instanceof ConstructBlock) continue;
        if (b instanceof OverlayFloor) {
            dpOverlays.push(b);
        } else if (b instanceof Floor) {
            dpFloors.push(b);
        } else {
            dpBlocks.push(b);
        }
    }

    if (dpFloors.length + dpOverlays.length + dpBlocks.length === 0) {
        print("[Patchsthosus Test] 0 dp-* blocks loaded! Ensure DataPatch assets are in server config/assets/ (or loaded on this map).");
        return "0 dp-* blocks found.";
    }

    dpFloors.sort(function(a, b) { return a.name.localeCompare(b.name); });
    dpOverlays.sort(function(a, b) { return a.name.localeCompare(b.name); });
    dpBlocks.sort(function(a, b) { return (a.size - b.size) || a.name.localeCompare(b.name); });

    function areaHasCore(x0, y0, sz) {
        for (var dx = -1; dx <= sz; dx++) {
            for (var dy = -1; dy <= sz; dy++) {
                var t = Vars.world.tile(x0 + dx, y0 + dy);
                if (t && t.build && t.build.block && t.build.block.name.indexOf("core") !== -1) {
                    return true;
                }
            }
        }
        return false;
    }

    var curX = MARGIN;
    var curY = MARGIN;
    var floorsPlaced = 0, overlaysPlaced = 0, blocksPlaced = 0, unitsSpawned = 0;

    // 1. Place all dp-* Floor blocks (3x3 swatch each so variants & edges are visible)
    for (var fi = 0; fi < dpFloors.length; fi++) {
        var fl = dpFloors[fi];
        if (curX + 3 >= mapW - MARGIN) { curX = MARGIN; curY += 4; }
        if (curY + 3 >= mapH - MARGIN) break;
        if (!areaHasCore(curX, curY, 3)) {
            for (var fx = 0; fx < 3; fx++) {
                for (var fy = 0; fy < 3; fy++) {
                    var ft = Vars.world.tile(curX + fx, curY + fy);
                    if (ft) {
                        ft.setNet(Blocks.air);
                        ft.setFloorNet(fl, Blocks.air);
                    }
                }
            }
            floorsPlaced++;
        }
        curX += 4;
    }
    if (floorsPlaced > 0) { curX = MARGIN; curY += 5; }

    // 2. Place all dp-* OverlayFloor / Ore blocks (2x2 swatch on stone)
    for (var oi = 0; oi < dpOverlays.length; oi++) {
        var ov = dpOverlays[oi];
        if (curX + 2 >= mapW - MARGIN) { curX = MARGIN; curY += 3; }
        if (curY + 2 >= mapH - MARGIN) break;
        if (!areaHasCore(curX, curY, 2)) {
            for (var ox = 0; ox < 2; ox++) {
                for (var oy = 0; oy < 2; oy++) {
                    var ot = Vars.world.tile(curX + ox, curY + oy);
                    if (ot) {
                        ot.setNet(Blocks.air);
                        ot.setFloorNet(Blocks.stone, ov);
                    }
                }
            }
            overlaysPlaced++;
        }
        curX += 3;
    }
    if (overlaysPlaced > 0) { curX = MARGIN; curY += 5; }

    // 3. Place all dp-* Walls, Props, Turrets, Ducts, Conduits, Crafters, Cores, etc.
    var rowMaxSize = 1;
    for (var bi = 0; bi < dpBlocks.length; bi++) {
        var blk = dpBlocks[bi];
        var sz = Math.max(1, blk.size);
        if (curX + sz + 1 >= mapW - MARGIN) {
            curX = MARGIN;
            curY += rowMaxSize + 2;
            rowMaxSize = 1;
        }
        if (curY + sz + 1 >= mapH - MARGIN) break;

        var cx = curX + ((sz - 1) >> 1);
        var cy = curY + ((sz - 1) >> 1);
        var ct = Vars.world.tile(cx, cy);
        if (ct && !areaHasCore(curX, curY, sz)) {
            for (var bx = 0; bx < sz; bx++) {
                for (var by = 0; by < sz; by++) {
                    var bt = Vars.world.tile(curX + bx, curY + by);
                    if (bt) {
                        bt.setNet(Blocks.air);
                        if (bt.floor().isLiquid || !bt.floor().placeableOn) {
                            bt.setFloorNet(Blocks.stone, Blocks.air);
                        }
                    }
                }
            }
            var placeTeam = blk.hasBuilding() ? TEAM : Team.derelict;
            ct.setNet(blk, placeTeam, 0);
            blocksPlaced++;
        }
        if (sz > rowMaxSize) rowMaxSize = sz;
        curX += sz + 2;
    }

    // 4. Spawn all dp-* Units in a grid above the placed blocks
    curX = MARGIN + 2;
    curY += rowMaxSize + 8;

    var dpUnits = [];
    var allUnits = Vars.content.units();
    for (var ui = 0; ui < allUnits.size; ui++) {
        var u = allUnits.get(ui);
        if (!u || !u.name.startsWith("dp-") || u.internal) continue;
        if (!INCLUDE_MISSILES && (u instanceof MissileUnitType)) continue;
        dpUnits.push(u);
    }
    dpUnits.sort(function(a, b) { return (a.hitSize - b.hitSize) || a.name.localeCompare(b.name); });

    var rowStepY = 6;
    for (var si = 0; si < dpUnits.length; si++) {
        var ut = dpUnits[si];
        var cellTiles = Math.max(4, Math.ceil(ut.hitSize / Vars.tilesize) + 2);
        if (curX + cellTiles >= mapW - MARGIN) {
            curX = MARGIN + 2;
            curY += rowStepY;
            rowStepY = 6;
        }
        if (curY >= mapH - MARGIN) {
            curY = Math.max(MARGIN + 4, mapH - MARGIN - 4);
        }
        var midTileX = Math.floor(curX + cellTiles / 2);
        var midTileY = Math.floor(curY + cellTiles / 2);
        if (ut.naval) {
            var r = Math.max(2, Math.floor(cellTiles / 2));
            for (var wx = -r; wx <= r; wx++) {
                for (var wy = -r; wy <= r; wy++) {
                    var wt = Vars.world.tile(midTileX + wx, midTileY + wy);
                    if (wt && !wt.build) wt.setFloorNet(Blocks.deepwater, Blocks.air);
                }
            }
        }
        var spawned = ut.spawn(TEAM, (curX + cellTiles / 2) * Vars.tilesize, (curY + cellTiles / 2) * Vars.tilesize);
        if (spawned) unitsSpawned++;
        if (cellTiles + 2 > rowStepY) rowStepY = cellTiles + 2;
        curX += cellTiles + 1;
    }

    var msg = "[Patchsthosus Test] Placed " + floorsPlaced + " dp-* floors, " +
              overlaysPlaced + " dp-* overlays, " + blocksPlaced + " dp-* blocks/buildings, " +
              "and spawned " + unitsSpawned + " dp-* units!";
    print(msg);
    return msg;
})();
