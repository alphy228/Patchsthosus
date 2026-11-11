package patchsthosus;

import arc.struct.Seq;
import mindustry.Vars;
import mindustry.content.Blocks;
import mindustry.game.Team;
import mindustry.gen.Unit;
import mindustry.type.UnitType;
import mindustry.type.unit.MissileUnitType;
import mindustry.world.Block;
import mindustry.world.Tile;
import mindustry.world.blocks.ConstructBlock;
import mindustry.world.blocks.environment.Floor;
import mindustry.world.blocks.environment.OverlayFloor;

/**
 * Utility that places all {@code dp-*} blocks (floors, overlays, environment walls/props,
 * and functional buildings) and spawns all {@code dp-*} units in organized grids on an
 * active test map for visual and functional verification.
 */
public final class PatchsthosusTestSpawner {
    private static final String DP_PREFIX = "dp-";

    public record SpawnSummary(int floorsPlaced, int overlaysPlaced, int blocksPlaced, int unitsSpawned) {}

    private PatchsthosusTestSpawner() {}

    public static SpawnSummary populateCurrentMap(Team team, boolean includeMissiles) {
        if (Vars.world == null || Vars.world.tiles == null) {
            return new SpawnSummary(0, 0, 0, 0);
        }
        int mapW = Vars.world.width();
        int mapH = Vars.world.height();
        int margin = 6;

        // Ensure infinite unit cap so all dp-* units can coexist simultaneously during testing
        if (Vars.state != null && Vars.state.rules != null) {
            Vars.state.rules.unitCap = Math.max(Vars.state.rules.unitCap, 2000);
            Vars.state.rules.unitCapVariable = false;
        }

        Seq<Block> dpFloors = new Seq<>();
        Seq<Block> dpOverlays = new Seq<>();
        Seq<Block> dpBlocks = new Seq<>();

        for (Block b : Vars.content.blocks()) {
            if (b == null || !b.name.startsWith(DP_PREFIX) || b instanceof ConstructBlock) continue;
            if (b instanceof OverlayFloor) {
                dpOverlays.add(b);
            } else if (b instanceof Floor) {
                dpFloors.add(b);
            } else {
                dpBlocks.add(b);
            }
        }

        dpFloors.sort((a, b) -> a.name.compareTo(b.name));
        dpOverlays.sort((a, b) -> a.name.compareTo(b.name));
        dpBlocks.sort((a, b) -> {
            int cmp = Integer.compare(a.size, b.size);
            return cmp != 0 ? cmp : a.name.compareTo(b.name);
        });

        int curX = margin;
        int curY = margin;
        int floorsPlaced = 0;
        int overlaysPlaced = 0;
        int blocksPlaced = 0;

        // 1. Place all dp-* Floor blocks (3x3 swatch per floor so variants & edges are visible)
        for (Block fl : dpFloors) {
            if (curX + 3 >= mapW - margin) {
                curX = margin;
                curY += 4;
            }
            if (curY + 3 >= mapH - margin) break;
            for (int dx = 0; dx < 3; dx++) {
                for (int dy = 0; dy < 3; dy++) {
                    Tile t = Vars.world.tile(curX + dx, curY + dy);
                    if (t != null && !hasCoreNearby(t)) {
                        t.setNet(Blocks.air);
                        t.setFloorNet(fl, Blocks.air);
                    }
                }
            }
            floorsPlaced++;
            curX += 4;
        }

        if (floorsPlaced > 0) {
            curX = margin;
            curY += 5;
        }

        // 2. Place all dp-* OverlayFloor / Ore blocks (2x2 swatch on stone)
        for (Block ov : dpOverlays) {
            if (curX + 2 >= mapW - margin) {
                curX = margin;
                curY += 3;
            }
            if (curY + 2 >= mapH - margin) break;
            for (int dx = 0; dx < 2; dx++) {
                for (int dy = 0; dy < 2; dy++) {
                    Tile t = Vars.world.tile(curX + dx, curY + dy);
                    if (t != null && !hasCoreNearby(t)) {
                        t.setNet(Blocks.air);
                        t.setFloorNet(Blocks.stone, ov);
                    }
                }
            }
            overlaysPlaced++;
            curX += 3;
        }

        if (overlaysPlaced > 0) {
            curX = margin;
            curY += 5;
        }

        // 3. Place all dp-* Blocks & Buildings (turrets, ducts, conduits, crafters, cores, env walls/props)
        int rowMaxSize = 1;
        for (Block blk : dpBlocks) {
            int sz = Math.max(1, blk.size);
            if (curX + sz + 1 >= mapW - margin) {
                curX = margin;
                curY += rowMaxSize + 2;
                rowMaxSize = 1;
            }
            if (curY + sz + 1 >= mapH - margin) break;

            // Compute tile center using Mindustry's multiblock offset convention:
            // center tile index = bottomLeft + (size - 1) / 2
            int centerX = curX + (sz - 1) / 2;
            int centerY = curY + (sz - 1) / 2;
            Tile centerTile = Vars.world.tile(centerX, centerY);

            if (centerTile != null && !areaHasCore(curX, curY, sz)) {
                // Ensure solid floor underneath so placement succeeds even over water/space
                for (int dx = 0; dx < sz; dx++) {
                    for (int dy = 0; dy < sz; dy++) {
                        Tile ft = Vars.world.tile(curX + dx, curY + dy);
                        if (ft != null) {
                            ft.setNet(Blocks.air);
                            if (ft.floor().isLiquid || !ft.floor().placeableOn) {
                                ft.setFloorNet(Blocks.stone, Blocks.air);
                            }
                        }
                    }
                }
                Team placeTeam = blk.hasBuilding() ? team : Team.derelict;
                centerTile.setNet(blk, placeTeam, 0);
                blocksPlaced++;
            }

            rowMaxSize = Math.max(rowMaxSize, sz);
            curX += sz + 2;
        }

        // 4. Spawn all dp-* Units in a grid above the block showcase
        curX = margin + 2;
        curY += rowMaxSize + 8;
        int unitsSpawned = 0;

        Seq<UnitType> dpUnits = new Seq<>();
        for (UnitType u : Vars.content.units()) {
            if (u == null || !u.name.startsWith(DP_PREFIX) || u.internal) continue;
            if (!includeMissiles && u instanceof MissileUnitType) continue;
            dpUnits.add(u);
        }
        dpUnits.sort((a, b) -> Float.compare(a.hitSize, b.hitSize));

        int rowStepY = 6;
        for (UnitType ut : dpUnits) {
            int cellTiles = Math.max(4, (int) Math.ceil(ut.hitSize / Vars.tilesize) + 2);
            if (curX + cellTiles >= mapW - margin) {
                curX = margin + 2;
                curY += rowStepY;
                rowStepY = 6;
            }
            if (curY >= mapH - margin) {
                // Wrap Y gently if map is small so remaining units still spawn
                curY = Math.max(margin + 4, mapH - margin - 4);
            }
            float wx = (curX + cellTiles / 2f) * Vars.tilesize;
            float wy = (curY + cellTiles / 2f) * Vars.tilesize;

            // Ensure naval units get deep water under them so they don't take beaching/drowning penalties
            if (ut.naval) {
                int r = Math.max(2, cellTiles / 2);
                for (int dx = -r; dx <= r; dx++) {
                    for (int dy = -r; dy <= r; dy++) {
                        Tile wt = Vars.world.tile(curX + cellTiles / 2 + dx, curY + cellTiles / 2 + dy);
                        if (wt != null && wt.build == null) {
                            wt.setFloorNet(Blocks.deepwater, Blocks.air);
                        }
                    }
                }
            }

            Unit spawned = ut.spawn(team, wx, wy);
            if (spawned != null) {
                unitsSpawned++;
            }
            rowStepY = Math.max(rowStepY, cellTiles + 2);
            curX += cellTiles + 1;
        }

        return new SpawnSummary(floorsPlaced, overlaysPlaced, blocksPlaced, unitsSpawned);
    }

    private static boolean hasCoreNearby(Tile tile) {
        return tile.build != null && tile.build.block != null && tile.build.block.name.contains("core");
    }

    private static boolean areaHasCore(int x0, int y0, int size) {
        for (int dx = -1; dx <= size; dx++) {
            for (int dy = -1; dy <= size; dy++) {
                Tile t = Vars.world.tile(x0 + dx, y0 + dy);
                if (t != null && hasCoreNearby(t)) return true;
            }
        }
        return false;
    }
}
