package patchsthosus;

import arc.Events;
import arc.files.Fi;
import arc.struct.Seq;
import arc.util.CommandHandler;
import arc.util.Log;
import arc.util.Strings;
import mindustry.Vars;
import mindustry.core.World;
import mindustry.game.EventType.RulesLoadEvent;
import mindustry.game.EventType.ServerLoadEvent;
import mindustry.game.Rules;
import mindustry.game.Team;
import mindustry.gen.Player;
import mindustry.maps.Map;
import mindustry.mod.Plugin;
import mindustry.mod.data.DataAsset;
import mindustry.mod.data.DataAssetType;

/**
 * Mindustry dedicated server plugin that automatically detects raw Asthosus mod {@code .msav}
 * maps in {@code config/maps/} and converts them in memory into vanilla-compatible Patchsthosus
 * maps on load — relying strictly on Mindustry's native {@code config/assets/} folder without
 * modifying map files on disk or embedding DataPatch assets into maps.
 */
public class PatchsthosusPlugin extends Plugin {
    private boolean worldHookInstalled = false;

    @Override
    public void init() {
        Events.on(ServerLoadEvent.class, e -> {
            installWorldMapHook();
            int count = refreshCustomMaps();
            Seq<DataAsset> serverAssets = AsthosusMapConverter.queryServerAssets(null);
            int contentFiles = serverAssets.count(a -> a.getType() == DataAssetType.content);
            if (contentFiles > 0) {
                Log.info(
                    "[Patchsthosus] Ready: @ server DataPatch assets (@ content files) in config/assets/; @ Asthosus mod map(s) ready in config/maps/.",
                    serverAssets.size, contentFiles, count
                );
            } else {
                Log.warn(
                    "[Patchsthosus] Server loaded (@ Asthosus map(s) found), but config/assets/ has 0 DataPatch content files! " +
                    "Extract asthosus-datapatch.zip into config/assets/ and run 'reloadassets'.",
                    count
                );
            }
        });

        // ServerControl overwrites Vars.state.rules via map.applyRules(mode) right after world.loadMap
        // and then fires RulesLoadEvent: enforce planet=sun, hideBannedBlocks=true, and non-dp-* bans here too.
        Events.on(RulesLoadEvent.class, e -> {
            Map activeMap = Vars.state != null ? Vars.state.map : null;
            if (activeMap != null && "true".equals(activeMap.tags.get(AsthosusMapConverter.TAG_CONVERTED))) {
                AsthosusMapConverter.applyPlanetRules(e.rules, activeMap);
            }
        });
    }

    /**
     * Replaces {@link Vars#world} with a lightweight subclass overriding {@link World#loadMap(Map, Rules)}
     * so raw Asthosus {@code .msav} files in {@code config/maps/} are converted on load while vanilla
     * and non-Asthosus maps delegate directly to {@code super.loadMap(map, checkRules)}.
     */
    private void installWorldMapHook() {
        if (worldHookInstalled) return;
        Vars.world = new World() {
            @Override
            public void loadMap(Map map, Rules checkRules) {
                if (AsthosusMapConverter.isAsthosusMap(map)) {
                    AsthosusMapConverter.loadConvertedMap(map);
                } else {
                    super.loadMap(map, checkRules);
                }
            }
        };
        worldHookInstalled = true;
    }

    /**
     * Scans {@code Vars.maps.customMaps()} and rewrites {@code map.tags} in memory for any raw
     * Asthosus mod map ({@code mods: []}, {@code hideBannedBlocks: true}, {@code dp-*} rules/spawns/
     * objectives/genfilters/locales, and zero map-attached assets) while keeping {@code config/maps/*.msav} untouched.
     */
    public int refreshCustomMaps() {
        if (Vars.maps == null) return 0;
        int converted = 0;
        for (Map map : Vars.maps.customMaps()) {
            if (AsthosusMapConverter.isAsthosusMap(map)) {
                AsthosusMapConverter.sanitizeMapTagsInMemory(map);
                converted++;
            }
        }
        return converted;
    }

    @Override
    public void registerServerCommands(CommandHandler handler) {
        handler.register("patchsthosus-status", "Show Patchsthosus config/assets/ status and detected Asthosus maps.", args -> {
            Seq<DataAsset> serverAssets = AsthosusMapConverter.queryServerAssets(null);
            int contentCount = serverAssets.count(a -> a.getType() == DataAssetType.content);
            int spriteCount = serverAssets.count(a -> a.getType() == DataAssetType.image);
            Log.info(
                "[Patchsthosus] config/assets/: @ total assets (@ content, @ sprites).",
                serverAssets.size, contentCount, spriteCount
            );
            int found = refreshCustomMaps();
            Log.info("[Patchsthosus] Detected @ Asthosus custom map(s) in @:", found, Vars.customMapDirectory.absolutePath());
            for (Map m : Vars.maps.customMaps()) {
                if (AsthosusMapConverter.isAsthosusMap(m)) {
                    Log.info("  - @ (@, @x@, origPlanet=@)",
                        Strings.stripColors(m.name()),
                        m.file.name(),
                        m.width,
                        m.height,
                        m.tags.get(AsthosusMapConverter.TAG_ORIG_PLANET, "unknown")
                    );
                }
            }
        });

        handler.register("patchsthosus-reload", "Reload custom maps and refresh Asthosus in-memory map tags.", args -> {
            Vars.maps.reload();
            int count = refreshCustomMaps();
            Log.info("[Patchsthosus] Reloaded custom maps (@ Asthosus map(s) ready). Run 'reloadassets' to reload config/assets/.", count);
        });

        handler.register("patchsthosus-export", "<mapName|all> [outDir]",
            "Export converted Patchsthosus .msav map(s) WITHOUT embedding server assets.", args -> {
                if (!AsthosusMapConverter.hasServerDataAssets()) {
                    Log.err("[Patchsthosus] Cannot export: config/assets/ has no DataPatch content files loaded.");
                    return;
                }
                Fi outDir = args.length >= 2
                    ? new Fi(args[1])
                    : Vars.dataDirectory.child("exported-patchsthosus-maps");
                outDir.mkdirs();

                refreshCustomMaps();
                String target = args[0];
                Seq<Map> targets = new Seq<>();
                if ("all".equalsIgnoreCase(target)) {
                    for (Map m : Vars.maps.customMaps()) {
                        if (AsthosusMapConverter.isAsthosusMap(m)) targets.add(m);
                    }
                } else {
                    Map m = Vars.maps.customMaps().find(map ->
                        Strings.stripColors(map.name()).replace(' ', '_').equalsIgnoreCase(target.replace(' ', '_'))
                        || map.file.name().equalsIgnoreCase(target)
                        || map.file.nameWithoutExtension().equalsIgnoreCase(target)
                    );
                    if (m != null) targets.add(m);
                }

                if (targets.isEmpty()) {
                    Log.err("[Patchsthosus] No matching Asthosus map found for '@'.", target);
                    return;
                }

                for (Map m : targets) {
                    try {
                        Fi outFile = outDir.child(m.file.nameWithoutExtension() + "-patchsthosus.msav");
                        AsthosusMapConverter.exportConvertedMapWithoutAssets(m, outFile);
                        Log.info("[Patchsthosus] Exported '@' -> @ (@ KB, 0 embedded server assets)",
                            Strings.stripColors(m.name()), outFile.absolutePath(), outFile.length() / 1024L);
                    } catch (Throwable t) {
                        Log.err("[Patchsthosus] Failed to export map '" + m.file.name() + "'", t);
                    }
                }
            }
        );

        handler.register("patchsthosus-test", "[team] [missiles]",
            "Place all dp-* blocks and spawn all dp-* units on the active map for testing.", args -> {
                if (!Vars.state.isPlaying() && !Vars.state.isPaused()) {
                    Log.err("[Patchsthosus] Host a map first (e.g. 'host' an empty sandbox map), then run 'patchsthosus-test'.");
                    return;
                }
                ensureDpContentLoadedForTesting();
                Team team = Team.sharded;
                if (args.length >= 1) {
                    for (Team t : Team.all) {
                        if (t != null && t.name != null && t.name.equalsIgnoreCase(args[0])) {
                            team = t;
                            break;
                        }
                    }
                }
                boolean includeMissiles = args.length >= 2 && ("true".equalsIgnoreCase(args[1]) || "missiles".equalsIgnoreCase(args[1]));
                PatchsthosusTestSpawner.SpawnSummary res = PatchsthosusTestSpawner.populateCurrentMap(team, includeMissiles);
                Log.info(
                    "[Patchsthosus] Test showcase spawned on team '@': @ floors, @ overlays, @ blocks/buildings, @ units.",
                    team.name, res.floorsPlaced(), res.overlaysPlaced(), res.blocksPlaced(), res.unitsSpawned()
                );
            }
        );
    }

    @Override
    public void registerClientCommands(CommandHandler handler) {
        handler.<Player>register("patchsthosus-test", "[missiles]",
            "(Admin) Place all dp-* blocks and spawn all dp-* units on the current map.", (args, player) -> {
                if (!player.admin) {
                    player.sendMessage("[scarlet]Admin permission required.");
                    return;
                }
                ensureDpContentLoadedForTesting();
                boolean includeMissiles = args.length >= 1 && ("true".equalsIgnoreCase(args[0]) || "missiles".equalsIgnoreCase(args[0]));
                PatchsthosusTestSpawner.SpawnSummary res = PatchsthosusTestSpawner.populateCurrentMap(player.team(), includeMissiles);
                player.sendMessage(Strings.format(
                    "[accent][Patchsthosus][] Placed [stat]@[] floors, [stat]@[] overlays, [stat]@[] blocks, and spawned [stat]@[] dp-* units!",
                    res.floorsPlaced(), res.overlaysPlaced(), res.blocksPlaced(), res.unitsSpawned()
                ));
            }
        );
    }

    private static void ensureDpContentLoadedForTesting() {
        boolean anyLoaded = Vars.content.blocks().contains(b -> b != null && b.name.startsWith("dp-"));
        if (!anyLoaded) {
            Seq<DataAsset> serverAssets = AsthosusMapConverter.queryServerAssets(null);
            if (!serverAssets.isEmpty()) {
                Vars.state.data.load(serverAssets);
            }
        }
    }
}
