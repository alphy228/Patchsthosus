package patchsthosus;

import arc.Events;
import arc.files.Fi;
import arc.struct.ObjectMap;
import arc.struct.ObjectSet;
import arc.struct.Seq;
import arc.struct.StringMap;
import arc.util.Log;
import arc.util.Strings;
import arc.util.io.CounterInputStream;
import arc.util.serialization.JsonReader;
import arc.util.serialization.JsonValue;
import arc.util.serialization.JsonWriter;
import mindustry.Vars;
import mindustry.content.Blocks;
import mindustry.content.Planets;
import mindustry.ctype.ContentType;
import mindustry.ctype.MappableContent;
import mindustry.game.EventType;
import mindustry.game.GameStats;
import mindustry.game.Rules;
import mindustry.game.Teams.TeamData;
import mindustry.gen.Building;
import mindustry.gen.Groups;
import mindustry.io.JsonIO;
import mindustry.io.MapIO;
import mindustry.io.SaveFileReader;
import mindustry.io.SaveIO;
import mindustry.io.SaveReadState;
import mindustry.io.SaveVersion;
import mindustry.logic.LVar;
import mindustry.maps.Map;
import mindustry.maps.MapException;
import mindustry.mod.data.DataAsset;
import mindustry.mod.data.DataAssetType;
import mindustry.mod.data.PatchAsset;
import mindustry.type.Item;
import mindustry.type.ItemStack;
import mindustry.type.MapLocales;
import mindustry.world.Block;
import mindustry.world.Tile;
import mindustry.world.WorldContext;
import mindustry.world.blocks.logic.LogicBlock.LogicBuild;
import mindustry.world.blocks.logic.MessageBlock.MessageBuild;

import java.io.DataInput;
import java.io.DataInputStream;
import java.io.IOException;
import java.util.Locale;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.InflaterInputStream;

/**
 * Converts raw Asthosus mod {@code .msav} files (SaveVersion 4..13+) in {@code config/maps/}
 * on the fly into vanilla-compatible Patchsthosus worlds while keeping the original {@code .msav}
 * files untouched on disk and relying strictly on the dedicated server's native
 * {@code config/assets/} folder ({@link EventType.DataPatchLoadEvent}) rather than embedding
 * or applying DataPatch assets into map files.
 */
public final class AsthosusMapConverter {
    public static final String TAG_CONVERTED = "patchsthosus-converted";
    public static final String TAG_ORIG_PLANET = "patchsthosus-planet";
    public static final String TAG_HIDDEN_ITEMS = "patchsthosus-hidden-items";

    private static final String MOD_PREFIX = "asthosus-";
    private static final String DP_PREFIX = "dp-";
    private static final String SERVER_ASSET_PREFIX = "server-assets/";

    private static final Pattern PLANET_RULE_PATTERN = Pattern.compile(
        "(?:^|[,{\\s])\"?planet\"?\\s*:\\s*\"?(asthosus-[A-Za-z0-9_-]+)\"?"
    );

    private static final Pattern ASTHOSUS_TOKEN_PATTERN = Pattern.compile(
        "(@status-asthosus-|@sfx-asthosus-|@asthosus-|item-asthosus-|asthosus-)([A-Za-z0-9_-]+)"
    );

    private AsthosusMapConverter() {}

    /**
     * Queries the server's native {@code config/assets/} registry via {@link EventType.DataPatchLoadEvent}
     * without duplicating or embedding assets into maps.
     */
    public static Seq<DataAsset> queryServerAssets(Seq<PatchAsset> mapLocalPatches) {
        Seq<DataAsset> assets = new Seq<>();
        if (mapLocalPatches != null) {
            for (PatchAsset pa : mapLocalPatches) {
                if (pa != null) assets.add(pa);
            }
        }
        Events.fire(new EventType.DataPatchLoadEvent(assets));
        assets.sort();
        return assets;
    }

    /**
     * Returns true if {@code config/assets/} has DataPatch content files loaded by {@code ServerControl}.
     */
    public static boolean hasServerDataAssets() {
        Seq<DataAsset> assets = queryServerAssets(null);
        return assets.contains(a -> a.getType() == DataAssetType.content);
    }

    /**
     * Returns true if {@code map} is a raw Asthosus mod map (or already tagged by this plugin).
     */
    public static boolean isAsthosusMap(Map map) {
        if (map == null || !map.custom || map.file == null || !map.file.exists()) {
            return false;
        }
        if ("true".equals(map.tags.get(TAG_CONVERTED))) {
            return true;
        }
        for (String key : new String[]{"mods", "rules", "genfilters", "locales", "controlledType", "sectorPreset"}) {
            String val = map.tags.get(key, "");
            if (containsAsthosus(val)) {
                return true;
            }
        }
        return peekContentHeaderHasAsthosus(map.file);
    }

    private static boolean containsAsthosus(String s) {
        return s != null && s.toLowerCase(Locale.ROOT).contains("asthosus");
    }

    /**
     * Peeks only up to the {@code content} header region of an {@code .msav} file to check
     * whether any mapped content entry uses the {@code asthosus-} mod prefix.
     */
    public static boolean peekContentHeaderHasAsthosus(Fi msavFile) {
        try (CounterInputStream counter = new CounterInputStream(new InflaterInputStream(msavFile.read(16384)));
             DataInputStream stream = new DataInputStream(counter)) {
            SaveIO.readHeader(stream);
            int version = stream.readInt();
            SaveVersion ver = SaveIO.versions.get(version);
            if (ver == null) return false;

            skipLengthPrefixedRegion(stream); // meta
            if (version >= 12) {
                skipLengthPrefixedRegion(stream); // patches
            }

            int contentRegionLen = stream.readInt();
            if (contentRegionLen <= 0) return false;
            int mapped = stream.readUnsignedByte();
            for (int i = 0; i < mapped; i++) {
                stream.readByte(); // ContentType ordinal
                int total = stream.readShort();
                for (int j = 0; j < total; j++) {
                    String name = stream.readUTF();
                    if (name.startsWith(MOD_PREFIX) || name.startsWith("item-" + MOD_PREFIX)) {
                        return true;
                    }
                }
            }
        } catch (Throwable ignored) {
            // Ignore unreadable or non-standard files
        }
        return false;
    }

    /**
     * Rewrites {@code map.tags} in-memory so {@code ServerControl} / {@code Map.applyRules} /
     * {@code NetworkIO.writeWorld} see clean vanilla-compatible tags ({@code mods: []},
     * {@code dp-*} rules/spawns/loadout/objectives/weather, {@code genfilters} world logic,
     * {@code locales}, and {@code hideBannedBlocks: true}) without touching {@code config/maps/}
     * and without attaching assets to the map.
     */
    public static void sanitizeMapTagsInMemory(Map map) {
        if (map == null) return;
        sanitizeMetaTags(map.tags);
    }

    public static String sanitizeMetaTags(StringMap tags) {
        String existingPlanet = tags.get(TAG_ORIG_PLANET, "");
        String rawRules = tags.get("rules", "{}");
        String detectedPlanet = !existingPlanet.isEmpty() ? existingPlanet : detectOriginalPlanet(rawRules);

        if (!tags.containsKey(TAG_HIDDEN_ITEMS)) {
            String legacyHidden = extractLegacyHiddenItemsCsv(rawRules);
            if (!legacyHidden.isEmpty()) {
                tags.put(TAG_HIDDEN_ITEMS, legacyHidden);
            }
        }

        if (!detectedPlanet.isEmpty()) {
            tags.put(TAG_ORIG_PLANET, detectedPlanet);
        }
        tags.put(TAG_CONVERTED, "true");
        tags.put("mods", "[]");
        // Never mark maps as carrying embedded/map-attached external assets; assets live in server config/assets/
        tags.remove("hasExternalAssets");

        String sectorPreset = tags.get("sectorPreset", "");
        if (sectorPreset.startsWith(MOD_PREFIX)) {
            tags.remove("sectorPreset");
        }

        if (tags.containsKey("controlledType")) {
            tags.put("controlledType", rewriteIdentifierText(tags.get("controlledType", "")));
        }

        if (tags.containsKey("genfilters")) {
            tags.put("genfilters", rewriteGenFiltersJson(tags.get("genfilters", "")));
        }

        if (tags.containsKey("locales")) {
            tags.put("locales", rewriteLocalesJson(tags.get("locales", "{}")));
        }

        tags.put("rules", rewriteRulesJson(rawRules, detectedPlanet));
        return detectedPlanet;
    }

    public static String extractLegacyHiddenItemsCsv(String rulesJson) {
        if (rulesJson == null || !rulesJson.contains("hiddenBuildItems")) return "";
        try {
            JsonValue root = new JsonReader().parse(rulesJson);
            if (root == null || !root.isObject()) return "";
            JsonValue hbi = root.get("hiddenBuildItems");
            if (hbi == null) return "";
            if (hbi.isObject() && hbi.has("values")) {
                hbi = hbi.get("values");
            }
            if (hbi != null && hbi.isArray()) {
                Seq<String> names = new Seq<>();
                for (JsonValue v = hbi.child; v != null; v = v.next) {
                    String s = v.asString();
                    if (s != null && !s.isBlank()) {
                        names.add(rewriteSingleToken(s.trim()));
                    }
                }
                return names.toString(",");
            }
        } catch (Throwable ignored) {
        }
        return "";
    }

    public static String detectOriginalPlanet(String rulesJson) {
        if (rulesJson == null || rulesJson.isEmpty()) return "";
        try {
            JsonValue root = new JsonReader().parse(rulesJson);
            if (root != null && root.isObject() && root.has("planet")) {
                String p = root.getString("planet", "");
                if (p.startsWith(MOD_PREFIX)) {
                    return p;
                }
            }
        } catch (Throwable ignored) {
        }
        Matcher m = PLANET_RULE_PATTERN.matcher(rulesJson);
        return m.find() ? m.group(1) : "";
    }

    public static String rewriteRulesJson(String rulesJson, String originalPlanet) {
        if (rulesJson == null || rulesJson.isBlank()) {
            rulesJson = "{}";
        }
        try {
            JsonValue root = new JsonReader().parse(rulesJson);
            if (root == null || !root.isObject()) {
                return rewriteIdentifierText(rulesJson);
            }

            boolean isAsthosusPlanet = "asthosus-asthosus".equals(originalPlanet) || "asthosus-trecara".equals(originalPlanet);

            // Rewrite all asthosus-* content names across objectives, completionLogicCode, TextureMarker,
            // spawns, loadout, weather, bannedBlocks, bannedUnits, revealedBlocks, researched, blockLimits, etc.
            rewriteJsonValueInPlace(root);

            // Strip legacy v7 hiddenBuildItems field (removed in Mindustry v8 / v156+)
            root.remove("hiddenBuildItems");

            // Always use Planets.sun so dp-* items/blocks are visible on Mindustry v8
            setOrAddStringChild(root, "planet", "sun");

            // Always hide banned non-Asthosus blocks from the build menu
            setOrAddBooleanChild(root, "hideBannedBlocks", true);

            if (isAsthosusPlanet && !root.has("coreDestroyClear")) {
                root.addChild("coreDestroyClear", new JsonValue(true));
            }

            return root.toJson(JsonWriter.OutputType.minimal);
        } catch (Throwable t) {
            Log.warn("[Patchsthosus] Fallback text rewrite for rules JSON: @", t.getMessage());
            return rewriteIdentifierText(rulesJson);
        }
    }

    /**
     * Rewrites the Map Editor Generation tab's filter list ({@code genfilters}), including
     * {@code LogicFilter.code} world logic MLOG scripts and {@code OreFilter} / {@code ScatterFilter}
     * / {@code ClearFilter} / {@code TerrainFilter} block identifiers.
     */
    public static String rewriteGenFiltersJson(String filtersJson) {
        if (filtersJson == null || filtersJson.isBlank()) return filtersJson;
        try {
            JsonValue root = new JsonReader().parse(filtersJson);
            if (root == null) return rewriteIdentifierText(filtersJson);
            rewriteJsonValueInPlace(root);
            return root.toJson(JsonWriter.OutputType.minimal);
        } catch (Throwable ignored) {
            return rewriteIdentifierText(filtersJson);
        }
    }

    public static String rewriteLocalesJson(String localesJson) {
        if (localesJson == null || localesJson.isBlank()) return localesJson;
        try {
            JsonValue root = new JsonReader().parse(localesJson);
            if (root == null) return rewriteIdentifierText(localesJson);
            rewriteJsonValueInPlace(root);
            return root.toJson(JsonWriter.OutputType.minimal);
        } catch (Throwable ignored) {
            return rewriteIdentifierText(localesJson);
        }
    }

    private static void setOrAddStringChild(JsonValue obj, String key, String val) {
        JsonValue existing = obj.get(key);
        if (existing != null) {
            existing.set(val);
        } else {
            obj.addChild(key, new JsonValue(val));
        }
    }

    private static void setOrAddBooleanChild(JsonValue obj, String key, boolean val) {
        JsonValue existing = obj.get(key);
        if (existing != null) {
            existing.set(val);
        } else {
            obj.addChild(key, new JsonValue(val));
        }
    }

    private static void rewriteJsonValueInPlace(JsonValue node) {
        if (node == null) return;
        if (node.name != null) {
            node.setName(rewriteSingleToken(node.name));
        }
        if (node.isObject() || node.isArray()) {
            for (JsonValue child = node.child; child != null; child = child.next) {
                if ("planet".equals(child.name) && child.isString()) {
                    String p = child.asString();
                    if (p != null && (p.startsWith(MOD_PREFIX) || p.startsWith(DP_PREFIX))) {
                        child.set("sun");
                        continue;
                    }
                }
                rewriteJsonValueInPlace(child);
            }
        } else if (node.isString()) {
            String s = node.asString();
            if (s != null) {
                node.set(rewriteIdentifierText(s));
            }
        }
    }

    /**
     * Rewrites {@code asthosus-*} references inside strings, MLOG processor/filter/objective code,
     * rich-text icon tags, and content identifiers to {@code dp-*}.
     */
    public static String rewriteIdentifierText(String input) {
        if (input == null || !containsAsthosus(input)) return input;

        if ("asthosus-asthosus".equals(input) || "asthosus-trecara".equals(input)) {
            return "sun";
        }

        Matcher m = ASTHOSUS_TOKEN_PATTERN.matcher(input);
        StringBuilder sb = new StringBuilder(input.length());
        while (m.find()) {
            String prefix = m.group(1);
            String rest = m.group(2);
            String full = prefix + rest;
            String replacement;
            if ("asthosus-asthosus".equals(full) || "asthosus-trecara".equals(full)) {
                replacement = "sun";
            } else if ("@status-asthosus-".equals(prefix)) {
                replacement = "@status-dp-" + rest;
            } else if ("@sfx-asthosus-".equals(prefix)) {
                replacement = "@sfx-dp-" + rest;
            } else if ("@asthosus-".equals(prefix)) {
                replacement = "@dp-" + rest;
            } else if ("item-asthosus-".equals(prefix)) {
                replacement = "item-dp-" + rest;
            } else {
                replacement = DP_PREFIX + rest;
            }
            m.appendReplacement(sb, Matcher.quoteReplacement(replacement));
        }
        m.appendTail(sb);
        return sb.toString();
    }

    private static String rewriteSingleToken(String key) {
        if (key == null) return null;
        if ("asthosus-asthosus".equals(key) || "asthosus-trecara".equals(key)) {
            return "sun";
        }
        if (key.startsWith(MOD_PREFIX)) {
            return DP_PREFIX + key.substring(MOD_PREFIX.length());
        }
        return rewriteIdentifierText(key);
    }

    public static void applyPlanetRules(Rules rules, Map map) {
        if (rules == null) return;
        String origPlanet = map != null ? map.tags.get(TAG_ORIG_PLANET, "") : "";
        String hiddenItems = map != null ? map.tags.get(TAG_HIDDEN_ITEMS, "") : "";
        applyPlanetRules(rules, origPlanet, hiddenItems);
    }

    /**
     * Disables ALL non-Asthosus ({@code !name.startsWith("dp-")}) blocks, enables
     * {@code rules.hideBannedBlocks = true}, sets {@code rules.planet = Planets.sun}, and
     * enforces Asthosus vs Trecara cross-planet item exclusions once {@code dp-*} content is
     * registered in {@link Vars#content}.
     */
    public static void applyPlanetRules(Rules rules, String originalPlanet, String legacyHiddenCsv) {
        if (rules == null) return;

        rules.planet = Planets.sun;
        rules.hideBannedBlocks = true;

        boolean isAsthosus = "asthosus-asthosus".equals(originalPlanet);
        boolean isTrecara = "asthosus-trecara".equals(originalPlanet);
        boolean hasLegacyHidden = legacyHiddenCsv != null && !legacyHiddenCsv.isEmpty();

        if (rules.blockWhitelist) {
            // In whitelist mode, Rules.isBanned(b) is `true != bannedBlocks.contains(b)`.
            // Remove any non-dp-* blocks (unless explicitly revealed) so non-Asthosus blocks remain disabled.
            Seq<Block> toDrop = new Seq<>();
            for (Block b : rules.bannedBlocks) {
                if (b != null && !b.name.startsWith(DP_PREFIX) && !rules.revealedBlocks.contains(b)) {
                    toDrop.add(b);
                }
            }
            for (Block b : toDrop) {
                rules.bannedBlocks.remove(b);
            }
            return;
        }

        // 1. Disable ALL non-Asthosus blocks (`!block.name.startsWith("dp-")`)
        for (Block block : Vars.content.blocks()) {
            if (block == null || block == Blocks.air) continue;
            if (!block.name.startsWith(DP_PREFIX) && !rules.revealedBlocks.contains(block)) {
                rules.bannedBlocks.add(block);
            }
        }

        // 2. Also apply Asthosus vs Trecara planet tech split & legacy v7 hiddenBuildItems on dp-* blocks
        if (!isAsthosus && !isTrecara && !hasLegacyHidden) {
            return;
        }

        ObjectSet<Item> disallowedItems = new ObjectSet<>();
        if (hasLegacyHidden) {
            for (String token : legacyHiddenCsv.split(",")) {
                Item item = Vars.content.item(token.trim());
                if (item != null) disallowedItems.add(item);
            }
        }
        if (isAsthosus || isTrecara) {
            for (Item item : Vars.content.items()) {
                if (item == null) continue;
                if (isAsthosus && item.name.startsWith("dp-22v-")) {
                    disallowedItems.add(item);
                } else if (isTrecara && item.name.startsWith("dp-01a-")) {
                    disallowedItems.add(item);
                }
            }
        }

        if (!disallowedItems.isEmpty()) {
            for (Block block : Vars.content.blocks()) {
                if (block == null || !block.name.startsWith(DP_PREFIX)) continue;
                if (block.requirements == null || block.requirements.length == 0) continue;
                if (rules.revealedBlocks.contains(block)) continue;
                for (ItemStack stack : block.requirements) {
                    if (stack != null && stack.item != null && disallowedItems.contains(stack.item)) {
                        rules.bannedBlocks.add(block);
                        break;
                    }
                }
            }
        }
    }

    /**
     * Loads a raw Asthosus mod {@code .msav} map directly into {@link Vars#world} using the
     * DataPatch assets already loaded by Mindustry's dedicated server from {@code config/assets/}.
     * Never modifies {@code config/maps/} and never embeds server assets into maps.
     */
    public static void loadConvertedMap(Map map) {
        long t0 = System.currentTimeMillis();
        sanitizeMapTagsInMemory(map);
        String originalPlanet = map.tags.get(TAG_ORIG_PLANET, "");

        Seq<PatchAsset> extraMapPatches = extractEmbeddedMapPatches(map.file);
        Seq<DataAsset> serverAssets = queryServerAssets(extraMapPatches);
        if (!serverAssets.contains(a -> a.getType() == DataAssetType.content)) {
            throw new MapException(
                map,
                "Asthosus DataPatch assets not found in server 'config/assets/'! " +
                "Extract asthosus-datapatch.zip into 'config/assets/' and run 'reloadassets'."
            );
        }

        // Reset world/state cleanly and load server DataPatch assets (registers all dp-* content & @dp-* logicVars)
        Vars.logic.reset();
        Vars.state.data.load(serverAssets);

        WorldContext filterContext = Vars.world.filterContext(map);

        try (CounterInputStream counter = new CounterInputStream(new InflaterInputStream(map.file.read(32768)));
             DataInputStream stream = new DataInputStream(counter)) {

            SaveIO.readHeader(stream);
            int version = stream.readInt();
            SaveVersion ver = SaveIO.versions.get(version);
            if (ver == null) {
                throw new IOException("Unsupported Mindustry save version: " + version);
            }

            SaveReadState readState = new SaveReadState(filterContext);
            final String[] detectedPlanetHolder = {originalPlanet};

            // 1. Read & sanitize meta region (rules, objectives, genfilters world logic, locales)
            ver.readRegion("meta", stream, counter, in -> {
                StringMap fileMeta = ver.readStringMap(in);
                String p = sanitizeMetaTags(fileMeta);
                if (detectedPlanetHolder[0].isEmpty() && !p.isEmpty()) {
                    detectedPlanetHolder[0] = p;
                    map.tags.put(TAG_ORIG_PLANET, p);
                }
                if (fileMeta.containsKey(TAG_HIDDEN_ITEMS) && !map.tags.containsKey(TAG_HIDDEN_ITEMS)) {
                    map.tags.put(TAG_HIDDEN_ITEMS, fileMeta.get(TAG_HIDDEN_ITEMS));
                }
                // Sync sanitized rules, genfilters (LogicFilter world logic), and locales to map.tags
                // BEFORE ver.readMap runs FilterContext.applyFilters() and BEFORE ServerControl calls map.applyRules()!
                if (fileMeta.containsKey("genfilters")) {
                    map.tags.put("genfilters", fileMeta.get("genfilters"));
                }
                if (fileMeta.containsKey("locales")) {
                    map.tags.put("locales", fileMeta.get("locales"));
                }
                map.tags.put("rules", fileMeta.get("rules", "{}"));

                Vars.state.wave = fileMeta.getInt("wave");
                Vars.state.wavetime = fileMeta.getFloat("wavetime", Vars.state.rules.waveSpacing);
                Vars.state.tick = fileMeta.getFloat("tick");
                Vars.state.stats = JsonIO.read(GameStats.class, fileMeta.get("stats", "{}"));
                Vars.state.mapLocales = JsonIO.read(MapLocales.class, fileMeta.get("locales", "{}"));

                readState.ruleString = fileMeta.get("rules", "{}");
                ver.readRules(readState);
                applyPlanetRules(Vars.state.rules, map);
                Vars.state.map = map;
            });

            // 2. Skip patches region for SaveVersion >= 12 (server config/assets/ already loaded above)
            if (version >= 12) {
                skipLengthPrefixedRegion(stream);
            }

            // 3. Read & remap content header (asthosus-* -> dp-*) WITHOUT unloading state.data
            ver.readRegion("content", stream, counter, AsthosusMapConverter::readAndRemapContentHeader);

            // 3b. Skip patches region for SaveVersion == 11 (ordered right after content)
            if (version == 11) {
                skipLengthPrefixedRegion(stream);
            }

            // 4. Read map tiles & buildings (FilterContext.end() executes converted genfilters LogicFilter here!)
            ver.readRegion("map", stream, counter, in -> ver.readMap(in, readState));

            // 5. Read world & team entities
            ver.readRegion("entities", stream, counter, in -> ver.readEntities(in, readState));

            // 6. Read markers (SaveVersion >= 8)
            if (version >= 8) {
                ver.readRegion("markers", stream, counter, ver::readMarkers);
            }

            // 7. Read custom chunks (SaveVersion >= 7)
            if (version >= 7) {
                ver.readRegion("custom", stream, counter, ver::readCustomChunks);
            }

            // 8. Post-load live world fixes (MLOG World/Micro Processors, Message blocks, rules)
            int rewrittenProcessors = rewriteWorldProcessors();
            Vars.state.map = map;
            applyPlanetRules(Vars.state.rules, map);

            Events.fire(new EventType.SaveLoadEvent(true));

            if (!Vars.state.teams.getActive().contains(TeamData::hasCore)) {
                throw new MapException(map, "Map has no cores!");
            }

            long dt = System.currentTimeMillis() - t0;
            Log.info(
                "[Patchsthosus] Converted & loaded '@' (@, saveVer=@, @x@, planet=@, processorsUpdated=@) in @ms.",
                Strings.stripColors(map.name()), map.file.name(), version,
                Vars.world.width(), Vars.world.height(),
                detectedPlanetHolder[0].isEmpty() ? "vanilla" : detectedPlanetHolder[0],
                rewrittenProcessors, dt
            );
        } catch (MapException me) {
            throw me;
        } catch (Throwable t) {
            Log.err("[Patchsthosus] Failed to convert Asthosus map '" + map.file + "'", t);
            throw new MapException(map, "Patchsthosus conversion failed: " + t.getMessage());
        } finally {
            Vars.content.setTemporaryMapper(null);
            Vars.world.setGenerating(false);
        }
    }

    /**
     * Reads the binary {@code content} header and remaps every {@code asthosus-*} identifier
     * to its loaded {@code dp-*} counterpart before installing {@code content.setTemporaryMapper}.
     */
    private static void readAndRemapContentHeader(DataInput stream) throws IOException {
        int mapped = stream.readUnsignedByte();
        MappableContent[][] table = new MappableContent[ContentType.all.length][0];

        for (int i = 0; i < mapped; i++) {
            ContentType type = ContentType.all[stream.readByte()];
            int total = stream.readShort();
            table[type.ordinal()] = new MappableContent[total];

            for (int j = 0; j < total; j++) {
                String rawName = stream.readUTF();
                String targetName = remapContentHeaderName(type, rawName);
                String lookup = (type == ContentType.block)
                    ? SaveFileReader.fallback.get(targetName, targetName)
                    : targetName;
                table[type.ordinal()][j] = Vars.content.getByName(type, lookup);
            }
        }

        Vars.content.setTemporaryMapper(table);
    }

    public static String remapContentHeaderName(ContentType type, String rawName) {
        if (rawName == null) return "";
        return switch (type) {
            case item, block, liquid, status, unit, weather ->
                rawName.startsWith(MOD_PREFIX) ? DP_PREFIX + rawName.substring(MOD_PREFIX.length()) : rawName;
            case planet ->
                rawName.startsWith(MOD_PREFIX) ? "sun" : rawName;
            case unitStance ->
                rawName.startsWith("item-" + MOD_PREFIX) ? "mineauto" : rawName;
            default -> rawName;
        };
    }

    /**
     * Rewrites {@code @asthosus-*}, {@code @status-asthosus-*}, {@code @sfx-asthosus-*}, and
     * {@code asthosus-*} inside every {@link LogicBuild} processor (and {@link MessageBuild})
     * on the loaded map, preserving non-constant runtime variable values.
     */
    public static int rewriteWorldProcessors() {
        ObjectSet<Building> visited = new ObjectSet<>();
        int updated = 0;

        for (Building b : Groups.build) {
            if (b != null && visited.add(b) && rewriteBuildingContentRefs(b)) {
                updated++;
            }
        }

        if (Vars.world != null && Vars.world.tiles != null) {
            int w = Vars.world.width(), h = Vars.world.height();
            for (int x = 0; x < w; x++) {
                for (int y = 0; y < h; y++) {
                    Tile t = Vars.world.rawTile(x, y);
                    if (t != null && t.build != null && visited.add(t.build)) {
                        if (rewriteBuildingContentRefs(t.build)) updated++;
                    }
                }
            }
        }

        return updated;
    }

    private static boolean rewriteBuildingContentRefs(Building build) {
        if (build instanceof LogicBuild lb) {
            return rewriteProcessorBuild(lb);
        }
        if (build instanceof MessageBuild mb && mb.message != null && containsAsthosus(mb.message.toString())) {
            String updated = rewriteIdentifierText(mb.message.toString());
            if (!updated.equals(mb.message.toString())) {
                mb.message.setLength(0);
                mb.message.append(updated);
                return true;
            }
        }
        return false;
    }

    private static boolean rewriteProcessorBuild(LogicBuild lb) {
        lb.checkReadCode();
        if (lb.code == null || !containsAsthosus(lb.code)) {
            return false;
        }
        String newCode = rewriteIdentifierText(lb.code);
        if (newCode.equals(lb.code)) {
            return false;
        }

        // Snapshot non-constant runtime variable state before recompiling MLOG assembly
        ObjectMap<String, LVar> savedVars = new ObjectMap<>();
        if (lb.executor != null && lb.executor.vars != null) {
            for (LVar v : lb.executor.vars) {
                if (v != null && !v.constant && !(v.isobj && v.objval == null)) {
                    LVar copy = new LVar(v.name);
                    copy.isobj = v.isobj;
                    copy.objval = v.objval;
                    copy.numval = v.numval;
                    savedVars.put(v.name, copy);
                }
            }
        }

        lb.updateCode(newCode, true, asm -> {
            for (ObjectMap.Entry<String, LVar> entry : savedVars.entries()) {
                LVar target = asm.getVar(entry.key);
                if (target != null && !target.constant) {
                    target.isobj = entry.value.isobj;
                    target.objval = entry.value.objval;
                    target.numval = entry.value.numval;
                }
            }
        });
        return true;
    }

    /**
     * Extracts any map-local JSON stat patches embedded inside the {@code patches} region
     * of a Save11/Save12/Save13 {@code .msav} file, rewriting {@code asthosus-*} -> {@code dp-*}.
     */
    private static Seq<PatchAsset> extractEmbeddedMapPatches(Fi msavFile) {
        Seq<PatchAsset> extras = new Seq<>();
        try (CounterInputStream counter = new CounterInputStream(new InflaterInputStream(msavFile.read(16384)));
             DataInputStream stream = new DataInputStream(counter)) {
            SaveIO.readHeader(stream);
            int version = stream.readInt();
            if (version < 11) return extras;

            skipLengthPrefixedRegion(stream); // meta
            if (version == 11) {
                skipLengthPrefixedRegion(stream); // content comes before patches in Save11
            }

            int patchRegionLen = stream.readInt();
            if (patchRegionLen <= 0) return extras;

            if (version == 11) {
                int count = stream.readUnsignedByte();
                for (int i = 0; i < count; i++) {
                    byte[] bytes = new byte[stream.readInt()];
                    stream.readFully(bytes);
                    String text = rewriteIdentifierText(new String(bytes, Strings.utf8));
                    extras.add(new PatchAsset(text));
                }
            } else if (version == 12) {
                stream.readInt(); // reserved
                int count = stream.readInt();
                for (int i = 0; i < count; i++) {
                    byte[] bytes = new byte[stream.readInt()];
                    stream.readFully(bytes);
                    String text = rewriteIdentifierText(new String(bytes, Strings.utf8));
                    extras.add(new PatchAsset(text));
                }
            } else {
                int fmt = stream.readInt();
                if (fmt == 2) {
                    int count = stream.readInt();
                    for (int i = 0; i < count; i++) {
                        int typeOrd = stream.readByte();
                        String path = stream.readUTF();
                        boolean embedded = stream.readBoolean();
                        if (!embedded) {
                            byte[] hash = new byte[32];
                            stream.readFully(hash);
                        } else if (typeOrd == 0) { // DataAssetType.patch
                            byte[] bytes = new byte[stream.readInt()];
                            stream.readFully(bytes);
                            PatchAsset pa = new PatchAsset(rewriteIdentifierText(new String(bytes, Strings.utf8)));
                            pa.setPath(path);
                            extras.add(pa);
                        } else if (typeOrd == 1) { // DataAssetType.content
                            stream.readShort();
                            int len = stream.readInt();
                            skipFully(stream, len);
                        } else {
                            int len = stream.readInt();
                            skipFully(stream, len);
                        }
                    }
                }
            }
        } catch (Throwable ignored) {
        }
        return extras;
    }

    /**
     * Exports a converted SaveVersion 13 {@code .msav} map WITHOUT applying or embedding any
     * {@code server-assets/} DataPatch files into the map (so the exported map relies strictly
     * on the server's {@code config/assets/} folder).
     */
    public static void exportConvertedMapWithoutAssets(Map map, Fi outFile) throws IOException {
        loadConvertedMap(map);
        Vars.state.rules = map.rules();
        applyPlanetRules(Vars.state.rules, map);

        // Strip server-assets/* from orderedAssets before MapIO.writeMap so zero server assets
        // are written into the map's patches chunk while keeping dp-* content active for writeContentHeader!
        Vars.state.data.getAllAssets().removeAll(a -> a != null && a.path != null && a.path.startsWith(SERVER_ASSET_PREFIX));
        map.tags.remove("hasExternalAssets");

        outFile.parent().mkdirs();
        MapIO.writeMap(outFile, map, false);
        map.tags.remove("hasExternalAssets");
    }

    private static void skipLengthPrefixedRegion(DataInput stream) throws IOException {
        int len = stream.readInt();
        skipFully(stream, len);
    }

    private static void skipFully(DataInput stream, int len) throws IOException {
        int remaining = len;
        byte[] buf = new byte[Math.min(Math.max(remaining, 1), 16384)];
        while (remaining > 0) {
            int chunk = Math.min(remaining, buf.length);
            stream.readFully(buf, 0, chunk);
            remaining -= chunk;
        }
    }
}
