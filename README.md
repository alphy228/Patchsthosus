# Patchsthosus

Play **Asthosus** on **unmodded vanilla Mindustry v8 (`v156` / `v160.7+`) clients** using Mindustry's native server-side **DataPatch** system (`config/assets/`) + automatic server-side `.msav` map conversion (`patchsthosus-plugin.jar`).

---

## Repository Contents

| Path | Description |
|---|---|
| `mod_to_datapatch.py` | Standalone Python 3 converter that turns JSON/HJSON Mindustry mods (like `Catana791/Asthosus`) into a Mindustry DataPatch `.zip` fitting the strict `500x500` `data-patch-reserved-env` atlas in **1 page**, while synthesizing missing multi-layer block `-full` icons, `RegionPart` `-outline` sprites, crawler `-segment-outline` sprites, and tank `-treads{r}-{i}` frames. |
| `patchsthosus-plugin/` | Java 17 Gradle server plugin (`patchsthosus-plugin.jar`) that automatically converts raw Asthosus `.msav` maps in `config/maps/` into Patchsthosus maps in memory — relying strictly on `config/assets/` without embedding assets into maps. |
| `scripts/test_all_dp_console.js` | Mindustry JS Console (`F8` / server `js`) script that places **all `dp-*` blocks** (floors, overlays, props, turrets, ducts, conduits, crafters, cores) and spawns **all `dp-*` units** on an empty test map. |
| `scripts/test_all_dp_world_processor.mlog` | Pure MLOG World Processor script (`< 300` instructions) that places **all `dp-*` blocks** and spawns **all `dp-*` units** without needing the JS console. |
| `scripts/generate_test_mlog.py` | Generator that builds `test_all_dp_world_processor.mlog` from any DataPatch `.zip`. |
| `.github/workflows/release.yml` | GitHub Actions workflow that fetches the latest `Catana791/Asthosus` release, generates `asthosus-datapatch.zip` (asserting 1-page `500x500` env atlas fit), builds `patchsthosus-plugin.jar`, and publishes a GitHub Release with both artifacts. |

---

## Dedicated Server Setup

1. Download **`asthosus-datapatch.zip`** and **`patchsthosus-plugin.jar`** from Releases (or build locally).
2. **Extract `asthosus-datapatch.zip` into `config/assets/`** (do **not** place it in `config/mods/`):
   ```bash
   mkdir -p config/assets config/mods config/maps
   unzip -o asthosus-datapatch.zip -d config/assets/
   ```
   Your `config/assets/` folder will contain `content/`, `patches/`, `sprites/`, `sounds/`, `music/`, and `bundles/`.
3. **Install the map converter plugin** in `config/mods/`:
   ```bash
   cp patchsthosus-plugin.jar config/mods/
   ```
4. **Drop raw Asthosus `.msav` maps** into `config/maps/` and start Mindustry server (`java -jar server-release.jar`).
   - Run `maps` / `patchsthosus-status` / `host <mapName>` — vanilla clients connect directly and download `config/assets/` automatically!

---

## What `patchsthosus-plugin` Converts & Enforces

- **No map-attached assets**: Never sets `hasExternalAssets` or writes `server-assets/*` into map files — assets live exclusively in `config/assets/`.
- **Processors on the map (`LogicBuild` & `MessageBuild`)**: Rewrites `@asthosus-*`, `@status-asthosus-*`, `@sfx-asthosus-*`, `item-asthosus-*`, and `asthosus-*` to `dp-*` in MLOG processor code and rich-text messages.
- **Generation tab's world logic (`genfilters`)**: Rewrites `LogicFilter.code` MLOG scripts and `OreFilter` / `ScatterFilter` / `ClearFilter` / `TerrainFilter` block references before `WorldContext` runs map generation filters.
- **Objectives system (`MapObjectives`)**: Rewrites `rules.objectives` (`ResearchObjective`, `ProduceObjective`, `ItemObjective`, `CoreItemObjective`, `BuildCountObjective`, `UnitCountObjective`, `DestroyBlockObjective`, `DestroyBlocksObjective`, `completionLogicCode`, `TextureMarker`, and `locales`).
- **Disables all non-Asthosus blocks + `hideBannedBlocks`**: Enforces `rules.planet = Planets.sun`, `rules.hideBannedBlocks = true`, bans every non-`dp-*` block (`!= Blocks.air`, unless in `revealedBlocks`), and preserves Asthosus (`dp-01a-*`) vs Trecara (`dp-22v-*`) tech splits.

---

## Testing All `dp-*` Units & Blocks on an Empty Map

Host or open an empty `200x200+` sandbox map (with `config/assets/` loaded) and choose any of the three methods:

1. **Server / Admin Command** (when `patchsthosus-plugin.jar` is installed):
   - Server console: `patchsthosus-test`
   - In-game admin chat: `/patchsthosus-test`
2. **JS Console Script** (`scripts/test_all_dp_console.js`):
   - Press `F8` in Mindustry client (or use `js` on server) and paste `scripts/test_all_dp_console.js`.
3. **World Processor MLOG** (`scripts/test_all_dp_world_processor.mlog`):
   - Place a `world-processor` on an empty `200x200+` map and paste `scripts/test_all_dp_world_processor.mlog`.

---

## Local Build Instructions

```bash
# 1. Convert an Asthosus mod checkout/zip into a DataPatch asset zip:
python3 mod_to_datapatch.py /path/to/Asthosus asthosus-datapatch.zip --env-limit 500 --mode auto

# 2. Build the server plugin JAR (requires JDK 17):
./patchsthosus-plugin/gradlew -p patchsthosus-plugin clean jar
```
