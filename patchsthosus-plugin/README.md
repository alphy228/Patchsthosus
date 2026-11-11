# Patchsthosus Server Plugin (`patchsthosus-plugin`)

Mindustry v8 (`v156` / `v160.7+`) dedicated server plugin that **automatically converts raw Asthosus mod `.msav` maps in `config/maps/` into vanilla-compatible Patchsthosus maps on load** while relying strictly on Mindustry's native `config/assets/` folder.

## Key Design Guarantees

- **Zero map-embedded assets**: Never embeds or attaches DataPatch assets into maps (`hasExternalAssets` is never set, and exported maps contain `0` entries in their `patches` chunk). All `dp-*` content, sprites, sounds, music, and bundles are served natively from the server's `config/assets/` directory via Mindustry's `DataPatchLoadEvent`.
- **Untouched `config/maps/`**: Raw Asthosus `.msav` files (SaveVersion 7..13+) remain unmodified on disk.
- **Complete `asthosus-*` -> `dp-*` conversion**:
  1. Binary `content` header remapping (`item`, `block`, `liquid`, `status`, `unit`, `weather`, `planet` -> `sun`, `unitStance` -> `mineauto`).
  2. **Processors on the map** (`LogicBuild` Micro/Logic/Hyper/World Processors & `MessageBuild` rich text): rewrites `@asthosus-*`, `@status-asthosus-*`, `@sfx-asthosus-*`, `item-asthosus-*`, and `asthosus-*` to `dp-*` while preserving runtime variable state.
  3. **Generation tab world logic** (`genfilters` -> `LogicFilter.code`, `OreFilter`, `ScatterFilter`, `ClearFilter`, `TerrainFilter`): rewritten and synced to `map.tags` before `WorldContext` executes map filters.
  4. **Objectives system** (`rules.objectives` -> `ResearchObjective`, `ProduceObjective`, `BuildCountObjective`, `UnitCountObjective`, `DestroyBlockObjective`, `DestroyBlocksObjective`, `completionLogicCode`, `TextureMarker`, and `locales`).
- **Strict Asthosus build menu**: Automatically sets `rules.planet = Planets.sun`, enables `rules.hideBannedBlocks = true`, bans **all non-`dp-*` blocks**, and enforces Asthosus (`dp-01a-*`) vs Trecara (`dp-22v-*`) planet tech exclusions.

## Server Setup

1. Extract `asthosus-datapatch.zip` directly into `config/assets/` so you have:
   - `config/assets/content/`
   - `config/assets/patches/`
   - `config/assets/sprites/`
   - `config/assets/sounds/`
   - `config/assets/music/`
   - `config/assets/bundles/`
2. Copy `patchsthosus-plugin.jar` into `config/mods/`.
3. Place raw Asthosus `.msav` maps in `config/maps/` (do **not** install the Asthosus mod zip in `config/mods/`).
4. Start the server (`java -jar server-release.jar`) and `host <mapName>`!

## Server & Admin Commands

| Command | Scope | Description |
|---|---|---|
| `patchsthosus-status` | Server console | Show `config/assets/` counts and list detected Asthosus maps in `config/maps/`. |
| `patchsthosus-reload` | Server console | Reload custom maps and refresh in-memory Asthosus map tags (pair with `reloadassets` if `config/assets/` changed). |
| `patchsthosus-export <map\|all> [outDir]` | Server console | Export converted Save13 `.msav` map(s) **without** embedding server assets. |
| `patchsthosus-test [team] [missiles]` | Server console | Place all `dp-*` blocks (floors, overlays, props, buildings) and spawn all `dp-*` units on the active map. |
| `/patchsthosus-test [missiles]` | In-game Admin | In-game admin chat command to run the full `dp-*` block & unit test showcase on the active map. |

## Building

Requires Java 17:

```bash
./gradlew clean jar
# Or against a local Mindustry server JAR:
./gradlew clean jar -PserverJar=/path/to/server-release.jar
```

Output JAR: `build/libs/patchsthosus-plugin.jar`.
