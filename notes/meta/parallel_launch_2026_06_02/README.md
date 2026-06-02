# Manual Parallel Launch Pack — 2026-06-02

This pack is for manual Codex sessions launched over SSH on `omen01.local`.
It deliberately does not use Codex app `create_thread`, because that tool targets
the locally saved `/Users/ywr/odd-order` project rather than the remote
`/home/ywr/odd-order` checkout.

## Operating Rule

Every lane must run on `omen01.local` and use `/home/ywr/odd-order` as the main
checkout. Do not use `/Users/ywr/...` paths.

Each lane prompt is self-contained:

- It defines a dedicated worktree path and branch.
- It bootstraps `.lake/packages` and `references` as symlinks to the main
  checkout.
- It copies `.lake/build` into the lane worktree for warm-start builds.
- It forbids `lake update` and `push`.
- It includes an explicit goal and several hours of scoped work.

## Recommended Wave

Start the first five lanes. The sixth lane is optional if there is enough
capacity to monitor and merge results.

| Lane | Prompt File | Worktree | Goal |
|---|---|---|---|
| P1 | `prompts/lane_p1_peterfalvi_brauer_inertia.md` | `/home/ywr/odd-order-pf-brauer-inertia` | Complete issue 0053 Layer C: free conjugacy-class action to `inertia = H`. |
| P2 | `prompts/lane_p2_peterfalvi_s08_67_wiring.md` | `/home/ywr/odd-order-pf-s08-67` | Turn Peterfalvi (6.7) from atom-level infrastructure into a top theorem. |
| P3 | `prompts/lane_p3_peterfalvi_s09_estimates.md` | `/home/ywr/odd-order-pf-s09-estimates` | Advance (7.8) norm estimates and `CharacterEstimateData` construction. |
| I1 | `prompts/lane_i1_isaacs_ch07_pcomplement.md` | `/home/ywr/odd-order-isaacs-ch07-pcomp` | Replace the conditional Thm 7.1 scaffold with authentic proof steps. |
| B1 | `prompts/lane_b1_bg_s01_hall.md` | `/home/ywr/odd-order-bg-s01-hall` | Build the BG Prop 1.5 A-invariant Hall framework. |
| B2 | `prompts/lane_b2_bg_s05_narrow.md` | `/home/ywr/odd-order-bg-s05-narrow-manual` | Optional: push BG §5 narrow p-groups past the current sorries. |

## Merge Discipline

Do not merge lanes while they are still building or while another lane is editing
the same file. Expected conflicts:

- P1 and P2 both support Peterfalvi §8, but P1 should stay in representation
  theory infrastructure while P2 should stay in class-sum/S08 wiring.
- P2 and P3 should not edit each other's main files: P2 is S08/ClassSum, P3 is
  S09.
- B1 and B2 are independent BG §1 files.

At the end of each lane, require:

- `git status --short`
- commit hash if a commit was made
- build targets run
- remaining blockers

