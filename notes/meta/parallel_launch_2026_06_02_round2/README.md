# Manual Parallel Launch Pack Round 2 -- 2026-06-02

This pack replaces the first wave with larger, longer-running lanes.
It assumes manual Codex sessions over SSH on `omen01.local`, using the remote
checkout `/home/ywr/odd-order`.

Do not use local `/Users/ywr/...` paths for these lanes.

## Current State

- Keep running: `/home/ywr/odd-order-bg-s01-hall` on branch `codex/bg-s01-hall`.
- Removed completed worktrees: bg-s05, isaacs-ch07, pf-brauer, pf-s08, pf-s09.
- Main checkout: `/home/ywr/odd-order`, branch `main`.

## Why Round 2 Is Different

Round 1 lanes were too small: several prompts allowed a lane to stop after one
proof or one bridge theorem. Round 2 lanes have section-block goals and broad
milestone commit rules.

Every lane prompt says:

- set the lane goal explicitly at the start;
- do not stop after the first successful theorem or commit;
- commit larger logical milestones, then continue within the same ownership
  boundary;
- avoid tiny proof-step or single-helper commits; prefer one commit per major
  theorem block, subsection block, or coherent API slice;
- stop only when the whole section-block goal is done or a genuine blocker is
  identified without hoisting hard content into hypotheses;
- keep `lake build` green for the relevant focused target, and run full
  `lake build OddOrder` before final if feasible.

## Recommended Wave

Run the existing BG S01 lane plus four new lanes first. Start B7 only if there is
enough merge bandwidth, because it is foundation-heavy and semantically depends
on the B6 spine.

| Lane | Prompt File | Worktree | Goal |
|---|---|---|---|
| B1 | `prompts/lane_b1_continue_bg_s01_full_s01.md` | existing `/home/ywr/odd-order-bg-s01-hall` | Finish BG §1 as a section, not just Prop 1.5. |
| B5 | `prompts/lane_b5_bg_s05_complete.md` | `/home/ywr/odd-order-bg-s05-complete` | Complete BG §5 Narrow p-groups, including Thm 5.3 through 5.7 if constructible. |
| B6 | `prompts/lane_b6_bg_s07_s09_uniqueness_spine.md` | `/home/ywr/odd-order-bg-s07-s09-spine` | Build the faithful BG §7-§9 uniqueness spine and remove tractable sorries. |
| P4 | `prompts/lane_p4_peterfalvi_s08_s09_part_i.md` | `/home/ywr/odd-order-pf-part-i-capstone` | Finish Peterfalvi §8-§9 Part-I capstone: (6.8) and (7.10). |
| R1 | `prompts/lane_r1_character_infra_mackey_clifford.md` | `/home/ywr/odd-order-repr-infra` | Build representation-theory infrastructure needed by P4 and future Peterfalvi. |
| B7 | `prompts/lane_b7_bg_s10_s13_maximal_foundation.md` | `/home/ywr/odd-order-bg-s10-s13-foundation` | Optional: concrete BG §10-§13 maximal-subgroup foundation. |

## Worktree Setup Rule

Each new lane prompt contains its own setup commands. The invariant is:

- `.lake/packages` is a symlink to `/home/ywr/odd-order/.lake/packages`;
- `references` is a symlink to `/home/ywr/odd-order/references`;
- `.lake/build` is a per-worktree directory copied from main, never a symlink;
- never run `lake update` in a lane;
- never push unless explicitly instructed.

## Merge Discipline

- B1 owns BG §1 and stays in its existing worktree.
- B5 owns BG §5 and narrow p-group modules.
- B6 owns BG §7-§9 and shared uniqueness-spine setup modules.
- B7 owns BG §10-§13; it should import B6 foundations only after merge, not
  reimplement them.
- P4 owns Peterfalvi §8-§9 capstone consumer proofs.
- R1 owns representation-theory infrastructure and should avoid editing P4's
  capstone proofs except for small import/API adjustments.

At lane completion, require:

- `git status --short --branch`;
- commit hashes and brief change summary;
- exact build targets run;
- remaining blockers with file/line references.

