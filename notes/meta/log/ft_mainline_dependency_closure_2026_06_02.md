# FT mainline dependency closure (2026-06-02)

> ⚠ **STALE（履歴スナップショット, `main`@`4adc1a1`）**。scope / policy / 経路の判断は
> [`ft_path_policy.md`](../ft_path_policy.md) が正本（2026-06-15〜）。本ノートは import closure vs proof
> closure の分離分析として温存。

Snapshot: `main` at `4adc1a1`.

Goal: minimize work needed to make `OddOrder.feitThompson` genuinely `sorry`-free.
This note separates the compiler import closure from the mathematical proof
closure, because the current scaffold hides some BG local-analysis obligations
behind Peterfalvi hypotheses and proposition fields.

## C0: current Lean import closure

Start module:

- `OddOrder.FeitThompson`

Current direct path:

```text
FeitThompson
  -> BG.AppC_FinalContradiction
    -> Peterfalvi.S16_NonExistenceG
      -> Peterfalvi.S15_SAndT
      -> ...
      -> Peterfalvi.S08_CoherenceTheorems
```

Stats, counting only bare proof-term `sorry` lines:

- 61 files
- 94 bare `sorry`

Files with bare `sorry` in C0:

| file | sorry |
|---|---:|
| `OddOrder/FeitThompson.lean` | 1 |
| `OddOrder/BG/AppC_FinalContradiction.lean` | 4 |
| `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean` | 1 |
| `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean` | 1 |
| `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` | 7 |
| `OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean` | 11 |
| `OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean` | 10 |
| `OddOrder/Peterfalvi/S13_MaximalIII_IV.lean` | 10 |
| `OddOrder/Peterfalvi/S14_MaximalI.lean` | 14 |
| `OddOrder/Peterfalvi/S15_SAndT.lean` | 19 |
| `OddOrder/Peterfalvi/S16_NonExistenceG.lean` | 16 |

This is too small for planning: BG §7--§16 is not reached from
`FeitThompson.lean` yet, even though it is the source of the local-structure
inputs consumed by Peterfalvi §10--§16.

## C1: endpoint import closure

Start modules:

- `OddOrder.FeitThompson`
- `OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults`
- `OddOrder.BG.AppC_FinalContradiction`

Stats:

- 89 files
- 178 bare `sorry`

This is the smallest useful compiler-visible closure for the current endpoint:
BG §16 supplies Theorems A--E/I--II and the type-classification interface,
Peterfalvi §16 supplies the final field-normalizer configuration, and BG App.C
turns it into the contradiction.

C1 bare `sorry` distribution:

| block | files | sorry |
|---|---|---:|
| top bridge | `FeitThompson.lean` | 1 |
| BG App.C | `AppC_FinalContradiction.lean` | 4 |
| BG §7--§10, §12--§16 currently imported by BG §16 | `S07`, `S08`, `S09`, `S10`, `S12`, `S13`, `S14`, `S15`, `S16` | 84 |
| Peterfalvi §8--§16 | `S08`--`S16` | 89 |

## C2: honest FT mainline proof closure

C2 = C1 plus the BG sections that are mathematically on the BG local-analysis
spine but are not currently imported by the endpoint scaffold.

Add:

| file | reason | sorry |
|---|---|---:|
| `OddOrder/BG/Ch3_MaximalSubgroups/S11_ExceptionalMaximal.lean` | BG Chapter III maximal-subgroup chain; omitted from current import chain | 5 |
| `OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean` | narrow `p`-groups feeding later BG local analysis | 8 |

So the actionable FT mainline proof-fill target is:

- C1: 178 bare `sorry`
- plus BG §11 and §5: 13 bare `sorry`
- total: **191 bare `sorry`**

There is also a non-counted blocker:

- `issues/0051-bg-s04-thm-4-16-blackburn.md`
- BG §4 Theorem 4.16 is still an undeclared/unfinished mathematical endpoint in
  the notes. It does not show up as a bare `sorry` count if the final theorem
  statement is not present, but it is a real gate for §5 and the later local
  analysis.

## Off-mainline for the FT theorem

These remaining bare `sorry` are not in C2 and should not be attacked before a
proof explicitly needs them:

| block | sorry |
|---|---:|
| BG App.D CN-groups | 3 |
| BG App.E further results | 5 |
| Peterfalvi appendices (`Suzuki`, `Huppert`, `NearFields`, `Suzuki2Groups`, `FeitSibley`) | 16 |

Total off-mainline bare `sorry`: **24**.

This matches the repo total:

```text
191 mainline + 24 off-mainline = 215 bare sorry
```

## Working order

1. Close the non-counted BG §4/issue 0051 gate enough to support §5 and later BG
   local analysis.
2. Prove BG §5 narrow `p`-group results that later sections actually consume.
3. Prove Peterfalvi §8 `(6.8)` and §9 `(7.10)`; they sit at the bottom of the
   Peterfalvi §10--§16 chain.
4. Fill BG §7--§9 uniqueness/transitivity.
5. Fill BG §10--§13 maximal-subgroup machinery, including §11 even though it is
   not currently imported by the endpoint scaffold.
6. Fill BG §14--§16 endpoint theorems A--E/I--II and the type classification.
7. Fill Peterfalvi §10--§16 in order.
8. Fill BG App.C finite-field/norm-set calculation.
9. Replace the top-level `feitThompson` `sorry` by the minimal-counterexample
   reduction plus the constructed BG/Peterfalvi final contradiction.

