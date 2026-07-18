# odd-order

A complete formalization of the **Feit–Thompson Odd Order Theorem** in **Lean 4 + mathlib** — *every finite group of odd order is solvable* — together with the finite group theory it is built on.

```lean
theorem feitThompson {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    IsSolvable G
```

## Status

**The Odd Order Theorem is proved and axiom-clean** (2026-07-15):

```
#print axioms OddOrder.feitThompson
-- 'OddOrder.feitThompson' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no project-specific axioms — only Lean's three standard ones. The check is not a one-off:
[`OddOrder/AxiomsCheck.lean`](OddOrder/AxiomsCheck.lean) re-verifies the axiom dependencies of every
load-bearing result on each build and fails the build if anything falls outside the allowlist.

The project is now in its second phase: **formalizing the three source textbooks in full**, not merely
the path through them that the Odd Order Theorem happens to need.

## The byproduct: a finite group theory library

Proving Feit–Thompson requires nearly all of the finite group theory that mathlib does not yet have.
That machinery is the lasting output of this repository, and completing it is now a goal in its own right:

- **Isaacs**, *Finite Group Theory* (AMS GSM 92, 2008) — the general prerequisites: the Fitting subgroup,
  Hall subgroups and π-separability, coprime action, Frobenius groups, transfer, the Thompson subgroup
  and ZJ, the generalized Fitting subgroup `F*(G)`.
- **Bender–Glauberman**, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994) — the local
  analysis and the final contradiction.
- **Peterfalvi**, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000) — the
  character-theoretic half: the Dade isometry, coherence, and the exceptional-character arguments.
- **Gorenstein**, *Finite Groups* (1968) — **in part only**. Bender–Glauberman repeatedly defers proofs
  to Gorenstein ("**G**, Thm X.Y.Z"), most visibly around p-stability, ZJ, and small-rank p-groups.
  Where such a citation is not already covered by Isaacs or by mathlib, the Gorenstein proof is written
  out here (Theorems 3.4, 3.7/3.8/3.10, 4.15, 5.3.9–5.3.13, 7.6.5 among others, chiefly under
  `OddOrder/BG/`). Gorenstein is *not* being formalized as a book.

Coverage of the three books is tracked result by result. An audit on 2026-07-16 enumerated all
**815 numbered results**: 467 formalized at full book strength, 78 covered completely by mathlib itself,
54 present in a specialized form awaiting generalization, and 214 remaining work items. That audit is the
working scope document — see
[`notes/meta/three_books_full_survey_2026_07_16.md`](notes/meta/three_books_full_survey_2026_07_16.md).
Progress since then lives in the git history and in `issues/`.

Everything sits under the `OddOrder` namespace rather than being upstreamed piecemeal, but mathlib
naming and style conventions are followed throughout so that the general-purpose parts stay
upstreamable later.

## Building

```bash
lake exe cache get     # prebuilt mathlib oleans (first checkout, and after a mathlib bump)
lake build OddOrder
```

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain) and the mathlib revision in
[`lakefile.toml`](lakefile.toml). A full build is roughly 4,450 jobs.

## Repository layout

| Path | Contents |
|---|---|
| [`OddOrder/`](OddOrder/) | The Lean sources (~750 files). `Isaacs/`, `BG/`, `Peterfalvi/` mirror the three books; `GroupTheory/`, `Algebra/`, `Mathlib/` hold general-purpose material |
| [`OddOrder/FeitThompson.lean`](OddOrder/FeitThompson.lean) | The main theorem and the minimal-counterexample reduction |
| [`OddOrder/AxiomsCheck.lean`](OddOrder/AxiomsCheck.lean) | Build-time axiom audit of every load-bearing result |
| [`ROADMAP.md`](ROADMAP.md) | Long-range plan, phases, dependency graph, per-chapter checklists |
| [`CLAUDE.md`](CLAUDE.md) | Working conventions, and the contributor guide (`AGENTS.md` is a symlink to it) |
| `notes/` | Per-chapter roadmaps, design decisions, and source-text investigations |
| `issues/` | File-based issue tracker (`issues/` open, `pending/`, `closed/`) |
| `coq/` | Submodule: [math-comp/odd-order](https://github.com/math-comp/odd-order), the Coq/mathcomp formalization — a **read-only reference**, consulted because its comments fill in steps the textbooks elide. Nothing is translated from it |
| `references/` | Textbook PDFs and extracted Markdown — gitignored, kept in a separate private repository |

## How this is built

The formalization is written by AI agents working in parallel `git worktree` lanes, with a coordinating
process that merges a lane into `main` only after a full green build, an axiom audit, and a check that no
proved result has regressed to `sorry`. The conventions those agents follow — file granularity,
traceability from each Lean declaration back to the printed theorem number, naming, and what *not* to
do — are documented in [`CLAUDE.md`](CLAUDE.md).

Two deliberate choices are worth flagging for anyone reading the sources. The project does **not** use a
`leanblueprint`-style TeX dependency graph; the textbooks themselves play that role. And thin renaming
wrappers — around mathlib, or around existing results in this repository — are not written; the
correspondences are recorded in docstrings and in `notes/` instead.

The `sorry`s remaining in the tree (currently 23) all belong to the ongoing book-completion work. None is
reachable from `feitThompson`, which is precisely what the axiom check enforces.

## License

Apache License 2.0 — see [LICENSE](LICENSE).
