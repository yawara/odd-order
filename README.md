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
  to Gorenstein ("**G**, Thm X.Y.Z"), most visibly around p-stability, ZJ, and small-rank p-groups,
  and Peterfalvi's Appendix C likewise cites Gorenstein for the Brauer–Suzuki theorem (Ch. 12). Where
  such a citation is not already covered by Isaacs or by mathlib, the Gorenstein proof is written out
  here (Theorems 3.4, 3.7/3.8/3.10, 4.15, 5.3.9–5.3.13, 7.6.5, Brauer–Suzuki, among others, under
  `OddOrder/BG/` and `OddOrder/GroupTheory/`). The one open piece is the `Q₈` case of Brauer–Suzuki,
  which classically requires modular character theory: it is the tree's single remaining `sorry`,
  frozen as a deliberate long-term project. Gorenstein is *not* being formalized as a book.

Two proofs come from outside these books altogether: the books state the results but take the proofs
from the original literature, so the sources themselves are formalized here.

- **Higman**, "Suzuki 2-groups" (*Illinois Journal of Mathematics* 7, 1963). Peterfalvi's Appendix III
  restates Higman's classification of Suzuki 2-groups but explicitly takes its proof from the paper;
  that proof is formalized in full under [`OddOrder/Higman/`](OddOrder/Higman/) — about 65,000
  `sorry`-free lines, the largest single item in the library.
- **Huppert**, *Endliche Gruppen I* (1967), Kapitel II, Satz 3.2: a solvable 2-transitive permutation
  group has an elementary abelian regular normal subgroup. Needed by Peterfalvi's Appendix C.

Coverage of the three books is tracked result by result. An audit on 2026-07-16 enumerated all
**815 numbered results**: 467 formalized at full book strength, 78 covered completely by mathlib itself,
54 present in a specialized form awaiting generalization, and 214 remaining work items. That survey
([`notes/meta/three_books_full_survey_2026_07_16.md`](notes/meta/three_books_full_survey_2026_07_16.md))
is a snapshot of the phase-two starting point, not a live scope document — later spot checks found some
of its per-chapter labels unreliable. Current scope and progress are tracked in the git history and in
`issues/`, with each item re-verified against the tree before work starts.

Everything sits under the `OddOrder` namespace rather than being upstreamed piecemeal, but mathlib
naming and style conventions are followed throughout so that the general-purpose parts stay
upstreamable later. The tree builds with zero non-`sorry` warnings under mathlib's standard linter
set, enforced as a strict gate in CI.

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
| [`OddOrder/`](OddOrder/) | The Lean sources (~1,050 files). `Isaacs/`, `BG/`, `Peterfalvi/` mirror the three books; `Higman/` holds the Suzuki 2-groups paper; `GroupTheory/`, `Algebra/`, `Mathlib/` hold general-purpose material |
| [`OddOrder/FeitThompson.lean`](OddOrder/FeitThompson.lean) | The main theorem and the minimal-counterexample reduction |
| [`OddOrder/AxiomsCheck.lean`](OddOrder/AxiomsCheck.lean) | Build-time axiom audit of every load-bearing result |
| [`ROADMAP.md`](ROADMAP.md) | Long-range plan, phases, dependency graph, per-chapter checklists |
| [`CLAUDE.md`](CLAUDE.md) | Working conventions, and the contributor guide (`AGENTS.md` is a symlink to it) |
| `notes/` | Per-chapter roadmaps, design decisions, and source-text investigations |
| `issues/` | File-based issue tracker (`issues/` open, `pending/`, `closed/`) |
| `coq/` | Submodule: [math-comp/odd-order](https://github.com/math-comp/odd-order), the Coq/mathcomp formalization — a **read-only reference**, consulted because its comments fill in steps the textbooks elide. Nothing is translated from it |
| `references/` | Textbook PDFs and extracted Markdown — gitignored, kept in a separate private repository |

## Use of AI

AI agents were used **heavily** throughout this project: the overwhelming majority of the Lean code,
notes, and documentation was written by AI, and **not all of it has been human-reviewed**. What stands
between that and correctness is the Lean kernel — every proof is machine-checked, and the axiom audit
described above pins down exactly what each result depends on. Where reader skepticism remains
warranted is the *statements*: whether a Lean declaration faithfully renders the textbook theorem it
cites. Docstrings carry the book numbering precisely so that this correspondence can be checked.

## License

Apache License 2.0 — see [LICENSE](LICENSE).
