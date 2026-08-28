# odd-order

English | [日本語](README.ja.md)

A complete formalization of the **Feit–Thompson Odd Order Theorem** in **Lean 4 + mathlib** — *every finite group of odd order is solvable* — together with the finite group theory it is built on. It is the first formalization of the theorem in Lean.

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

No `sorryAx`, no project-specific axioms — only Lean's three standard ones.

**This is the first formalization of the theorem in Lean**; the only previous formalization is the
landmark Coq proof of Gonthier et al. (2012). The proof has also been verified outside this
repository: [lean-eval](https://lean-lang.org/eval/), the Lean community's formal-mathematics
benchmark, had posed `feit_thompson` as a challenge — stated independently of this project, in
plain mathlib vocabulary, with the note "there is no Lean port" — and this project's submission
([lean-eval-submissions#828](https://github.com/leanprover/lean-eval-submissions/issues/828),
2026-07-16) was its first accepted solution. Acceptance means the benchmark's comparator
re-checked the proof against the benchmark's own statement of the theorem, under the same
three-axiom allowlist; the self-contained submission as verified is public at
[yawara/odd-order-submission](https://github.com/yawara/odd-order-submission). Within days,
further solutions by others followed, the first of them a port of the Coq proof — the
formalization here was developed from the textbooks, not ported.

The project is now in its second phase: **formalizing the three source textbooks in full**, not merely
the path through them that the Odd Order Theorem needs.

> ✅ **The Lean sources (`OddOrder/`) are `sorry`-free as of 2026-08-07.** The last one to go was the
> `Q₈` case of the Brauer–Suzuki theorem — cited by the sources, proved in none of them. Closing it
> meant building modular character theory from scratch (`p`-modular systems, Brauer characters,
> blocks, defect groups, Brauer's three main theorems), following Navarro's *Characters and Blocks of
> Finite Groups*, Ch. 1–7. Note that `sorry`-free is *not* the same as "the three books are done":
> a result that has not been stated yet produces no `sorry`. Coverage is tracked separately, below.

> ✅ **Every numbered result in the three books is formalized as of 2026-08-08**, when an
> item-by-item audit of all **775 numbered results** — checked clause by clause against the book
> pages — was completed. The tally and its precise scope are in the coverage paragraph below.

> ★ **A question left open in print since 1993 was settled along the way** (2026-08-13): Problem 1
> of Bender–Glauberman's Appendix C has a negative answer, found here and machine-checked in Lean
> the same day. See "[An open problem resolved](#an-open-problem-resolved-problem-1-of-appendix-c)"
> below.

## Beyond the Feit–Thompson theorem: a finite group theory library

Proving Feit–Thompson requires a large body of finite group theory that mathlib does not yet have.
That theory makes up the bulk of this repository, and completing it is now a goal in its own right:

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
  here (Theorems 3.4, 3.7/3.8/3.10, 4.15, 5.3.9–5.3.13, 7.6.5, Brauer–Suzuki for `|S| ≥ 16`, among
  others, under `OddOrder/BG/` and `OddOrder/GroupTheory/`). Gorenstein is *not* being formalized as
  a book.

Three bodies of proof come from outside these books altogether: the books state the results but take
the proofs from the original literature, so the sources themselves are formalized here.

- **Higman**, "Suzuki 2-groups" (*Illinois Journal of Mathematics* 7, 1963). Peterfalvi's Appendix III
  restates Higman's classification of Suzuki 2-groups but explicitly takes its proof from the paper;
  that proof is formalized in full under [`OddOrder/Higman/`](OddOrder/Higman/) — about 65,000
  `sorry`-free lines, the largest single item in the library.
- **Navarro**, *Characters and Blocks of Finite Groups* (LMS LNS 250, 1998), Ch. 1–7. The `Q₈` case of
  Brauer–Suzuki is in none of the four books above: Gorenstein's Ch. 12 proves only `|S| ≥ 16` and
  states the order-8 case without proof ("all known proofs require the theory of modular characters" —
  a theory the book never develops), and mathlib has no modular representation theory at all. So it is
  built here from the ground up under
  [`OddOrder/GroupTheory/RepresentationTheory/Modular/`](OddOrder/GroupTheory/RepresentationTheory/Modular/)
  — `p`-modular systems, Brauer characters, decomposition and Cartan matrices, blocks and defect
  groups, the Brauer homomorphism and Brauer's three main theorems — about 29,000 lines feeding the
  character-theoretic argument of Navarro pp. 139–146.
- **Huppert**, *Endliche Gruppen I* (1967), Kapitel II, Satz 3.2: a solvable 2-transitive permutation
  group has an elementary abelian regular normal subgroup. Needed by Peterfalvi's Appendix C.

Coverage of the three books is tracked result by result — separately from the `sorry` count, which
measures something else entirely. An item-by-item audit, completed 2026-08-08, went through every
numbered result of the three books and checked it clause by clause against the book page images:
**775 numbered results** — 284 in Peterfalvi
([issue 0172](issues/closed/0172-peterfalvi-full-formalization.md)), 305 in Isaacs
([0176](issues/closed/0176-isaacs-full-formalization.md)), 186 in Bender–Glauberman
([0177](issues/closed/0177-bg-full-formalization.md)). Every one of them now has a Lean statement at
full book strength — proved, since the tree is `sorry`-free — or, for a number of classical facts
(mostly in Isaacs), is covered by mathlib itself, with the correspondence recorded in `notes/` rather
than as wrapper lemmas. Specialization debt — results present only in a form narrower than the
book's — is down to zero. What the audit does *not* cover is the unnumbered material: end-of-chapter
problems, remarks, and asides remain a separate, ongoing track in `issues/`, so "all numbered results"
is still not "the three books are done". (An earlier survey of 2026-07-16
([`notes/meta/three_books_full_survey_2026_07_16.md`](notes/meta/three_books_full_survey_2026_07_16.md))
enumerated the starting point of this phase; its counts and labels turned out partly unreliable and it
is kept only as a historical snapshot.)

Everything sits under the `OddOrder` namespace rather than being upstreamed piecemeal, but mathlib
naming and style conventions are followed throughout so that the general-purpose parts stay
upstreamable later. The tree builds with zero non-`sorry` warnings under mathlib's standard linter
set, enforced as a strict gate in CI.

## An open problem resolved: Problem 1 of Appendix C

This is the one place where the project produced new mathematics rather than formalizing existing
mathematics. Problem 1 of Bender–Glauberman's Appendix C (p. 152) was posed by Péterfalvi and first
appeared in print in Glauberman–Norton, "On a combinatorial problem associated with the odd order
theorem" (*Proc. Amer. Math. Soc.* **119** (1993), 1089–1094, p. 1094):

> Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

The hypothesis in question — condition (B) — asks for a group `G`, an injective homomorphism `σ`
into `G` from the Frobenius group `H = P ⋊ U` (the additive group of `𝔽_{p^q}` acted on by its
norm-one units), a finite abelian `p′`-subgroup `Q ≤ G`, and an element `y ∈ Q` such that `σ(P₀)`
normalizes `Q` and `σ(P₀)^y` normalizes `σ(U)` — `P₀` being the prime-field line of `P`. For
`p = 2` the configuration is realized in `SL(2, 2^q)` and in the Suzuki groups `Sz(2^q)` (the
paper's Examples 10 and 11); for `p ≥ 5` the paper's Proposition 7 rules it out (that proposition,
too, is formalized here). The case `p = 3` had been open since 1993, with no published resolution.

The answer is **no** — for every `q`, and with no finiteness assumption on `G`:

```lean
theorem hypothesisB_false (data : FieldNormalizerData p q G) (hp : p = 3) : False
```

where `FieldNormalizerData p q G` packages exactly the problem's two conditions (A) and (B) — only
`Q` is assumed finite, not `G`. The proof was completed on paper on 2026-08-13 and machine-checked
in Lean the same day; the theorem is axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only),
enforced at build time by [`AxiomsCheck.lean`](OddOrder/AxiomsCheck.lean). The final theorem is in
[`OddOrder/BG/AppC_Problem1SkewEndgame.lean`](OddOrder/BG/AppC_Problem1SkewEndgame.lean), at the top
of about 8,700 lines across 14 files written for the resolution. The mathematical write-up — the
theorem, the complete proof, and the paper-to-Lean correspondence — is
[`notes/bg/appC_problem1_resolution.md`](notes/bg/appC_problem1_resolution.md), with an overview of
the history, methodology, and verification in
[`notes/bg/appC_problem1_summary.md`](notes/bg/appC_problem1_summary.md).

## Building

```bash
lake exe cache get     # prebuilt mathlib oleans (first checkout, and after a mathlib bump)
lake build OddOrder
```

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain) and the mathlib revision in
[`lakefile.toml`](lakefile.toml). A full build is roughly 5,470 jobs.

## Repository layout

| Path | Contents |
|---|---|
| [`OddOrder/`](OddOrder/) | The Lean sources (~1,705 files, ~841,000 lines). `Isaacs/`, `BG/`, `Peterfalvi/` mirror the three books; `Higman/` holds the Suzuki 2-groups paper; `GroupTheory/`, `Algebra/`, `Mathlib/` hold general-purpose material, including `GroupTheory/RepresentationTheory/Modular/` for the block theory |
| [`OddOrder/FeitThompson.lean`](OddOrder/FeitThompson.lean) | The main theorem and the minimal-counterexample reduction |
| [`OddOrder/AxiomsCheck.lean`](OddOrder/AxiomsCheck.lean) | Build-time axiom audit of every load-bearing result |
| [`ROADMAP.md`](ROADMAP.md) | Long-range plan, phases, dependency graph, per-chapter checklists |
| [`CLAUDE.md`](CLAUDE.md) | Working conventions, and the contributor guide (`AGENTS.md` is a symlink to it) |
| `notes/` | Per-chapter roadmaps, design decisions, and source-text investigations |
| `issues/` | File-based issue tracker (`issues/` open, `pending/`, `closed/`) |
| `coq/` | Submodule: [math-comp/odd-order](https://github.com/math-comp/odd-order), the Coq/mathcomp formalization — a **read-only reference**, consulted because its comments fill in steps the textbooks elide. Nothing is translated from it |
| `references/` | Textbook PDFs, page images, and extracted text — a submodule pointing at a separate private repository, so the exact revision used is recorded. Not needed to build: CI does not fetch submodules |

## Use of AI

This project is driven by AI agents: nearly all of the Lean code, notes, and documentation is
written by AI, and **not all of it is human-reviewed**. Proof correctness does not depend on that
review: the Lean kernel machine-checks every proof, and the axiom audit
([`OddOrder/AxiomsCheck.lean`](OddOrder/AxiomsCheck.lean)) pins down exactly what each result
depends on. Where reader skepticism remains
warranted is the *statements*: whether a Lean declaration faithfully renders the textbook theorem it
cites. Docstrings carry the book numbering precisely so that this correspondence can be checked.
For the headline theorem, that check has also been performed externally: lean-eval's comparator
accepted this proof against the benchmark's own, independently written statement of the theorem
(see [Status](#status)).

## Citation

If this formalization is useful to you — the theorem, the surrounding library, or the resolution of
Problem 1 of Appendix C — please cite the repository. There are no versioned releases (the `v4.x` tags
mark Lean toolchain bumps, not project versions), so please also record the commit hash you used.
A machine-readable [`CITATION.cff`](CITATION.cff) is included; GitHub's "Cite this repository" button
is generated from it.

```bibtex
@software{ishida2026oddorder,
  author       = {Ishida, Yawara},
  title        = {{odd-order}: A formalization of the {Feit--Thompson Odd Order Theorem} in {Lean} 4},
  year         = {2026},
  url          = {https://github.com/yawara/odd-order},
  organization = {A.I.System Research, Inc.},
  license      = {Apache-2.0}
}
```

For the resolution of Problem 1 of Appendix C in particular, the write-up to point at is
[`notes/bg/appC_problem1_resolution.md`](notes/bg/appC_problem1_resolution.md), and the theorem is
`hypothesisB_false` in
[`OddOrder/BG/AppC_Problem1SkewEndgame.lean`](OddOrder/BG/AppC_Problem1SkewEndgame.lean). The author
of record is the human maintainer, Yawara ISHIDA (A.I.System Research, Inc.); the AI agents that
wrote most of the code (see [Use of AI](#use-of-ai)) are tools, not authors.

## License

Apache License 2.0 — see [LICENSE](LICENSE).
