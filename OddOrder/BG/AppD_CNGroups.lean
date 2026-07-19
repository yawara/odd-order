/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppB_Thm62
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity

/-!
# BG Appendix D: CN-Groups of Odd Order

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix D, pp. 153--156.

Appendix D is a guide to the Feit-Hall-Thompson CN-theorem proof.  It is not part of the main
BG-to-Peterfalvi proof path, but it records two reusable local-analysis consequences for a
**minimal simple** CN-group of odd order.

## De-opacification (2026-07-18)

This file previously carried the minimal-simplicity and nonsolvability conditions as *free*
`Prop` fields with self-carried proofs (`minimal_simple : Prop` together with
`minimal_simple_holds : minimal_simple`).  That made `MinimalSimpleCNHypothesis` inhabited for
**every** odd-order CN group (instantiate both fields with `True`), so Lemmas D.1 and D.2 as
stated asserted their conclusions for all odd CN groups — and in that reading **both are false**:

* **D.2** is refuted by `G = C₃` (abelian, hence CN, of odd order `3`): its Sylow `3`-subgroup is
  `P = ⊤ ≠ ⊥`, yet `derivedInG (N_G(P)) = ⊥`, so `P ≤ derivedInG (N_G(P))` fails.
* **D.1** is refuted by the solvable odd CN group `F_{3⁶} ⋊ (C₇ ⋊ C₃)` of order `3⁷·7`: its normal
  elementary abelian kernel `K = F_{3⁶}` lies in every Sylow `3`-subgroup, while `n₃ = 7 ≠ 1`
  (the quotient `C₇ ⋊ C₃` has seven Sylow `3`-subgroups), so distinct Sylow `3`-subgroups meet
  nontrivially.

The hypothesis is now the honest one: `IsCNGroup` together with the repository's standard
`OddOrder.BG.IsMinimalSimpleOdd` (used uniformly across BG §7--§16), for which both lemmas are
genuine theorems.  The former `CNTheoremReductionData` / `cnTheorem_reduction` "reduction package"
was deleted: its three components were exactly D.1, D.2 and Gorenstein Thm 14.2.2, so once D.1
and D.2 are honest statements the package is a contentless wrapper (and it was itself vacuous,
being dischargeable by `True`-instantiation).

## Status

D.1 and D.2 are stated at book strength and remain `sorry`-free-pending: their proofs need
**Gorenstein Ch. 14 §14.1** (the definition of a *3-step group* and Corollary 14.1.6).  This is
the sanctioned "Gorenstein as line-filler" case (BG cites **G** for a proof it omits).  D.2 is
short *given* D.1 (Focal Subgroup Theorem plus `G' = G` from simplicity).

**Update 2026-07-19** (issue 9133): that input is no longer absent.  In the edition transcribed
under `references/` the material is Chapter 12 §1, and it is being built in
`OddOrder.GroupTheory.CNGroupStructure`:

* `IsThreeStepGroup` — the definition, transcribed verbatim, with the two consequences D.1
  actually consumes (`oPiCore_pPrime_eq_bot`, `isPGroup_quotient` / `nontrivial_quotient`)
  proved `sorry`-free;
* `oPiCore_isSylow_or_isThreeStepGroup` — **Corollary 1.6, derived `sorry`-free** from
  Theorem 1.5 (`solvableCN_nilpotent_or_frobenius_or_threeStep`), which is now the single
  remaining `sorry` on this path; its steps 1, 2 and 3 are themselves proved.

So D.1's blocker has narrowed from "all of Gorenstein §14.1" to "the assembly of Theorem 1.5".
See the tracking issue for the current step-by-step state.

⚠ Do **not** discharge these vacuously from `feitThompson`.  The CN-theorem is an *input* to
Feit--Thompson (BG p. 153: it "is actually needed in **FT**, although not for the part covered by
this book"), so deriving Appendix D from `feitThompson` would invert the mathematical dependency
order and produce contentless declarations.
-/

namespace OddOrder.BG.AppD

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-! ## CN-groups -/

/-- A `CN`-group is a group in which every nonidentity element has nilpotent
centralizer. -/
def IsCNGroup (G : Type*) [Group G] : Prop :=
  ∀ x : G, x ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({x} : Set G))

/-- The standing hypothesis for BG Appendix D: `G` is a **minimal simple** CN-group of odd order.

Minimal simplicity and nonsolvability are carried by the repository's standard
`OddOrder.BG.IsMinimalSimpleOdd` (odd order, simple, not solvable, every proper subgroup
solvable); in particular the oddness of `|G|` is `minimalSimpleOdd.odd` and is not repeated. -/
structure MinimalSimpleCNHypothesis (G : Type*) [Group G] [Finite G] : Prop where
  /-- Every nonidentity element of `G` has nilpotent centralizer. -/
  cn : IsCNGroup G
  /-- `G` is a minimal simple group of odd order. -/
  minimalSimpleOdd : OddOrder.BG.IsMinimalSimpleOdd G

/-! ## Appendix D lemmas -/

/-- **BG Lemma D.1** (mmd L5155): in a minimal simple CN-group of odd order, the Sylow
`p`-subgroups form a TI family — two Sylow `p`-subgroups meeting nontrivially are equal.

⚠ Minimal simplicity is essential: for general odd CN-groups this is **false**
(`F_{3⁶} ⋊ (C₇ ⋊ C₃)`, see the module docstring).

Proof (BG, following **G**): needs Gorenstein Cor. 14.1.6 (a solvable `M` with `O_p(M) ≠ 1` and
`P ∩ M ≠ O_p(M)` is a *3-step group* for `p`) together with BG Theorem 6.2 (Glauberman
`Z(J(P)) ⊴ M`, present in this repository via the `L(P)` / Theorem B.4 substitute).  Corollary
14.1.6 is `OddOrder.GroupTheory.oPiCore_isSylow_or_isThreeStepGroup`, proved modulo Gorenstein's
Theorem 1.5 (see the module docstring); this proof is not yet assembled. -/
theorem sylow_eq_of_nontrivial_inter [Finite G] {p : ℕ} [Fact p.Prime]
    (hyp : MinimalSimpleCNHypothesis G) (P Q : Sylow p G)
    (hinter : ((P : Subgroup G) ⊓ (Q : Subgroup G)) ≠ ⊥) :
    (P : Subgroup G) = Q := by
  sorry

/-- **BG Lemma D.2** (mmd L5180): for a nontrivial Sylow subgroup `P` of a minimal simple
CN-group of odd order, the focal subgroup argument places `P` inside the derived subgroup of its
normalizer.

⚠ Minimal simplicity is essential: for general odd CN-groups this is **false** (`G = C₃`, see the
module docstring).

Proof (BG): the Focal Subgroup Theorem (BG Thm 1.17, available in mathlib as
`Subgroup.commutator_inf_eq_focalSubgroup`) together with `G' = G` (simplicity), given D.1. -/
theorem sylow_le_commutator_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    (hyp : MinimalSimpleCNHypothesis G) (P : Sylow p G)
    (hPne : (P : Subgroup G) ≠ ⊥) :
    (P : Subgroup G) ≤
      derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  sorry

end OddOrder.BG.AppD
