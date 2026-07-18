/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import OddOrder.Isaacs.Ch08_PermutationGroups.PSLSimple
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesis

/-!
# Peterfalvi Part II, Chapter I §3, Lemma 1 — the `PSL(2,q)` target

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Chapter I §3, p. 105.

This file discharges the target-group inputs to Lemma 1 when the normal
subgroup supplied by Theorem A is `PSL(2,q)` in its standard action on the
projective line, with `q` a power of two and `q > 2`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

open scoped LinearAlgebra.Projectivization

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega] [Finite G]

section /- 3: Application of the Induction Hypothesis (pp. 105–107) -/

omit [Finite G] in
/-- For the standard `PSL(2,F)` action on the projective line, the degree
minus one is a power of two when `F` has characteristic two. -/
theorem psl2_degree_twoPower {F : Type u} [Field F] [Finite F] [CharP F 2]
    {L : Subgroup G}
    (eL : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (eOmega : Omega →ₑ[eL.toMonoidHom] ℙ F (Fin 2 → F))
    (heOmega : Function.Bijective eOmega) :
    ∃ n : ℕ, Nat.card Omega - 1 = 2 ^ n := by
  classical
  let e : Omega ≃ ℙ F (Fin 2 → F) := Equiv.ofBijective eOmega heOmega
  have hdegree : Nat.card Omega = Nat.card F + 1 := by
    calc
      Nat.card Omega = Nat.card (ℙ F (Fin 2 → F)) := Nat.card_congr e
      _ = Nat.card F + 1 :=
        Projectivization.card_of_finrank_two F (Fin 2 → F)
          (Module.finrank_fin_fun F)
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  refine ⟨(n : ℕ), ?_⟩
  calc
    Nat.card Omega - 1 = Nat.card F := by rw [hdegree]; omega
    _ = 2 ^ (n : ℕ) := by simpa only [Fintype.card_eq_nat_card] using hn

omit [Finite G] in
/-- A projective special linear group of dimension two over a finite field of
characteristic two and order greater than two is simple; hence so is every
concretely isomorphic group. -/
theorem psl2_target_simple {F : Type u} [Field F] [Finite F] [CharP F 2]
    {L : Subgroup G} (hF : 2 < Nat.card F)
    (eL : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    IsSimpleGroup L := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hUnits : 1 < Fintype.card Fˣ := by
    rw [Fintype.card_units, Fintype.card_eq_nat_card]
    omega
  obtain ⟨u, hu⟩ :=
    Fintype.exists_ne_of_one_lt_card hUnits (1 : Fˣ)
  have huOne : (u : F) ≠ 1 := by
    intro h
    exact hu (Units.ext h)
  have huSq : (u : F) ^ 2 ≠ 1 := by
    rw [sq_ne_one_iff]
    exact ⟨huOne, by simpa only [CharTwo.neg_eq] using huOne⟩
  letI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    OddOrder.Isaacs.Ch08.isSimpleGroup_projectiveSpecialLinearGroup
      (Or.inr ⟨(u : F), Units.ne_zero u, huSq⟩)
  exact eL.isSimpleGroup

/-- **Peterfalvi Part II, Chapter I §3, Lemma 1, `PSL(2,q)` case.**
Concrete standard-action coordinates for `L ≅ PSL(2,F)`, with `F` a finite
field of characteristic two and order greater than two, imply that `Q` is a
`2`-group and identify both `O^{2′}(G)` and the join of the conjugates of `Q`
with `L`. -/
theorem Q_and_residual_of_psl2_target (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    {F : Type u} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F)
    (eL : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (eOmega : Omega →ₑ[eL.toMonoidHom] ℙ F (Fin 2 → F))
    (heOmega : Function.Bijective eOmega) :
    IsPGroup 2 hyp.Q ∧
      hyp.Q ≤ L ∧
      L = Subgroup.primeComplementResidual 2 G ∧
      L = (⨆ g : G, hyp.Q.map (MulAut.conj g).toMonoidHom) := by
  exact hyp.simple_normal_oddIndex_Q_core L hLnormal hLodd
    (psl2_target_simple hF eL)
    (psl2_degree_twoPower eL eOmega heOmega)

end

end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
