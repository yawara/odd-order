/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair

/-!
# Signed irreducible families induced from a TI-subset

Composition of the TI induction isometry (`ClassFunction.inner_induce_eq_of_isTISubset`,
Isaacs CTFG Lemma 7.7) with the orthonormal difference-pair structure theorem
(`isometry_difference_pair_structure`, Peterfalvi §3 (1.4)): for a TI-subset `A ⊆ G` with
normalizer-bound `H ≤ G` and `n ≥ 2` distinct equal-degree irreducible characters of `H`
agreeing pairwise off `A`, the induced differences `Ind_H^G (χ_i - χ_0)` are the signed
differences `ε • (μ_i - μ_0)` of `n` distinct irreducible characters of `G` with a uniform
sign `ε = ±1`.

This is the family-extraction step of the Coq `primeTIirr_spec` route
(`PFsection4.v:288-387`): applied column-by-column to the linear-character grid `ω_{ij}` of
`W = W₁ × W₂` (with `A := W ∖ W₂`, a TI-subset in the prime-TI context of Peterfalvi
(4.2)), it produces the per-column signed irreducible families whose cross-column matching
and `(3.9.a)` `V`-value identification then yield the prime-TI value identity `prTIirr_id`
(Peterfalvi (4.3.c)).
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory (IsTISubset)

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **Signed irreducible family extraction for TI induction** (Peterfalvi §3 (1.4) applied
to `τ := Ind_H^G` on a TI-subset; the family-extraction step of the Coq `primeTIirr_spec`
route).  For a TI-subset `A` with normalizer-bound `H` and `n ≥ 2` distinct equal-degree
irreducible characters `χ_i` of `H` agreeing off `A`, there are `n` distinct irreducible
characters `μ_i` of `G` and a uniform sign `ε = ±1` with
`Ind_H^G (χ_i - χ_0) = ε • (μ_i - μ_0)` for all `i`.

The three hypotheses of `isometry_difference_pair_structure` are discharged as follows:
the images are virtual characters (`induce_mem_ZIrr`), vanish at `1` (the degree formula
`induce_apply_one` and equal degrees), and the inner products are preserved (the TI
induction isometry `inner_induce_eq_of_isTISubset`, using that each difference is
supported on `A`). -/
theorem induce_difference_pair_structure_of_isTISubset
    (H : Subgroup G) [Invertible (Nat.card ↥H : ℂ)]
    {A : Set G} (hTI : IsTISubset A H)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (χ : Fin n → IrreducibleCharacter ↥H)
    (h_distinct : Function.Injective χ)
    (h_same_degree : ∀ i, ((χ i : ClassFunction ↥H ℂ) : ↥H → ℂ) 1
      = ((χ 0 : ClassFunction ↥H ℂ) : ↥H → ℂ) 1)
    (h_agree_off : ∀ i (x : ↥H), (x : G) ∉ A
      → (χ i : ClassFunction ↥H ℂ) x = (χ 0 : ClassFunction ↥H ℂ) x) :
    ∃ data : SignedIrreducibleDifferenceFamily G n,
      ∀ i, ClassFunction.induce H (irreducibleCharacterDifference χ i)
        = data.signedDifference i := by
  classical
  letI : Fintype ↥H := Fintype.ofFinite ↥H
  -- `Ind_H^G` as a `ℤ`-linear map.
  let τ : ClassFunction ↥H ℂ →ₗ[ℤ] ClassFunction G ℂ :=
    { toFun := ClassFunction.induce H
      map_add' := ClassFunction.induce_add H
      map_smul' := fun m θ => by
        simp only [RingHom.id_apply]
        rw [← Int.cast_smul_eq_zsmul ℂ m θ, ClassFunction.induce_smul,
          Int.cast_smul_eq_zsmul] }
  -- Each difference `χ_i - χ_0` vanishes off `A`.
  have h_vanish : ∀ i (x : ↥H), (x : G) ∉ A
      → irreducibleCharacterDifference χ i x = 0 := by
    intro i x hx
    change (χ i : ClassFunction ↥H ℂ) x - (χ 0 : ClassFunction ↥H ℂ) x = 0
    rw [h_agree_off i x hx, sub_self]
  have h_virtual : IsometryDifferenceImagesAreVirtual τ χ := fun i =>
    ClassFunction.induce_mem_ZIrr H
      (Submodule.sub_mem _ (χ i).isIrreducible.mem_ZIrr (χ 0).isIrreducible.mem_ZIrr)
  have h_degree_zero : IsometryDifferenceImagesVanishAtOne τ χ := by
    intro i
    have h1 : ClassFunction.induce H (irreducibleCharacterDifference χ i) (1 : G) = 0 := by
      rw [ClassFunction.induce_apply_one,
        irreducibleCharacterDifference_apply_one_of_same_degree χ h_same_degree i, mul_zero]
    exact h1
  have h_isom : ∀ i j,
      ClassFunction.inner (isometryDifferenceImage τ χ i) (isometryDifferenceImage τ χ j)
        = ClassFunction.inner (irreducibleCharacterDifference χ i)
            (irreducibleCharacterDifference χ j) := fun i j =>
    ClassFunction.inner_induce_eq_of_isTISubset H hTI (h_vanish i) (h_vanish j)
  obtain ⟨data, hdata⟩ := isometry_difference_pair_structure hn χ h_distinct
    h_same_degree τ h_virtual h_degree_zero h_isom
  exact ⟨data, fun i => hdata i⟩

end OddOrder.RepresentationTheory
