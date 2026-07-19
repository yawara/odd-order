/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanKernel

/-!
# Higman Lemma 3: the image and quotient have order two

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
p. 84.

After the kernel of the quotient endomorphism family has been identified
with `A`, the zero-or-identity dichotomy shows that the image has exactly
two elements. Noether’s first isomorphism theorem then gives `|C / A| = 2`.

The final exponent-at-most-four case split in Higman’s Lemma 3 is not claimed
here.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- A homomorphism with a proper kernel and precisely two possible values
has image of order two. -/
theorem natCard_range_eq_two_of_forall_eq_one_or_eq
    {C D : Type*} [Group C] [Group D]
    (f : C →* D) (t : D)
    (hvalues : ∀ u : C, f u = 1 ∨ f u = t)
    (hker : f.ker < ⊤) :
    Nat.card ↥f.range = 2 := by
  obtain ⟨u, -, hu⟩ := SetLike.exists_of_lt hker
  have hfu_ne : f u ≠ 1 := by
    simpa only [MonoidHom.mem_ker] using hu
  have hfut : f u = t := (hvalues u).resolve_left hfu_ne
  have ht_ne : (1 : D) ≠ t := by
    intro ht
    exact hfu_ne (hfut.trans ht.symm)
  rw [Nat.card_eq_two_iff]
  let x : f.range := ⟨1, f.range.one_mem⟩
  let y : f.range := ⟨t, ⟨u, hfut⟩⟩
  refine ⟨x, y, ?_, ?_⟩
  · intro hxy
    exact ht_ne (congrArg Subtype.val hxy)
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨v, hv⟩ := z.2
    rcases hvalues v with hvone | hvt
    · left
      apply Subtype.ext
      exact hv.symm.trans hvone
    · right
      apply Subtype.ext
      exact hv.symm.trans hvt

/-- Higman's zero-or-identity dichotomy and `ker = A` give image order two
whenever `A < C`. -/
theorem HigmanEndomorphismFamily.modTwoHom_range_natCard_eq_two
    {P ι : Type*} [Group P] [Finite ι]
    {A C : Subgroup P} [A.Normal]
    (hAC : A < C) (hAcomm : IsMulCommutative A)
    {e : ℕ}
    (ε : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (F : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      HigmanEndomorphismFamily
        (fun u : C ↦ MulAut.conjNormal (H := A) (u : P)⁻¹))
    (hzeroOne : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      ∀ u : C, F.modTwo u = 0 ∨ F.modTwo u = 1)
    (hker : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      (F.modTwoHom ε he subgroupConjInv_mul).ker = A.subgroupOf C) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    Nat.card ↥(F.modTwoHom ε he subgroupConjInv_mul).range = 2 := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  let f := F.modTwoHom ε he subgroupConjInv_mul
  let t : Multiplicative
      (Module.End (ZMod 2) (Additive (A ⧸ Agemo A 2 1))) :=
    Multiplicative.ofAdd 1
  have hvalues : ∀ u : C, f u = 1 ∨ f u = t := by
    intro u
    rcases hzeroOne u with hu | hu
    · left
      apply Multiplicative.toAdd.injective
      change F.modTwo u = 0
      exact hu
    · right
      apply Multiplicative.toAdd.injective
      change F.modTwo u = 1
      exact hu
  have hproper : f.ker < ⊤ := by
    rw [hker, lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact hAC.2
  exact natCard_range_eq_two_of_forall_eq_one_or_eq f t hvalues hproper

/-- The corresponding quotient `C/A` has order two by Noether's first
isomorphism theorem. -/
theorem HigmanEndomorphismFamily.modTwoHom_quotient_natCard_eq_two
    {P ι : Type*} [Group P] [Finite ι]
    {A C : Subgroup P} [A.Normal]
    (hAC : A < C) (hAcomm : IsMulCommutative A)
    {e : ℕ}
    (ε : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (F : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      HigmanEndomorphismFamily
        (fun u : C ↦ MulAut.conjNormal (H := A) (u : P)⁻¹))
    (hzeroOne : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      ∀ u : C, F.modTwo u = 0 ∨ F.modTwo u = 1)
    (hker : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      (F.modTwoHom ε he subgroupConjInv_mul).ker = A.subgroupOf C) :
    Nat.card (↥C ⧸ A.subgroupOf C) = 2 := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  let f := F.modTwoHom ε he subgroupConjInv_mul
  calc
    Nat.card (↥C ⧸ A.subgroupOf C) = Nat.card (↥C ⧸ f.ker) := by rw [hker]
    _ = Nat.card ↥f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    _ = 2 := F.modTwoHom_range_natCard_eq_two hAC hAcomm ε he hzeroOne hker

/-- **Higman, Suzuki 2-groups, Lemma 3** (p. 84): for the actual
inverse-conjugation family, actor transitivity and the exact kernel
criterion give `|C / A| = 2`.

This is the order conclusion preceding the final exponent-at-most-four
case split; that final case split is not asserted here. -/
theorem actualHigmanFamily_quotient_natCard_eq_two
    {P ι : Type*} [Group P] [Finite P] [Finite ι]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (htrans : ∀ x ∈ involutions P, ∀ y ∈ involutions P,
      ∃ g : X, (g : MulAut P) x = y)
    {A C : Subgroup P} [A.Normal]
    (hAC : A < C) (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant X.subtype A)
    (hCinv : IsAInvariant X.subtype C)
    (hAne : A ≠ ⊥)
    (hΦ : (frattini C).map C.subtype =
      (frattini A).map A.subtype)
    {e : ℕ}
    (ε : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e)
    (F : letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
      HigmanEndomorphismFamily
        (fun u : C ↦ MulAut.conjNormal (H := A) (u : P)⁻¹)) :
    Nat.card (↥C ⧸ A.subgroupOf C) = 2 := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  have hzeroOne : ∀ u : C, F.modTwo u = 0 ∨ F.modTwo u = 1 :=
    subgroupConjFamily_all_modTwo_eq_zero_or_one
      hAcomm X.subtype hAinv hCinv (by simpa using htrans) ε he F
  have hker :
      (F.modTwoHom ε he subgroupConjInv_mul).ker = A.subgroupOf C :=
    actualHigmanFamily_modTwoHom_ker_eq
      hP X htrans hAC.1 hAcomm hAinv hAne hΦ ε he F
  exact F.modTwoHom_quotient_natCard_eq_two
    hAC hAcomm ε he hzeroOne hker

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
