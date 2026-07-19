/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/

import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanNormalCover
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanImageOrder

/-!
# Higman Lemma 3: final case split

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
p. 84.

This file implements the final square identity and case split used to bound
the exponent of the normal abelian subgroup. The subgroup denoted
`A^(2-2η)` in the source is the range of `twoSubTwoMap`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.GroupTheory

/-- Higman's endomorphism `2 - 2 * nu(u)`, written multiplicatively. -/
def HigmanEndomorphismFamily.twoSubTwoMap
    {A C : Type*} [CommGroup A] [Group C]
    {conjInv : C → MulAut A}
    (F : HigmanEndomorphismFamily conjInv) (u : C) : A →* A :=
  addEndToMonoidEnd
    (2 • ((1 : AddMonoid.End (Additive A)) - F.ν u))

@[simp] theorem HigmanEndomorphismFamily.twoSubTwoMap_apply
    {A C : Type*} [CommGroup A] [Group C]
    {conjInv : C → MulAut A}
    (F : HigmanEndomorphismFamily conjInv) (u : C) (a : A) :
    F.twoSubTwoMap u a =
      (a * (addEndToMonoidEnd (F.ν u) a)⁻¹) ^ 2 := by
  apply Additive.ofMul.injective
  dsimp [twoSubTwoMap, addEndToMonoidEnd]
  rw [two_nsmul]
  change (((1 : AddMonoid.End (Additive A)) - F.ν u)
      (Additive.ofMul a) +
        ((1 : AddMonoid.End (Additive A)) - F.ν u)
          (Additive.ofMul a)) = _
  have hsub :
      ((1 : AddMonoid.End (Additive A)) - F.ν u) (Additive.ofMul a) =
        Additive.ofMul a + -(F.ν u (Additive.ofMul a)) := by
    rw [sub_eq_add_neg]
    change Additive.ofMul a + (-F.ν u) (Additive.ofMul a) =
      Additive.ofMul a + -(F.ν u (Additive.ofMul a))
    rfl
  rw [hsub]
  rw [two_nsmul]

/-- The square identity `(u a)^2 = u^2 a^(2 - 2 nu)` in Higman's
Lemma 3, with the final power written as `twoSubTwoMap`. -/
theorem actualHigmanFamily_mul_square_eq
    {P : Type*} [Group P] {A C : Subgroup P} [A.Normal]
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∀ (F : HigmanEndomorphismFamily
        (fun v : C ↦ MulAut.conjNormal (H := A) (v : P)⁻¹))
      (u : C) (a : A),
      ((u : P) * (a : P)) ^ 2 =
        (u : P) ^ 2 * ((F.twoSubTwoMap u a : A) : P) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  intro F u a
  let νm : A →* A := addEndToMonoidEnd (F.ν u)
  have hpoint := DFunLike.congr_fun (F.conj_eq_one_sub_two u)
    (Additive.ofMul a)
  have hconj :
      ((MulAut.conjNormal (H := A) (u : P)⁻¹) a : A) =
        a * (νm a) ^ (-2 : ℤ) := by
    have hpoint' := congrArg Additive.toMul hpoint
    change ((MulAut.conjNormal (H := A) (u : P)⁻¹) a : A) =
      Additive.toMul
        (Additive.ofMul a - 2 • F.ν u (Additive.ofMul a)) at hpoint'
    calc
      _ = Additive.toMul
          (Additive.ofMul a - 2 • F.ν u (Additive.ofMul a)) := hpoint'
      _ = a * (νm a) ^ (-2 : ℤ) := by
        have hz : (νm a) ^ (-2 : ℤ) = ((νm a) ^ 2)⁻¹ := by
          simp only [zpow_neg, zpow_ofNat]
        rw [hz]
        simp only [νm, addEndToMonoidEnd_apply, sub_eq_add_neg, two_nsmul,
          pow_two, toMul_add, toMul_neg, toMul_ofMul]
  have htheta :
      (((MulAut.conjNormal (H := A) (u : P)⁻¹) a : A) : P) =
        (u : P)⁻¹ * (a : P) * (u : P) := by
    dsimp
    simp
  have hconjP := congrArg A.subtype hconj
  change (((MulAut.conjNormal (H := A) (u : P)⁻¹) a : A) : P) =
    (((a * (νm a) ^ (-2 : ℤ)) : A) : P) at hconjP
  have hlast :
      (a * (νm a) ^ (-2 : ℤ)) * a = F.twoSubTwoMap u a := by
    rw [F.twoSubTwoMap_apply]
    have hzneg : (νm a) ^ (-2 : ℤ) = ((νm a) ^ 2)⁻¹ := by
      simp only [zpow_neg, zpow_ofNat]
    have hz : (νm a) ^ (-2 : ℤ) = ((νm a)⁻¹) ^ 2 :=
      hzneg.trans (inv_pow (νm a) 2).symm
    rw [hz]
    change (a * ((νm a)⁻¹) ^ 2) * a =
      (a * (νm a)⁻¹) ^ 2
    simp only [pow_two]
    ac_rfl
  calc
    ((u : P) * (a : P)) ^ 2 =
        (u : P) ^ 2 *
          (((MulAut.conjNormal (H := A) (u : P)⁻¹) a : A) : P) *
            (a : P) := by
      rw [htheta, pow_two]
      group
    _ = (u : P) ^ 2 *
        ((((a * (νm a) ^ (-2 : ℤ)) * a : A)) : P) := by
      rw [hconjP]
      simp only [Subgroup.coe_mul]
      group
    _ = (u : P) ^ 2 * ((F.twoSubTwoMap u a : A) : P) :=
      congrArg (fun x : A ↦ (u : P) ^ 2 * (x : P)) hlast


/-- Higman first final case is impossible: if `u²` lies in the image of
`2 - 2ν(u)`, a suitable element of `uA` is an involution outside `A`. -/
theorem actualHigmanFamily_sq_not_mem_twoSubTwoMap_range
    {P : Type*} [Group P] {A C : Subgroup P} [A.Normal]
    (hAcomm : IsMulCommutative A)
    (hinvA : involutions P ⊆ A) (u : C) (huA : (u : P) ∉ A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∀ F : HigmanEndomorphismFamily
        (fun v : C ↦ MulAut.conjNormal (H := A) (v : P)⁻¹),
      (u : P) ^ 2 ∉ (F.twoSubTwoMap u).range.map A.subtype := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  intro F hu2
  obtain ⟨b, hbRange, hb⟩ := Subgroup.mem_map.mp hu2
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hbRange
  have hua2 : ((u : P) * ((c⁻¹ : A) : P)) ^ 2 = 1 := by
    rw [actualHigmanFamily_mul_square_eq hAcomm F u c⁻¹,
      map_inv, hc, Subgroup.coe_inv]
    change (u : P) ^ 2 * (A.subtype b)⁻¹ = 1
    rw [hb]
    group
  have huaA : (u : P) * ((c⁻¹ : A) : P) ∉ A := by
    intro hmem
    apply huA
    have hprod := A.mul_mem hmem c.2
    simpa using hprod
  have hua1 : (u : P) * ((c⁻¹ : A) : P) ≠ 1 := by
    intro hone
    apply huaA
    rw [hone]
    exact A.one_mem
  exact huaA (hinvA ⟨hua2, hua1⟩)

/-- Squares of elements of `C \ A`, regarded inside `A`. -/
def higmanOutsideSquareSet
    {P : Type*} [Group P] (A C : Subgroup P) : Set A :=
  {b | ∃ v : C, (v : P) ∉ A ∧ (v : P) ^ 2 = (b : P)}

/-- Canonical form of Higman's `2 - 2 eta = 1 + alpha`. -/
def higmanSquareTwist
    {A : Type*} [CommGroup A] (α : MulAut A) : A →* A where
  toFun a := α a * a
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    ac_rfl

@[simp] theorem higmanSquareTwist_apply
    {A : Type*} [CommGroup A] (α : MulAut A) (a : A) :
    higmanSquareTwist α a = α a * a := rfl

private theorem outside_quotient_mk_eq
    {C : Type*} [Group C] [Finite C]
    (N : Subgroup C) [N.Normal]
    (hcard : Nat.card (C ⧸ N) = 2)
    {u v : C} (hu : u ∉ N) (hv : v ∉ N) :
    QuotientGroup.mk' N u = QuotientGroup.mk' N v := by
  obtain ⟨q, hqne, hqunique⟩ :=
    (Nat.card_eq_two_iff' (1 : C ⧸ N)).mp hcard
  have huq : QuotientGroup.mk' N u ≠ 1 := by
    intro h
    exact hu ((QuotientGroup.eq_one_iff u).mp h)
  have hvq : QuotientGroup.mk' N v ≠ 1 := by
    intro h
    exact hv ((QuotientGroup.eq_one_iff v).mp h)
  exact (hqunique _ huq).trans (hqunique _ hvq).symm

private theorem mul_subgroup_element_sq
    {P : Type*} [Group P] {A : Subgroup P} [A.Normal]
    (u : P) (a : A) :
    (u * (a : P)) ^ 2 =
      u ^ 2 *
        (((MulAut.conjNormal (H := A) u⁻¹) a * a : A) : P) := by
  rw [pow_two, pow_two, Subgroup.coe_mul, MulAut.conjNormal_apply]
  simp only [inv_inv]
  group

/-- With `|C/A| = 2`, the squares outside `A` form the single coset
`u^2 * A^(1+alpha_u)`. -/
theorem higmanOutsideSquareSet_eq_range_mul_twist
    {P : Type*} [Group P] [Finite P]
    {A C : Subgroup P} [A.Normal]
    (hAC : A ≤ C) (hAcomm : IsMulCommutative A)
    (hcard : Nat.card (↑C ⧸ A.subgroupOf C) = 2)
    (hsq : ∀ v : C, (v : P) ∉ A → (v : P) ^ 2 ∈ A)
    (u : C) (hu : (u : P) ∉ A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    let z : A := ⟨(u : P) ^ 2, hsq u hu⟩
    higmanOutsideSquareSet A C =
      Set.range (fun a : A ↦
        z * higmanSquareTwist
          (MulAut.conjNormal (H := A) (u : P)⁻¹) a) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  let z : A := ⟨(u : P) ^ 2, hsq u hu⟩
  ext b
  constructor
  · rintro ⟨v, hvA, hvb⟩
    have huN : u ∉ A.subgroupOf C := by
      simpa only [Subgroup.mem_subgroupOf] using hu
    have hvN : v ∉ A.subgroupOf C := by
      simpa only [Subgroup.mem_subgroupOf] using hvA
    have hq := outside_quotient_mk_eq (A.subgroupOf C) hcard huN hvN
    obtain ⟨aC, haC, hua⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := A.subgroupOf C)).mp hq
    let a : A := ⟨(aC : P), haC⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change (u : P) ^ 2 *
        (((MulAut.conjNormal (H := A) (u : P)⁻¹) a * a : A) : P) = (b : P)
    rw [← hvb, ← hua]
    exact (mul_subgroup_element_sq (u : P) a).symm
  · rintro ⟨a, rfl⟩
    let aC : C := ⟨(a : P), hAC a.2⟩
    let v : C := u * aC
    have hvA : (v : P) ∉ A := by
      intro hv
      apply hu
      have haInv : (a : P)⁻¹ ∈ A := A.inv_mem a.2
      have hvMul : (v : P) * (a : P)⁻¹ ∈ A := A.mul_mem hv haInv
      simpa [v, aC, mul_assoc] using hvMul
    refine ⟨v, hvA, ?_⟩
    change ((u : P) * (a : P)) ^ 2 =
      (u : P) ^ 2 *
        (((MulAut.conjNormal (H := A) (u : P)⁻¹) a * a : A) : P)
    exact mul_subgroup_element_sq (u : P) a


/-- The subgroup generated by a coset `z * range(delta)` is
`range(delta) sup <z>`. -/
theorem closure_range_mul_monoidHom_eq_sup_zpowers
    {A : Type*} [CommGroup A] (δ : A →* A) (z : A) :
    Subgroup.closure (Set.range fun a ↦ z * δ a) =
      δ.range ⊔ Subgroup.zpowers z := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    change z * δ a ∈ δ.range ⊔ Subgroup.zpowers z
    rw [mul_comm]
    exact Subgroup.mul_mem_sup
      (MonoidHom.mem_range.mpr ⟨a, rfl⟩) (Subgroup.mem_zpowers z)
  · apply sup_le
    · intro d hd
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hd
      have hzcoset : z * δ a ∈
          Subgroup.closure (Set.range fun b ↦ z * δ b) :=
        Subgroup.subset_closure ⟨a, rfl⟩
      have hz : z ∈ Subgroup.closure (Set.range fun b ↦ z * δ b) := by
        simpa using
          (Subgroup.subset_closure
            (show z * δ 1 ∈ Set.range (fun b ↦ z * δ b) from ⟨1, rfl⟩))
      have hmem := (Subgroup.closure
        (Set.range fun b ↦ z * δ b)).mul_mem
          (Subgroup.inv_mem _ hz) hzcoset
      simpa [mul_assoc] using hmem
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.subset_closure
          (show z ∈ Set.range (fun b ↦ z * δ b) by
            refine ⟨1, ?_⟩
            simp))

/-- Exact source-facing description of Higman's subgroup `B` generated by
outside squares. -/
theorem higmanOutsideSquare_closure_eq_twist_range_sup_zpowers
    {P : Type*} [Group P] [Finite P]
    {A C : Subgroup P} [A.Normal]
    (hAC : A ≤ C) (hAcomm : IsMulCommutative A)
    (hcard : Nat.card (↑C ⧸ A.subgroupOf C) = 2)
    (hsq : ∀ v : C, (v : P) ∉ A → (v : P) ^ 2 ∈ A)
    (u : C) (hu : (u : P) ∉ A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    let z : A := ⟨(u : P) ^ 2, hsq u hu⟩
    Subgroup.closure (higmanOutsideSquareSet A C) =
      (higmanSquareTwist
        (MulAut.conjNormal (H := A) (u : P)⁻¹)).range ⊔
          Subgroup.zpowers z := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  let z : A := ⟨(u : P) ^ 2, hsq u hu⟩
  rw [higmanOutsideSquareSet_eq_range_mul_twist
    hAC hAcomm hcard hsq u hu]
  exact closure_range_mul_monoidHom_eq_sup_zpowers _ _

open OddOrder.Isaacs.Ch03


/-- The subgroup generated by squares of elements of `C \ A` is preserved
by every ambient actor preserving `A` and `C`. -/
theorem higmanOutsideSquare_closure_isAInvariant
    {P X : Type*} [Group P] [Group X]
    (act : X →* MulAut P) {A C : Subgroup P}
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C) :
    IsAInvariant hAinv.restrict
      (Subgroup.closure (higmanOutsideSquareSet A C)) := by
  rw [isAInvariant_iff_smul_mem]
  intro x b hb
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hb
  · intro d hd
    apply Subgroup.subset_closure
    obtain ⟨v, hvA, hvd⟩ := hd
    let v' : C := hCinv.restrict x v
    refine ⟨v', ?_, ?_⟩
    · intro hv'A
      apply hvA
      have hinv : (act x)⁻¹ (v' : P) ∈ A :=
        hAinv.inv_smul_mem x hv'A
      simpa [v', IsAInvariant.restrict_apply_val] using hinv
    · have hmap := congrArg (fun y : P ↦ act x y) hvd
      simpa [v', map_pow, IsAInvariant.restrict_apply_val] using hmap
  · rw [map_one]
    exact (Subgroup.closure (higmanOutsideSquareSet A C)).one_mem
  · intro a b ha hb hia hib
    rw [map_mul]
    exact (Subgroup.closure _).mul_mem hia hib
  · intro a ha hia
    rw [map_inv]
    exact (Subgroup.closure _).inv_mem hia

open OddOrder.Isaacs.Ch03

private theorem subgroupConjInv_mul_right_eq
    {P : Type*} [Group P] {A : Subgroup P} [A.Normal]
    (hAcomm : IsMulCommutative A) (u : P) (a : A) :
    MulAut.conjNormal (H := A) (u * (a : P))⁻¹ =
      MulAut.conjNormal (H := A) u⁻¹ := by
  ext b
  let c : A := (MulAut.conjNormal (H := A) u⁻¹) b
  have hcval : (c : P) = u⁻¹ * (b : P) * u := by simp [c]
  have hac : (a : P) * (c : P) = (c : P) * (a : P) :=
    congrArg A.subtype (hAcomm.is_comm.comm a c)
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  simp only [inv_inv]
  change (u * (a : P))⁻¹ * (b : P) * (u * (a : P)) =
    u⁻¹ * (b : P) * u
  rw [mul_inv_rev]
  calc
    (a : P)⁻¹ * u⁻¹ * (b : P) * (u * (a : P)) =
        (a : P)⁻¹ * (u⁻¹ * (b : P) * u) * (a : P) := by group
    _ = (a : P)⁻¹ * (c : P) * (a : P) := by rw [hcval]
    _ = (c : P) := by rw [mul_assoc, ← hac]; simp
    _ = u⁻¹ * (b : P) * u := hcval

/-- In the unique nontrivial coset of `C/A`, inverse conjugation on `A`
commutes with the actor. -/
theorem subgroupConjInv_commutes_with_actor_of_quotient_natCard_eq_two
    {P X : Type*} [Group P] [Group X] [Finite P]
    (act : X →* MulAut P) {A C : Subgroup P} [A.Normal]
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    (hcard : Nat.card (↑C ⧸ A.subgroupOf C) = 2)
    (u : C) (hu : (u : P) ∉ A) (x : X) :
    hAinv.restrict x *
        MulAut.conjNormal (H := A) (u : P)⁻¹ =
      MulAut.conjNormal (H := A) (u : P)⁻¹ *
        hAinv.restrict x := by
  let ux : C := hCinv.restrict x u
  have huxA : (ux : P) ∉ A := by
    intro hmem
    apply hu
    have hinv : (act x)⁻¹ (ux : P) ∈ A :=
      hAinv.inv_smul_mem x hmem
    simpa [ux, IsAInvariant.restrict_apply_val] using hinv
  have huN : u ∉ A.subgroupOf C := by
    simpa only [Subgroup.mem_subgroupOf] using hu
  have huxN : ux ∉ A.subgroupOf C := by
    simpa only [Subgroup.mem_subgroupOf] using huxA
  have hq := outside_quotient_mk_eq
    (A.subgroupOf C) hcard huN huxN
  obtain ⟨aC, haC, hua⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := A.subgroupOf C)).mp hq
  let a : A := ⟨(aC : P), haC⟩
  have huaP : (u : P) * (a : P) = (ux : P) :=
    congrArg C.subtype hua
  have hsame :
      MulAut.conjNormal (H := A) (ux : P)⁻¹ =
        MulAut.conjNormal (H := A) (u : P)⁻¹ := by
    rw [← huaP]
    exact subgroupConjInv_mul_right_eq hAcomm (u : P) a
  have hcompat := subgroupConjInv_actor_compatible act hAinv hCinv x u
  change MulAut.conjNormal (H := A) (ux : P)⁻¹ =
    hAinv.restrict x *
      MulAut.conjNormal (H := A) (u : P)⁻¹ *
        (hAinv.restrict x)⁻¹ at hcompat
  have hconj : MulAut.conjNormal (H := A) (u : P)⁻¹ =
      hAinv.restrict x *
        MulAut.conjNormal (H := A) (u : P)⁻¹ *
          (hAinv.restrict x)⁻¹ := hsame.symm.trans hcompat
  have hr := congrArg
    (fun β : MulAut A ↦ β * hAinv.restrict x) hconj
  simpa [mul_assoc] using hr.symm

/-- Consequently the canonical subgroup `A^(2-2 eta)` is actor-invariant. -/
theorem higmanSquareTwist_range_isAInvariant
    {P X : Type*} [Group P] [Group X] [Finite P]
    (act : X →* MulAut P) {A C : Subgroup P} [A.Normal]
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    (hcard : Nat.card (↑C ⧸ A.subgroupOf C) = 2)
    (u : C) (hu : (u : P) ∉ A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    IsAInvariant hAinv.restrict
      (higmanSquareTwist
        (MulAut.conjNormal (H := A) (u : P)⁻¹)).range := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  rw [isAInvariant_iff_smul_mem]
  intro x d hd
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hd
  apply MonoidHom.mem_range.mpr
  refine ⟨hAinv.restrict x a, ?_⟩
  change MulAut.conjNormal (H := A) (u : P)⁻¹
      (hAinv.restrict x a) * hAinv.restrict x a =
    hAinv.restrict x
      (MulAut.conjNormal (H := A) (u : P)⁻¹ a * a)
  rw [map_mul]
  have hpoint := DFunLike.congr_fun
    (subgroupConjInv_commutes_with_actor_of_quotient_natCard_eq_two
      act hAcomm hAinv hCinv hcard u hu x) a
  change hAinv.restrict x
      (MulAut.conjNormal (H := A) (u : P)⁻¹ a) =
    MulAut.conjNormal (H := A) (u : P)⁻¹
      (hAinv.restrict x a) at hpoint
  rw [hpoint]

theorem isCyclic_sup_zpowers_quotient
    {A : Type*} [CommGroup A] (D : Subgroup A) (z : A) :
    IsCyclic
      (↑(D ⊔ Subgroup.zpowers z) ⧸
        D.subgroupOf (D ⊔ Subgroup.zpowers z)) := by
  let B := D ⊔ Subgroup.zpowers z
  let D' := D.subgroupOf B
  let Z' := (Subgroup.zpowers z).subgroupOf B
  let q : Z' →* (B ⧸ D') :=
    (QuotientGroup.mk' D').comp Z'.subtype
  have hqsurj : Function.Surjective q := by
    intro w
    refine QuotientGroup.induction_on w ?_
    rintro ⟨b, hb⟩
    obtain ⟨d, hd, k, hk, hdk⟩ := Subgroup.mem_sup.mp hb
    let kB : B := ⟨k, Subgroup.mem_sup_right hk⟩
    let k' : Z' := ⟨kB, Subgroup.mem_subgroupOf.mpr hk⟩
    refine ⟨k', ?_⟩
    change QuotientGroup.mk' D' (Z'.subtype k') =
      QuotientGroup.mk' D' (⟨b, hb⟩ : B)
    apply (QuotientGroup.mk'_eq_mk' (N := D')).mpr
    let dB : B := ⟨d, Subgroup.mem_sup_left hd⟩
    refine ⟨dB, Subgroup.mem_subgroupOf.mpr hd, ?_⟩
    apply Subtype.ext
    change k * d = b
    rw [mul_comm, hdk]
  haveI : IsCyclic ↑(Subgroup.zpowers z) := Subgroup.isCyclic_zpowers z
  haveI : IsCyclic Z' := by
    rw [(Subgroup.subgroupOfEquivOfLe
      (le_sup_right : Subgroup.zpowers z ≤ B)).isCyclic]
    infer_instance
  exact isCyclic_of_surjective q hqsurj

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- The purely lattice-theoretic last step of Higman's Lemma 1
contradiction. -/
theorem false_of_invariant_lt_cyclic_of_layer_quotients_noncyclic
    {A X : Type*} [CommGroup A] [Finite A] [Group X]
    (act : X →* MulAut A) {e : ℕ}
    (classify : ∀ U : Subgroup A, IsAInvariant act U →
      ∃ s ≤ e, U = Agemo A 2 s)
    (layerNotCyclic : ∀ {s t : ℕ}, s < t → t ≤ e →
      ¬ IsCyclic
        (↑(Agemo A 2 s) ⧸
          (Agemo A 2 t).subgroupOf (Agemo A 2 s)))
    {D B : Subgroup A}
    (hDinv : IsAInvariant act D) (hBinv : IsAInvariant act B)
    (hDB : D < B)
    (hcyc : IsCyclic (↑B ⧸ D.subgroupOf B)) : False := by
  obtain ⟨t, hte, hDt⟩ := classify D hDinv
  obtain ⟨s, hse, hBs⟩ := classify B hBinv
  have hst : s < t := by
    have hstle : s ≤ t := by
      by_contra hnot
      have hts : t ≤ s := Nat.le_of_not_ge hnot
      apply hDB.ne
      apply le_antisymm hDB.le
      rw [hBs, hDt]
      exact Agemo.anti hts
    exact hstle.lt_of_ne (by
      intro hEq
      apply hDB.ne
      rw [hBs, hDt, hEq])
  subst D
  subst B
  exact layerNotCyclic hst hte hcyc

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

private theorem cyclic_finite_unique_order_two
    {P : Type*} [Group P] [Finite P] [IsCyclic P] {s t : P}
    (hs_ord : orderOf s = 2) (ht_ord : orderOf t = 2) : s = t := by
  letI : Fintype P := Fintype.ofFinite P
  have h2_dvd : (2 : ℕ) ∣ Fintype.card P := by
    rw [← hs_ord]
    exact orderOf_dvd_card
  have h_card : Fintype.card {x : P // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient h2_dvd,
      Nat.totient_two]
  haveI : Subsingleton {x : P // orderOf x = 2} :=
    Fintype.card_le_one_iff_subsingleton.mp h_card.le
  exact congrArg Subtype.val
    (Subsingleton.elim
      (⟨s, hs_ord⟩ : {x : P // orderOf x = 2})
      ⟨t, ht_ord⟩)

/-- The last nontrivial Agemo layer is not cyclic when the ambient
homocyclic group has two distinct involutions. -/
theorem not_isCyclic_lastAgemoLayer_of_two_involutions
    {A ι : Type*} [CommGroup A] [Finite A] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e)))) (he : 0 < e)
    {x y : A} (hx : x ∈ involutions A) (hy : y ∈ involutions A)
    (hxy : x ≠ y) :
    ¬ IsCyclic ↑(Agemo A 2 (e - 1)) := by
  intro hcyc
  letI : IsCyclic ↑(Agemo A 2 (e - 1)) := hcyc
  let x' : ↑(Agemo A 2 (e - 1)) :=
    ⟨x, (sq_eq_one_iff_mem_lastAgemoLayer ε he).mp hx.1⟩
  let y' : ↑(Agemo A 2 (e - 1)) :=
    ⟨y, (sq_eq_one_iff_mem_lastAgemoLayer ε he).mp hy.1⟩
  have hxord : orderOf x' = 2 := by
    exact orderOf_eq_prime (p := 2) (Subtype.ext hx.1) (by
      intro hx1
      apply hx.2
      exact congrArg Subtype.val hx1)
  have hyord : orderOf y' = 2 := by
    exact orderOf_eq_prime (p := 2) (Subtype.ext hy.1) (by
      intro hy1
      apply hy.2
      exact congrArg Subtype.val hy1)
  apply hxy
  exact congrArg Subtype.val
    (cyclic_finite_unique_order_two hxord hyord)

/-- No quotient of two distinct Agemo layers is cyclic when the
homocyclic group has two distinct involutions. -/
theorem not_isCyclic_agemoQuotient_of_two_involutions
    {A ι : Type*} [CommGroup A] [Finite A] {e s t : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (hst : s < t) (hte : t ≤ e)
    {x y : A} (hx : x ∈ involutions A) (hy : y ∈ involutions A)
    (hxy : x ≠ y) :
    ¬ IsCyclic
      (↑(Agemo A 2 s) ⧸
        (Agemo A 2 t).subgroupOf (Agemo A 2 s)) := by
  intro hcyc
  have hs : s < e := lt_of_lt_of_le hst hte
  let M := Agemo A 2 s
  let D := (Agemo A 2 t).subgroupOf M
  let N := (Agemo A 2 (s + 1)).subgroupOf M
  have hDt : Agemo A 2 t ≤ Agemo A 2 (s + 1) :=
    Agemo.anti (by omega)
  have hDN : D ≤ N := by
    intro a ha
    exact hDt ha
  let q : (M ⧸ D) →* (M ⧸ N) :=
    QuotientGroup.map D N (MonoidHom.id M) (by
      simpa [Subgroup.comap_id] using hDN)
  have hqsurj : Function.Surjective q := by
    intro z
    refine QuotientGroup.induction_on z ?_
    intro a
    refine ⟨QuotientGroup.mk a, ?_⟩
    rfl
  letI : IsCyclic (M ⧸ D) := hcyc
  have hnextCyc : IsCyclic (M ⧸ N) :=
    isCyclic_of_surjective q hqsurj
  letI : IsCyclic (M ⧸ N) := hnextCyc
  have hlastCyc : IsCyclic ↑(Agemo A 2 (e - 1)) :=
    isCyclic_of_surjective
      (agemoSuccQuotientEquivLast ε hs).toMonoidHom
      (agemoSuccQuotientEquivLast ε hs).surjective
  exact not_isCyclic_lastAgemoLayer_of_two_involutions ε (by omega)
    hx hy hxy hlastCyc

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- Higman's canonical `2 - 2 nu(u)` is exactly `1 + alpha_u`.
This identifies the source notation without introducing a second subgroup. -/
theorem HigmanEndomorphismFamily.twoSubTwoMap_eq_squareTwist
    {P : Type*} [Group P] {A C : Subgroup P} [A.Normal]
    (hAcomm : IsMulCommutative A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∀ (F : HigmanEndomorphismFamily
        (fun v : C ↦ MulAut.conjNormal (H := A) (v : P)⁻¹))
      (u : C),
      F.twoSubTwoMap u =
        higmanSquareTwist
          (MulAut.conjNormal (H := A) (u : P)⁻¹) := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  intro F u
  ext a
  have hcanonical := actualHigmanFamily_mul_square_eq hAcomm F u a
  have htwist := mul_subgroup_element_sq (u : P) a
  exact mul_left_cancel (hcanonical.symm.trans htwist)

/-- Exact source-facing description of Higman's subgroup `B`, using the
canonical range `A^(2-2 eta)` rather than a duplicate twist map. -/
theorem higmanOutsideSquare_closure_eq_twoSubTwoMap_range_sup_zpowers
    {P : Type*} [Group P] [Finite P]
    {A C : Subgroup P} [A.Normal]
    (hAC : A ≤ C) (hAcomm : IsMulCommutative A)
    (hcard : Nat.card (↑C ⧸ A.subgroupOf C) = 2)
    (hsq : ∀ v : C, (v : P) ∉ A → (v : P) ^ 2 ∈ A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∀ (F : HigmanEndomorphismFamily
        (fun v : C ↦ MulAut.conjNormal (H := A) (v : P)⁻¹))
      (u : C) (hu : (u : P) ∉ A),
      let z : A := ⟨(u : P) ^ 2, hsq u hu⟩
      Subgroup.closure (higmanOutsideSquareSet A C) =
        (F.twoSubTwoMap u).range ⊔ Subgroup.zpowers z := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  intro F u hu
  let z : A := ⟨(u : P) ^ 2, hsq u hu⟩
  rw [F.twoSubTwoMap_eq_squareTwist hAcomm u]
  exact higmanOutsideSquare_closure_eq_twist_range_sup_zpowers
    hAC hAcomm hcard hsq u hu

/-- The canonical subgroup `A^(2-2 eta)` is actor-invariant. -/
theorem HigmanEndomorphismFamily.twoSubTwoMap_range_isAInvariant
    {P X : Type*} [Group P] [Group X] [Finite P]
    (act : X →* MulAut P) {A C : Subgroup P} [A.Normal]
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    (hcard : Nat.card (↑C ⧸ A.subgroupOf C) = 2) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∀ (F : HigmanEndomorphismFamily
        (fun v : C ↦ MulAut.conjNormal (H := A) (v : P)⁻¹))
      (u : C) ( _hu : (u : P) ∉ A),
      IsAInvariant hAinv.restrict (F.twoSubTwoMap u).range := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  intro F u _hu
  rw [F.twoSubTwoMap_eq_squareTwist hAcomm u]
  exact higmanSquareTwist_range_isAInvariant
    act hAcomm hAinv hCinv hcard u _hu

/-- Higman's second final case is impossible. If `u^2` is outside the
canonical range `A^(2-2 eta)`, the subgroup generated by outside squares is
a strictly larger invariant subgroup with cyclic quotient. -/
theorem actualHigmanFamily_second_case_false
    {P X : Type*} [Group P] [Finite P] [Group X]
    (act : X →* MulAut P) {A C : Subgroup P} [A.Normal]
    (hAC : A ≤ C) (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant act A) (hCinv : IsAInvariant act C)
    {e : ℕ}
    (classify : ∀ U : Subgroup A, IsAInvariant hAinv.restrict U →
      ∃ s ≤ e, U = Agemo A 2 s)
    (layerNotCyclic : ∀ {s t : ℕ}, s < t → t ≤ e →
      ¬ IsCyclic
        (↑(Agemo A 2 s) ⧸
          (Agemo A 2 t).subgroupOf (Agemo A 2 s)))
    (hcard : Nat.card (↑C ⧸ A.subgroupOf C) = 2)
    (hsq : ∀ v : C, (v : P) ∉ A → (v : P) ^ 2 ∈ A) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∀ (F : HigmanEndomorphismFamily
        (fun v : C ↦ MulAut.conjNormal (H := A) (v : P)⁻¹))
      (u : C) (hu : (u : P) ∉ A),
      ((⟨(u : P) ^ 2, hsq u hu⟩ : A) ∉
        (F.twoSubTwoMap u).range) → False := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  intro F u hu hzD
  let z : A := ⟨(u : P) ^ 2, hsq u hu⟩
  let D : Subgroup A := (F.twoSubTwoMap u).range
  let B : Subgroup A := Subgroup.closure (higmanOutsideSquareSet A C)
  have hzNotD : z ∉ D := by
    simpa [z, D] using hzD
  have hBform : B = D ⊔ Subgroup.zpowers z := by
    exact higmanOutsideSquare_closure_eq_twoSubTwoMap_range_sup_zpowers
      hAC hAcomm hcard hsq F u hu
  have hDinv : IsAInvariant hAinv.restrict D :=
    F.twoSubTwoMap_range_isAInvariant
      act hAcomm hAinv hCinv hcard u hu
  have hBinv : IsAInvariant hAinv.restrict B :=
    higmanOutsideSquare_closure_isAInvariant act hAinv hCinv
  have hDBle : D ≤ B := by
    rw [hBform]
    exact le_sup_left
  have hzB : z ∈ B := by
    rw [hBform]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hDB : D < B := lt_of_le_of_ne hDBle (by
    intro hEq
    apply hzNotD
    rw [hEq]
    exact hzB)
  have hcyc : IsCyclic (↑B ⧸ D.subgroupOf B) := by
    rw [hBform]
    exact isCyclic_sup_zpowers_quotient D z
  exact false_of_invariant_lt_cyclic_of_layer_quotients_noncyclic
    hAinv.restrict classify layerNotCyclic hDinv hBinv hDB hcyc

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

/-- A homocyclic `2`-group of common cyclic height at most two has exponent
dividing four. -/
theorem pow_four_eq_one_of_homocyclic_of_not_three_le
    {A ι : Type*} [CommGroup A] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (hnot : ¬ 3 ≤ e) (a : A) :
    a ^ 4 = 1 := by
  have he : e ≤ 2 := by omega
  have hpow : a ^ (2 ^ e) = 1 :=
    pow_two_pow_eq_one_of_equiv_pi_zmod ε a
  have horder : orderOf a ∣ 2 ^ e :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hdvd : 2 ^ e ∣ 4 := by
    simpa using Nat.pow_dvd_pow 2 he
  exact orderOf_dvd_iff_pow_eq_one.mp (horder.trans hdvd)

/-- Ambient distinct involutions lying in `A` give distinct involutions of
the subtype group `A`. -/
private theorem exists_distinct_involutions_subtype_of_subset
    {P : Type*} [Group P] {A : Subgroup P}
    (hinvA : involutions P ⊆ A)
    {x y : P} (hx : x ∈ involutions P) (hy : y ∈ involutions P)
    (hxy : x ≠ y) :
    ∃ xA yA : A,
      xA ∈ involutions A ∧ yA ∈ involutions A ∧ xA ≠ yA := by
  let xA : A := ⟨x, hinvA hx⟩
  let yA : A := ⟨y, hinvA hy⟩
  refine ⟨xA, yA, ?_, ?_, ?_⟩
  · refine ⟨Subtype.ext hx.1, ?_⟩
    intro h
    apply hx.2
    exact congrArg Subtype.val h
  · refine ⟨Subtype.ext hy.1, ?_⟩
    intro h
    apply hy.2
    exact congrArg Subtype.val h
  · intro h
    apply hxy
    exact congrArg Subtype.val h

/-- **Higman, Suzuki 2-groups, Lemma 3** (pp. 83--84).

Let a subgroup `X ≤ Aut(P)` act transitively on the involutions of the
finite `2`-group `P`, which has at least two involutions. If a normal
`X`-invariant subgroup `C` covers the normal abelian `X`-invariant subgroup
`A`, and their ambient Frattini images agree, then every element of `A` has
fourth power one.

The homocyclic coordinates, their common height, and the chosen Higman
endomorphism family are constructed internally. The source assumes `P` is
nonabelian, but that hypothesis is not used in this branch. -/
theorem NormalInvariantCover.pow_four_eq_one_of_frattini_map_eq
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (htrans : ∀ x ∈ involutions P, ∀ y ∈ involutions P,
      ∃ g : X, (g : MulAut P) x = y)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    {A C : Subgroup P}
    (hcover : NormalInvariantCover X.subtype A C)
    (hAcomm : IsMulCommutative A)
    (hΦ : (frattini C).map C.subtype =
      (frattini A).map A.subtype) :
    ∀ a : A, a ^ 4 = 1 := by
  by_cases hAeq : A = ⊥
  · intro a
    apply Subtype.ext
    have ha : (a : P) = 1 := by
      have : (a : P) ∈ (⊥ : Subgroup P) := by
        rw [← hAeq]
        exact a.2
      simpa using this
    simp [ha]
  have hAne : A ≠ ⊥ := hAeq
  letI : A.Normal := hcover.left.1
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  have hinvA : involutions P ⊆ A :=
    involutions_subset_of_nontrivial_invariant
      hP X htrans hcover.left.2 hAne
  have htransA : ∀ x ∈ involutions A, ∀ y ∈ involutions A,
      ∃ g : X, hcover.left.2.restrict g x = y :=
    restricted_involutions_transitive X.subtype hcover.left.2
      (by simpa using htrans)
  obtain ⟨ι, hι, e, _hepos, hε, classify⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      (hP.to_subgroup A) hcover.left.2.restrict htransA
  letI : Fintype ι := hι
  obtain ⟨ε⟩ := hε
  intro a
  by_cases he : 3 ≤ e
  · obtain ⟨x, y, hx, hy, hxy⟩ := hmulti
    obtain ⟨xA, yA, hxA, hyA, hxyA⟩ :=
      exists_distinct_involutions_subtype_of_subset hinvA hx hy hxy
    have layerNotCyclic : ∀ {s t : ℕ}, s < t → t ≤ e →
        ¬ IsCyclic
          (↑(Agemo A 2 s) ⧸
            (Agemo A 2 t).subgroupOf (Agemo A 2 s)) := by
      intro s t hst hte
      exact not_isCyclic_agemoQuotient_of_two_involutions
        ε hst hte hxA hyA hxyA
    let F : HigmanEndomorphismFamily
        (fun u : C ↦ MulAut.conjNormal (H := A) (u : P)⁻¹) :=
      chosenHigmanEndomorphismFamily
        hP hcover.le hAcomm hΦ ε
    have hcard : Nat.card (↑C ⧸ A.subgroupOf C) = 2 :=
      actualHigmanFamily_quotient_natCard_eq_two
        hP X htrans hcover.lt hAcomm hcover.left.2 hcover.right.2
          hAne hΦ ε he F
    have hsq : ∀ v : C, (v : P) ∉ A → (v : P) ^ 2 ∈ A := by
      intro v _
      exact Subgroup.map_subtype_le (Agemo A 2 1)
        (square_mem_agemo_one_of_frattini_map_eq
          hP hcover.le hAcomm hΦ v.2)
    obtain ⟨uP, huC, huA⟩ := SetLike.exists_of_lt hcover.lt
    let u : C := ⟨uP, huC⟩
    have hu : (u : P) ∉ A := by simpa [u] using huA
    let z : A := ⟨(u : P) ^ 2, hsq u hu⟩
    have hfirst : (u : P) ^ 2 ∉
        (F.twoSubTwoMap u).range.map A.subtype :=
      actualHigmanFamily_sq_not_mem_twoSubTwoMap_range
        hAcomm hinvA u hu F
    have hzD : z ∉ (F.twoSubTwoMap u).range := by
      intro hz
      apply hfirst
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    exact False.elim
      (actualHigmanFamily_second_case_false
        X.subtype hcover.le hAcomm hcover.left.2 hcover.right.2
          classify layerNotCyclic hcard hsq F u hu hzD)
  · exact pow_four_eq_one_of_homocyclic_of_not_three_le ε he a

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
