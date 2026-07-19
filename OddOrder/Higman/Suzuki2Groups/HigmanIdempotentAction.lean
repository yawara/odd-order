/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import OddOrder.GroupTheory.PRank
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Higman.Suzuki2Groups.AgemoLayers
import OddOrder.Higman.Suzuki2Groups.HigmanFrattiniConsequences
import OddOrder.Higman.Suzuki2Groups.HigmanIdempotents

/-!
# Higman Lemma 3: the actual idempotent action on `A / A²`

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 3,
pp. 83--84.

This file formalizes the following connected part of Higman's argument:

* Frattini equality gives the expression `α = 1 - 2ν` and the relation
  `4(ν² - ν) = 0` for inverse conjugation by an element of `C`;
* when the homocyclic exponent is at least eight, `ν` induces an idempotent
  `ZMod 2`-linear endomorphism of the actual quotient `A / A²`;
* the ambient actor induces a `ZMod 2` representation on this same quotient,
  transitive on its nonzero vectors under Higman Lemma 1's hypotheses;
* the inverse-conjugation family satisfies the product-reversal and actor
  covariance identities used in the next stage of Lemma 3.

No cancellation identity for the chosen lifts, pairwise commutativity of the
resulting idempotent family, or exponent-at-most-four conclusion is claimed
here.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory.Suzuki2Group

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03

section FrattiniLift

/-- The Frattini-equality branch of Higman Lemma 3 supplies both the
one-minus-two expression for conjugation and its `4(ν² - ν) = 0`
consequence. -/
theorem exists_addEnd_eq_one_sub_two_and_four_nsmul_of_frattini_map_eq
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A C : Subgroup P} [A.Normal]
    (hAC : A ≤ C) (hAcomm : IsMulCommutative A)
    (hΦ : (frattini C).map C.subtype = (frattini A).map A.subtype)
    {ι : Type*} [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    {u : P} (hu : u ∈ C) :
    letI : CommGroup A :=
      { (inferInstance : Group A) with
        mul_comm := hAcomm.is_comm.comm }
    ∃ ν : AddMonoid.End (Additive A),
      (MulAut.conjNormal (H := A) u⁻¹).toMonoidHom.toAdditive =
          (1 : AddMonoid.End (Additive A)) - 2 • ν ∧
        4 • (ν * ν - ν) = 0 := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  have hu2map :=
    square_mem_agemo_one_of_frattini_map_eq hP hAC hAcomm hΦ hu
  obtain ⟨a2, _, ha2⟩ := Subgroup.mem_map.mp hu2map
  have hu2A : u ^ 2 ∈ A := by
    rw [← ha2]
    exact a2.2
  have hmod : ∀ a : A,
      MulAut.conjNormal (H := A) u⁻¹ a * a⁻¹ ∈ Agemo A 2 1 := by
    intro a
    apply (Subgroup.mem_map_iff_mem A.subtype_injective).mp
    have h := conjugation_mul_inv_mem_agemo_one_of_frattini_map_eq
      hP hAC hAcomm hΦ hu a.2
    simpa using h
  let α : MulAut A := MulAut.conjNormal (H := A) u⁻¹
  obtain ⟨ν, hαν⟩ := exists_addEnd_eq_one_sub_two ε α hmod
  refine ⟨ν, hαν, four_nsmul_mul_sub_self_eq_zero hαν ?_⟩
  apply addEnd_mul_self_eq_one_of_mulAut_mul_self_eq_one
  exact conjNormal_inv_sq_eq_one_of_sq_mem hAcomm hu2A

end FrattiniLift

section ActualModTwoEnd

/-- Reinterpret an additive endomorphism of `Additive A` as an endomorphism
of the chosen commutative group structure on `A`. -/
def addEndToMonoidEnd {A : Type*} [CommGroup A]
    (ν : AddMonoid.End (Additive A)) : A →* A where
  toFun a := Additive.toMul (ν (Additive.ofMul a))
  map_one' := congrArg Additive.toMul ν.map_zero
  map_mul' a b := congrArg Additive.toMul
    (ν.map_add (Additive.ofMul a) (Additive.ofMul b))

@[simp] theorem addEndToMonoidEnd_apply
    {A : Type*} [CommGroup A] (ν : AddMonoid.End (Additive A)) (a : A) :
    addEndToMonoidEnd ν a = Additive.toMul (ν (Additive.ofMul a)) :=
  rfl

/-- Every additive endomorphism of an abelian group preserves its square
subgroup. -/
theorem agemo_one_le_comap_toMultiplicative
    {A : Type*} [CommGroup A] (ν : AddMonoid.End (Additive A)) :
    Agemo A 2 1 ≤ (Agemo A 2 1).comap (addEndToMonoidEnd ν) := by
  intro a ha
  obtain ⟨b, hb⟩ := (mem_agemo_iff_of_comm (p := 2) (n := 1)).mp ha
  apply (mem_agemo_iff_of_comm (p := 2) (n := 1)).mpr
  refine ⟨addEndToMonoidEnd ν b, ?_⟩
  rw [hb]
  change ν (2 • Additive.ofMul b) = 2 • ν (Additive.ofMul b)
  exact map_nsmul ν _ _

/-- The endomorphism induced by `ν` on the actual group quotient `A/A²`. -/
def actualModTwoAddEnd
    {A : Type*} [CommGroup A] (ν : AddMonoid.End (Additive A)) :
    AddMonoid.End (Additive (A ⧸ Agemo A 2 1)) :=
  (QuotientGroup.map (Agemo A 2 1) (Agemo A 2 1)
    (addEndToMonoidEnd ν) (agemo_one_le_comap_toMultiplicative ν)).toAdditive

@[simp] theorem actualModTwoAddEnd_mk
    {A : Type*} [CommGroup A] (ν : AddMonoid.End (Additive A)) (a : A) :
    actualModTwoAddEnd ν (Additive.ofMul (QuotientGroup.mk a)) =
      Additive.ofMul (QuotientGroup.mk (addEndToMonoidEnd ν a)) :=
  rfl

/-- In a homocyclic group of exponent at least eight, every element killed
by four belongs to the square subgroup. -/
theorem toMul_mem_agemo_one_of_four_nsmul_eq_zero
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e) {x : Additive A} (hx : 4 • x = 0) :
    Additive.toMul x ∈ Agemo A 2 1 := by
  let E : Additive A ≃+ HomocyclicModel ι e :=
    (MulEquiv.toAdditive ε).trans additivePiMultiplicativeEquiv
  have hEx : 4 • E x = 0 := by
    simpa only [map_nsmul, map_zero] using congrArg E hx
  obtain ⟨y, hy⟩ := exists_two_smul_of_four_nsmul_eq_zero he (E x) hEx
  apply (mem_agemo_iff_of_comm (p := 2) (n := 1)).mpr
  refine ⟨Additive.toMul (E.symm y), ?_⟩
  change x = 2 • E.symm y
  apply E.injective
  rw [map_nsmul, E.apply_symm_apply]
  exact hy.trans (Nat.cast_smul_eq_nsmul (CoefficientRing e) 2 y)

/-- The defect `ν² - ν` takes values in `A²` under Higman's four-torsion
relation. -/
theorem mul_sub_self_toMul_mem_agemo_one
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e) (ν : AddMonoid.End (Additive A))
    (h4 : 4 • (ν * ν - ν) = 0) (x : Additive A) :
    Additive.toMul ((ν * ν - ν) x) ∈ Agemo A 2 1 := by
  apply toMul_mem_agemo_one_of_four_nsmul_eq_zero ε he
  have hx := DFunLike.congr_fun h4 x
  simpa using hx

/-- The endomorphism induced by `ν` on the actual quotient `A/A²` is
idempotent whenever `4(ν² - ν) = 0`. -/
theorem actualModTwoAddEnd_idempotent
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e) (ν : AddMonoid.End (Additive A))
    (h4 : 4 • (ν * ν - ν) = 0) :
    actualModTwoAddEnd ν * actualModTwoAddEnd ν = actualModTwoAddEnd ν := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
    apply Additive.toMul.injective
    exact ha.symm
  subst q
  change actualModTwoAddEnd ν
      (actualModTwoAddEnd ν (Additive.ofMul (QuotientGroup.mk a))) =
    actualModTwoAddEnd ν (Additive.ofMul (QuotientGroup.mk a))
  let νm : A →* A := addEndToMonoidEnd ν
  calc
    _ = actualModTwoAddEnd ν
        (Additive.ofMul (QuotientGroup.mk (νm a))) :=
      congrArg (actualModTwoAddEnd ν)
        (actualModTwoAddEnd_mk (A := A) ν a)
    _ = Additive.ofMul (QuotientGroup.mk (νm (νm a))) := by
      simpa only [νm] using actualModTwoAddEnd_mk (A := A) ν (νm a)
    _ = Additive.ofMul (QuotientGroup.mk (νm a)) := by
      apply Additive.toMul.injective
      change QuotientGroup.mk (νm (νm a)) = QuotientGroup.mk (νm a)
      rw [QuotientGroup.eq_iff_div_mem]
      have hδ := mul_sub_self_toMul_mem_agemo_one ε he ν h4 (Additive.ofMul a)
      change νm (νm a) / νm a ∈ Agemo A 2 1 at hδ
      exact hδ
    _ = actualModTwoAddEnd ν (Additive.ofMul (QuotientGroup.mk a)) :=
      (actualModTwoAddEnd_mk (A := A) ν a).symm

/-- The actual quotient `A/A²` has exponent two. -/
theorem actualQuotient_two_nsmul_eq_zero
    {A : Type*} [CommGroup A]
    (q : Additive (A ⧸ Agemo A 2 1)) : 2 • q = 0 := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  apply Additive.toMul.injective
  change q.toMul ^ 2 = 1
  rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  simpa using (Agemo.mem_of_eq_pow (G := A) (p := 2) (n := 1) a)

noncomputable instance actualQuotientModTwoModule
    {A : Type*} [CommGroup A] :
    Module (ZMod 2) (Additive (A ⧸ Agemo A 2 1)) :=
  AddCommGroup.zmodModule actualQuotient_two_nsmul_eq_zero

/-- The induced endomorphism on `A/A²`, reinterpreted as a `ZMod 2`-linear
map. -/
noncomputable def actualModTwoEnd
    {A : Type*} [CommGroup A] (ν : AddMonoid.End (Additive A)) :
    Module.End (ZMod 2) (Additive (A ⧸ Agemo A 2 1)) :=
  (actualModTwoAddEnd ν).toZModLinearMap 2

@[simp] theorem actualModTwoEnd_mk
    {A : Type*} [CommGroup A] (ν : AddMonoid.End (Additive A)) (a : A) :
    actualModTwoEnd ν (Additive.ofMul (QuotientGroup.mk a)) =
      Additive.ofMul (QuotientGroup.mk (addEndToMonoidEnd ν a)) :=
  rfl

@[simp] theorem actualModTwoEnd_zero
    {A : Type*} [CommGroup A] :
    actualModTwoEnd (0 : AddMonoid.End (Additive A)) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
    apply Additive.toMul.injective
    exact ha.symm
  subst q
  simp [actualModTwoEnd_mk, addEndToMonoidEnd]

@[simp] theorem actualModTwoEnd_one
    {A : Type*} [CommGroup A] :
    actualModTwoEnd (1 : AddMonoid.End (Additive A)) = 1 := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
    apply Additive.toMul.injective
    exact ha.symm
  subst q
  simp [actualModTwoEnd_mk, addEndToMonoidEnd]

@[simp] theorem actualModTwoEnd_add
    {A : Type*} [CommGroup A]
    (ν μ : AddMonoid.End (Additive A)) :
    actualModTwoEnd (ν + μ) = actualModTwoEnd ν + actualModTwoEnd μ := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
    apply Additive.toMul.injective
    exact ha.symm
  subst q
  apply Additive.toMul.injective
  change (QuotientGroup.mk (addEndToMonoidEnd (ν + μ) a) :
      A ⧸ Agemo A 2 1) =
    (QuotientGroup.mk (addEndToMonoidEnd ν a) : A ⧸ Agemo A 2 1) *
      QuotientGroup.mk (addEndToMonoidEnd μ a)
  rw [← QuotientGroup.mk_mul]
  rfl

@[simp] theorem actualModTwoEnd_mul
    {A : Type*} [CommGroup A]
    (ν μ : AddMonoid.End (Additive A)) :
    actualModTwoEnd (ν * μ) = actualModTwoEnd ν * actualModTwoEnd μ := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
    apply Additive.toMul.injective
    exact ha.symm
  subst q
  simp [actualModTwoEnd_mk, addEndToMonoidEnd, AddMonoid.End.coe_mul,
    Module.End.mul_apply]

/-- Linear form of `actualModTwoAddEnd_idempotent`. -/
theorem actualModTwoEnd_idempotent
    {A ι : Type*} [CommGroup A] [Finite ι] {e : ℕ}
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (he : 3 ≤ e) (ν : AddMonoid.End (Additive A))
    (h4 : 4 • (ν * ν - ν) = 0) :
    actualModTwoEnd ν * actualModTwoEnd ν = actualModTwoEnd ν := by
  apply LinearMap.ext
  intro q
  change actualModTwoAddEnd ν (actualModTwoAddEnd ν q) =
    actualModTwoAddEnd ν q
  exact DFunLike.congr_fun (actualModTwoAddEnd_idempotent ε he ν h4) q

end ActualModTwoEnd

section ActualActorRepresentation

/-- The action induced by `φ` on the actual quotient `A/A²`. -/
noncomputable def actualAgemoOneQuotientAction
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) : X →* MulAut (A ⧸ Agemo A 2 1) :=
  (IsAInvariant.of_characteristic φ).quotientMulAutHom

/-- The actual `A/A²` action as a representation over `ZMod 2`. -/
noncomputable def actualAgemoOneQuotientRepresentation
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) :
    Representation (ZMod 2) X (Additive (A ⧸ Agemo A 2 1)) where
  toFun g :=
    (mulAutToZModTwoLinearEquiv (actualAgemoOneQuotientAction φ g)).toLinearMap
  map_one' := by
    rw [map_one]
    exact Module.End.one_eq_id.symm
  map_mul' g h := by
    simp [actualAgemoOneQuotientAction, mulAutToZModTwoLinearEquiv]

@[simp] theorem actualAgemoOneQuotientRepresentation_apply
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) (g : X)
    (q : Additive (A ⧸ Agemo A 2 1)) :
    actualAgemoOneQuotientRepresentation φ g q =
      Additive.ofMul (actualAgemoOneQuotientAction φ g q.toMul) :=
  rfl

/-- The zeroth successive Agemo quotient. -/
abbrev ZeroLayer (A : Type*) [CommGroup A] :=
  ↥(Agemo A 2 0) ⧸
    (Agemo A 2 1).subgroupOf (Agemo A 2 0)

/-- Regard every element of `A` as an element of `Agemo⁰(A) = A`. -/
def toAgemoZero {A : Type*} [CommGroup A] : A →* ↥(Agemo A 2 0) :=
  (MonoidHom.id A).codRestrict (Agemo A 2 0) fun a ↦ by
    rw [agemo_zero_eq_top]
    exact Subgroup.mem_top a

/-- The map from the actual quotient `A/A²` to the zeroth Agemo layer. -/
def actualQuotientToZeroLayer
    {A : Type*} [CommGroup A] :
    A ⧸ Agemo A 2 1 →* ZeroLayer A := by
  apply QuotientGroup.map (Agemo A 2 1)
    ((Agemo A 2 1).subgroupOf (Agemo A 2 0)) toAgemoZero
  intro a ha
  change toAgemoZero a ∈
    (Agemo A 2 1).subgroupOf (Agemo A 2 0)
  exact ha

/-- Forget the `Agemo⁰(A)` subtype in the opposite direction. -/
def zeroLayerToActualQuotient
    {A : Type*} [CommGroup A] :
    ZeroLayer A →* A ⧸ Agemo A 2 1 := by
  apply QuotientGroup.map
    ((Agemo A 2 1).subgroupOf (Agemo A 2 0))
    (Agemo A 2 1) (Agemo A 2 0).subtype
  intro a ha
  exact ha

/-- The actual quotient `A/A²` is explicitly the zeroth successive Agemo
quotient. -/
noncomputable def actualQuotientEquivZeroLayer
    {A : Type*} [CommGroup A] :
    (A ⧸ Agemo A 2 1) ≃* ZeroLayer A := by
  apply MonoidHom.toMulEquiv actualQuotientToZeroLayer
    zeroLayerToActualQuotient
  · ext q
    rfl
  · ext q
    rfl

@[simp] theorem actualQuotientEquivZeroLayer_mk
    {A : Type*} [CommGroup A] (a : A) :
    actualQuotientEquivZeroLayer (QuotientGroup.mk a) =
      QuotientGroup.mk (toAgemoZero a) :=
  rfl

/-- The explicit equivalence intertwines the direct quotient action and the
zeroth successive-layer action. -/
theorem actualQuotientEquivZeroLayer_equivariant
    {A X : Type*} [CommGroup A] [Group X]
    (φ : X →* MulAut A) (g : X) (q : A ⧸ Agemo A 2 1) :
    actualQuotientEquivZeroLayer (actualAgemoOneQuotientAction φ g q) =
      agemoSuccQuotientAction φ 0 g (actualQuotientEquivZeroLayer q) := by
  refine QuotientGroup.induction_on q ?_
  intro a
  rfl

/-- Higman Lemma 1 transitivity, transported to nonzero vectors of the
direct `ZMod 2` representation on `A/A²`. -/
theorem actualAgemoOneQuotientRepresentation_transitive_on_nonzero
    {A X ι : Type*} [CommGroup A] [Group X] {e : ℕ}
    (φ : X →* MulAut A)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ e))))
    (htrans : ∀ x ∈ involutions A, ∀ y ∈ involutions A,
      ∃ g : X, (φ g) x = y)
    (he : 0 < e)
    (q r : Additive (A ⧸ Agemo A 2 1))
    (hq : q ≠ 0) (hr : r ≠ 0) :
    ∃ g : X, actualAgemoOneQuotientRepresentation φ g q = r := by
  let E : (A ⧸ Agemo A 2 1) ≃* ZeroLayer A :=
    actualQuotientEquivZeroLayer
  have hEq : E q.toMul ≠ 1 := by
    intro h
    apply hq
    apply Additive.toMul.injective
    apply E.injective
    simpa using h
  have hEr : E r.toMul ≠ 1 := by
    intro h
    apply hr
    apply Additive.toMul.injective
    apply E.injective
    simpa using h
  obtain ⟨g, hg⟩ :=
    agemoSuccQuotientAction_transitive_on_nonidentity
      φ ε htrans he (E q.toMul) (E r.toMul) hEq hEr
  refine ⟨g, ?_⟩
  apply Additive.toMul.injective
  apply E.injective
  change E (actualAgemoOneQuotientAction φ g q.toMul) = E r.toMul
  rw [actualQuotientEquivZeroLayer_equivariant]
  exact hg

end ActualActorRepresentation

section ConjugationFamily

/-- Conjugation on a normal subgroup respects the inverse of a product.
The order reverses because `(u * v)⁻¹ = v⁻¹ * u⁻¹`. -/
theorem conjNormal_mul_inv
    {P : Type*} [Group P] {A : Subgroup P} [A.Normal]
    (u v : P) :
    MulAut.conjNormal (H := A) (u * v)⁻¹ =
      MulAut.conjNormal (H := A) v⁻¹ *
        MulAut.conjNormal (H := A) u⁻¹ := by
  rw [mul_inv_rev, map_mul]

/-- Restricting an ambient actor to an invariant normal subgroup intertwines
the conjugation family with conjugation inside `MulAut A`. -/
theorem conjNormal_actor_apply_inv
    {P X : Type*} [Group P] [Group X]
    {A : Subgroup P} [A.Normal]
    (act : X →* MulAut P) (hAinv : IsAInvariant act A)
    (x : X) (u : P) :
    MulAut.conjNormal (H := A) (act x u)⁻¹ =
      hAinv.restrict x * MulAut.conjNormal (H := A) u⁻¹ *
        (hAinv.restrict x)⁻¹ := by
  ext a
  have hinv :
      (((hAinv.restrict x)⁻¹ a : A) : P) =
        (act x)⁻¹ (a : P) := by
    rw [← (hAinv.restrict).map_inv x,
      IsAInvariant.restrict_apply_val, act.map_inv]
  rw [MulAut.conjNormal_apply]
  simp only [MulAut.mul_apply, IsAInvariant.restrict_apply_val]
  rw [MulAut.conjNormal_apply, hinv]
  simp only [map_mul, map_inv, MulAut.apply_inv_self]

end ConjugationFamily

end OddOrder.Higman.Suzuki2Groups
