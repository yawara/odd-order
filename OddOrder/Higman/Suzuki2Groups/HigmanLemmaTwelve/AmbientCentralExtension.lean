/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.MixedCommutators

/-!
# Higman's Lemma 12: the ambient central extension

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
p. 90.

Before the B/C/D case analysis, the length-three group is a class-two central
extension with elementary-abelian kernel `Φ(P)`.  This file establishes the
ambient identities needed to put the two `A(n, -)` factors over one common
central coordinate:

* `[P, P] = Φ(P)`;
* `Φ(P) ≤ Z(P)`;
* the first positive lower-central term is `Φ(P)` and the next is trivial;
* the denominator of the second lower-central layer is trivial.

The reverse inclusion `Φ(P) ≤ [P, P]` is substantive.  The derived subgroup
is nontrivial and actor-invariant, so transitivity puts every involution in it.
Every nonidentity element of the elementary-abelian `Φ(P)` is an involution.
The same involution argument puts `Φ(P)` in the center.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open scoped commutatorElement
open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

universe uP uF

section /- Higman Lemma 12: ambient central extension (p. 90) -/

/-- **Higman Lemma 12 (p. 90), ambient central-extension step.**

In the length-three case, the derived subgroup is the Frattini subgroup, and
this common subgroup is central. -/
theorem commutator_eq_frattini_and_frattini_le_center_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    _root_.commutator P = frattini P ∧
      frattini P ≤ Subgroup.center P := by
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hcommNe : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h => hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcommNe
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  have hinvComm : involutions P ⊆ _root_.commutator P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive (IsAInvariant.commutator_self Y.subtype) hcommNe
  have hPhiComm : frattini P ≤ _root_.commutator P := by
    intro z hz
    by_cases hzOne : z = 1
    · exact hzOne ▸ (_root_.commutator P).one_mem
    · apply hinvComm
      exact ⟨congrArg Subtype.val (hEA.pow_eq_one ⟨z, hz⟩), hzOne⟩
  have hcommPhi : _root_.commutator P ≤ frattini P :=
    OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP
  have hcommEq : _root_.commutator P = frattini P :=
    le_antisymm hcommPhi hPhiComm
  have hinvCenter : involutions P ⊆ Subgroup.center P :=
    involutions_subset_center_of_transitive hP Y hxi.transitive
  have hPhiCenter : frattini P ≤ Subgroup.center P := by
    intro z hz
    by_cases hzOne : z = 1
    · exact hzOne ▸ (Subgroup.center P).one_mem
    · apply hinvCenter
      exact ⟨congrArg Subtype.val (hEA.pow_eq_one ⟨z, hz⟩), hzOne⟩
  exact ⟨hcommEq, hPhiCenter⟩

/-- The first positive lower-central term is the Frattini subgroup in the
length-three case. -/
theorem lowerCentralTerm_one_eq_frattini_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    lowerCentralTerm P 1 = frattini P := by
  rw [lowerCentralTerm, Subgroup.top_lowerCentralSeries_one,
    (commutator_eq_frattini_and_frattini_le_center_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime).1]

/-- The second positive lower-central term is trivial in the length-three
case, so the ambient group has nilpotency class at most two. -/
theorem lowerCentralTerm_two_eq_bot_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    lowerCentralTerm P 2 = ⊥ := by
  have heq :=
    commutator_eq_frattini_and_frattini_le_center_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hle : (⊤ : Subgroup P).lowerCentralSeries 1 ≤
      Subgroup.center P := by
    rw [Subgroup.top_lowerCentralSeries_one, heq.1]
    exact heq.2
  simpa [lowerCentralTerm] using
    (Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup P) hle)

/-- The subgroup generated by ambient squares is exactly the Frattini
subgroup in the length-three case. -/
theorem agemo_one_eq_frattini_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    Agemo P 2 1 = frattini P := by
  have hcomm :=
    (commutator_eq_frattini_and_frattini_le_center_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime).1
  apply le_antisymm
  · rw [Agemo, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simpa using IsPGroup.pow_mem_frattini hP x
  · rw [← hcomm]
    exact commutator_le_agemo_two_one P

/-- Squaring in the ambient length-three group lands in its second
lower-central term. -/
theorem lowerCentralSquaresLieInSecond_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    LowerCentralSquaresLieInSecond P := by
  apply lowerCentralSquaresLieInSecond_of_agemo_eq
  rw [agemo_one_eq_frattini_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime,
    lowerCentralTerm_one_eq_frattini_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime]

/-- The zeroth lower-central layer is the ambient quotient by `Φ(P)` in
the length-three case. -/
theorem lowerCentralLayerKernel_zero_eq_frattini_subgroupOf_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    lowerCentralLayerKernel P 0 =
      (frattini P).subgroupOf (lowerCentralTerm P 0) := by
  rw [lowerCentralLayerKernel_zero_eq_of_squares_le P
      (lowerCentralSquaresLieInSecond_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime),
    lowerCentralTerm_one_eq_frattini_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime]

/-- Ambient form of the zeroth-layer kernel identity. -/
theorem lowerCentralLayerKernelInAmbient_zero_eq_frattini_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    lowerCentralLayerKernelInAmbient P 0 = frattini P := by
  rw [lowerCentralLayerKernelInAmbient_zero_eq_of_squares_le P
      (lowerCentralSquaresLieInSecond_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime),
    lowerCentralTerm_one_eq_frattini_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime]

/-- The denominator of the second lower-central layer is trivial in the
length-three case. -/
theorem lowerCentralLayerKernel_one_eq_bot_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    lowerCentralLayerKernel P 1 = ⊥ := by
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have htermOne :=
    lowerCentralTerm_one_eq_frattini_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hEAOne : IsElementaryAbelian 2 ↑(lowerCentralTerm P 1) := by
    rw [htermOne]
    exact hEA
  letI : CommGroup ↑(lowerCentralTerm P 1) :=
    { (inferInstance : Group ↑(lowerCentralTerm P 1)) with
      mul_comm := hEAOne.comm }
  have hAgemo : Agemo ↑(lowerCentralTerm P 1) 2 1 = ⊥ := by
    rw [agemo_eq_range_powMonoidHom]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      apply Subgroup.mem_bot.mpr
      simpa using hEAOne.pow_eq_one x
    · exact bot_le
  have hAmbient : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime,
      hAgemo]
    simp
  rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbient]
  simp

end

namespace XiLengthTwoTypeAData

variable {S : Type uP} [Group S]
variable (data : XiLengthTwoTypeAData.{uP, uF} S)

local instance : Field data.F := data.fieldF
local instance : Finite data.F := data.finiteF
local instance : CharP data.F 2 := data.charTwoF
local instance : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2

/-- The short exact sequence carried by an inclusive type-A model.

Both the central-kernel and quotient coordinates are transported from the
concrete quadratic extension along `equivModel`. -/
noncomputable def modelExtension :
    GroupExtension (Multiplicative data.F) S (Multiplicative data.F) := by
  let E := QuadraticExtension.extension
    (typeAQuadraticMap data.phi)
    (Module.finBasis (ZMod 2) data.F)
  exact
    { inl := data.equivModel.symm.toMonoidHom.comp E.inl
      rightHom := E.rightHom.comp data.equivModel.toMonoidHom
      inl_injective := data.equivModel.symm.injective.comp E.inl_injective
      range_inl_eq_ker_rightHom := by
        rw [MonoidHom.range_comp, E.range_inl_eq_ker_rightHom]
        exact (MonoidHom.ker_comp_mulEquiv E.rightHom data.equivModel).symm
      rightHom_surjective :=
        E.rightHom_surjective.comp data.equivModel.surjective }

/-- Projection from an inclusive type-A model to its quotient field
coordinate. -/
noncomputable def modelProjection : S →* Multiplicative data.F :=
  data.modelExtension.rightHom

/-- The quotient-coordinate projection of an inclusive type-A model is
onto. -/
theorem modelProjection_surjective :
    Function.Surjective data.modelProjection :=
  data.modelExtension.rightHom_surjective

/-- An element is killed by the type-A model projection exactly when its
square is one. -/
theorem mem_modelProjection_ker_iff_sq_eq_one (x : S) :
    x ∈ data.modelProjection.ker ↔ x ^ 2 = 1 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd (data.equivModel x).quotient = 1 ↔ x ^ 2 = 1
  constructor
  · intro hx
    have hquot : (data.equivModel x).quotient = 0 := by
      simpa using congrArg Multiplicative.toAdd hx
    apply data.equivModel.injective
    rw [map_pow, map_one, TypeAModel.sq_eq_inl_quadraticMap]
    simp [hquot]
  · intro hx
    have hmodel : (data.equivModel x) ^ 2 = 1 := by
      simpa only [map_pow, map_one] using congrArg data.equivModel hx
    rw [TypeAModel.sq_eq_inl_quadraticMap] at hmodel
    have hinl : Multiplicative.ofAdd
        ((data.equivModel x).quotient *
          data.phi (data.equivModel x).quotient) = 1 := by
      apply (QuadraticExtension.extension
        (typeAQuadraticMap data.phi)
        (Module.finBasis (ZMod 2) data.F)).inl_injective
      simpa using hmodel
    have hprod :
        (data.equivModel x).quotient *
          data.phi (data.equivModel x).quotient = 0 := by
      simpa using congrArg Multiplicative.toAdd hinl
    have hquot : (data.equivModel x).quotient = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact data.phi.injective (by simpa using h)
    simp [hquot]

/-- Inside an ambient group, the type-A quotient-coordinate kernel is the
intersection with the ambient Frattini subgroup.

This is a group-level coordinate identification.  It does not yet assert
compatibility with the ambient actor action. -/
theorem modelProjection_ker_eq_frattini_subgroupOf
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (data : XiLengthTwoTypeAData.{uP, uF} S)
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P)) :
    data.modelProjection.ker = (frattini P).subgroupOf S := by
  ext x
  rw [data.mem_modelProjection_ker_iff_sq_eq_one]
  change x ^ 2 = 1 ↔ (x : P) ∈ frattini P
  constructor
  · intro hx
    by_cases hxOne : (x : P) = 1
    · simp [hxOne]
    · apply hinvPhi
      exact ⟨by simpa using congrArg Subtype.val hx, hxOne⟩
  · intro hx
    apply Subtype.ext
    simpa using congrArg Subtype.val (hEA.pow_eq_one ⟨(x : P), hx⟩)

/-- The type-A central-kernel coordinate, transported onto the factor's
intersection with the ambient Frattini subgroup.

This is a group equivalence.  Compatibility with the ambient actor action is
not asserted here. -/
noncomputable def modelKernelEquivFrattiniSubgroupOf
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (data : XiLengthTwoTypeAData.{uP, uF} S)
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P)) :
    Multiplicative data.F ≃* (frattini P).subgroupOf S :=
  (MonoidHom.ofInjective data.modelExtension.inl_injective).trans
    (MulEquiv.subgroupCongr
      (data.modelExtension.range_inl_eq_ker_rightHom.trans
        (data.modelProjection_ker_eq_frattini_subgroupOf hinvPhi hEA)))

/-- If the ambient Frattini subgroup lies in the modeled factor, its type-A
kernel coordinate is a coordinate on that ambient subgroup itself.

This remains a group equivalence; no field multiplication or actor action is
transported by this definition. -/
noncomputable def modelKernelEquivFrattini
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (data : XiLengthTwoTypeAData.{uP, uF} S)
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hPhiS : frattini P ≤ S) :
    Multiplicative data.F ≃* frattini P :=
  (data.modelKernelEquivFrattiniSubgroupOf hinvPhi hEA).trans
    (Subgroup.subgroupOfEquivOfLe hPhiS)

/-- The quotient of a type-A factor by its intersection with the ambient
Frattini subgroup is its defining additive field.

This equivalence records the group quotient coordinate only; equivariance
under the ambient actor remains a separate obligation. -/
noncomputable def modelQuotientEquivFrattiniSubgroupOf
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (data : XiLengthTwoTypeAData.{uP, uF} S)
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P)) :
    S ⧸ (frattini P).subgroupOf S ≃* Multiplicative data.F := by
  letI : ((frattini P).subgroupOf S).Normal :=
    (inferInstance : (frattini P).Normal).subgroupOf S
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (data.modelProjection_ker_eq_frattini_subgroupOf
        hinvPhi hEA).symm).trans
      data.modelExtension.quotientKerRightHomEquivRight

end XiLengthTwoTypeAData

namespace XiLengthThreeTypeAFactorData

variable {P : Type uP} [Group P]
variable {Y : Subgroup (MulAut P)}
variable (data : XiLengthThreeTypeAFactorData P Y)

local instance : Field data.left_model.F := data.left_model.fieldF
local instance : Finite data.left_model.F := data.left_model.finiteF
local instance : CharP data.left_model.F 2 := data.left_model.charTwoF
local instance : Algebra (ZMod 2) data.left_model.F :=
  ZMod.algebra data.left_model.F 2
local instance : Field data.right_model.F := data.right_model.fieldF
local instance : Finite data.right_model.F := data.right_model.finiteF
local instance : CharP data.right_model.F 2 := data.right_model.charTwoF
local instance : Algebra (ZMod 2) data.right_model.F :=
  ZMod.algebra data.right_model.F 2

/-- The actual additive transition between the two type-A kernel fields,
obtained by identifying both kernels with the same ambient `Φ(P)`.

This is the honest common central coordinate available at the group level.
It is deliberately not promoted to a ring equivalence or an actor-equivariant
map; those are further obligations in Higman's B/C/D case analysis. -/
noncomputable def kernelCoordinateTransition
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P)) :
    Multiplicative data.left_model.F ≃*
      Multiplicative data.right_model.F :=
  (data.left_model.modelKernelEquivFrattini hinvPhi hEA
      data.frattini_lt_left.le).trans
    (data.right_model.modelKernelEquivFrattini hinvPhi hEA
      data.frattini_lt_right.le).symm

/-- The noncommuting mixed-factor witness gives a nonzero value of the
actual ambient lower-central bilinear pairing.

The representatives retain their provenance in the left and right factors;
this is the coordinate-free entry point for Higman's eigenvalue comparison
on the mixed products `[x_i,y_j]`. -/
theorem exists_mixed_lowerCentralCommutatorBilinear_ne_zero
    (hxi : IsXiActor Y)
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    (hK1 : lowerCentralLayerKernel P 1 = ⊥) :
    ∃ x y : lowerCentralTerm P 0,
      (x : P) ∈ data.left ∧
      (y : P) ∈ data.right ∧
      lowerCentralCommutatorBilinear P
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y)) ≠ 0 := by
  obtain ⟨x, y, hxy⟩ :=
    data.exists_commutatorElement_ne_one hxi hinvPhi hEA
  let x0 : lowerCentralTerm P 0 :=
    ⟨(x : P), by simp [lowerCentralTerm]⟩
  let y0 : lowerCentralTerm P 0 :=
    ⟨(y : P), by simp [lowerCentralTerm]⟩
  refine ⟨x0, y0, x.property, y.property, ?_⟩
  rw [lowerCentralCommutatorBilinear_mk]
  intro hzero
  have hvalueOne : lowerCentralCommutatorValue P x0 y0 = 1 := by
    simpa using congrArg Additive.toMul hzero
  have hmem : lowerCentralCommutator P x0 y0 ∈
      lowerCentralLayerKernel P 1 :=
    (QuotientGroup.eq_one_iff _).mp hvalueOne
  rw [hK1] at hmem
  have hcommOne : ⁅(x : P), (y : P)⁆ = 1 := by
    have hsub : lowerCentralCommutator P x0 y0 = 1 :=
      Subgroup.mem_bot.mp hmem
    simpa [lowerCentralCommutator, x0, y0] using congrArg Subtype.val hsub
  exact hxy hcommOne

end XiLengthThreeTypeAFactorData

end OddOrder.Higman.Suzuki2Groups
