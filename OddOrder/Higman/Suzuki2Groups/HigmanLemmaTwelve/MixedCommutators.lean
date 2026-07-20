/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthTwoModels

/-!
# Higman's Lemma 12: nonzero mixed commutators

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
p. 90.

After identifying the two complementary ξ-length-two factors as
`A(n, θ)` and `A(n, φ)`, Higman observes that the factors cannot commute
elementwise.  If they did, choose a nonidentity `g ∈ Φ(P)` and square roots
`x² = y² = g` in the two factors.  Then `xy⁻¹` would be an involution outside
`Φ(P)`, contradicting that every involution lies in `Φ(P)`.

The square roots here are constructed rather than assumed.  In every honest
`XiLengthTwoTypeAData` model, the element with quotient coordinate `1` and
central coordinate `0` squares to the nonidentity central element with
coordinate `1`.  Actor transitivity transports this root to any prescribed
ambient involution while invariance keeps it inside the chosen factor.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups
open scoped commutatorElement

universe uP uF

section /- Higman Lemma 12: mixed commutators (p. 90) -/

namespace XiLengthTwoTypeAData

/-- The element with quotient coordinate one and central coordinate zero in
an inclusive type-A model, transported back to the modeled group. -/
noncomputable def squareWitness
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) : P := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  exact data.equivModel.symm ⟨1, 0⟩

/-- The central element with coordinate one in an inclusive type-A model,
transported back to the modeled group. -/
noncomputable def squareInvolution
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) : P := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  exact data.equivModel.symm ⟨0, 1⟩

/-- The canonical type-A witness squares to the central element with
coordinate one. -/
theorem squareWitness_sq_eq_squareInvolution
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) :
    data.squareWitness ^ 2 = data.squareInvolution := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  apply data.equivModel.injective
  rw [map_pow]
  simp only [squareWitness, squareInvolution, MulEquiv.apply_symm_apply]
  rw [TypeAModel.sq_eq_inl_quadraticMap]
  simp only [map_one, one_mul]
  rfl

/-- The canonical central element of a type-A model is nonidentity. -/
theorem squareInvolution_ne_one
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) :
    data.squareInvolution ≠ 1 := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  intro h
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  have hm : (⟨0, 1⟩ : TypeAModel data.phi) = 1 := by
    simpa only [squareInvolution, MulEquiv.apply_symm_apply, map_one] using
      congrArg data.equivModel h
  apply (one_ne_zero : (1 : data.F) ≠ 0)
  simpa using congrArg BilinearTwistedProduct.central hm

/-- The canonical central element of a type-A model has square one. -/
theorem squareInvolution_sq_eq_one
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) :
    data.squareInvolution ^ 2 = 1 := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  apply data.equivModel.injective
  rw [map_pow, map_one]
  simp only [squareInvolution, MulEquiv.apply_symm_apply]
  rw [TypeAModel.sq_eq_inl_quadraticMap]
  simp

/-- The square of the canonical type-A witness is nonidentity. -/
theorem squareWitness_sq_ne_one
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) :
    data.squareWitness ^ 2 ≠ 1 := by
  rw [data.squareWitness_sq_eq_squareInvolution]
  exact data.squareInvolution_ne_one

/-- The square of the canonical type-A witness has square one. -/
theorem squareWitness_sq_sq_eq_one
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) :
    (data.squareWitness ^ 2) ^ 2 = 1 := by
  rw [data.squareWitness_sq_eq_squareInvolution]
  exact data.squareInvolution_sq_eq_one

/-- The square of the canonical type-A witness is an involution. -/
theorem squareWitness_sq_mem_involutions
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) :
    data.squareWitness ^ 2 ∈ involutions P :=
  ⟨data.squareWitness_sq_sq_eq_one, data.squareWitness_sq_ne_one⟩

/-- Every ambient involution has a square root in an invariant type-A
factor.  Transitivity transports the concrete model's canonical root. -/
theorem exists_sq_eq_of_mem_ambient_involutions
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    (hxi : IsXiActor Y)
    {S : Subgroup P} (hSinv : IsAInvariant Y.subtype S)
    (data : XiLengthTwoTypeAData.{uP, uF} S)
    {z : P} (hz : z ∈ involutions P) :
    ∃ x : S, ((x ^ 2 : S) : P) = z := by
  let w : S := data.squareWitness
  have hwS : w ^ 2 ∈ involutions S := by
    simpa only [w] using data.squareWitness_sq_mem_involutions
  have hwP : ((w ^ 2 : S) : P) ∈ involutions P := by
    refine ⟨congrArg Subtype.val hwS.1, ?_⟩
    intro h
    exact hwS.2 (Subtype.ext h)
  obtain ⟨a, ha⟩ := hxi.transitive ((w ^ 2 : S) : P) hwP z hz
  refine ⟨hSinv.restrict a w, ?_⟩
  calc
    (((hSinv.restrict a) w) ^ 2 : S).val =
        ((hSinv.restrict a) (w ^ 2) : S).val :=
      congrArg Subtype.val (map_pow (hSinv.restrict a) w 2).symm
    _ = z := (IsAInvariant.restrict_apply_val hSinv a (w ^ 2)).trans ha

end XiLengthTwoTypeAData

namespace XiLengthThreeTypeAFactorData

/-- The two complementary factors in Higman's Lemma 12 cannot commute
elementwise.  Otherwise equal square roots of one Frattini involution would
produce an involution outside the Frattini subgroup. -/
theorem exists_not_commute
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    (data : XiLengthThreeTypeAFactorData P Y)
    (hxi : IsXiActor Y)
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P)) :
    ∃ x : data.left, ∃ y : data.right,
      ¬ Commute (x : P) (y : P) := by
  let g : P := (data.left_model.squareWitness ^ 2 : data.left)
  have hgLeft : data.left_model.squareWitness ^ 2 ∈
      involutions data.left :=
    data.left_model.squareWitness_sq_mem_involutions
  have hg : g ∈ involutions P := by
    refine ⟨?_, ?_⟩
    · simpa [g] using congrArg Subtype.val hgLeft.1
    · intro h
      apply hgLeft.2
      apply Subtype.ext
      simpa [g] using h
  obtain ⟨x, hx⟩ :=
    XiLengthTwoTypeAData.exists_sq_eq_of_mem_ambient_involutions
      hxi data.left_invariant data.left_model hg
  obtain ⟨y, hy⟩ :=
    XiLengthTwoTypeAData.exists_sq_eq_of_mem_ambient_involutions
      hxi data.right_invariant data.right_model hg
  have hxP : (x : P) ^ 2 = g := by simpa using hx
  have hyP : (y : P) ^ 2 = g := by simpa using hy
  refine ⟨x, y, ?_⟩
  intro hcomm
  let z : P := (x : P) * (y : P)⁻¹
  have hzNotPhi : z ∉ frattini P := by
    intro hzPhi
    have hzRight : z ∈ data.right :=
      data.frattini_lt_right.le hzPhi
    have hxRight : (x : P) ∈ data.right := by
      have hzy : z * (y : P) ∈ data.right :=
        data.right.mul_mem hzRight y.property
      simpa [z, mul_assoc] using hzy
    have hxInf : (x : P) ∈ data.left ⊓ data.right :=
      ⟨x.property, hxRight⟩
    have hxPhi : (x : P) ∈ frattini P := by
      rw [← data.inf_eq_frattini]
      exact hxInf
    have hxPow : (x : P) ^ 2 = 1 := by
      simpa using congrArg Subtype.val
        (hEA.pow_eq_one ⟨(x : P), hxPhi⟩)
    exact hg.2 (hxP.symm.trans hxPow)
  have hzSq : z ^ 2 = 1 := by
    calc
      z ^ 2 = (x : P) ^ 2 * ((y : P)⁻¹) ^ 2 := by
        simpa only [z] using hcomm.inv_right.mul_pow 2
      _ = (x : P) ^ 2 * ((y : P) ^ 2)⁻¹ := by rw [inv_pow]
      _ = g * g⁻¹ := by rw [hxP, hyP]
      _ = 1 := mul_inv_cancel g
  have hzNe : z ≠ 1 := by
    intro hzOne
    exact hzNotPhi (hzOne ▸ (frattini P).one_mem)
  exact hzNotPhi (hinvPhi ⟨hzSq, hzNe⟩)

/-- The mixed commutator map of the two complementary factors is nonzero. -/
theorem exists_commutatorElement_ne_one
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    (data : XiLengthThreeTypeAFactorData P Y)
    (hxi : IsXiActor Y)
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P)) :
    ∃ x : data.left, ∃ y : data.right,
      ⁅(x : P), (y : P)⁆ ≠ 1 := by
  obtain ⟨x, y, hxy⟩ := data.exists_not_commute hxi hinvPhi hEA
  refine ⟨x, y, ?_⟩
  intro hcommutator
  exact hxy (commutatorElement_eq_one_iff_commute.mp hcommutator)

end XiLengthThreeTypeAFactorData

/-- **Higman Lemma 12 (p. 90), nonzero mixed-commutator step.**

The two complementary `A(n, -)` factors contain elements which do not
commute.  This is the source argument preceding the B/C/D case split. -/
theorem xiLengthThreeTypeAFactorData_exists_with_nontrivial_mixed_commutator
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
    ∃ data : XiLengthThreeTypeAFactorData P Y,
      ∃ x : data.left, ∃ y : data.right,
        ⁅(x : P), (y : P)⁆ ≠ 1 := by
  obtain ⟨data⟩ :=
    xiLengthThreeTypeAFactorData_exists
      hP hncomm hmulti hxi hlen hprime
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive
      (IsAInvariant.of_characteristic Y.subtype) hPhiNeBot
  exact ⟨data, data.exists_commutatorElement_ne_one hxi hinvPhi hEA⟩

end

end OddOrder.Higman.Suzuki2Groups
