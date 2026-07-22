/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniGradedCommutators

/-!
# Higman's Lemma 13: commutators into the Frattini square

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

In the exponent-four branch the commutator of a middle Frattini class and
an outer class has a literal value in `Phi(P)^2`.  This file constructs
the full bilinear map

`Phi(P) / Phi(P)^2 × P / Phi(P) -> Phi(P)^2`

directly from raw commutators.  It is not obtained by reversing the natural
map from a lower-central layer.  The left descent uses
`Phi(P)^2 <= Z(P)`; the right descent uses commutativity of `Phi(P)`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped commutatorElement IsMulCommutative

universe uP

local instance instFrattiniSquareCommutatorLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance instFrattiniSquareCommutatorLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- A Frattini element with nontrivial square witnesses that the ambient
group is nontrivial. -/
private theorem nontrivial_of_exists_frattini_pow_two_ne_one
    {P : Type uP} [Group P]
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    Nontrivial P := by
  obtain ⟨z, hz⟩ := hexists
  refine ⟨⟨(z : P), 1, ?_⟩⟩
  intro h
  apply hz
  apply Subtype.ext
  rw [show z = 1 from Subtype.ext h, one_pow]

/-- A commutator is multiplicative in the right slot when the correction
commutator is central. -/
private theorem commutatorElement_mul_right_of_mem_center
    {G : Type*} [Group G] (a b c : G)
    (hc : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ =
        ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by simp only [mul_assoc]
    _ = ⁅a, b⁆ * (⁅a, c⁆ * b * b⁻¹) := by
      rw [Subgroup.mem_center_iff.mp hc b]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by simp

/-- A commutator is multiplicative in the left slot when the correction
commutator is central. -/
private theorem commutatorElement_mul_left_of_mem_center
    {G : Type*} [Group G] (a b c : G)
    (hb : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hconj : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
    calc
      a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ * a * a⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hb a]
      _ = ⁅b, c⁆ := by simp
  rw [hconj]
  exact (Subgroup.mem_center_iff.mp hb ⁅a, c⁆).symm

/-- The raw commutator of an element of `Phi(P)` with an ambient
representative, regarded as an element of the literal subgroup
`Phi(P)^2`. -/
def frattiniSquareCommutatorValue
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z : frattini P) (x : lowerCentralTerm P 0) :
    frattiniSquare P :=
  ⟨⁅(z : P), (x : P)⁆,
    commutator_frattini_top_le_frattiniSquare_of_exponent_four
      hP hxi hPhiComm hexists
        (Subgroup.commutator_mem_commutator z.property
          (Subgroup.mem_top (x : P)))⟩

@[simp]
theorem frattiniSquareCommutatorValue_apply_val
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z : frattini P) (x : lowerCentralTerm P 0) :
    ((frattiniSquareCommutatorValue
      hP hxi hPhiComm hexists z x : frattiniSquare P) : P) =
      ⁅(z : P), (x : P)⁆ :=
  rfl

/-- The raw square-valued commutator is multiplicative in its Frattini
slot. -/
theorem frattiniSquareCommutatorValue_mul_left
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z z' : frattini P) (x : lowerCentralTerm P 0) :
    frattiniSquareCommutatorValue
        hP hxi hPhiComm hexists (z * z') x =
      frattiniSquareCommutatorValue hP hxi hPhiComm hexists z x *
    frattiniSquareCommutatorValue
          hP hxi hPhiComm hexists z' x := by
  letI : Nontrivial P :=
    nontrivial_of_exists_frattini_pow_two_ne_one hexists
  apply Subtype.ext
  exact commutatorElement_mul_left_of_mem_center _ _ _
    (frattiniSquare_le_center_of_exponent_four
      hP hxi hPhiComm hfour
        (frattiniSquareCommutatorValue
          hP hxi hPhiComm hexists z' x).property)

/-- The raw square-valued commutator is multiplicative in its ambient
slot. -/
theorem frattiniSquareCommutatorValue_mul_right
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z : frattini P) (x x' : lowerCentralTerm P 0) :
    frattiniSquareCommutatorValue
        hP hxi hPhiComm hexists z (x * x') =
      frattiniSquareCommutatorValue hP hxi hPhiComm hexists z x *
    frattiniSquareCommutatorValue
          hP hxi hPhiComm hexists z x' := by
  letI : Nontrivial P :=
    nontrivial_of_exists_frattini_pow_two_ne_one hexists
  apply Subtype.ext
  exact commutatorElement_mul_right_of_mem_center _ _ _
    (frattiniSquare_le_center_of_exponent_four
      hP hxi hPhiComm hfour
        (frattiniSquareCommutatorValue
          hP hxi hPhiComm hexists z x').property)

/-- Before quotienting either input, the commutator is a bihomomorphism
`Phi(P) -> P -> Phi(P)^2`. -/
noncomputable def frattiniSquareCommutatorBihomRaw
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    frattini P →* lowerCentralTerm P 0 →* frattiniSquare P := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  exact {
    toFun := fun z => {
      toFun := frattiniSquareCommutatorValue
        hP hxi hPhiComm hexists z
      map_one' := by
        apply Subtype.ext
        exact commutatorElement_one_right (z : P)
      map_mul' := frattiniSquareCommutatorValue_mul_right
        hP hxi hPhiComm hfour hexists z }
    map_one' := by
      ext x
      exact commutatorElement_one_left (x : P)
    map_mul' := by
      intro z z'
      ext x
      exact congrArg Subtype.val
        (frattiniSquareCommutatorValue_mul_left
          hP hxi hPhiComm hfour hexists z z' x) }

/-- The raw bihomomorphism kills the square subgroup in its Frattini
slot because `Phi(P)^2` is central. -/
theorem frattiniSquareCommutatorBihomRaw_ker_left
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {z : frattini P} (hz : z ∈ Agemo (frattini P) 2 1)
    (x : lowerCentralTerm P 0) :
    frattiniSquareCommutatorBihomRaw
        hP hxi hPhiComm hfour hexists z x = 1 := by
  letI : Nontrivial P :=
    nontrivial_of_exists_frattini_pow_two_ne_one hexists
  apply Subtype.ext
  change ⁅(z : P), (x : P)⁆ = 1
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  have hzSquare : (z : P) ∈ frattiniSquare P := by
    have hz' : z ∈
        (frattiniSquare P).subgroupOf (frattini P) := by
      rw [frattiniSquare_subgroupOf_frattini_eq_agemo]
      exact hz
    exact hz'
  exact (Subgroup.mem_center_iff.mp
    (frattiniSquare_le_center_of_exponent_four
      hP hxi hPhiComm hfour hzSquare) (x : P)).symm

/-- The raw bihomomorphism kills the degree-zero lower-central denominator
in its ambient slot because that denominator maps to `Phi(P)`, which is
commutative. -/
theorem frattiniSquareCommutatorBihomRaw_ker_right
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z : frattini P)
    {x : lowerCentralTerm P 0}
    (hx : x ∈ lowerCentralLayerKernel P 0) :
    frattiniSquareCommutatorBihomRaw
        hP hxi hPhiComm hfour hexists z x = 1 := by
  apply Subtype.ext
  change ⁅(z : P), (x : P)⁆ = 1
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  have hxAmbient : (x : P) ∈
      lowerCentralLayerKernelInAmbient P 0 :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [lowerCentralLayerKernelInAmbient_zero_eq_frattini P hP] at hxAmbient
  exact congrArg Subtype.val
    (hPhiComm.is_comm.comm z (⟨(x : P), hxAmbient⟩ : frattini P))

/-- Descend the ambient input to the actual outer layer `P / Phi(P)`. -/
noncomputable def frattiniSquareCommutatorBihomRight
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    frattini P →* lowerCentralLayer P 0 →* frattiniSquare P := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  exact {
    toFun := fun z =>
      QuotientGroup.lift
        (lowerCentralLayerKernel P 0)
        (frattiniSquareCommutatorBihomRaw
          hP hxi hPhiComm hfour hexists z)
        (fun x hx => MonoidHom.mem_ker.mpr
          (frattiniSquareCommutatorBihomRaw_ker_right
            hP hxi hPhiComm hfour hexists z hx))
    map_one' := by
      ext q
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.lift_mk', MonoidHom.one_apply, map_one]
    map_mul' := by
      intro z z'
      ext q
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply,
        QuotientGroup.mk'_apply, QuotientGroup.lift_mk', map_mul] }

/-- The fully descended multiplicative bracket
`Phi(P)/Phi(P)^2 -> P/Phi(P) -> Phi(P)^2`. -/
noncomputable def frattiniSquareCommutatorBihom
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    frattiniMiddleLayer P →*
      lowerCentralLayer P 0 →* frattiniSquare P := by
  dsimp only
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  apply QuotientGroup.lift
    (Agemo (frattini P) 2 1)
    (frattiniSquareCommutatorBihomRight
      hP hxi hPhiComm hfour hexists)
  intro z hz
  rw [MonoidHom.mem_ker]
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  change frattiniSquareCommutatorBihomRaw
      hP hxi hPhiComm hfour hexists z x = 1
  exact frattiniSquareCommutatorBihomRaw_ker_left
    hP hxi hPhiComm hfour hexists hz x

@[simp]
theorem frattiniSquareCommutatorBihom_mk
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z : frattini P) (x : lowerCentralTerm P 0) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniSquareCommutatorBihom hP hxi hPhiComm hfour hexists
        (QuotientGroup.mk z)
        (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x) =
      frattiniSquareCommutatorValue
        hP hxi hPhiComm hexists z x := by
  dsimp only
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  change frattiniSquareCommutatorBihomRaw
      hP hxi hPhiComm hfour hexists z x =
    frattiniSquareCommutatorValue hP hxi hPhiComm hexists z x
  rfl

/-- **Higman Lemma 13 (p. 92), the square-valued commutator.**

This is the actual `F₂`-bilinear bracket
`Phi(P)/Phi(P)^2 × P/Phi(P) -> Phi(P)^2`. -/
noncomputable def frattiniSquareCommutatorBilinear
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    Additive (frattiniMiddleLayer P) →ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0) →ₗ[ZMod 2]
        Additive (frattiniSquare P) := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  exact mixedBihomToZModTwoBilinear
    (frattiniSquareCommutatorBihom
      hP hxi hPhiComm hfour hexists)

@[simp]
theorem frattiniSquareCommutatorBilinear_mk
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z : frattini P) (x : lowerCentralTerm P 0) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    frattiniSquareCommutatorBilinear
        hP hxi hPhiComm hfour hexists
        (Additive.ofMul (QuotientGroup.mk z))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x)) =
      Additive.ofMul
        (frattiniSquareCommutatorValue
          hP hxi hPhiComm hexists z x) := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  change Additive.ofMul
      (frattiniSquareCommutatorBihom hP hxi hPhiComm hfour hexists
        (QuotientGroup.mk z)
        (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x)) = _
  rw [frattiniSquareCommutatorBihom_mk]

/-- On representatives, the square-valued bracket vanishes exactly when
the ambient representatives commute. -/
theorem frattiniSquareCommutatorBilinear_mk_eq_zero_iff
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z : frattini P) (x : lowerCentralTerm P 0) :
    let hSquareEA :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hSquareEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    frattiniSquareCommutatorBilinear
        hP hxi hPhiComm hfour hexists
        (Additive.ofMul (QuotientGroup.mk z))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x)) = 0 ↔
      Commute (z : P) (x : P) := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  rw [frattiniSquareCommutatorBilinear_mk]
  change frattiniSquareCommutatorValue
      hP hxi hPhiComm hexists z x = 1 ↔ _
  constructor
  · intro h
    apply commutatorElement_eq_one_iff_mul_comm.mp
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr h

end OddOrder.Higman.Suzuki2Groups
