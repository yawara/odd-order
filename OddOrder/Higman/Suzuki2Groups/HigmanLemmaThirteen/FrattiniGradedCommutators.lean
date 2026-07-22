/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.FrattiniMiddleCoordinates

/-!
# Higman's Lemma 13: commutators in the middle Frattini layer

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The first lower-central commutator has codomain
`gamma_2(P) / (gamma_2(P)^2 gamma_3(P))`, which is not identified with
`Phi(P) / Phi(P)^2`.  In the exponent-four branch its denominator maps into
`Phi(P)^2`, so there is instead a natural linear map from that lower-central
layer to the literal middle Frattini quotient.  Composing this map with the
existing lower-central commutator gives the honest bracket

`P / Phi(P) × P / Phi(P) -> Phi(P) / Phi(P)^2`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped commutatorElement IsMulCommutative

universe uP

local instance instFrattiniGradedLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

noncomputable local instance instFrattiniGradedLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- The ambient Frattini square, pulled back to `Phi(P)`, is definitionally
the first internal Agemo subgroup. -/
theorem frattiniSquare_subgroupOf_frattini_eq_agemo
    {P : Type uP} [Group P] :
    (frattiniSquare P).subgroupOf (frattini P) =
      Agemo (frattini P) 2 1 := by
  apply Subgroup.map_injective (frattini P).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le frattiniSquare_le_frattini]
  rfl

/-- The first lower-central term `gamma_2(P)` lies in `Phi(P)` for a finite
`2`-group. -/
theorem lowerCentralTerm_one_le_frattini_of_isPGroup
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P) :
    lowerCentralTerm P 1 ≤ frattini P := by
  rw [lowerCentralTerm, Subgroup.top_lowerCentralSeries_one]
  exact OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP

/-- In the exponent-four branch, the ambient denominator of the degree-one
lower-central layer lies in `Phi(P)^2`.

Squares from `gamma_2(P)` are squares in `Phi(P)`.  The other summand is
`gamma_3(P)`, which lies in `[Phi(P),P]` and hence in `Phi(P)^2`. -/
theorem lowerCentralLayerKernelInAmbient_one_le_frattiniSquare
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    lowerCentralLayerKernelInAmbient P 1 ≤ frattiniSquare P := by
  have hTermOne : lowerCentralTerm P 1 ≤ frattini P :=
    lowerCentralTerm_one_le_frattini_of_isPGroup hP
  have hPhiCommLe : ⁅frattini P, (⊤ : Subgroup P)⁆ ≤
      frattiniSquare P :=
    commutator_frattini_top_le_frattiniSquare_of_exponent_four
      hP hxi hPhiComm hexists
  have hTermTwo : lowerCentralTerm P 2 ≤ frattiniSquare P := by
    rw [lowerCentralTerm, Subgroup.lowerCentralSeries_succ,
      Subgroup.top_lowerCentralSeries_one]
    exact (Subgroup.commutator_mono hTermOne le_rfl).trans hPhiCommLe
  rw [lowerCentralLayerKernelInAmbient_eq]
  apply sup_le
  · rw [Subgroup.map_le_iff_le_comap, Agemo, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    let xPhi : frattini P := ⟨(x : P), hTermOne x.property⟩
    change (xPhi : P) ^ 2 ∈ frattiniSquare P
    apply Subgroup.mem_map.mpr
    refine ⟨xPhi ^ 2, ?_, rfl⟩
    simpa using
      (Agemo.mem_of_eq_pow (G := frattini P) (p := 2) (n := 1) xPhi)
  · simpa only [Nat.reduceAdd] using hTermTwo

/-- Inclusion of `gamma_2(P)` into the ambient Frattini subgroup. -/
def lowerCentralTermOneInFrattini
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P) :
    lowerCentralTerm P 1 →* frattini P :=
  Subgroup.inclusion (lowerCentralTerm_one_le_frattini_of_isPGroup hP)

@[simp]
theorem lowerCentralTermOneInFrattini_apply_val
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (x : lowerCentralTerm P 1) :
    ((lowerCentralTermOneInFrattini hP x : frattini P) : P) = (x : P) :=
  rfl

/-- The natural group homomorphism from the degree-one lower-central layer
to the literal middle Frattini quotient. -/
def lowerCentralLayerOneToFrattiniMiddle
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    lowerCentralLayer P 1 →* frattiniMiddleLayer P := by
  apply QuotientGroup.map
    (lowerCentralLayerKernel P 1) (Agemo (frattini P) 2 1)
      (lowerCentralTermOneInFrattini hP)
  intro x hx
  rw [← frattiniSquare_subgroupOf_frattini_eq_agemo]
  change (x : P) ∈ frattiniSquare P
  apply lowerCentralLayerKernelInAmbient_one_le_frattiniSquare
    hP hxi hPhiComm hexists
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

@[simp]
theorem lowerCentralLayerOneToFrattiniMiddle_mk
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x : lowerCentralTerm P 1) :
    lowerCentralLayerOneToFrattiniMiddle
        hP hxi hPhiComm hexists
        (QuotientGroup.mk' (lowerCentralLayerKernel P 1) x) =
      QuotientGroup.mk' (Agemo (frattini P) 2 1)
        (lowerCentralTermOneInFrattini hP x) :=
  rfl

/-- Linear form of the natural map from the degree-one lower-central layer
to `Phi(P) / Phi(P)^2`. -/
noncomputable def lowerCentralLayerOneToFrattiniMiddleLinear
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    Additive (lowerCentralLayer P 1) →ₗ[ZMod 2]
      Additive (frattiniMiddleLayer P) := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  exact {
    (lowerCentralLayerOneToFrattiniMiddle
      hP hxi hPhiComm hexists).toAdditive with
    map_smul' := ZMod.map_smul
      (lowerCentralLayerOneToFrattiniMiddle
        hP hxi hPhiComm hexists).toAdditive }

/-- **Higman Lemma 13 (p. 92), the middle Frattini commutator.**

This is the actual lower-central commutator followed by the natural map to
`Phi(P) / Phi(P)^2`; no equality between the two quotient carriers is
assumed. -/
noncomputable def frattiniMiddleCommutatorBilinear
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    Additive (lowerCentralLayer P 0) →ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0) →ₗ[ZMod 2]
        Additive (frattiniMiddleLayer P) := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  exact (lowerCentralCommutatorBilinear P).compr₂
    (lowerCentralLayerOneToFrattiniMiddleLinear
      hP hxi hPhiComm hexists)

@[simp]
theorem frattiniMiddleCommutatorBilinear_mk
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x y : lowerCentralTerm P 0) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinear hP hxi hPhiComm hexists
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y)) =
      Additive.ofMul
        (QuotientGroup.mk' (Agemo (frattini P) 2 1)
          (lowerCentralTermOneInFrattini hP
            (lowerCentralCommutator P x y))) := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  change lowerCentralLayerOneToFrattiniMiddleLinear
      hP hxi hPhiComm hexists
      (lowerCentralCommutatorBilinear P
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y))) = _
  rw [lowerCentralCommutatorBilinear_mk]
  rfl

/-- On representatives, the middle bracket vanishes exactly when the raw
commutator lies in the ambient subgroup `Phi(P)^2`. -/
theorem frattiniMiddleCommutatorBilinear_mk_eq_zero_iff
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (x y : lowerCentralTerm P 0) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinear hP hxi hPhiComm hexists
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y)) = 0 ↔
      ⁅(x : P), (y : P)⁆ ∈ frattiniSquare P := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  rw [frattiniMiddleCommutatorBilinear_mk]
  change QuotientGroup.mk' (Agemo (frattini P) 2 1)
      (lowerCentralTermOneInFrattini hP
        (lowerCentralCommutator P x y)) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    ← frattiniSquare_subgroupOf_frattini_eq_agemo]
  rfl

/-- Commutators of two classes represented in one restricted length-three
factor vanish in the common middle Frattini layer. -/
theorem frattiniMiddleCommutatorBilinear_eq_zero_of_mem_restricted_factor
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
    (x y : lowerCentralTerm P 0)
    (hx : (x : P) ∈ S) (hy : (y : P) ∈ S) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCommutatorBilinear hP hxi hPhiComm hexists
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y)) = 0 := by
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  apply (frattiniMiddleCommutatorBilinear_mk_eq_zero_iff
    hP hxi hPhiComm hexists x y).2
  exact commutatorElement_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four
    hP hmulti hxi hprime hPhiComm hexists
      hSinv hPhiS hlenS hncommS hx hy

end OddOrder.Higman.Suzuki2Groups
