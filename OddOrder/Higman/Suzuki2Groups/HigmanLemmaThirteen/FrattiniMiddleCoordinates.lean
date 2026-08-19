/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.RestrictedFactorNormalForms

/-!
# Higman's Lemma 13: common coordinates on the middle Frattini layer

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

In the exponent-four branch the two restricted length-three factors share
the ambient middle layer `Phi(P) / Phi(P)^2`.  This file constructs that
literal quotient and identifies it canonically with `Phi(P)^2` by squaring.
The construction is independent of either restricted factor: its kernel
calculation uses transitivity on involutions and the nontriviality of the
ambient Frattini square.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- Higman's middle Frattini layer `Phi(P) / Phi(P)^2`, with the square
subgroup represented internally inside `Phi(P)`. -/
abbrev frattiniMiddleLayer (P : Type uP) [Group P] :=
  frattini P ⧸ Agemo (frattini P) 2 1

/-- Squaring from `Phi(P)` into the actual ambient subgroup `Phi(P)^2`.

The codomain membership is literal: a square in `Phi(P)` belongs to its
first Agemo subgroup and is then mapped along the ambient subtype. -/
def frattiniSquarePowerHom
    {P : Type uP} [Group P]
    (hPhiComm : IsMulCommutative (frattini P)) :
    frattini P →* frattiniSquare P where
  toFun z := ⟨(z : P) ^ 2, by
    change (z : P) ^ 2 ∈
      (Agemo (frattini P) 2 1).map (frattini P).subtype
    refine ⟨z ^ 2, ?_, rfl⟩
    simpa using
      (Agemo.mem_of_eq_pow (G := frattini P) (p := 2) (n := 1) z)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' z w := by
    apply Subtype.ext
    have hcomm : Commute z w := hPhiComm.is_comm.comm z w
    have hcommP : Commute (z : P) (w : P) :=
      congrArg Subtype.val hcomm
    change ((z : P) * (w : P)) ^ 2 =
      (z : P) ^ 2 * (w : P) ^ 2
    exact hcommP.mul_pow 2

@[simp]
theorem frattiniSquarePowerHom_apply_val
    {P : Type uP} [Group P]
    (hPhiComm : IsMulCommutative (frattini P))
    (z : frattini P) :
    ((frattiniSquarePowerHom hPhiComm z : frattiniSquare P) : P) =
      (z : P) ^ 2 :=
  rfl

/-- Every ambient involution lies in the nontrivial invariant subgroup
`Phi(P)^2`.  This is the branch fact used to identify the kernel of the
middle-layer square map. -/
theorem involutions_subset_frattiniSquare_of_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    involutions P ⊆ frattiniSquare P := by
  exact involutions_subset_of_nontrivial_invariant
    hP Y hxi.transitive
      ((frattiniSquareNormalInvariant Y.subtype).2.2)
      (frattiniSquare_ne_bot_of_exists_pow_two_ne_one hexists)

/-- The kernel of squaring `Phi(P) → Phi(P)^2` is exactly the internal
square subgroup of `Phi(P)`.

For the forward inclusion, an element with square one is either the identity
or an ambient involution, hence lies in the nontrivial invariant subgroup
`Phi(P)^2`.  For the reverse inclusion, write an Agemo element as a square
and use the exponent-four hypothesis. -/
theorem frattiniSquarePowerHom_ker_eq_agemo
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    (frattiniSquarePowerHom hPhiComm).ker =
      Agemo (frattini P) 2 1 := by
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  ext z
  constructor
  · intro hz
    rw [MonoidHom.mem_ker] at hz
    have hzTwo : (z : P) ^ 2 = 1 := by
      simpa using congrArg Subtype.val hz
    by_cases hzOne : (z : P) = 1
    · have hzSub : z = 1 := Subtype.ext hzOne
      rw [hzSub]
      exact Subgroup.one_mem _
    · have hzSquare : (z : P) ∈ frattiniSquare P :=
        involutions_subset_frattiniSquare_of_exponent_four
          hP hxi hexists ⟨hzTwo, hzOne⟩
      change (z : P) ∈
        (Agemo (frattini P) 2 1).map (frattini P).subtype at hzSquare
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzSquare
      have hwEq : w = z := Subtype.ext hwz
      simpa [hwEq] using hw
  · intro hz
    obtain ⟨y, hy⟩ := mem_agemo_iff_of_comm.mp hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hzVal : (z : P) = (y : P) ^ 2 := by
      simpa using congrArg Subtype.val hy
    have hyFour : (y : P) ^ 4 = 1 := by
      simpa using congrArg Subtype.val (hfour y)
    change (z : P) ^ 2 = 1
    rw [hzVal]
    calc
      ((y : P) ^ 2) ^ 2 = (y : P) ^ 4 := by group
      _ = 1 := hyFour

/-- Squaring onto the ambient Frattini square is surjective.  In a
commutative group every element of the first Agemo subgroup is an actual
square, rather than merely a product of square generators. -/
theorem frattiniSquarePowerHom_surjective
    {P : Type uP} [Group P]
    (hPhiComm : IsMulCommutative (frattini P)) :
    Function.Surjective (frattiniSquarePowerHom hPhiComm) := by
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro x
  have hx : (x : P) ∈
      (Agemo (frattini P) 2 1).map (frattini P).subtype := x.property
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y, hy⟩ := mem_agemo_iff_of_comm.mp hz
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have hzVal : (z : P) = (y : P) ^ 2 := by
    simpa using congrArg Subtype.val hy
  exact hzVal.symm.trans hzx

/-- **Higman Lemma 13 (p. 92), canonical middle-layer square
equivalence.**

Squaring identifies the actual quotient `Phi(P) / Phi(P)^2` with the common
ambient subgroup `Phi(P)^2`. -/
noncomputable def frattiniMiddleSquareEquiv
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    frattiniMiddleLayer P ≃* frattiniSquare P :=
  (QuotientGroup.quotientMulEquivOfEq
      (frattiniSquarePowerHom_ker_eq_agemo
        hP hxi hPhiComm hfour hexists).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (frattiniSquarePowerHom hPhiComm)
      (frattiniSquarePowerHom_surjective hPhiComm))

@[simp]
theorem frattiniMiddleSquareEquiv_mk
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    (z : frattini P) :
    frattiniMiddleSquareEquiv hP hxi hPhiComm hfour hexists
        (QuotientGroup.mk z) =
      frattiniSquarePowerHom hPhiComm z :=
  rfl

/-- Linear form of the canonical square equivalence. -/
noncomputable def frattiniMiddleSquareLinearEquiv
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
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hSquareEA.zmodModule
    Additive (frattiniMiddleLayer P) ≃ₗ[ZMod 2]
      Additive (frattiniSquare P) := by
  dsimp only
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : CommGroup (frattiniSquare P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  exact (MulEquiv.toAdditive
      (frattiniMiddleSquareEquiv
        hP hxi hPhiComm hfour hexists)).toLinearEquiv
    (fun c x => ZMod.map_smul
      (MulEquiv.toAdditive
        (frattiniMiddleSquareEquiv
          hP hxi hPhiComm hfour hexists)).toAddMonoidHom c x)

/-- **Higman Lemma 13 (p. 92), common middle coordinate.**

The canonical square equivalence, followed by the already chosen common
coordinate on `Phi(P)^2` and inverse Frobenius, gives one coordinate on
`Phi(P) / Phi(P)^2` before either restricted factor is chosen. -/
noncomputable def frattiniMiddleCoordinate
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n : Nat}
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    Additive (frattiniMiddleLayer P) ≃ₗ[ZMod 2]
      GaloisField 2 n := by
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  letI : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  letI : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  letI : CommGroup (frattiniSquare P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  let frobeniusInv : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n :=
    { (frobeniusEquiv (GaloisField 2 n) 2).symm.toAddEquiv with
      map_smul' := fun c x => ZMod.map_smul
        (frobeniusEquiv (GaloisField 2 n) 2).symm.toAddEquiv.toAddMonoidHom
          c x }
  exact ((frattiniMiddleSquareLinearEquiv
      hP hxi hPhiComm hfour hexists).trans eSquare).trans frobeniusInv

@[simp]
theorem frattiniMiddleCoordinate_mk
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n : Nat}
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (z : frattini P) :
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
        (Additive.ofMul (QuotientGroup.mk z)) =
      (frobeniusEquiv (GaloisField 2 n) 2).symm
        (eSquare (Additive.ofMul
          (frattiniSquarePowerHom hPhiComm z))) :=
  rfl

/-- The canonical middle-layer square equivalence intertwines the quotient
action on `Phi(P) / Phi(P)^2` with the ambient action on `Phi(P)^2`. -/
theorem frattiniMiddleSquareEquiv_equivariant
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
      (frattiniSquareNormalInvariant Y.subtype).2.2
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ (c : Y) (q : frattiniMiddleLayer P),
      frattiniMiddleSquareEquiv hP hxi hPhiComm hfour hexists
          (actualAgemoOneQuotientAction hPhiInv.restrict c q) =
        hSquareInv.restrict c
          (frattiniMiddleSquareEquiv
            hP hxi hPhiComm hfour hexists q) := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  intro c q
  refine QuotientGroup.induction_on q ?_
  intro z
  change frattiniMiddleSquareEquiv hP hxi hPhiComm hfour hexists
      (QuotientGroup.mk (hPhiInv.restrict c z)) =
    hSquareInv.restrict c
      (frattiniMiddleSquareEquiv hP hxi hPhiComm hfour hexists
        (QuotientGroup.mk z))
  rw [frattiniMiddleSquareEquiv_mk, frattiniMiddleSquareEquiv_mk]
  apply Subtype.ext
  change ((c : MulAut P) (z : P)) ^ 2 =
    (c : MulAut P) ((z : P) ^ 2)
  exact (map_pow (c : MulAut P) (z : P) 2).symm

/-- In the common middle coordinate, the chosen Singer generator acts by
`Frob⁻¹(nu)`.  Thus the middle scalar is the canonical square root of the
scalar `nu` on `Phi(P)^2`, independently of either restricted factor. -/
theorem frattiniMiddleCoordinate_generator_compatible
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {n : Nat} (c : Y)
    (eSquare :
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n)
    (hconj :
      let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
        (frattiniSquareNormalInvariant Y.subtype).2.2
      let hSquareEA :=
        frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
      letI : IsMulCommutative (frattiniSquare P) :=
        IsMulCommutative.of_comm hSquareEA.comm
      letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
        hSquareEA.zmodModule
      eSquare.conj (elabRepresentation 2 hSquareInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    letI : CommGroup (frattini P) :=
      { (inferInstance : Group (frattini P)) with
        mul_comm := hPhiComm.is_comm.comm }
    ∀ q : Additive (frattiniMiddleLayer P),
      frattiniMiddleCoordinate hP hxi hPhiComm hfour hexists eSquare
          (actualAgemoOneQuotientRepresentation hPhiInv.restrict c q) =
        (frobeniusEquiv (GaloisField 2 n) 2).symm nu *
          frattiniMiddleCoordinate
            hP hxi hPhiComm hfour hexists eSquare q := by
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  let hSquareEA :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : CommGroup (frattini P) :=
    { (inferInstance : Group (frattini P)) with
      mul_comm := hPhiComm.is_comm.comm }
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hSquareEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hSquareEA.zmodModule
  intro q
  change (frobeniusEquiv (GaloisField 2 n) 2).symm
      (eSquare (Additive.ofMul
        (frattiniMiddleSquareEquiv hP hxi hPhiComm hfour hexists
          (actualAgemoOneQuotientAction hPhiInv.restrict c q.toMul)))) =
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu *
      (frobeniusEquiv (GaloisField 2 n) 2).symm
        (eSquare (Additive.ofMul
          (frattiniMiddleSquareEquiv hP hxi hPhiComm hfour hexists q.toMul)))
  rw [frattiniMiddleSquareEquiv_equivariant
    hP hxi hPhiComm hfour hexists c q.toMul]
  have hcompat :
      eSquare (Additive.ofMul
        (hSquareInv.restrict c
          (frattiniMiddleSquareEquiv
            hP hxi hPhiComm hfour hexists q.toMul))) =
        nu * eSquare (Additive.ofMul
          (frattiniMiddleSquareEquiv
            hP hxi hPhiComm hfour hexists q.toMul)) := by
    have h := DFunLike.congr_fun hconj
      (eSquare (Additive.ofMul
        (frattiniMiddleSquareEquiv
          hP hxi hPhiComm hfour hexists q.toMul)))
    simpa [LinearEquiv.conj_apply, elabRepresentation_apply] using h
  rw [hcompat]
  exact map_mul (frobeniusEquiv (GaloisField 2 n) 2).symm nu
    (eSquare (Additive.ofMul
      (frattiniMiddleSquareEquiv
        hP hxi hPhiComm hfour hexists q.toMul)))

end OddOrder.Higman.Suzuki2Groups
