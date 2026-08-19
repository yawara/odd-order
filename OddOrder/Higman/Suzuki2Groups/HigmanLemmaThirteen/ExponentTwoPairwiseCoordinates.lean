/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoPairwiseFrattini

/-!
# Higman's Lemma 13: common Frattini coordinates in the exponent-two branch

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

When `Φ(P)` has exponent two, it is elementary abelian.  Actor transitivity
then supplies one common Singer coordinate on the actual ambient subgroup
`Φ(P)`.  For each pairwise join, its intrinsic Frattini subgroup maps onto
this same ambient subgroup.  This file turns that equality into an explicit
equivariant `ZMod 2`-linear equivalence.

Choosing the ambient coordinate before restricting to any pair is essential:
the three pairwise applications of Higman's Lemma 12 must compare the
parameters of the same length-two factors in one coordinate system.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative TensorProduct

universe uP

/-- The ambient Frattini subgroup is elementary abelian when it has exponent two. -/
theorem frattini_isElementaryAbelian_of_exponent_two
    {P : Type uP} [Group P]
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    IsElementaryAbelian 2 (frattini P) := by
  refine ⟨?_, htwo⟩
  intro x y
  exact (Commute.of_orderOf_dvd_two
    (fun z => by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact htwo z)
    x y).eq

/-- **Higman Lemma 13 (p. 93), common ambient Singer coordinate.**

The actor admits one finite-field coordinate on the actual ambient Frattini
subgroup.  The returned generator acts as multiplication by the primitive
scalar `nu`; `b` is the corresponding Frobenius eigenbasis after scalar
extension.  The coordinate is chosen before any pairwise join. -/
theorem exists_ambientFrattiniSingerCoordinates_of_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hEA : IsElementaryAbelian 2 (frattini P) :=
      frattini_isElementaryAbelian_of_exponent_two htwo
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hEA.zmodModule
    let n := Module.finrank (ZMod 2) (Additive (frattini P))
    ∃ (c : Y)
      (e : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n)
      (b : Basis (Fin n) (GaloisField 2 n)
        (TensorProduct (ZMod 2) (GaloisField 2 n)
          (Additive (frattini P)))),
      2 ≤ n ∧
      (∀ g : Y, g ∈ Subgroup.zpowers c) ∧
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      e.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu ∧
      Algebra.adjoin (ZMod 2) ({nu} : Set (GaloisField 2 n)) = ⊤ ∧
      ∀ i, (elabRepresentation 2 hPhiInv.restrict c).baseChange
          (GaloisField 2 n) (b i) =
        nu ^ (2 ^ i.val) • b i := by
  classical
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  have hEA : IsElementaryAbelian 2 (frattini P) :=
    frattini_isElementaryAbelian_of_exponent_two htwo
  let : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  let : CommGroup (frattini P) := inferInstance
  let : Module (ZMod 2) (Additive (frattini P)) :=
    hEA.zmodModule
  let n := Module.finrank (ZMod 2) (Additive (frattini P))
  let rho : Representation (ZMod 2) Y (Additive (frattini P)) :=
    elabRepresentation 2 hPhiInv.restrict
  have htransInv : ∀ x ∈ involutions (frattini P),
      ∀ y ∈ involutions (frattini P),
        ∃ g : Y, hPhiInv.restrict g x = y :=
    restricted_involutions_transitive Y.subtype hPhiInv hxi.transitive
  have htrans : ∀ v w : Additive (frattini P),
      v ≠ 0 → w ≠ 0 → ∃ g : Y, rho g v = w := by
    intro v w hv hw
    have hvInv : v.toMul ∈ involutions (frattini P) := by
      refine ⟨hEA.pow_eq_one v.toMul, ?_⟩
      intro hvOne
      apply hv
      apply Additive.toMul.injective
      simpa using hvOne
    have hwInv : w.toMul ∈ involutions (frattini P) := by
      refine ⟨hEA.pow_eq_one w.toMul, ?_⟩
      intro hwOne
      apply hw
      apply Additive.toMul.injective
      simpa using hwOne
    obtain ⟨g, hg⟩ := htransInv v.toMul hvInv w.toMul hwInv
    refine ⟨g, ?_⟩
    change Additive.ofMul (hPhiInv.restrict g v.toMul) = w
    simpa using congrArg Additive.ofMul hg
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hbot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hbot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hPhiInv hPhiNeBot
  obtain ⟨x, y, hxInv, hyInv, hxy⟩ := hmulti
  let xPhi : frattini P := ⟨x, hinvPhi hxInv⟩
  let yPhi : frattini P := ⟨y, hinvPhi hyInv⟩
  have hxPhiOne : xPhi ≠ 1 := by
    intro hx
    exact hxInv.2 (congrArg Subtype.val hx)
  have hyPhiOne : yPhi ≠ 1 := by
    intro hy
    exact hyInv.2 (congrArg Subtype.val hy)
  have hxyPhi : xPhi ≠ yPhi := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hOneNot : 1 ∉ ({xPhi, yPhi} : Set (frattini P)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxPhiOne.symm, hyPhiOne.symm⟩
  have hxNot : xPhi ∉ ({yPhi} : Set (frattini P)) := by
    simpa only [Set.mem_singleton_iff] using hxyPhi
  have hsetCard :
      ({1, xPhi, yPhi} : Set (frattini P)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hOneNot,
      Set.ncard_insert_of_notMem hxNot]
    simp
  have hthree : 3 ≤ Nat.card (frattini P) := by
    have hle := Set.ncard_mono
      (Set.subset_univ ({1, xPhi, yPhi} : Set (frattini P)))
    rw [hsetCard, Set.ncard_univ] at hle
    exact hle
  have hcard : Nat.card (frattini P) = 2 ^ n := by
    simpa [n] using hEA.card_eq_pow_finrank
  have hnTwo : 2 ≤ n := by
    by_contra hn
    have hnle : n ≤ 1 := by omega
    interval_cases n <;>
      norm_num only [pow_zero, pow_one] at hcard <;> omega
  let : IsCyclic Y := hxi.cyclic
  let : CommGroup Y := IsCyclic.commGroup
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := Y)
  obtain ⟨e, nu, b, hprim, hconj, hgen, hb⟩ :=
    exists_singerFrobeniusEigenbasis_of_transitive_generator
      rho n hnTwo rfl htrans c hcgen
  exact ⟨c, e, nu, b, hnTwo, hcgen, hprim, hconj, hgen, hb⟩

/-- The intrinsic Frattini subgroup of a pairwise join maps onto the
ambient Frattini subgroup. -/
theorem frattini_sup_map_subtype_eq_ambientFrattini
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {R S : Subgroup P}
    (hRinv : IsAInvariant Y.subtype R)
    (hPhiR : frattini P < R)
    (dataR : XiLengthTwoTypeAData.{uP, 0} R) :
    (frattini ↥(R ⊔ S)).map (R ⊔ S).subtype =
      frattini P := by
  have hPhiJoin : frattini P ≤ R ⊔ S :=
    hPhiR.le.trans le_sup_left
  rw [frattini_sup_eq_ambientFrattini_subgroupOf
    hP hxi htwo hRinv hPhiR dataR,
    Subgroup.map_subgroupOf_eq_of_le hPhiJoin]

/-- Group identification of the intrinsic Frattini subgroup of a pairwise
join with the ambient Frattini subgroup. -/
noncomputable def pairwiseJoinFrattiniEquivAmbientFrattini
    {P : Type uP} [Group P]
    {J : Subgroup P}
    (hMap : (frattini J).map J.subtype = frattini P) :
    frattini J ≃* frattini P :=
  (Subgroup.equivMapOfInjective
      (frattini J) J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hMap)

/-- The join-to-ambient Frattini equivalence is the ambient subtype
embedding on underlying elements. -/
@[simp]
theorem pairwiseJoinFrattiniEquivAmbientFrattini_apply_val
    {P : Type uP} [Group P]
    {J : Subgroup P}
    (hMap : (frattini J).map J.subtype = frattini P)
    (x : frattini J) :
    ((pairwiseJoinFrattiniEquivAmbientFrattini hMap x :
        frattini P) : P) = (x : J) := by
  simp [pairwiseJoinFrattiniEquivAmbientFrattini,
    Subgroup.coe_equivMapOfInjective_apply,
    MulEquiv.subgroupCongr_apply]

/-- Linear form of the pairwise join's Frattini identification, using the
elementary-abelian structure transported from the ambient subgroup. -/
noncomputable def pairwiseJoinFrattiniLinearEquivAmbientFrattini
    {P : Type uP} [Group P]
    {J : Subgroup P}
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    (hMap : (frattini J).map J.subtype = frattini P) :
    let hJoinEA : IsElementaryAbelian 2 (frattini J) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm
        hPhiEA
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
      hJoinEA.zmodModule
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    Additive (frattini J) ≃ₗ[ZMod 2]
      Additive (frattini P) := by
  let hJoinEA : IsElementaryAbelian 2 (frattini J) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm
      hPhiEA
  letI : IsMulCommutative (frattini J) :=
    IsMulCommutative.of_comm hJoinEA.comm
  letI : CommGroup (frattini J) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini J)) :=
    hJoinEA.zmodModule
  letI : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  letI : CommGroup (frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  exact (MulEquiv.toAdditive
      (pairwiseJoinFrattiniEquivAmbientFrattini hMap)).toLinearEquiv
    (fun c x => ZMod.map_smul
      (MulEquiv.toAdditive
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap)).toAddMonoidHom
          c x)

/-- The join-to-ambient Frattini linear equivalence intertwines the
restricted join action with the ambient action on `Φ(P)`. -/
theorem pairwiseJoinFrattiniLinearEquivAmbientFrattini_equivariant
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {J : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    (hMap : (frattini J).map J.subtype = frattini P) :
    let hJoinPhiInv : IsAInvariant hJinv.restrict (frattini J) :=
      IsAInvariant.of_characteristic hJinv.restrict
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hJoinEA : IsElementaryAbelian 2 (frattini J) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm
        hPhiEA
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
      hJoinEA.zmodModule
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    ∀ (g : Y) (v : Additive (frattini J)),
      pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap
          (elabRepresentation 2 hJoinPhiInv.restrict g v) =
        elabRepresentation 2 hPhiInv.restrict g
          (pairwiseJoinFrattiniLinearEquivAmbientFrattini
            hPhiEA hMap v) := by
  dsimp only
  let hJoinPhiInv : IsAInvariant hJinv.restrict (frattini J) :=
    IsAInvariant.of_characteristic hJinv.restrict
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hJoinEA : IsElementaryAbelian 2 (frattini J) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm
      hPhiEA
  let : IsMulCommutative (frattini J) :=
    IsMulCommutative.of_comm hJoinEA.comm
  let : CommGroup (frattini J) := inferInstance
  let : Module (ZMod 2) (Additive (frattini J)) :=
    hJoinEA.zmodModule
  let : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  let : CommGroup (frattini P) := inferInstance
  let : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  intro g v
  change pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA hMap
        (elabRepresentation 2 hJoinPhiInv.restrict g
          (Additive.ofMul v.toMul)) =
      elabRepresentation 2 hPhiInv.restrict g
        (pairwiseJoinFrattiniLinearEquivAmbientFrattini
          hPhiEA hMap (Additive.ofMul v.toMul))
  rw [elabRepresentation_apply]
  change Additive.ofMul
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap
          (hJoinPhiInv.restrict g v.toMul)) =
      elabRepresentation 2 hPhiInv.restrict g
        (Additive.ofMul
          (pairwiseJoinFrattiniEquivAmbientFrattini hMap v.toMul))
  rw [elabRepresentation_apply]
  have hmul :
      pairwiseJoinFrattiniEquivAmbientFrattini hMap
          (hJoinPhiInv.restrict g v.toMul) =
        hPhiInv.restrict g
          (pairwiseJoinFrattiniEquivAmbientFrattini hMap v.toMul) := by
    apply Subtype.ext
    rw [pairwiseJoinFrattiniEquivAmbientFrattini_apply_val,
      IsAInvariant.restrict_apply_val hPhiInv,
      pairwiseJoinFrattiniEquivAmbientFrattini_apply_val,
      IsAInvariant.restrict_apply_val hJoinPhiInv,
      IsAInvariant.restrict_apply_val hJinv]
  exact congrArg Additive.ofMul hmul

/-- Transporting the common ambient Singer coordinate through a pairwise
join's Frattini equivalence preserves its scalar normal form. -/
theorem pairwiseJoinFrattiniSingerCoordinate_conj
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {J : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hPhiEA : IsElementaryAbelian 2 (frattini P))
    (hMap : (frattini J).map J.subtype = frattini P)
    {n : Nat}
    (c : Y)
    (ePhi :
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n)
    (hconj :
      let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
        IsAInvariant.of_characteristic Y.subtype
      letI : IsMulCommutative (frattini P) :=
        IsMulCommutative.of_comm hPhiEA.comm
      letI : Module (ZMod 2) (Additive (frattini P)) :=
        hPhiEA.zmodModule
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu) :
    let hJoinPhiInv :
        IsAInvariant hJinv.restrict.range.subtype (frattini J) :=
      IsAInvariant.of_characteristic hJinv.restrict.range.subtype
    let hJoinEA : IsElementaryAbelian 2 (frattini J) :=
      IsElementaryAbelian.of_mulEquiv
        (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm
        hPhiEA
    letI : IsMulCommutative (frattini J) :=
      IsMulCommutative.of_comm hJoinEA.comm
    letI : Module (ZMod 2) (Additive (frattini J)) :=
      hJoinEA.zmodModule
    letI : IsMulCommutative (frattini P) :=
      IsMulCommutative.of_comm hPhiEA.comm
    letI : Module (ZMod 2) (Additive (frattini P)) :=
      hPhiEA.zmodModule
    let cJ : hJinv.restrict.range := hJinv.restrict.rangeRestrict c
    let eJoin :=
      (pairwiseJoinFrattiniLinearEquivAmbientFrattini
        hPhiEA hMap).trans ePhi
    eJoin.conj
        (elabRepresentation 2 hJoinPhiInv.restrict cJ) =
      Algebra.lmul (ZMod 2) (GaloisField 2 n) nu := by
  classical
  dsimp only
  let hJoinPhiInvY : IsAInvariant hJinv.restrict (frattini J) :=
    IsAInvariant.of_characteristic hJinv.restrict
  let hJoinPhiInv :
      IsAInvariant hJinv.restrict.range.subtype (frattini J) :=
    IsAInvariant.of_characteristic hJinv.restrict.range.subtype
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let hJoinEA : IsElementaryAbelian 2 (frattini J) :=
    IsElementaryAbelian.of_mulEquiv
      (pairwiseJoinFrattiniEquivAmbientFrattini hMap).symm
      hPhiEA
  let : IsMulCommutative (frattini J) :=
    IsMulCommutative.of_comm hJoinEA.comm
  let : CommGroup (frattini J) := inferInstance
  let : Module (ZMod 2) (Additive (frattini J)) :=
    hJoinEA.zmodModule
  let : IsMulCommutative (frattini P) :=
    IsMulCommutative.of_comm hPhiEA.comm
  let : CommGroup (frattini P) := inferInstance
  let : Module (ZMod 2) (Additive (frattini P)) :=
    hPhiEA.zmodModule
  let E := pairwiseJoinFrattiniLinearEquivAmbientFrattini
    hPhiEA hMap
  let cJ : hJinv.restrict.range := hJinv.restrict.rangeRestrict c
  let eJoin := E.trans ePhi
  have hPhiCompat : ∀ w,
      ePhi (elabRepresentation 2 hPhiInv.restrict c w) =
        nu * ePhi w := by
    intro w
    have h := DFunLike.congr_fun hconj (ePhi w)
    simpa [LinearEquiv.conj_apply] using h
  have hJoinCompat : ∀ v,
      eJoin (elabRepresentation 2 hJoinPhiInv.restrict cJ v) =
        nu * eJoin v := by
    intro v
    have hRangeAction :
        elabRepresentation 2 hJoinPhiInv.restrict cJ v =
          elabRepresentation 2 hJoinPhiInvY.restrict c v := by
      apply Additive.toMul.injective
      change hJoinPhiInv.restrict cJ v.toMul =
        hJoinPhiInvY.restrict c v.toMul
      apply Subtype.ext
      simp [cJ, IsAInvariant.restrict_apply_val]
    change ePhi
        (E (elabRepresentation 2 hJoinPhiInv.restrict cJ v)) =
      nu * ePhi (E v)
    rw [hRangeAction, show E
        (elabRepresentation 2 hJoinPhiInvY.restrict c v) =
        elabRepresentation 2 hPhiInv.restrict c (E v) by
      simpa [E] using
        pairwiseJoinFrattiniLinearEquivAmbientFrattini_equivariant
          hJinv hPhiEA hMap c v]
    exact hPhiCompat _
  apply LinearMap.ext
  intro beta
  change eJoin
      (elabRepresentation 2 hJoinPhiInv.restrict cJ
        (eJoin.symm beta)) = nu * beta
  rw [hJoinCompat]
  simp
end

end OddOrder.Higman.Suzuki2Groups
