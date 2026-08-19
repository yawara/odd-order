/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentFourJacobi
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.AmbientCentralExtension

/-!
# Higman's Lemma 13: common coordinates on the Frattini square

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

In the exponent-four branch, the two restricted length-three factors share
the same internal Frattini image `Φ(P)²`.  Before choosing coordinates on
either factor, this file chooses one Singer generator and one finite-field
coordinate for the actual ambient actor action on that common subgroup.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open Module
open scoped IsMulCommutative TensorProduct

universe uP

/-- In the exponent-four branch, `Φ(P)²` is elementary abelian of exponent
two.  Commutativity is inherited from `Φ(P)`, while the exponent statement
is the square-of-a-square calculation. -/
theorem frattiniSquare_isElementaryAbelian_of_exponent_four
    {P : Type uP} [Group P]
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1) :
    IsElementaryAbelian 2 (frattiniSquare P) := by
  constructor
  · intro x y
    apply Subtype.ext
    let xPhi : frattini P :=
      ⟨x, frattiniSquare_le_frattini x.property⟩
    let yPhi : frattini P :=
      ⟨y, frattiniSquare_le_frattini y.property⟩
    simpa [xPhi, yPhi] using
      congrArg Subtype.val (hPhiComm.is_comm.comm xPhi yPhi)
  · intro x
    apply Subtype.ext
    exact pow_two_eq_one_of_mem_frattiniSquare
      hPhiComm hfour x.property

/-- **Higman Lemma 13 (p. 92), common `Φ(P)²` Singer coordinates.**

The ambient actor admits one common finite-field coordinate on `Φ(P)²`,
chosen before coordinates on either restricted length-three factor.  The
returned generator acts as multiplication by the primitive scalar `nu`,
and `b` is the corresponding Frobenius eigenbasis after scalar extension.
The dimension is at least two because all ambient involutions lie in the
nontrivial invariant subgroup `Φ(P)²`. -/
theorem exists_frattiniSquareSingerCoordinates_of_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
      (frattiniSquareNormalInvariant Y.subtype).2.2
    let hEA : IsElementaryAbelian 2 (frattiniSquare P) :=
      frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
    letI : IsMulCommutative (frattiniSquare P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive (frattiniSquare P)) :=
      hEA.zmodModule
    let n := Module.finrank (ZMod 2) (Additive (frattiniSquare P))
    ∃ (c : Y)
      (e : Additive (frattiniSquare P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n)
      (b : Basis (Fin n) (GaloisField 2 n)
        (TensorProduct (ZMod 2) (GaloisField 2 n)
          (Additive (frattiniSquare P)))),
      2 ≤ n ∧
      (∀ g : Y, g ∈ Subgroup.zpowers c) ∧
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      e.conj (elabRepresentation 2 hSquareInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu ∧
      Algebra.adjoin (ZMod 2) ({nu} : Set (GaloisField 2 n)) = ⊤ ∧
      ∀ i, (elabRepresentation 2 hSquareInv.restrict c).baseChange
          (GaloisField 2 n) (b i) =
        nu ^ (2 ^ i.val) • b i := by
  classical
  dsimp only
  let hSquareInv : IsAInvariant Y.subtype (frattiniSquare P) :=
    (frattiniSquareNormalInvariant Y.subtype).2.2
  have hEA : IsElementaryAbelian 2 (frattiniSquare P) :=
    frattiniSquare_isElementaryAbelian_of_exponent_four hPhiComm hfour
  let : IsMulCommutative (frattiniSquare P) :=
    IsMulCommutative.of_comm hEA.comm
  let : CommGroup (frattiniSquare P) := inferInstance
  let : Module (ZMod 2) (Additive (frattiniSquare P)) :=
    hEA.zmodModule
  let n := Module.finrank (ZMod 2) (Additive (frattiniSquare P))
  let rho : Representation (ZMod 2) Y (Additive (frattiniSquare P)) :=
    elabRepresentation 2 hSquareInv.restrict
  have htransInv : ∀ x ∈ involutions (frattiniSquare P),
      ∀ y ∈ involutions (frattiniSquare P),
        ∃ g : Y, hSquareInv.restrict g x = y :=
    restricted_involutions_transitive Y.subtype hSquareInv hxi.transitive
  have htrans : ∀ v w : Additive (frattiniSquare P),
      v ≠ 0 → w ≠ 0 → ∃ g : Y, rho g v = w := by
    intro v w hv hw
    have hvInv : v.toMul ∈ involutions (frattiniSquare P) := by
      refine ⟨hEA.pow_eq_one v.toMul, ?_⟩
      intro hvOne
      apply hv
      apply Additive.toMul.injective
      simpa using hvOne
    have hwInv : w.toMul ∈ involutions (frattiniSquare P) := by
      refine ⟨hEA.pow_eq_one w.toMul, ?_⟩
      intro hwOne
      apply hw
      apply Additive.toMul.injective
      simpa using hwOne
    obtain ⟨g, hg⟩ := htransInv v.toMul hvInv w.toMul hwInv
    refine ⟨g, ?_⟩
    change Additive.ofMul (hSquareInv.restrict g v.toMul) = w
    simpa using congrArg Additive.ofMul hg
  have hSquareNeBot : frattiniSquare P ≠ (⊥ : Subgroup P) :=
    frattiniSquare_ne_bot_of_exists_pow_two_ne_one hexists
  have hinvSquare : involutions P ⊆ frattiniSquare P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSquareInv hSquareNeBot
  obtain ⟨x, y, hxInv, hyInv, hxy⟩ := hmulti
  let xSquare : frattiniSquare P := ⟨x, hinvSquare hxInv⟩
  let ySquare : frattiniSquare P := ⟨y, hinvSquare hyInv⟩
  have hxSquareOne : xSquare ≠ 1 := by
    intro hx
    exact hxInv.2 (congrArg Subtype.val hx)
  have hySquareOne : ySquare ≠ 1 := by
    intro hy
    exact hyInv.2 (congrArg Subtype.val hy)
  have hxySquare : xSquare ≠ ySquare := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hOneNot : 1 ∉ ({xSquare, ySquare} : Set (frattiniSquare P)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxSquareOne.symm, hySquareOne.symm⟩
  have hxNot : xSquare ∉ ({ySquare} : Set (frattiniSquare P)) := by
    simpa only [Set.mem_singleton_iff] using hxySquare
  have hsetCard :
      ({1, xSquare, ySquare} : Set (frattiniSquare P)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hOneNot,
      Set.ncard_insert_of_notMem hxNot]
    simp
  have hthree : 3 ≤ Nat.card (frattiniSquare P) := by
    have hle := Set.ncard_mono
      (Set.subset_univ ({1, xSquare, ySquare} : Set (frattiniSquare P)))
    rw [hsetCard, Set.ncard_univ] at hle
    exact hle
  have hcard : Nat.card (frattiniSquare P) = 2 ^ n := by
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

end OddOrder.Higman.Suzuki2Groups
