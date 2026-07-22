/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentFourFactors
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralDegreeThree

/-!
# Higman's Lemma 13: the exponent-four Jacobi relation

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

For either restricted length-three factor, internal commutators lie in its
Frattini subgroup, whose ambient image is Φ(P)². Higman's Jacobi identity
then swaps the last two entries of a mixed triple commutator. This file
establishes the actual subgroup membership and the lower-central
faithfulness needed to state that identity for raw elements of P.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open scoped commutatorElement IsMulCommutative
open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

local instance instExponentFourJacobiLayerIsMulCommutative
    (P : Type uP) [Group P] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer P i) :=
  ⟨⟨(lowerCentralLayer_isElementaryAbelian P i).1⟩⟩

noncomputable local instance instExponentFourJacobiLayerZModTwoModule
    (P : Type uP) [Group P] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- **Higman Lemma 13 (p. 92), same-factor commutators.**

The commutator of two elements of a restricted length-three factor lies in
the factor's internal Frattini subgroup, hence in the common ambient
subgroup Φ(P)². -/
theorem commutatorElement_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
    {x x' : P} (hx : x ∈ S) (hx' : x' ∈ S) :
    ⁅x, x'⁆ ∈ frattiniSquare P := by
  have hPhiMap :=
    frattini_map_eq_frattiniSquare_of_restricted_lengthThree_exponent_four
      hP hmulti hxi hprime hPhiComm hexists
        hSinv hPhiS hlenS hncommS
  let xS : S := ⟨x, hx⟩
  let xS' : S := ⟨x', hx'⟩
  have hcommS : ⁅xS, xS'⁆ ∈ frattini S :=
    (OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup
      (hP.to_subgroup S))
      (OddOrder.Isaacs.Ch04.commutatorElement_mem_commutator_top xS xS')
  have hmap : S.subtype ⁅xS, xS'⁆ ∈ (frattini S).map S.subtype :=
    Subgroup.mem_map_of_mem S.subtype hcommS
  rw [hPhiMap] at hmap
  rw [map_commutatorElement] at hmap
  change ⁅x, x'⁆ ∈ frattiniSquare P at hmap
  exact hmap

/-- In the exponent-four branch, the denominator of the third
lower-central layer is trivial.

Indeed, γ₂(P) ≤ Φ(P), hence γ₃(P) ≤ [Φ(P),P] ≤ Φ(P)². The latter is
central and has exponent two, so γ₄(P)=1 and both factors of the degree-three
layer denominator vanish. -/
theorem lowerCentralLayerKernel_two_eq_bot_of_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    lowerCentralLayerKernel P 2 = ⊥ := by
  letI : Nontrivial P := by
    obtain ⟨z, hz⟩ := hexists
    refine ⟨⟨(z : P), 1, ?_⟩⟩
    intro h
    apply hz
    apply Subtype.ext
    rw [show z = 1 from Subtype.ext h, one_pow]
  have hPhiCommLe :=
    commutator_frattini_top_le_frattiniSquare_of_exponent_four
      hP hxi hPhiComm hexists
  have hTwoSquare : lowerCentralTerm P 2 ≤ frattiniSquare P := by
    rw [lowerCentralTerm, Subgroup.lowerCentralSeries_succ,
      Subgroup.top_lowerCentralSeries_one]
    exact (Subgroup.commutator_mono
      (OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP)
      le_rfl).trans hPhiCommLe
  have hSquareCenter := frattiniSquare_le_center_of_exponent_four
    hP hxi hPhiComm hfour
  have hSquareComm : ⁅frattiniSquare P, (⊤ : Subgroup P)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hSquareCenter
  have hThreeBot : lowerCentralTerm P 3 = ⊥ := by
    apply le_bot_iff.mp
    rw [lowerCentralTerm, Subgroup.lowerCentralSeries_succ]
    exact (Subgroup.commutator_mono hTwoSquare le_rfl).trans
      (le_of_eq hSquareComm)
  have hAgemoBot : Agemo (lowerCentralTerm P 2) 2 1 = ⊥ := by
    rw [eq_bot_iff, Agemo, Subgroup.closure_le]
    rintro g ⟨z, rfl⟩
    have hzSquare : (z : P) ∈ frattiniSquare P :=
      hTwoSquare z.property
    have hzTwoP :=
      pow_two_eq_one_of_mem_frattiniSquare hPhiComm hfour hzSquare
    have hzTwo : z ^ 2 = 1 := Subtype.ext hzTwoP
    simp [hzTwo]
  simp [lowerCentralLayerKernel, hAgemoBot, hThreeBot]

/-- **Higman Lemma 13 (p. 92), Jacobi relation.**

If `x,x'` lie in either restricted length-three factor, then the two mixed
triple commutators with first entry `y` agree.  The associated-graded
Jacobi identity applies because `[x,x']` lies in the central subgroup
`Φ(P)²`; triviality of the degree-three denominator then lifts the equality
from the graded layer back to raw elements of `P`. -/
theorem tripleCommutator_swap_last_of_mem_restricted_lengthThree_factor_exponent_four
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : NormalInvariantCover Y.subtype (frattini P) S)
    (hlenS : HasXiLengthThree hSinv.restrict.range.subtype)
    (hncommS : ¬ IsMulCommutative S)
    {x x' y : P} (hx : x ∈ S) (hx' : x' ∈ S) :
    ⁅⁅y, x⁆, x'⁆ = ⁅⁅y, x'⁆, x⁆ := by
  letI : Nontrivial P := by
    obtain ⟨z, hz⟩ := hexists
    refine ⟨⟨(z : P), 1, ?_⟩⟩
    intro h
    apply hz
    apply Subtype.ext
    rw [show z = 1 from Subtype.ext h, one_pow]
  let x₀ : lowerCentralTerm P 0 :=
    ⟨x, by simp [lowerCentralTerm]⟩
  let x₁ : lowerCentralTerm P 0 :=
    ⟨x', by simp [lowerCentralTerm]⟩
  let y₀ : lowerCentralTerm P 0 :=
    ⟨y, by simp [lowerCentralTerm]⟩
  let xbar : Additive (lowerCentralLayer P 0) :=
    Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x₀)
  let xbar' : Additive (lowerCentralLayer P 0) :=
    Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x₁)
  let ybar : Additive (lowerCentralLayer P 0) :=
    Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0) y₀)
  have hxxSquare : ⁅x, x'⁆ ∈ frattiniSquare P :=
    commutatorElement_mem_frattiniSquare_of_mem_restricted_lengthThree_factor_exponent_four
      hP hmulti hxi hprime hPhiComm hexists
        hSinv hPhiS hlenS hncommS hx hx'
  have hxxCenter : ⁅x, x'⁆ ∈ Subgroup.center P :=
    frattiniSquare_le_center_of_exponent_four
      hP hxi hPhiComm hfour hxxSquare
  have hrawMiddle :
      lowerCentralDegreeThreeCommutator P
          (lowerCentralCommutator P x₀ x₁) y₀ = 1 := by
    apply Subtype.ext
    change ⁅⁅x, x'⁆, y⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hxxCenter y).symm
  have hmiddle :
      lowerCentralTripleCommutatorTrilinear P xbar xbar' ybar = 0 := by
    simp only [xbar, xbar', ybar,
      lowerCentralTripleCommutatorTrilinear_mk]
    apply Additive.ofMul.injective
    change lowerCentralDegreeThreeCommutatorValue P
      (lowerCentralCommutator P x₀ x₁) y₀ = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [hrawMiddle]
    exact Subgroup.one_mem _
  have hsym :
      lowerCentralTripleCommutatorTrilinear P xbar' ybar xbar =
        lowerCentralTripleCommutatorTrilinear P ybar xbar' xbar := by
    rw [lowerCentralTripleCommutatorTrilinear_apply,
      lowerCentralTripleCommutatorTrilinear_apply,
      lowerCentralCommutatorBilinear_comm P ybar xbar']
  have hJ :=
    lowerCentralTripleCommutatorTrilinear_jacobi P ybar xbar xbar'
  rw [hmiddle, add_zero, hsym] at hJ
  have hgraded :
      lowerCentralTripleCommutatorTrilinear P ybar xbar xbar' =
        lowerCentralTripleCommutatorTrilinear P ybar xbar' xbar :=
    (eq_neg_of_add_eq_zero_left hJ).trans
      (ZModModule.neg_eq_self _)
  have hq :
      lowerCentralDegreeThreeCommutatorValue P
          (lowerCentralCommutator P y₀ x₀) x₁ =
        lowerCentralDegreeThreeCommutatorValue P
          (lowerCentralCommutator P y₀ x₁) x₀ := by
    apply Additive.ofMul.injective
    simpa only [ybar, xbar, xbar',
      lowerCentralTripleCommutatorTrilinear_mk] using hgraded
  have hK2 : lowerCentralLayerKernel P 2 = ⊥ :=
    lowerCentralLayerKernel_two_eq_bot_of_exponent_four
      hP hxi hPhiComm hfour hexists
  have hmkInj : Function.Injective
      (QuotientGroup.mk' (lowerCentralLayerKernel P 2)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by
      rw [QuotientGroup.ker_mk']
      exact hK2)
  have hraw :
      lowerCentralDegreeThreeCommutator P
          (lowerCentralCommutator P y₀ x₀) x₁ =
        lowerCentralDegreeThreeCommutator P
          (lowerCentralCommutator P y₀ x₁) x₀ := by
    apply hmkInj
    simpa only [lowerCentralDegreeThreeCommutatorValue] using hq
  simpa [lowerCentralDegreeThreeCommutator, lowerCentralCommutator,
    y₀, x₀, x₁] using congrArg Subtype.val hraw

end OddOrder.Higman.Suzuki2Groups
