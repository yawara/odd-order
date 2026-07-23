/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.LengthFourDescent
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthTwoModels

/-!
# Higman's Lemma 13: descent to a proper noncommutative subgroup

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The opening paragraph reduces `ξ`-length greater than four to length four:
a longer normal invariant chain has a proper normal invariant coatom whose
restricted faithful actor still has a four-step chain.  This coatom cannot
be abelian.  Indeed, its coatom property would make it maximal normal
invariant abelian; Lemma 9 then gives exponent at most four, contradicting
the direct Agemo obstruction for a restricted four-step chain.

The hypothesis excluding exact length four is essential.  A bare
four-step chain can end at a coatom, in which case restriction to that
coatom leaves only three strict steps.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 92), proper-subgroup descent.**

If the normal invariant subgroup poset has `ξ`-length at least four but not
exactly four, then a normal invariant coatom contains a four-step prefix of
a five-step chain.  Its faithful restricted actor therefore still has
`ξ`-length at least four.  Under Higman's standing prime-support
hypotheses, Lemma 9 and the Agemo obstruction force this proper subgroup to
be noncommutative. -/
theorem exists_proper_noncommutative_xiLengthAtLeastFour_descent
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthAtLeastFour Y.subtype)
    (hnotExact : ¬ HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    ∃ (S : Subgroup P) (hSinv : IsAInvariant Y.subtype S),
      S.Normal ∧ S ≠ ⊤ ∧
        ¬ IsMulCommutative S ∧
          HasXiLengthAtLeastFour hSinv.restrict.range.subtype := by
  have hnotFive :
      ¬ ∀ A B C D E F : NormalInvariantSubgroup Y.subtype,
        A < B → B < C → C < D → D < E → E < F → False := by
    intro hnoFive
    exact hnotExact ⟨hlen, hnoFive⟩
  push Not at hnotFive
  obtain ⟨A, B, C, D, E, F, hAB, hBC, hCD, hDE, hEF, _⟩ :=
    hnotFive
  have hFtop : F ≤ normalInvariantTop Y.subtype := by
    change F.1 ≤ (⊤ : Subgroup P)
    exact le_top
  have hEtop : E < normalInvariantTop Y.subtype :=
    hEF.trans_le hFtop
  obtain ⟨Sterm, hES, hStop⟩ :=
    exists_le_covBy_of_lt hEtop
  let S : Subgroup P := Sterm.1
  let hSinv : IsAInvariant Y.subtype S := Sterm.2.2
  have hAS : A.1 ≤ S :=
    hAB.le.trans (hBC.le.trans (hCD.le.trans (hDE.le.trans hES)))
  have hBS : B.1 ≤ S :=
    hBC.le.trans (hCD.le.trans (hDE.le.trans hES))
  have hCS : C.1 ≤ S :=
    hCD.le.trans (hDE.le.trans hES)
  have hDS : D.1 ≤ S :=
    hDE.le.trans hES
  let A' : NormalInvariantSubgroup hSinv.restrict.range.subtype :=
    xiLengthDescentSubgroupOf hSinv A
  let B' : NormalInvariantSubgroup hSinv.restrict.range.subtype :=
    xiLengthDescentSubgroupOf hSinv B
  let C' : NormalInvariantSubgroup hSinv.restrict.range.subtype :=
    xiLengthDescentSubgroupOf hSinv C
  let D' : NormalInvariantSubgroup hSinv.restrict.range.subtype :=
    xiLengthDescentSubgroupOf hSinv D
  have hA'B' : A' < B' := by
    exact xiLengthDescentSubgroupOf_lt hSinv hAS hBS hAB
  have hB'C' : B' < C' := by
    exact xiLengthDescentSubgroupOf_lt hSinv hBS hCS hBC
  have hC'D' : C' < D' := by
    exact xiLengthDescentSubgroupOf_lt hSinv hCS hDS hCD
  have hbotB' :
      normalInvariantBot hSinv.restrict.range.subtype < B' := by
    have hbotA' :
        normalInvariantBot hSinv.restrict.range.subtype ≤ A' := by
      change (⊥ : Subgroup S) ≤ A.1.subgroupOf S
      exact bot_le
    exact hbotA'.trans_lt hA'B'
  have hDtop : D' <
      normalInvariantTop hSinv.restrict.range.subtype := by
    have hDltS : D.1 < S := hDE.trans_le hES
    change D.1.subgroupOf S < (⊤ : Subgroup S)
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hDS]
    simpa [← MonoidHom.range_eq_map] using hDltS
  have hlenS : HasXiLengthAtLeastFour
      hSinv.restrict.range.subtype :=
    ⟨B', C', D', hbotB', hB'C', hC'D', hDtop⟩
  have hSnormal : S.Normal := Sterm.2.1
  have hSneTop : S ≠ (⊤ : Subgroup P) := by
    intro htop
    apply hStop.lt.ne
    apply Subtype.ext
    exact htop
  have hSnotComm : ¬ IsMulCommutative S := by
    intro hcommS
    let hCover : NormalInvariantCover Y.subtype S ⊤ :=
      { left := Sterm.2
        right := ⟨inferInstance, IsAInvariant.top Y.subtype⟩
        covBy := by
          simpa [S, normalInvariantTop] using hStop }
    let hSmax : IsMaximalNormalInvariantAbelian Y.subtype S :=
      { isNormalInvariant := Sterm.2
        isMulCommutative := hcommS
        maximal := by
          intro T hT hTcomm hST
          rcases hCover.eq_left_or_eq_right hT hST le_top with hTS | hTtop
          · exact hTS
          · exfalso
            apply hncomm
            refine IsMulCommutative.of_comm fun x y => ?_
            have hx : x ∈ T := by
              rw [hTtop]
              exact Subgroup.mem_top x
            have hy : y ∈ T := by
              rw [hTtop]
              exact Subgroup.mem_top y
            exact congrArg Subtype.val
              (hTcomm.is_comm.comm (⟨x, hx⟩ : T) ⟨y, hy⟩) }
    have hinv : (involutions P).Nonempty := by
      obtain ⟨x, _, hx, _, _⟩ := hmulti
      exact ⟨x, hx⟩
    have hYodd : Odd (Nat.card Y) :=
      actor_card_odd_of_primeSupport hP hinv hprime
    have hSfour : ∀ s : S, s ^ 4 = 1 :=
      (higmanLemmaNine_of_transitive hP Y hxi.cyclic hxi.transitive
        hYodd hmulti hncomm S hSmax).1
    have hxiS : IsXiActor hSinv.restrict.range :=
      restricted_range_isXiActor hxi hSinv
    exact (not_hasXiLengthAtLeastFour_of_isMulCommutative_of_pow_four
      (hP.to_subgroup S) hxiS.transitive hcommS hSfour) hlenS
  exact ⟨S, hSinv, hSnormal, hSneTop, hSnotComm, hlenS⟩

end OddOrder.Higman.Suzuki2Groups
