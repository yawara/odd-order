/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.CompositionSeries

/-!
# Higman's Lemma 13: lengths of the Frattini quotient

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 92.

The branch-specific composition series descend to the Frattini quotient:

* in the exponent-four branch, `P / Φ(P)` has `ξ`-length two;
* in the exponent-two branch, `P / Φ(P)` has `ξ`-length three.

The no-long-chain clauses are proved by pulling an arbitrary quotient chain
back to `P`.  Prepending the already constructed lower Frattini step gives
a five-step ambient chain, contradicting exact `ξ`-length four.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 92), exponent-four quotient length.**

When `Φ(P)` has exponent four, the induced actor on `P / Φ(P)` has
exact `ξ`-length two. -/
theorem quotient_hasXiLengthTwo_of_xiLengthFour_exponent_four
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (hPhiComm : IsMulCommutative (frattini P))
    (hfour : ∀ z : frattini P, z ^ 4 = 1)
    (hexists : ∃ z : frattini P, z ^ 2 ≠ 1) :
    HasXiLengthTwo
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let q := QuotientGroup.mk' (frattini P)
  let qact := hPhiInv.quotientMulAutHom
  obtain ⟨B, hbotSquare, hSquarePhi, hPhiB, hBtop⟩ :=
    exists_frattini_composition_series_of_xiLengthFour_exponent_four
      hP hncomm hmulti hxi hlen hprime hPhiComm hfour hexists
  let Mbar : NormalInvariantSubgroup qact :=
    ⟨B.1.map q,
      ⟨B.2.1.map q
          (QuotientGroup.mk'_surjective (frattini P)),
        hPhiInv.map_quotient B.2.2⟩⟩
  have hPhiBLe : frattini P ≤ B.1 := hPhiB.le
  have hPhiBLt : frattini P < B.1 := hPhiB.lt
  have hBtopLt : B.1 < (⊤ : Subgroup P) := hBtop.lt
  have hbotMbar : normalInvariantBot qact < Mbar := by
    change (⊥ : Subgroup (P ⧸ frattini P)) < B.1.map q
    rw [← Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))]
    simpa [q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hPhiBLe] using hPhiBLt
  have hMbarTop : Mbar < normalInvariantTop qact := by
    change B.1.map q < (⊤ : Subgroup (P ⧸ frattini P))
    rw [← Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))]
    simpa [q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hPhiBLe] using hBtopLt
  refine ⟨Mbar, hbotMbar, hMbarTop, ?_⟩
  intro A B' C D hAB hBC hCD
  let lift (U : NormalInvariantSubgroup qact) :
      NormalInvariantSubgroup Y.subtype :=
    ⟨U.1.comap q,
      ⟨U.2.1.comap q, hPhiInv.comap_quotient U.2.2⟩⟩
  have hAB' : lift A < lift B' := by
    change A.1.comap q < B'.1.comap q
    exact (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2 hAB
  have hBC' : lift B' < lift C := by
    change B'.1.comap q < C.1.comap q
    exact (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2 hBC
  have hCD' : lift C < lift D := by
    change C.1.comap q < D.1.comap q
    exact (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2 hCD
  have hPhiLiftA :
      frattiniNormalInvariant Y.subtype ≤ lift A := by
    change frattini P ≤ A.1.comap q
    exact QuotientGroup.le_comap_mk' (frattini P) A.1
  have hSquareLiftA :
      frattiniSquareNormalInvariant Y.subtype < lift A :=
    lt_of_lt_of_le hSquarePhi.lt hPhiLiftA
  exact hlen.no_chain_of_length_five
    hbotSquare.lt hSquareLiftA hAB' hBC' hCD'

/-- **Higman Lemma 13 (p. 92), exponent-two quotient length.**

When `Φ(P)` has exponent two, the induced actor on `P / Φ(P)` has
exact `ξ`-length three. -/
theorem quotient_hasXiLengthThree_of_xiLengthFour_exponent_two
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    HasXiLengthThree
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let q := QuotientGroup.mk' (frattini P)
  let qact := hPhiInv.quotientMulAutHom
  obtain ⟨B, C, hbotPhi, hPhiB, hBC, hCtop⟩ :=
    exists_frattini_composition_series_of_xiLengthFour_exponent_two
      hP hncomm hxi hlen htwo
  let Bbar : NormalInvariantSubgroup qact :=
    ⟨B.1.map q,
      ⟨B.2.1.map q
          (QuotientGroup.mk'_surjective (frattini P)),
        hPhiInv.map_quotient B.2.2⟩⟩
  let Cbar : NormalInvariantSubgroup qact :=
    ⟨C.1.map q,
      ⟨C.2.1.map q
          (QuotientGroup.mk'_surjective (frattini P)),
        hPhiInv.map_quotient C.2.2⟩⟩
  have hPhiBLe : frattini P ≤ B.1 := hPhiB.le
  have hPhiCLe : frattini P ≤ C.1 :=
    hPhiB.le.trans hBC.le
  have hPhiBLt : frattini P < B.1 := hPhiB.lt
  have hBCLt : B.1 < C.1 := hBC.lt
  have hCtopLt : C.1 < (⊤ : Subgroup P) := hCtop.lt
  have hbotBbar : normalInvariantBot qact < Bbar := by
    change (⊥ : Subgroup (P ⧸ frattini P)) < B.1.map q
    rw [← Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))]
    simpa [q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hPhiBLe] using hPhiBLt
  have hBbarCbar : Bbar < Cbar := by
    change B.1.map q < C.1.map q
    rw [← Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))]
    simpa [q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hPhiBLe,
      sup_eq_right.mpr hPhiCLe] using hBCLt
  have hCbarTop : Cbar < normalInvariantTop qact := by
    change C.1.map q < (⊤ : Subgroup (P ⧸ frattini P))
    rw [← Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))]
    simpa [q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hPhiCLe] using hCtopLt
  refine ⟨Bbar, Cbar, hbotBbar, hBbarCbar, hCbarTop, ?_⟩
  intro A B' C' D E hAB hBC hCD hDE
  let lift (U : NormalInvariantSubgroup qact) :
      NormalInvariantSubgroup Y.subtype :=
    ⟨U.1.comap q,
      ⟨U.2.1.comap q, hPhiInv.comap_quotient U.2.2⟩⟩
  have hAB' : lift A < lift B' := by
    change A.1.comap q < B'.1.comap q
    exact (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2 hAB
  have hBC' : lift B' < lift C' := by
    change B'.1.comap q < C'.1.comap q
    exact (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2 hBC
  have hCD' : lift C' < lift D := by
    change C'.1.comap q < D.1.comap q
    exact (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2 hCD
  have hDE' : lift D < lift E := by
    change D.1.comap q < E.1.comap q
    exact (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2 hDE
  have hPhiLiftA :
      frattiniNormalInvariant Y.subtype ≤ lift A := by
    change frattini P ≤ A.1.comap q
    exact QuotientGroup.le_comap_mk' (frattini P) A.1
  have hbotLiftA : normalInvariantBot Y.subtype < lift A :=
    lt_of_lt_of_le hbotPhi.lt hPhiLiftA
  exact hlen.no_chain_of_length_five
    hbotLiftA hAB' hBC' hCD' hDE'

end OddOrder.Higman.Suzuki2Groups
