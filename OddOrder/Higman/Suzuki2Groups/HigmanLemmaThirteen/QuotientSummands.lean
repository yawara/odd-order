/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.QuotientLengths
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke

/-!
# Higman's Lemma 13: invariant summands of the Frattini quotient

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

Maschke's theorem converts the exact quotient lengths obtained in the
previous leaf into invariant direct-sum decompositions:

* a length-two elementary abelian quotient has two nonzero proper summands;
* a length-three elementary abelian quotient has three such summands.

The second construction keeps a chosen chain `U < B`: first complement `B`,
then complement `U`, and put `V = B ⊓ C` for the latter complement `C`.
Modularity gives `U ⊔ V = B`, so the three summands retain the two prescribed
composition steps.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P]

/-- An elementary abelian coprime action of exact `ξ`-length two splits as
two nonzero proper invariant summands. -/
theorem exists_two_complementary_invariant_summands_of_xiLengthTwo
    {E A : Type*} [Group E] [Finite E] [Group A] [Finite A]
    {act : A →* MulAut E}
    (hlen : HasXiLengthTwo act)
    (htwoE : 2 ∣ Nat.card E)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card E))
    (hEA : IsElementaryAbelian 2 E) :
    ∃ U W : Subgroup E,
      IsAInvariant act U ∧ IsAInvariant act W ∧
        U ≠ ⊥ ∧ U ≠ ⊤ ∧ W ≠ ⊥ ∧ W ≠ ⊤ ∧
          U ⊓ W = ⊥ ∧ U ⊔ W = ⊤ := by
  obtain ⟨U, hUbot, hUtop⟩ := hlen.exists_middle
  have hUbot' : (⊥ : Subgroup E) < U.1 := hUbot
  have hUtop' : U.1 < (⊤ : Subgroup E) := hUtop
  obtain ⟨W, hWinv, hUWbot, hUWtop⟩ :=
    OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_of_isElementaryAbelian
      htwoE hcop hEA U.2.2
  have hWbot : W ≠ (⊥ : Subgroup E) := by
    intro hW
    apply hUtop'.ne
    simpa [hW] using hUWtop
  have hWtop : W ≠ (⊤ : Subgroup E) := by
    intro hW
    apply hUbot'.ne'
    simpa [hW] using hUWbot
  exact ⟨U.1, W, U.2.2, hWinv, hUbot'.ne', hUtop'.ne,
    hWbot, hWtop, hUWbot, hUWtop⟩

/-- An elementary abelian coprime action of exact `ξ`-length three splits as
three nonzero proper invariant summands.  Their partial sums reproduce a
chosen strict chain from bottom to top. -/
theorem exists_three_complementary_invariant_summands_of_xiLengthThree
    {E A : Type*} [Group E] [Finite E] [Group A] [Finite A]
    {act : A →* MulAut E}
    (hlen : HasXiLengthThree act)
    (htwoE : 2 ∣ Nat.card E)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card E))
    (hEA : IsElementaryAbelian 2 E) :
    ∃ U V W : Subgroup E,
      IsAInvariant act U ∧ IsAInvariant act V ∧
        IsAInvariant act W ∧
        U ≠ ⊥ ∧ U ≠ ⊤ ∧ V ≠ ⊥ ∧ V ≠ ⊤ ∧
        W ≠ ⊥ ∧ W ≠ ⊤ ∧ U ⊓ V = ⊥ ∧
          (U ⊔ V) ⊓ W = ⊥ ∧ U ⊔ V ⊔ W = ⊤ := by
  letI : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := hEA.comm }
  obtain ⟨U, B, hbotU, hUB, hBtop⟩ := hlen.exists_chain
  have hUbot' : (⊥ : Subgroup E) < U.1 := hbotU
  have hUB' : U.1 < B.1 := hUB
  have hBtop' : B.1 < (⊤ : Subgroup E) := hBtop
  have hUtop' : U.1 < (⊤ : Subgroup E) := hUB'.trans hBtop'
  have hBbot' : (⊥ : Subgroup E) < B.1 := hUbot'.trans hUB'
  obtain ⟨W, hWinv, hBWbot, hBWtop⟩ :=
    OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_of_isElementaryAbelian
      htwoE hcop hEA B.2.2
  obtain ⟨C, hCinv, hUCbot, hUCtop⟩ :=
    OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_of_isElementaryAbelian
      htwoE hcop hEA U.2.2
  let V : Subgroup E := B.1 ⊓ C
  have hVinv : IsAInvariant act V := B.2.2.inf hCinv
  have hUVbot : U.1 ⊓ V = (⊥ : Subgroup E) := by
    change U.1 ⊓ (B.1 ⊓ C) = ⊥
    rw [← inf_assoc, inf_eq_left.mpr hUB'.le, hUCbot]
  have hUVB : U.1 ⊔ V = B.1 := by
    change U.1 ⊔ (B.1 ⊓ C) = B.1
    rw [inf_comm B.1 C, ← sup_inf_assoc_of_le C hUB'.le,
      hUCtop, top_inf_eq]
  have hVbot : V ≠ (⊥ : Subgroup E) := by
    intro hV
    apply hUB'.ne
    simpa [hV] using hUVB
  have hVtop : V ≠ (⊤ : Subgroup E) := by
    intro hV
    apply hBtop'.ne
    exact top_unique (hV ▸ (show V ≤ B.1 from inf_le_left))
  have hWbot : W ≠ (⊥ : Subgroup E) := by
    intro hW
    apply hBtop'.ne
    simpa [hW] using hBWtop
  have hWtop : W ≠ (⊤ : Subgroup E) := by
    intro hW
    apply hBbot'.ne'
    simpa [hW] using hBWbot
  refine ⟨U.1, V, W, U.2.2, hVinv, hWinv,
    hUbot'.ne', ?_, hVbot, hVtop, hWbot, hWtop,
    hUVbot, ?_, ?_⟩
  · exact hUtop'.ne
  · simpa [hUVB] using hBWbot
  · simpa [hUVB] using hBWtop

/-- **Higman Lemma 13 (p. 92), exponent-four quotient summands.**

The length-two action induced on `P / Φ(P)` splits into two nonzero proper
invariant summands. -/
theorem exists_two_invariant_quotient_summands_of_xiLengthFour_exponent_four
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
    ∃ U W : Subgroup (P ⧸ frattini P),
      IsAInvariant
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)).quotientMulAutHom U ∧
        IsAInvariant
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)).quotientMulAutHom W ∧
        U ≠ ⊥ ∧ U ≠ ⊤ ∧ W ≠ ⊥ ∧ W ≠ ⊤ ∧
          U ⊓ W = ⊥ ∧ U ⊔ W = ⊤ := by
  letI : Nontrivial P := by
    obtain ⟨x, y, _, _, hxy⟩ := hmulti
    exact ⟨⟨x, y, hxy⟩⟩
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let qact := hPhiInv.quotientMulAutHom
  have hqLen : HasXiLengthTwo qact :=
    quotient_hasXiLengthTwo_of_xiLengthFour_exponent_four
      hP hncomm hmulti hxi hlen hprime hPhiComm hfour hexists
  have hPhiNeTop : frattini P ≠ (⊤ : Subgroup P) :=
    frattini_ne_top_of_nontrivial
  letI : Nontrivial (P ⧸ frattini P) :=
    Subgroup.nontrivial_quotient_of_ne_top hPhiNeTop
  have hinv : (involutions P).Nonempty := by
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    exact ⟨x, hx⟩
  have hYodd : Odd (Nat.card Y) :=
    actor_card_odd_of_primeSupport hP hinv hprime
  have hQp : IsPGroup 2 (P ⧸ frattini P) :=
    hP.to_quotient (frattini P)
  have htwoQ : 2 ∣ Nat.card (P ⧸ frattini P) :=
    hQp.card_eq_or_dvd.resolve_left
      (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance))
  have hcop : Nat.Coprime (Nat.card Y)
      (Nat.card (P ⧸ frattini P)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    rw [hn]
    exact hYodd.coprime_two_right.pow_right n
  exact exists_two_complementary_invariant_summands_of_xiLengthTwo
    hqLen htwoQ hcop hP.quotient_frattini_isElementaryAbelian

/-- **Higman Lemma 13 (p. 92), exponent-two quotient summands.**

The length-three action induced on `P / Φ(P)` splits into three nonzero
proper invariant summands whose partial sums form its composition chain. -/
theorem exists_three_invariant_quotient_summands_of_xiLengthFour_exponent_two
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
    (htwo : ∀ z : frattini P, z ^ 2 = 1) :
    ∃ U V W : Subgroup (P ⧸ frattini P),
      IsAInvariant
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)).quotientMulAutHom U ∧
        IsAInvariant
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)).quotientMulAutHom V ∧
        IsAInvariant
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)).quotientMulAutHom W ∧
        U ≠ ⊥ ∧ U ≠ ⊤ ∧ V ≠ ⊥ ∧ V ≠ ⊤ ∧
        W ≠ ⊥ ∧ W ≠ ⊤ ∧ U ⊓ V = ⊥ ∧
          (U ⊔ V) ⊓ W = ⊥ ∧ U ⊔ V ⊔ W = ⊤ := by
  letI : Nontrivial P := by
    obtain ⟨x, y, _, _, hxy⟩ := hmulti
    exact ⟨⟨x, y, hxy⟩⟩
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let qact := hPhiInv.quotientMulAutHom
  have hqLen : HasXiLengthThree qact :=
    quotient_hasXiLengthThree_of_xiLengthFour_exponent_two
      hP hncomm hxi hlen htwo
  have hPhiNeTop : frattini P ≠ (⊤ : Subgroup P) :=
    frattini_ne_top_of_nontrivial
  letI : Nontrivial (P ⧸ frattini P) :=
    Subgroup.nontrivial_quotient_of_ne_top hPhiNeTop
  have hinv : (involutions P).Nonempty := by
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    exact ⟨x, hx⟩
  have hYodd : Odd (Nat.card Y) :=
    actor_card_odd_of_primeSupport hP hinv hprime
  have hQp : IsPGroup 2 (P ⧸ frattini P) :=
    hP.to_quotient (frattini P)
  have htwoQ : 2 ∣ Nat.card (P ⧸ frattini P) :=
    hQp.card_eq_or_dvd.resolve_left
      (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance))
  have hcop : Nat.Coprime (Nat.card Y)
      (Nat.card (P ⧸ frattini P)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    rw [hn]
    exact hYodd.coprime_two_right.pow_right n
  exact exists_three_complementary_invariant_summands_of_xiLengthThree
    hqLen htwoQ hcop hP.quotient_frattini_isElementaryAbelian

end OddOrder.Higman.Suzuki2Groups
