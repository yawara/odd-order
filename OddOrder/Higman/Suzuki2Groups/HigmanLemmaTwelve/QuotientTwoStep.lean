/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthThreeReduction
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke

/-!
# Higman's Lemma 12: the two-step Frattini quotient

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 12, p. 90.

For a noncommutative Suzuki 2-group of ξ-length three, this leaf identifies
the Frattini subgroup with the first term of a three-cover composition
series.  It follows that the actor induced on the Frattini quotient has
ξ-length two.  Maschke's theorem then splits the unique middle term of the
quotient by a complementary nontrivial proper invariant subgroup.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP uX

variable {P : Type uP} [Group P]
variable {X : Type uX} [Group X]

/-- In a noncommutative length-three Suzuki group, the Frattini subgroup is
the first term of an actual three-cover composition series. -/
theorem exists_frattini_composition_series_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hEA : IsElementaryAbelian 2 ↥(frattini P)) :
    ∃ B : NormalInvariantSubgroup Y.subtype,
      normalInvariantBot Y.subtype ⋖
          frattiniNormalInvariant Y.subtype ∧
        frattiniNormalInvariant Y.subtype ⋖ B ∧
          B ⋖ normalInvariantTop Y.subtype := by
  obtain ⟨A, B, hbotA, hAB, hBtop⟩ := hlen.exists_composition_series
  have hAne : A.1 ≠ (⊥ : Subgroup P) := by
    exact ne_of_gt (show (⊥ : Subgroup P) < A.1 from hbotA.lt)
  have hinvA : involutions P ⊆ A.1 :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive A.2.2 hAne
  have hPhiA : frattini P ≤ A.1 := by
    intro z hz
    by_cases hz1 : z = 1
    · exact hz1 ▸ A.1.one_mem
    · apply hinvA
      refine ⟨?_, hz1⟩
      exact congrArg Subtype.val (hEA.pow_eq_one ⟨z, hz⟩)
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  let phi := frattiniNormalInvariant Y.subtype
  have hbotPhi : normalInvariantBot Y.subtype < phi := by
    change (⊥ : Subgroup P) < frattini P
    exact bot_lt_iff_ne_bot.mpr hPhiNeBot
  have hPhiAle : phi ≤ A := hPhiA
  have hphiA : phi = A :=
    (hbotA.eq_or_eq hbotPhi.le hPhiAle).resolve_left hbotPhi.ne'
  subst A
  exact ⟨B, by simpa [phi], by simpa [phi] using hAB, hBtop⟩

/-- The quotient by the elementary-abelian Frattini first factor has
ξ-length two for the induced actor. -/
theorem quotient_hasXiLengthTwo_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hEA : IsElementaryAbelian 2 ↥(frattini P)) :
    HasXiLengthTwo
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let q := QuotientGroup.mk' (frattini P)
  let qact := hPhiInv.quotientMulAutHom
  obtain ⟨B, hbotPhi, hPhiB, hBtop⟩ :=
    exists_frattini_composition_series_of_xiLengthThree
      hP hncomm hxi hlen hEA
  let Mbar : NormalInvariantSubgroup qact :=
    ⟨B.1.map q, ⟨B.2.1.map q (QuotientGroup.mk'_surjective (frattini P)),
      hPhiInv.map_quotient B.2.2⟩⟩
  have hPhiB_le : frattini P ≤ B.1 := hPhiB.le
  have hPhiB_lt : frattini P < B.1 := by
    have h := hPhiB.lt
    change frattini P < B.1 at h
    exact h
  have hBtop_lt : B.1 < (⊤ : Subgroup P) := by
    have h := hBtop.lt
    change B.1 < (⊤ : Subgroup P) at h
    exact h
  have hbotMbar : normalInvariantBot qact < Mbar := by
    change (⊥ : Subgroup (P ⧸ frattini P)) < B.1.map q
    rw [← Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))]
    simpa [q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hPhiB_le] using hPhiB_lt
  have hMbarTop : Mbar < normalInvariantTop qact := by
    change B.1.map q < (⊤ : Subgroup (P ⧸ frattini P))
    rw [← Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))]
    simpa [q, QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hPhiB_le] using hBtop_lt
  refine ⟨Mbar, hbotMbar, hMbarTop, ?_⟩
  intro A B' C D hAB hBC hCD
  let lift (U : NormalInvariantSubgroup qact) :
      NormalInvariantSubgroup Y.subtype :=
    ⟨U.1.comap q, ⟨U.2.1.comap q,
      hPhiInv.comap_quotient U.2.2⟩⟩
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
  have hbotLiftA : normalInvariantBot Y.subtype < lift A :=
    lt_of_lt_of_le hbotPhi.lt hPhiLiftA
  exact hlen.no_chain_of_length_four hbotLiftA hAB' hBC' hCD'

/-- **Higman Lemma 12 (p. 90), quotient two-summand step.**

The induced actor on `P / Φ(P)` has two composition steps. Maschke's
theorem splits its middle term off by a second nontrivial proper invariant
summand. -/
theorem exists_complementary_invariant_quotient_summands_of_xiLengthThree
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
    ∃ U W : Subgroup (P ⧸ frattini P),
      IsAInvariant
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)).quotientMulAutHom U ∧
        IsAInvariant
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)).quotientMulAutHom W ∧
        U ≠ ⊥ ∧ U ≠ ⊤ ∧ W ≠ ⊥ ∧ W ≠ ⊤ ∧
          U ⊓ W = ⊥ ∧ U ⊔ W = ⊤ := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let qact := hPhiInv.quotientMulAutHom
  have hEA : IsElementaryAbelian 2 ↥(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hqLen : HasXiLengthTwo qact :=
    quotient_hasXiLengthTwo_of_xiLengthThree
      hP hncomm hxi hlen hEA
  obtain ⟨U, hUbot, hUtop⟩ := hqLen.exists_middle
  have hUbot' : (⊥ : Subgroup (P ⧸ frattini P)) < U.1 := by
    exact hUbot
  have hUtop' : U.1 < (⊤ : Subgroup (P ⧸ frattini P)) := by
    exact hUtop
  obtain ⟨B, _hbotPhi, hPhiB, hBtop⟩ :=
    exists_frattini_composition_series_of_xiLengthThree
      hP hncomm hxi hlen hEA
  have hPhiB' : frattini P < B.1 := by
    have h := hPhiB.lt
    change frattini P < B.1 at h
    exact h
  have hBtop' : B.1 < (⊤ : Subgroup P) := by
    have h := hBtop.lt
    change B.1 < (⊤ : Subgroup P) at h
    exact h
  have hPhiNeTop : frattini P ≠ (⊤ : Subgroup P) :=
    (hPhiB'.trans hBtop').ne
  letI : Nontrivial (P ⧸ frattini P) :=
    Subgroup.nontrivial_quotient_of_ne_top hPhiNeTop
  have hinv : (involutions P).Nonempty := by
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    exact ⟨x, hx⟩
  have hYodd : Odd (Nat.card Y) := by
    have hinvOdd := involutions_ncard_odd_of_isPGroup hP hinv
    exact Nat.not_even_iff_odd.mp fun hYeven =>
      hinvOdd.not_two_dvd_nat
        (hprime 2 Nat.prime_two (Even.two_dvd hYeven))
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
  have hQEA : IsElementaryAbelian 2 (P ⧸ frattini P) :=
    hP.quotient_frattini_isElementaryAbelian
  obtain ⟨W, hWinv, hUWbot, hUWtop⟩ :=
    OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_of_isElementaryAbelian
      htwoQ hcop hQEA U.2.2
  have hWbot : W ≠ (⊥ : Subgroup (P ⧸ frattini P)) := by
    intro hW
    apply hUtop'.ne
    simpa [hW] using hUWtop
  have hWtop : W ≠ (⊤ : Subgroup (P ⧸ frattini P)) := by
    intro hW
    apply hUbot'.ne'
    simpa [hW] using hUWbot
  exact ⟨U.1, W, U.2.2, hWinv, hUbot'.ne', hUtop'.ne,
    hWbot, hWtop, hUWbot, hUWtop⟩

/-- Pull complementary nonzero proper invariant summands of the Frattini
quotient back to complementary invariant subgroups of the original group. -/
theorem frattiniPreimages_of_complementary_invariant_quotient_summands
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {U W : Subgroup (P ⧸ frattini P)}
    (hUinv : IsAInvariant
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom U)
    (hWinv : IsAInvariant
      (IsAInvariant.of_characteristic Y.subtype :
        IsAInvariant Y.subtype (frattini P)).quotientMulAutHom W)
    (hUbot : U ≠ ⊥) (hUtop : U ≠ ⊤)
    (hWbot : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hUWbot : U ⊓ W = ⊥) (hUWtop : U ⊔ W = ⊤) :
    ∃ X Z : Subgroup P,
      IsAInvariant Y.subtype X ∧
        IsAInvariant Y.subtype Z ∧
        frattini P < X ∧ X < ⊤ ∧
        frattini P < Z ∧ Z < ⊤ ∧
        X ≠ ⊥ ∧ Z ≠ ⊥ ∧
        X ⊓ Z = frattini P ∧ X ⊔ Z = ⊤ := by
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  let q := QuotientGroup.mk' (frattini P)
  let X := U.comap q
  let Z := W.comap q
  have hXinv : IsAInvariant Y.subtype X := by
    simpa [X, q] using hPhiInv.comap_quotient hUinv
  have hZinv : IsAInvariant Y.subtype Z := by
    simpa [Z, q] using hPhiInv.comap_quotient hWinv
  have hPhiX : frattini P < X := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (bot_lt_iff_ne_bot.mpr hUbot)
    simpa [X, q, QuotientGroup.ker_mk'] using h
  have hXtop : X < (⊤ : Subgroup P) := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (lt_top_iff_ne_top.mpr hUtop)
    simpa [X, q] using h
  have hPhiZ : frattini P < Z := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (bot_lt_iff_ne_bot.mpr hWbot)
    simpa [Z, q, QuotientGroup.ker_mk'] using h
  have hZtop : Z < (⊤ : Subgroup P) := by
    have h := (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective (frattini P))).2
        (lt_top_iff_ne_top.mpr hWtop)
    simpa [Z, q] using h
  have hXZinf : X ⊓ Z = frattini P := by
    calc
      X ⊓ Z = (U ⊓ W).comap q := by
        exact (Subgroup.comap_inf U W q).symm
      _ = (⊥ : Subgroup (P ⧸ frattini P)).comap q := by rw [hUWbot]
      _ = frattini P := by simp [q, QuotientGroup.ker_mk']
  have hXZsup : X ⊔ Z = (⊤ : Subgroup P) := by
    calc
      X ⊔ Z = (U ⊔ W).comap q :=
        Subgroup.comap_sup_eq (f := q) U W
          (QuotientGroup.mk'_surjective (frattini P))
      _ = (⊤ : Subgroup (P ⧸ frattini P)).comap q := by rw [hUWtop]
      _ = ⊤ := Subgroup.comap_top q
  exact ⟨X, Z, hXinv, hZinv, hPhiX, hXtop, hPhiZ, hZtop,
    ne_of_gt (lt_of_le_of_lt bot_le hPhiX),
    ne_of_gt (lt_of_le_of_lt bot_le hPhiZ), hXZinf, hXZsup⟩

/-- **Higman Lemma 12 (p. 90), complementary Frattini preimages.**

The two quotient summands lift to proper normal actor-invariant subgroups
whose intersection is `Φ(P)` and whose join is all of `P`. -/
theorem exists_complementary_invariant_frattini_preimages_of_xiLengthThree
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
    ∃ X Z : Subgroup P,
      X.Normal ∧ IsAInvariant Y.subtype X ∧
        Z.Normal ∧ IsAInvariant Y.subtype Z ∧
        frattini P < X ∧ X < ⊤ ∧
        frattini P < Z ∧ Z < ⊤ ∧
        X ≠ ⊥ ∧ Z ≠ ⊥ ∧
        X ⊓ Z = frattini P ∧ X ⊔ Z = ⊤ := by
  obtain ⟨U, W, hUinv, hWinv, hUbot, hUtop, hWbot, hWtop,
      hUWbot, hUWtop⟩ :=
    exists_complementary_invariant_quotient_summands_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  obtain ⟨X, Z, hXinv, hZinv, hPhiX, hXtop, hPhiZ, hZtop,
      hXbot, hZbot, hXZinf, hXZsup⟩ :=
    frattiniPreimages_of_complementary_invariant_quotient_summands
      hUinv hWinv hUbot hUtop hWbot hWtop hUWbot hUWtop
  have hXnormal : X.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiX.le)
  have hZnormal : Z.Normal :=
    Subgroup.Normal.of_commutator_le P
      ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
        hPhiZ.le)
  exact ⟨X, Z, hXnormal, hXinv, hZnormal, hZinv, hPhiX, hXtop,
    hPhiZ, hZtop, hXbot, hZbot, hXZinf, hXZsup⟩

/-- Invariance under the range actor is equivalent to invariance under the
original actor. -/
theorem isAInvariant_range_subtype_iff
    {A G : Type*} [Group A] [Group G]
    (act : A →* MulAut G) (K : Subgroup G) :
    IsAInvariant act.range.subtype K ↔ IsAInvariant act K := by
  rw [isAInvariant_iff_smul_mem, isAInvariant_iff_smul_mem]
  constructor
  · intro h a g hg
    exact h (act.rangeRestrict a) g hg
  · rintro h ⟨_, a, rfl⟩ g hg
    exact h a g hg

/-- **Higman Lemma 12 (p. 90), restricted ξ-length.**

If `Φ(P) < S < P` and `S` is actor-invariant, then the faithful range of
the actor restricted to `S` has ξ-length two. -/
theorem restricted_range_hasXiLengthTwo_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hEA : IsElementaryAbelian 2 ↑(frattini P))
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P)) :
    HasXiLengthTwo hSinv.restrict.range.subtype := by
  let ract := hSinv.restrict.range.subtype
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  let phiS : Subgroup S := (frattini P).subgroupOf S
  have hphiSNormal : phiS.Normal := by
    exact (inferInstance : (frattini P).Normal).subgroupOf S
  have hphiY : IsAInvariant hSinv.restrict phiS := by
    exact hSinv.subgroupOf (IsAInvariant.of_characteristic Y.subtype)
  have hphiRange : IsAInvariant ract phiS := by
    exact (isAInvariant_range_subtype_iff hSinv.restrict phiS).2 hphiY
  let phiTerm : NormalInvariantSubgroup ract :=
    ⟨phiS, ⟨hphiSNormal, hphiRange⟩⟩
  have hbotPhi : normalInvariantBot ract < phiTerm := by
    change (⊥ : Subgroup S) < phiS
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective]
    simp only [Subgroup.map_bot]
    rw [show phiS.map S.subtype = frattini P by
      exact Subgroup.map_subgroupOf_eq_of_le hPhiS.le]
    exact bot_lt_iff_ne_bot.mpr hPhiNeBot
  have hPhiTop : phiTerm < normalInvariantTop ract := by
    change phiS < (⊤ : Subgroup S)
    rw [← Subgroup.map_lt_map_iff_of_injective S.subtype_injective]
    rw [show phiS.map S.subtype = frattini P by
      exact Subgroup.map_subgroupOf_eq_of_le hPhiS.le]
    simpa [← MonoidHom.range_eq_map] using hPhiS
  refine ⟨phiTerm, hbotPhi, hPhiTop, ?_⟩
  intro A B C D hAB hBC hCD
  have hbotAle : normalInvariantBot ract ≤ A := by
    change (⊥ : Subgroup S) ≤ A.1
    exact bot_le
  have hbotB : normalInvariantBot ract < B :=
    lt_of_le_of_lt hbotAle hAB
  have hbotC : normalInvariantBot ract < C := hbotB.trans hBC
  have hbotD : normalInvariantBot ract < D := hbotC.trans hCD
  have lift_nontrivial :
      ∀ K : NormalInvariantSubgroup ract,
        K ≠ normalInvariantBot ract →
          ∃ L : NormalInvariantSubgroup Y.subtype,
            L.1 = K.1.map S.subtype := by
    intro K hKne
    have hKvalNeBot : K.1 ≠ (⊥ : Subgroup S) := by
      intro hKbot
      apply hKne
      apply Subtype.ext
      exact hKbot
    have hKmapNeBot : K.1.map S.subtype ≠ (⊥ : Subgroup P) := by
      intro hKmap
      apply hKvalNeBot
      exact (Subgroup.map_eq_bot_iff_of_injective
        K.1 S.subtype_injective).mp hKmap
    have hKY : IsAInvariant hSinv.restrict K.1 :=
      (isAInvariant_range_subtype_iff hSinv.restrict K.1).1 K.2.2
    have hKmapInv : IsAInvariant Y.subtype (K.1.map S.subtype) :=
      aInvariant_map_subtype_of_restrict hSinv hKY
    have hinvK : involutions P ⊆ K.1.map S.subtype :=
      involutions_subset_of_nontrivial_invariant
        hP Y hxi.transitive hKmapInv hKmapNeBot
    have hPhiK : frattini P ≤ K.1.map S.subtype := by
      intro z hz
      by_cases hz1 : z = 1
      · exact hz1 ▸ (K.1.map S.subtype).one_mem
      · apply hinvK
        refine ⟨?_, hz1⟩
        exact congrArg Subtype.val (hEA.pow_eq_one ⟨z, hz⟩)
    have hcommK : _root_.commutator P ≤ K.1.map S.subtype :=
      (OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans hPhiK
    have hKmapNormal : (K.1.map S.subtype).Normal := by
      apply (Subgroup.commutator_top_left_le_iff
        (H := K.1.map S.subtype)).mp
      exact (Subgroup.commutator_mono le_rfl le_top).trans hcommK
    exact ⟨⟨K.1.map S.subtype, ⟨hKmapNormal, hKmapInv⟩⟩, rfl⟩
  obtain ⟨B', hB'⟩ := lift_nontrivial B hbotB.ne'
  obtain ⟨C', hC'⟩ := lift_nontrivial C hbotC.ne'
  obtain ⟨D', hD'⟩ := lift_nontrivial D hbotD.ne'
  have hbotB' : normalInvariantBot Y.subtype < B' := by
    change (⊥ : Subgroup P) < B'.1
    rw [hB']
    have hbotBval : (⊥ : Subgroup S) < B.1 := hbotB
    have hmap := (Subgroup.map_lt_map_iff_of_injective
      S.subtype_injective).2 hbotBval
    simpa using hmap
  have hB'C' : B' < C' := by
    change B'.1 < C'.1
    rw [hB', hC']
    exact (Subgroup.map_lt_map_iff_of_injective
      S.subtype_injective).2 hBC
  have hC'D' : C' < D' := by
    change C'.1 < D'.1
    rw [hC', hD']
    exact (Subgroup.map_lt_map_iff_of_injective
      S.subtype_injective).2 hCD
  have hD'top : D' < normalInvariantTop Y.subtype := by
    change D'.1 < (⊤ : Subgroup P)
    rw [hD']
    exact lt_of_le_of_lt (Subgroup.map_subtype_le D.1) hStop
  exact hlen.no_chain_of_length_four hbotB' hB'C' hC'D' hD'top

end OddOrder.Higman.Suzuki2Groups
