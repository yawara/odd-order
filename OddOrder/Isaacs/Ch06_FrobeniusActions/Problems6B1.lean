/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroupQuotient
import OddOrder.Isaacs.Ch06_FrobeniusActions.ProblemsMonomialSetup

/-!
# Isaacs Problem 6B.1 — Frobenius 補群は Frobenius 群を含まない (書籍 p. 195)

**主張**: 任意の Frobenius 群は**可解**な Frobenius 部分群を含む。したがって Frobenius 補群
(= Frobenius 作用の作用側) は Frobenius 群を部分群として持てない。

**構成**:

* **前半** `exists_isSolvable_isFrobeniusGroup_of_isFrobeniusGroup`:
  Frobenius 群 `G` (核 `N`, 補群 `A`) から素数位数 `p` の元 `y ∈ A` を取り, `⟨y⟩` 不変な
  非自明可換部分群 `M ≤ N` を取る (Isaacs Thm 3.23 経由の既存 API)。`M⟨y⟩` は可解
  (可換 `M` の上に巡回商) な Frobenius 群。
* **後半** `false_of_frobeniusAction_actorSubgroup_isFrobeniusGroup`:
  Frobenius 補群 `A` の部分群 `B` が Frobenius 群なら, 前半で得た可解 Frobenius 部分群を
  `A` の部分群へ移して (`IsFrobeniusGroup.mapEquiv`), **Isaacs Thm 6.9 の可解分岐**
  `false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup` に流し込むと矛盾。

書籍が「deduce」と書いているのはこの合成のこと — 可解性の仮定は前半で外れる。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6B.1: 可解 Frobenius 部分群 (p. 195) -/

/-- **Isaacs Problem 6B.1 の前半** (p. 195): 任意の有限 Frobenius 群は**可解**な Frobenius
部分群を含む。

素数位数の元 `y` を補群 `A` から取り, `⟨y⟩` 不変な非自明可換部分群 `M ≤ N` に対し `M⟨y⟩` を
とればよい。 -/
theorem exists_isSolvable_isFrobeniusGroup_of_isFrobeniusGroup
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G} (hF : IsFrobeniusGroup G N A) :
    ∃ (H : Subgroup G) (K L : Subgroup ↥H), IsSolvable ↥H ∧ IsFrobeniusGroup ↥H K L := by
  classical
  haveI hNormN : N.Normal := hF.isNormal
  haveI hAnt : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hF.ne_bot_complement
  haveI hNnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hF.ne_bot_kernel
  -- (1) 補群から素数位数の元 `y` を取る (Cauchy)
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.mpr hAnt).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥A := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥A) p
    (by rwa [← Nat.card_eq_fintype_card])
  have hyne : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact hp.one_lt.ne hy
  -- (2) `B := ⟨y⟩` は可解
  haveI : IsSolvable ↥(Subgroup.zpowers y) := by
    refine isSolvable_of_comm fun a b => ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hk, ← zpow_add, ← zpow_add, add_comm]
  -- (3) `⟨y⟩` 不変な非自明可換部分群 `M ≤ N`
  letI : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have hact : IsFrobeniusAction ↥A ↥N := hF.toFrobeniusAction
  obtain ⟨M, hMnt, hMcomm, hMinv⟩ :=
    exists_actorSubgroup_invariant_nontrivial_abelian_subgroup_of_solvable hact
      (Subgroup.zpowers y)
  haveI := hMnt
  haveI := hMcomm
  -- (4) `G` の中へ移す
  set M' : Subgroup G := M.map N.subtype with hM'def
  set Y : Subgroup G := Subgroup.zpowers ((y : ↥A) : G) with hYdef
  set H : Subgroup G := M' ⊔ Y with hHdef
  have hM'N : M' ≤ N := by rintro _ ⟨m, _, rfl⟩; exact m.2
  have hYA : Y ≤ A := Subgroup.zpowers_le.mpr y.2
  have hyG : ((y : ↥A) : G) ≠ 1 := fun h => hyne (Subtype.ext h)
  have hM'card : Nat.card ↥M' = Nat.card ↥M :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective M N.subtype (Subgroup.subtype_injective N)).symm.toEquiv
  haveI hM'nt : Nontrivial ↥M' := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hM'card]
    exact Finite.one_lt_card_iff_nontrivial.mpr hMnt
  -- 共役不変性: `y` は `M'` を正規化する
  have hconjM : ∀ b : ↥(Subgroup.zpowers y), ∀ g : G, g ∈ M' →
      ((b : ↥A) : G) * g * ((b : ↥A) : G)⁻¹ ∈ M' := by
    rintro b _ ⟨m, hm, rfl⟩
    exact ⟨(b : ↥A) • m, hMinv b m hm, rfl⟩
  have hyNorm : ((y : ↥A) : G) ∈ Subgroup.normalizer M' := by
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
    · exact hconjM ⟨y, Subgroup.mem_zpowers y⟩ g hg
    · have := hconjM ⟨y⁻¹, inv_mem (Subgroup.mem_zpowers y)⟩ _ hg
      simpa [mul_assoc] using this
  have hYnorm : Y ≤ Subgroup.normalizer M' := Subgroup.zpowers_le.mpr hyNorm
  -- (5) 位数と補群性
  have hNA : N ⊓ A = ⊥ := by rw [← disjoint_iff]; exact hF.isComplement.disjoint
  have hYcard : Nat.card ↥Y = p := by
    rw [hYdef, Nat.card_zpowers, Subgroup.orderOf_coe, hy]
  have hcop : Nat.Coprime (Nat.card ↥M') (Nat.card ↥Y) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hM'N)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYA)
        hF.coprime_card_kernel_complement)
  have hcardH : Nat.card ↥H = Nat.card ↥M' * Nat.card ↥Y :=
    card_sup_of_le_normalizer_of_coprime hYnorm hcop
  have hM'H : M' ≤ H := le_sup_left
  have hYH : Y ≤ H := le_sup_right
  have hcardM'sub : Nat.card ↥(M'.subgroupOf H) = Nat.card ↥M' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'H).toEquiv
  have hcardYsub : Nat.card ↥(Y.subgroupOf H) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv
  have hdisj : Disjoint (M'.subgroupOf H) (Y.subgroupOf H) := by
    rw [disjoint_iff_inf_le]
    intro z hz
    have hzone : (z : G) = 1 := by
      have : (z : G) ∈ N ⊓ A := ⟨hM'N hz.1, hYA hz.2⟩
      rw [hNA, Subgroup.mem_bot] at this
      exact this
    simpa [Subgroup.mem_bot] using Subtype.ext hzone
  have hcompl : Subgroup.IsComplement' (M'.subgroupOf H) (Y.subgroupOf H) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint
      (by rw [hcardM'sub, hcardYsub, hcardH]) hdisj
  haveI hMnormal : (M'.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgH : (g : G) ∈ Subgroup.normalizer M' := by
      exact (sup_le Subgroup.le_normalizer hYnorm : H ≤ Subgroup.normalizer M') g.2
    exact (Subgroup.mem_normalizer_iff.mp hgH (n : G)).mp hn
  -- (6) Frobenius 性と可解性
  refine ⟨H, M'.subgroupOf H, Y.subgroupOf H, ?_, ?_⟩
  · -- 可解: 可換な正規部分群 + 素数位数の商
    have hM'commutes : ∀ a b : ↥M', a * b = b * a := by
      rintro ⟨_, u, hu, rfl⟩ ⟨_, v, hv, rfl⟩
      refine Subtype.ext ?_
      have h := congrArg (fun z : ↥M => ((z : ↥N) : G)) (hMcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
      simpa using h
    haveI : IsSolvable ↥M' := isSolvable_of_comm hM'commutes
    haveI : IsSolvable ↥(M'.subgroupOf H) :=
      solvable_of_solvable_injective (f := (Subgroup.subgroupOfEquivOfLe hM'H).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hM'H).injective
    haveI : IsCyclic (↥H ⧸ M'.subgroupOf H) := by
      refine isCyclic_of_prime_card (p := p) ?_
      have hmul := Subgroup.card_mul_index (M'.subgroupOf H)
      rw [hcardM'sub] at hmul
      have heq : Nat.card ↥M' * (M'.subgroupOf H).index = Nat.card ↥M' * Nat.card ↥Y := by
        rw [hmul, hcardH]
      have hidx := Nat.eq_of_mul_eq_mul_left Nat.card_pos heq
      change (M'.subgroupOf H).index = p
      rw [hidx, hYcard]
    haveI : IsSolvable (↥H ⧸ M'.subgroupOf H) := by
      refine isSolvable_of_comm fun a b => ?_
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥H ⧸ M'.subgroupOf H)
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
      rw [← zpow_add, ← zpow_add, add_comm]
    exact solvable_of_ker_le_range (M'.subgroupOf H).subtype
      (QuotientGroup.mk' (M'.subgroupOf H)) (by rw [QuotientGroup.ker_mk']; simp)
  · refine isFrobeniusGroup_of_prime_complement_fixedFree hcompl ?_ ?_ ?_
    · rw [hcardYsub, hYcard]; exact hp
    · have hnt : Nontrivial ↥(M'.subgroupOf H) := by
        refine Finite.one_lt_card_iff_nontrivial.mp ?_
        rw [hcardM'sub]
        exact Finite.one_lt_card_iff_nontrivial.mpr hM'nt
      exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt
    · intro n hn hfix
      by_contra hne
      have hnN : (n : G) ∈ N := hM'N hn
      have hnne : (n : G) ≠ 1 := fun h => hne (Subtype.ext h)
      have hyH : ((y : ↥A) : G) ∈ H := hYH (Subgroup.mem_zpowers _)
      have := hfix ⟨((y : ↥A) : G), hyH⟩ (Subgroup.mem_zpowers _)
      exact hF.conj_frobenius _ y.2 hyG _ hnN hnne (congrArg Subtype.val this)

/-- **Isaacs Problem 6B.1 の後半** (p. 195) ⭐: Frobenius 補群は Frobenius 群を部分群として
持てない (可解性の仮定なし)。

`false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup` (Isaacs Thm 6.9 の
可解分岐) の可解仮定を, 前半の「可解 Frobenius 部分群の存在」で除去したもの。 -/
theorem false_of_frobeniusAction_actorSubgroup_isFrobeniusGroup
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U] (hFrob : IsFrobeniusAction A U)
    (B : Subgroup A) {N C : Subgroup ↥B} (hGroup : IsFrobeniusGroup ↥B N C) :
    False := by
  obtain ⟨H, K, L, hHsol, hHF⟩ := exists_isSolvable_isFrobeniusGroup_of_isFrobeniusGroup hGroup
  have e : ↥H ≃* ↥(H.map B.subtype) :=
    Subgroup.equivMapOfInjective H B.subtype (Subgroup.subtype_injective B)
  haveI := hHsol
  haveI : IsSolvable ↥(H.map B.subtype) :=
    solvable_of_solvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  exact false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup hFrob
    (H.map B.subtype) (hHF.mapEquiv e)

end

end OddOrder.Isaacs.Ch06
