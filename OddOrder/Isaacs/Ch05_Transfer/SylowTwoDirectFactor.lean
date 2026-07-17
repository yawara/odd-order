/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-! # Isaacs Cor 5.19 (一般形): Sylow 2 が strict-max cyclic 直積因子を持てば非単純 (p. 167)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Corollary 5.19 (p. 167) の書籍一般形:
非可換有限群 `G` の Sylow 2-部分群 `P` が巡回部分群の直積で, そのうち 1 つが他の全てより
真に大きいとき, `G` は単純でない.

## Encoding

書籍の内部直積 `P = A × B₂ × ⋯ × Bₙ` (各因子 cyclic, `|A| = a > |Bᵢ|`) を
`A B : Subgroup ↥P`, `A ⊔ B = ⊤` で encode する. strict-max 条件は
「`B := B₂ ⋯ Bₙ` の exponent が `a / 2` を割る」に落ちる (各 `Bᵢ` は cyclic 2-group で
`|Bᵢ| ≤ a / 2`, かつ `a / 2` は 2-冪ゆえ `|Bᵢ| ∣ a / 2`) — 本ファイルの仮定 `hB_exp`
がこれを捕捉する. `P` abelian は書籍では直積分解から従うが, `B` の内部構造 (cyclic
直積) を落とした encoding なので仮定に取る. また直積の交わり自明性 (`Disjoint A B`)
は証明に不要なので仮定から落とした — いずれも書籍仮定より弱い仮定で同結論ゆえ
書籍強度以上.

既存の cyclic Sylow₂ 版 `not_isSimpleGroup_of_isCyclic_sylow_two`
(`OddOrder/Isaacs/Ch05_Transfer/Basic.lean`) は本定理の `B = ⊥` 特殊化に相当する.

核となる道具は Thm 5.18 強形
`eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer` (同 `Basic.lean`).
-/

namespace OddOrder.Isaacs.Ch05

open scoped commutatorElement
open scoped IsMulCommutative

variable {G : Type*} [Group G]

section /- 5C: Cor 5.19 一般形 (p. 167) -/

/-- involution の生成する巡回部分群は `{1, s}` に潰れる: `s ^ 2 = 1` なら
`x ∈ zpowers s` は `x = 1` か `x = s`. -/
theorem eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {H : Type*} [Group H] {s x : H}
    (hs : s ^ 2 = 1) (hx : x ∈ Subgroup.zpowers s) : x = 1 ∨ x = s := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hs' : s ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hs
  have hkey : s ^ i = s ^ (i % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod i 2]
    rw [zpow_add, zpow_mul, hs', one_zpow, one_mul]
  rcases Int.emod_two_eq i with h | h
  · left; rw [← hi, hkey, h, zpow_zero]
  · right; rw [← hi, hkey, h, zpow_one]

/-- **Isaacs Cor 5.19 (一般形)** (p. 167): 非可換有限群 `G` の Sylow 2-部分群 `P` が
巡回部分群の直積で, そのうち 1 つが他の全てより真に大きいとき, `G` は単純でない.

Encoding (書籍強度以上): `A B ≤ ↥P` with `A ⊔ B = ⊤`, `A` cyclic, `2 ≤ |A| =: a`,
`B` の exponent が `a / 2` を割る (`hB_exp` — 書籍の「`A` が strict max cyclic 直積因子」
はこの形に落ちる). `P` abelian (`hPab`) は書籍では cyclic 直積分解から従うが, `B` の
内部構造を落とした encoding なので仮定に取る. `Disjoint A B` は証明に不要なので
仮定しない. 既存 `not_isSimpleGroup_of_isCyclic_sylow_two` は `B = ⊥` の特殊化.

**証明** (Isaacs p.167): `a = 2 ^ k` (`A ≤ P` は 2-group), `m := a / 2`. 生成元 `g` で
`A = ⟨g⟩`, `s := g ^ m` は位数 2. `P` abelian なので任意の `x = u * v` (`u ∈ A`,
`v ∈ B`) について `x ^ m = u ^ m * v ^ m = u ^ m ∈ ⟨s⟩` (`v ^ m = 1` は `hB_exp`).
`n ∈ N_G(P)` に対し `n s n⁻¹` は `P` の元 `n g n⁻¹` の `m` 乗ゆえ `⟨s⟩ = {1, s}` に
属し, 共役ゆえ `≠ 1`, よって `n s n⁻¹ = s` — つまり `s ∈ Z(N_G(P))`. Thm 5.18 強形
(`eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer`) で `s ∈ G' ⇒ s = 1`
だが `s ≠ 1`, ゆえ `G' ≠ ⊤`. `G` simple なら `G' ∈ {⊥, ⊤}` ⇒ `G' = ⊥` ⇒ `G` abelian
で `hG_nonab` と矛盾. -/
theorem not_isSimpleGroup_of_sylow_two_cyclic_strict_max_factor
    [Finite G] (hG_nonab : ¬ IsMulCommutative G) (P : Sylow 2 G) [P.FiniteIndex]
    [hPab : IsMulCommutative ↥(P : Subgroup G)]
    {A B : Subgroup ↥(P : Subgroup G)} [hA : IsCyclic ↥A]
    (hAB_top : A ⊔ B = ⊤)
    (ha : 2 ≤ Nat.card A)
    (hB_exp : ∀ x ∈ B, x ^ (Nat.card A / 2) = 1) :
    ¬ IsSimpleGroup G := by
  intro hSimp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- |A| = 2^k (A ≤ P は 2-group), 2 ≤ |A| ⇒ 2 ∣ |A|
  obtain ⟨k, hk_card⟩ := IsPGroup.iff_card.mp (P.isPGroup'.to_subgroup A)
  have h2_dvd : 2 ∣ Nat.card A := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero] at hk_card; omega
    · rw [hk_card]; exact dvd_pow_self 2 hkpos.ne'
  set m := Nat.card A / 2
  have hm2 : m * 2 = Nat.card A := Nat.div_mul_cancel h2_dvd
  have hm_ne : m ≠ 0 := by omega
  -- 生成元 g of A, gb := g in ↥P: A = zpowers gb, orderOf gb = |A|
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  set gb : ↥(P : Subgroup G) := (g : ↥(P : Subgroup G))
  have hA_eq : Subgroup.zpowers gb = A := by
    have htop : Subgroup.zpowers g = (⊤ : Subgroup ↥A) :=
      (Subgroup.eq_top_iff' _).mpr hg
    have hmap := MonoidHom.map_zpowers A.subtype g
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    rw [hmap]
    rfl
  have hgb_ord : orderOf gb = Nat.card A := by
    rw [← Nat.card_zpowers, hA_eq]
  -- s := gb ^ m は involution
  set s : ↥(P : Subgroup G) := gb ^ m with hs_def
  have hs_sq : s ^ 2 = 1 := by
    rw [hs_def, ← pow_mul, hm2, ← hgb_ord]
    exact pow_orderOf_eq_one gb
  have hs_ne_one : s ≠ 1 := by
    rw [hs_def]
    apply pow_ne_one_of_lt_orderOf hm_ne
    rw [hgb_ord]
    omega
  -- m 乗写像の像は zpowers s に落ちる (A ⊔ B = ⊤ + B は m 乗で潰れる)
  have h_pow_mem : ∀ x : ↥(P : Subgroup G), x ^ m ∈ Subgroup.zpowers s := by
    intro x
    have hx : x ∈ A ⊔ B := hAB_top.ge (Subgroup.mem_top x)
    have hx' : ∃ u ∈ A, ∃ v ∈ B, u * v = x := Subgroup.mem_sup.mp hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx'
    have huv : (u * v) ^ m = u ^ m * v ^ m := (Commute.all u v).mul_pow m
    rw [huv, hB_exp v hv, mul_one]
    rw [← hA_eq] at hu
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← hi, ← zpow_natCast (gb ^ i) m, ← zpow_mul, zpow_mul', zpow_natCast, ← hs_def]
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
  -- G 側へ: t := ↑s ∈ P, t ≠ 1
  have ht_inP : (s : G) ∈ (P : Subgroup G) := s.2
  have ht_ne_one : (s : G) ≠ 1 := fun h => hs_ne_one (OneMemClass.coe_eq_one.mp h)
  have hsG : (s : G) = (gb : G) ^ m := by
    rw [hs_def]; exact SubmonoidClass.coe_pow gb m
  have hts_sq : (s : G) ^ 2 = 1 := by
    rw [← SubmonoidClass.coe_pow, hs_sq, OneMemClass.coe_one]
  have h_pow_mem_G : ∀ y ∈ (P : Subgroup G), y ^ m ∈ Subgroup.zpowers ((s : G)) := by
    intro y hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (h_pow_mem ⟨y, hy⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have h1 := congrArg (fun z : ↥(P : Subgroup G) => (z : G)) hi
    simpa using h1
  -- ↑s ∈ Z(N_G(P)): 共役 n s n⁻¹ は P の元の m 乗 ⇒ ⟨s⟩ = {1, s} に属し ≠ 1 ⇒ = s
  have ht_central : ∀ n ∈ Subgroup.normalizer (P : Set G), n * (s : G) = (s : G) * n := by
    intro n hn
    have hw_inP : n * (gb : G) * n⁻¹ ∈ (P : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hn _).mp gb.2
    have h_conj_eq : n * (s : G) * n⁻¹ = (n * (gb : G) * n⁻¹) ^ m := by
      rw [conj_pow, hsG]
    have h_mem : n * (s : G) * n⁻¹ ∈ Subgroup.zpowers ((s : G)) := by
      rw [h_conj_eq]
      exact h_pow_mem_G _ hw_inP
    have h_ne_one : n * (s : G) * n⁻¹ ≠ 1 := by
      intro h0
      apply ht_ne_one
      have h2 : (s : G) = n⁻¹ * (n * (s : G) * n⁻¹) * n := by group
      rw [h0] at h2
      simpa using h2
    rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hts_sq h_mem with h1 | heq
    · exact absurd h1 h_ne_one
    · calc n * (s : G) = n * (s : G) * n⁻¹ * n := by group
        _ = (s : G) * n := by rw [heq]
  -- Thm 5.18 強形: ↑s ∈ G' なら ↑s = 1, だが ↑s ≠ 1 ⇒ ↑s ∉ G'
  have h_not_in_comm : (s : G) ∉ commutator G := fun h_in =>
    ht_ne_one
      (eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer P h_in ht_inP
        ht_central)
  -- endgame: G simple ⇒ G' ∈ {⊥, ⊤}; ⊤ は ↑s ∉ G' に反し, ⊥ は G abelian ⇒ 矛盾
  have h_comm_normal : (commutator G).Normal := inferInstance
  rcases hSimp.eq_bot_or_eq_top_of_normal _ h_comm_normal with h_bot | h_top
  · apply hG_nonab
    refine ⟨⟨fun x y => ?_⟩⟩
    have h_comm_mem : ⁅x, y⁆ ∈ commutator G := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h_bot, Subgroup.mem_bot] at h_comm_mem
    rwa [commutatorElement_eq_one_iff_mul_comm] at h_comm_mem
  · exact h_not_in_comm (by rw [h_top]; exact Subgroup.mem_top _)

end -- 5C

end OddOrder.Isaacs.Ch05
