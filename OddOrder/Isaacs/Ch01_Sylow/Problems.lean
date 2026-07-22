/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow

/-!
# Isaacs Chapter 1 — Problems (演習問題)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 1 "Sylow Theory"
(pp. 1-44) の章末演習問題 (Problems 1A–1G) の Lean 化。

**scope 拡大** (issue 9205 ③ / campaign 1055、ユーザー裁定 2026-07-22): 従来の被覆測定
(`notes/isaacs/frontier_measured_2026_07_19.md`) は「番号付き結果のみ」で演習を対象外に
していたが、本ファイル以降で演習も形式化対象に加える。

## 方針 (CLAUDE.md ラッパー方針)

- mathlib / repo に直接対応がある演習は **docstring で対応を記録** (純粋リネームは書かない)。
- Isaacs の仮定形が mathlib と異なる (例: 「`p` より小さい素数が `|G|` を割らない」vs `minFac`)
  場合は **仮定変換の橋渡し補題**を書く (意味のあるラッパー例外)。
- それ以外は実証明。
-/

namespace OddOrder.Isaacs.Ch01

section /- Problems 1A: Group actions and counting (pp. 7-8) -/

/-- **Isaacs Problem 1A.1**. 有限群 `G` の素数指数 `p` の部分群 `H` について、
`p` より小さい素数が `|G|` を割らないならば `H ⊴ G`。

mathlib の `Subgroup.normal_of_index_eq_minFac_card` (指数 = `|G|` の最小素因数 ⟹ 正規) への
橋渡し: Isaacs の「`p` より小さい素数が `|G|` を割らない」仮定を `p = (Nat.card G).minFac` に
変換する (`p` は素数で `|G|` を割る ⟹ `minFac ≤ p`、仮定 ⟹ `p ≤ minFac`)。 -/
theorem normal_of_prime_index_of_no_smaller_prime {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hHp : H.index = p)
    (hsmall : ∀ q, q.Prime → q ∣ Nat.card G → p ≤ q) : H.Normal := by
  apply Subgroup.normal_of_index_eq_minFac_card
  have hdvd : p ∣ Nat.card G := hHp ▸ H.index_dvd_card
  have hcard1 : Nat.card G ≠ 1 := fun h1 => hp.ne_one (Nat.dvd_one.mp (h1 ▸ hdvd))
  rw [hHp]
  exact le_antisymm (hsmall _ (Nat.minFac_prime hcard1) (Nat.minFac_dvd _))
    (Nat.minFac_le_of_dvd hp.two_le hdvd)

/-- **Isaacs Problem 1A.9**. `|G| = p·m` で `p` は素数かつ `p > m` ならば、`G` は位数 `p` の
部分群をちょうど 1 つ持つ。

証明: `0 < m < p` ゆえ `p ∤ m`、よって `|G|` の `p`-部分は `p` ちょうど (`v_p(|G|) = 1`)、
Sylow `p`-部分群は位数 `p`。Sylow の個数 `nₚ ∣ [G:P] = m < p` かつ `nₚ ≡ 1 (mod p)` から
`nₚ = 1` ⟹ Sylow は一意。位数 `p` の部分群は必ず Sylow `p`-部分群ゆえ一意。 -/
theorem exists_unique_subgroup_card_eq_of_prime_gt {G : Type*} [Group G] [Finite G] {p m : ℕ}
    (hp : p.Prime) (hcard : Nat.card G = p * m) (hpm : m < p) :
    ∃! P : Subgroup G, Nat.card P = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  have hcardpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.mul_zero] at hcard; omega
    · exact h
  have hpm_ndvd : ¬ p ∣ m := Nat.not_dvd_of_pos_of_lt hm0 hpm
  have hfact : (Nat.card G).factorization p = 1 := by
    rw [hcard, Nat.factorization_mul hp.pos.ne' hm0.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self hp, Nat.factorization_eq_zero_of_not_dvd hpm_ndvd]
  have hPcard : Nat.card (P : Subgroup G) = p := by
    rw [Sylow.card_eq_multiplicity, hfact, pow_one]
  -- Sylow の個数 nₚ = 1
  have hnp : Nat.card (Sylow p G) = 1 := by
    have hPindex : P.index = m := by
      have h := Subgroup.card_mul_index (P : Subgroup G)
      rw [hPcard, hcard] at h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    have hdvd : Nat.card (Sylow p G) ∣ m := hPindex ▸ P.card_dvd_index
    have hlt : Nat.card (Sylow p G) < p := lt_of_le_of_lt (Nat.le_of_dvd hm0 hdvd) hpm
    have hmodeq : Nat.card (Sylow p G) % p = 1 % p := card_sylow_modEq_one p G
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp.one_lt] at hmodeq
  have hsub : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hnp).1
  refine ⟨(P : Subgroup G), hPcard, ?_⟩
  intro Q hQ
  have hQfact : Nat.card (Q : Subgroup G) = p ^ (Nat.card G).factorization p := by
    rw [hQ, hfact, pow_one]
  have hQP : Sylow.ofCard Q hQfact = P := Subsingleton.elim _ _
  rw [← Sylow.coe_ofCard Q hQfact, hQP]

end

/-! ## mathlib で被覆される演習 (docstring 記録、純粋ラッパーは書かない)

- **Problem 1A.6** (置換指標による軌道計数 = Burnside / Cauchy–Frobenius の補題):
  置換指標 `χ(g) = |{a | a·g = a}|` について `∑_{g∈G} χ(g) = n·|G|` (`n` = 軌道数) は
  mathlib の `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` そのもの
  (`Mathlib/GroupTheory/GroupAction/Quotient.lean`)。中間項 `∑_{a} |G_a|` との等式は
  orbit–stabilizer から従う。

- **Problem 1A.8** (Cauchy の定理): 素数 `p ∣ |G|` ⟹ `G` は位数 `p` の元を持つ、は mathlib の
  `exists_prime_orderOf_dvd_card`。McKay の証明 (`ℤ/p` が `x₁⋯xₚ=1` なる `p`-組の集合に
  巡回シフトで作用し、不動点 = 対角 `(x,…,x)` with `xᵖ=1`) が、まさに mathlib の証明戦略。
  位数 `p` の元の個数 `≡ -1 (mod p)` の精緻化は本ファイルの 1A.9 で使う。
-/

end OddOrder.Isaacs.Ch01
