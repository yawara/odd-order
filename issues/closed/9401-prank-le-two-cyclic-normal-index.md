---
id: 9401
slug: prank-le-two-cyclic-normal-index
title: "pRank ≤ 2 from a cyclic subgroup of index ≤ p"
created: 2026-07-20
---

# shared-infra claim (lane c): `pRank C p ≤ 2` from a cyclic subgroup of index `≤ p`

## 求める形

```lean
theorem pRank_le_two_of_isCyclic_of_index_le_prime
    {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    {K : Subgroup C} (hK : IsCyclic ↥K) (hidx : K.index ≤ p) :
    pRank C p ≤ 2
```

置き場所 = `OddOrder/GroupTheory/PRank.lean` (pRank API の topical home、BG 内容ゼロ)。

## 既存検索の結果 (2026-07-20 実測、重複なし)

`pRank ... ≤ 2` を**結論**する既存定理は 8 件あるが、いずれも別の仮説から:

| 既存 | 仮説 |
|---|---|
| `S04_SmallRankBasic.normalAbelian_pRank_le_two_of_scn3_empty` | `SCN₃(R) = ∅` |
| `S04d_GorThm415.pRank_le_two_of_scn3_empty` | 同上 (**G** 5.4.15) |
| `S05_NarrowSCN.pRank_centralizer_le_two_of_maximalElementaryAbelian_card_prime_sq` | 極大 elem.ab. の位数 `p²` |
| `S04g_Thm418.pRank_{sylow_,}le_two_of_sylow_le_fitting` | Sylow ≤ F(G) |
| `S12_ECore.pRank_{M_,}le_two` | `SubgroupESetup` |
| `S09_Lemma95.pRank_opiCoreInG_singleton_le_two_of_rank_le_two` | `rank ≤ 2` |

⟹ 「cyclic 部分群 + 指数 ≤ p」からの版は**無い**。

## 証明 (交叉と積公式だけ、mathlib API で閉じる)

`E ≤ C` を elementary abelian とする。

1. `E ⊓ K ≤ K` は cyclic、かつ `≤ E` ゆえ指数 `p` ⟹ **`|E ⊓ K| ≤ p`**
   (生成元 `g` に `g ^ p = 1` ⟹ `orderOf g ∣ p`)。
2. `Subgroup.card_HK_mul_card_inf_eq_card_mul_card E K`:
   `|↑E * ↑K| · |E ⊓ K| = |E| · |K|`。左の集合は `C` の部分集合ゆえ `|↑E * ↑K| ≤ |C|`。
3. `|C| = K.index · |K|` かつ `K.index ≤ p` ⟹ `|C| ≤ p · |K|`。
4. ⟹ `|E| · |K| ≤ p · |K| · p` ⟹ **`|E| ≤ p²`** (`|K| > 0` で約分)。
5. `Nat.log p |E| ≤ Nat.log p (p^2) = 2` ⟹ `pRank_le_iff` で閉じる。

⚠ 積公式は**集合積のまま**使うので `K` の normal 性は**不要** (特殊化債務を作らない)。

## 消費者

- issue 3021 / BG App.E E.3(b): `pRank ↥(C_R(R₀)) p ≤ 2`。
  `C_R(R₀) = R₀ ⊔ R₁` (`|R₀| = p`, `R₁` cyclic, `Disjoint R₀ R₁`) に適用し、
  `R₁.subgroupOf C` を `K` に取る (`index = p`)。
  BG の 1 行「Since `C_R(R₀) = R₀ × R₁`, we have `R₀ ∩ Z = 1`」の実質。
- 将来: BG §4/§5 の narrow 機構は同型の rank 評価を多用するので 2 消費者目は出やすい。

## 状態 — ✅ 完了 (2026-07-20)

- [x] `PRank.lean:666` に `pRank_le_two_of_isCyclic_of_index_le_prime` として追加、leaf build green
      (`normal` 仮説は予定どおり不要と確認して落とした)。
- [x] AppE の `RegularOperatorSetup.pRank_centralizer_R₀_le_two` から消費
      (`K = R₁.subgroupOf C_R(R₀)`、`index = p` は `card_centralizer_R₀` から)。
- [x] AxiomsCheck 登録済。

⚠ 実装上のメモ: `Nat.card (↑E * ↑K : Set G)` は `open scoped Pointwise` が要る
(`PRank.lean` は元々 open していないので宣言直前に `open scoped Pointwise in` を置いた)。
