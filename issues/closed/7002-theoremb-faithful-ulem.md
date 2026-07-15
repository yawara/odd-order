---
id: 7002
slug: theoremb-faithful-ulem
title: "BG theoremB hU に U≤M 欠落 + B(1) ∀p:ℕ 過剰一般化 — faithful 化して B(1) 配線"
created: 2026-06-16
---

# BG theoremB hU に U≤M 欠落 + B(1) ∀p:ℕ 過剰一般化 — faithful 化して B(1) 配線

`OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean`。

## 背景

2026-06-16 の cite-closable §16 監査で、BG Theorem B の第1 conjunct「Every Sylow subgroup of
U is abelian of rank ≤ 2」(mmd L4373) を §12 cite のみで sorry-free 化できると判明し、
standalone 補題 `theoremB_U_sylow_abelian_rank_le_two` (commit `3b8ec0a4`) を landing 済み。
ただし endpoint `theoremB_U_and_A_tame` (`S16_MainResults.lean:167`) の statement に
**2 つの faithfulness 欠陥**があり、そのままでは B(1) を直接配線できない。

### 検出された statement 欠陥

1. **`U ≤ M` 欠落**: theoremB の仮説は `hU : IsHallSubgroup ((κ∪σ)ᶜ) (U.subgroupOf M)` のみ。
   `U.subgroupOf M` の Hall 性は `U ≤ M` を導かない (U が M からはみ出していてもよい)。
   §12 の supporting-subgroup reduction (`exists_subgroupESetup_with_le`, M 内で動く) は
   `U ≤ M` を要求。mmd では `U ⊆ M` は `M = K U M_σ` 設定の一部で foundational。
   → theoremA (`:143`) / theoremC (`:185`) も同じ `hU` パターンで `U≤M` を持たない (同型バグ)。
2. **`∀ p : ℕ` 過剰一般化**: B(1) conjunct は `∀ p : ℕ, ∀ P, P≤U → IsPGroup p P → …` と
   素数性を課さない。"Sylow subgroup" = 素数 p-群。合成数 p では `IsPGroup p P` を
   非可換 `{q,r}`-群 (奇数位数でも Frobenius `7⋊3` 等) が満たすため、abelian 主張が **false**。
   faithful 形は `∀ p, p.Prime → …`。

## やること

- [ ] theoremB の署名に `(hUM : U ≤ M)` を追加 + B(1) conjunct を `∀ p, p.Prime → …` に修正
      (theoremA/C も同様に揃えるか要検討)
- [ ] consumer 修正: `S16_MainResults.lean:635` / `:687` が `(theoremB … hG hM hU).2.2.2.2` (=B(5))
      を消費。`hUM` 追加で両 call site (= `theoremII_tame_embedding` 内) が `U ≤ M` を供給する必要
      → 当該文脈で取れるか確認 (取れなければ threading)
- [ ] B(1) conjunct を `theoremB_U_sylow_abelian_rank_le_two hG hM hUM hU` で discharge
      (残り B(2)-B(5) は §14/§15 gated ゆえ theoremB の sorry は残る = 部分 discharge)

## 完了条件

theoremB が faithful 署名 (hUM + p.Prime) になり、B(1) conjunct が `theoremB_U_sylow_abelian_rank_le_two`
で discharge され、consumer (635/687) と full build + AxiomsCheck が green。

## 参照

- 補題: `theoremB_U_sylow_abelian_rank_le_two` (`S16_MainResults.lean`, commit `3b8ec0a4`)
- トリガー: §14 (Lane H) / §15 (Lane G) landing 後の theoremB 本格証明時、または faithfulness 整備の独立タスク
- 同種の triviality/over-claim バグ前例: Cor 15.3 / Thm A(3) / Cor 15.4 (Lane G, `notes/bg/s15_16_audit.md` §6)
