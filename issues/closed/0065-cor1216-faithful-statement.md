---
id: 65
slug: cor1216-faithful-statement
title: "BG Cor 12.16(a)(b) faithful statement を S12_E に追加 (G de-axiom 用)"
created: 2026-06-12
owner: Lane F (bg-s12)
---

# BG Cor 12.16(a)(b) faithful statement を S12_E に追加 (G de-axiom 用)

## ✅ F 側完了 (2026-06-12)

S12_E.lean に 2 statement を追加 (sorry'd, build 緑, full build 3780):
- `sigma_subgroup_pRank_normalizer_le_one` (Cor 12.16(a): `r_p(N_H(Y)) ≤ 1`)
- `sigma_subgroup_not_mem_primeFactors_derived_of_tau1` (Cor 12.16(b): `p ∉ π(N_H(Y)')`)

drop-in 署名から `maximalSubgroupsContaining Y` (Subgroup 引数; 元の `(Y : Set G)` は型誤り) に
修正。それ以外は issue 通り。BG 原文 (mmd L3453-3456) と照合し faithful 確認済み。
**G は main 同期後、forward axiom 2 本をこの 2 定理の cite に置換可能** (de-axiom handshake step 2)。
本 issue は G の de-axiom + issue 8000 closed まで open のまま。

## ✅ G 側完了 (2026-06-13, Lane G)

main 同期後、G が forward axiom 2 本を削除し cite 先を上記 2 定理へ差し替え (de-axiom 完了)。
Lemma 13.1・Cor 13.2 とも新規 axiom 0、issue 8000 closed。**残るは F の本体 proof**
(S12_E の 2 sorry を §12 cascade で埋める) — それで §13 が自動 unconditional 化。F が proof 完了時に
本 issue を closed へ。

## 依頼者・経緯

**hub → Lane F への依頼** (2026-06-12, ユーザー指示)。

Lane G (`bg-s13`, §13) は Lemma 13.1 を **BG Corollary 12.16(a)(b)** に依存して証明したが、
着工前 STATEMENT AUDIT (issue 8000) で **S12_E に 12.16(a)/(b) の faithful な statement が
存在しない**と判明した:

- `S12_E.lean:64` `sigma_subgroup_conj_into_Msigma` は docstring が「Cor 12.16(a)」だが、
  実際に述べているのは mmd Cor 12.16 の**前置節**「Y is conjugate to a subgroup of M_σ」のみ。
  BG が (a)/(b) と番号付けする **rank bound `r_p(N_H(Y))≤1` / π-bound `p∉π(N_H(Y)')` は未述**。

そのため G は暫定的に **forward axiom** 2 本を宣言して §13 を進めた
(`cor1216_pRank_normalizer_le_one` / `cor1216_not_mem_primeFactors_derived_of_tau1`,
issue 8000, ユーザー裁可)。**この forward axiom があるため G は現在 hub で auto-merge されず
HOLD 中** (G は Lemma 13.1 ASSEMBLY COMPLETE まで到達済みだが main に載らない)。

## 依頼内容 (Lane F)

**S12_E (または §12 leaf) に BG Cor 12.16(a)/(b) の faithful な statement を追加**してほしい。
**証明は `sorry` でよい** — これは BG Cor 12.16 の実 §12 内容で、full proof は F の cascade の
中で後から埋めればよい。**まず statement を main に載せることが G の unblock に直結する**ので、
12.12 の合間に先行して入れてほしい (小タスク: 2 個の sorry'd theorem)。

### drop-in 署名 (issue 8000 より; 正確な repo idiom は S12_E 側で調整)

```lean
-- BG Corollary 12.16(a) (mmd L3453-3456):
-- Y は G の非自明 σ(M)-部分群, p ∈ π(E) ∩ β(G)', H ∈ ℳ(Y) は M と非共役 ⟹ r_p(N_H(Y)) ≤ 1.
theorem sigma_subgroup_pRank_normalizer_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining (Y : Set G))
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p ≤ 1 := by
  sorry

-- BG Corollary 12.16(b) (mmd L3453, 3456): 同設定 + p ∈ τ₁(M) ⟹ p ∉ π(N_H(Y)').
theorem sigma_subgroup_not_mem_primeFactors_derived_of_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    (hpτ1 : p ∈ tau1 M)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining (Y : Set G))
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    p ∉ (Nat.card ↥(derivedInG (H ⊓ Subgroup.normalizer (Y : Set G)))).primeFactors := by
  sorry
```

(注: `H ∈ ℳ(Y)` と `N_H(Y)` の正確な型は S12_E の `maximalSubgroupsContaining` / `pRank` 慣用に
合わせること。`pRank ↥M p = 2` の用例 = `S12_Lemma1211.lean:301`。名前は明快なら多少変えてよい
— **G が de-axiom 時に cite 名を合わせる**。)

## ⚠ hub 向け注意 (sorry ゲートの例外扱い)

この依頼で F が入れる statement は **意図的に sorry'd (+2 実 sorry)**。hub の merge-monitor は
通常「sorry 増 = abort」だが、**この 2 件は faithful scaffold ゆえ例外的に合流を許可する**
(forward axiom を sorry'd theorem に置換する方向 = 健全化)。hub は F の commit が本 issue の
2 statement であることを確認の上、+2 を許容してマージする。

## de-axiom ハンドシェイク (完了後)

1. **F**: 上記 2 statement を S12_E に追加 (sorry'd) → commit → hub が +2 許容で main 合流。
2. **G**: main 同期後、`axiom cor1216_pRank_normalizer_le_one` →
   `S12...sigma_subgroup_pRank_normalizer_le_one` の cite に置換、同様に (b)。
   ⟹ **G の forward axiom 2 本が消滅** → G が auto-merge 可能になり HOLD 解除。
3. issue 8000 / 本 issue とも de-axiom 完了で closed。

## 完了条件

- S12_E に Cor 12.16(a)/(b) の faithful statement が存在 (sorry'd 可)、`lake build` 緑。
- G が `exact`/`apply` で cite して forward axiom を除去できる署名になっている。

## 参照

- issue 8000 (`issues/8000-s13-blocked-cor1216ab.md`, G 側; bg-s13 branch)
- mmd: `references/bg/local-analysis.mmd` L3453-3476 (Cor 12.16)
- repo: `S12_E.lean:64` (前置節のみ・誤ラベル), `S12_Lemma1211.lean:301` (`pRank=2` 用例)

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

Cor 12.16(a)(b) proven: 専用 leaf `S12_Corollary1216.lean` (S12_E から移動) が実 sorry 0 (検証 2026-07-02)。
