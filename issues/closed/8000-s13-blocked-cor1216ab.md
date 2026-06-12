---
id: 8000
slug: s13-blocked-cor1216ab
title: "§13 blocker: Cor 12.16(a)(b) statement が S12_E に未露出 (§13 全体が gate)"
created: 2026-06-12
---

# §13 blocker: Cor 12.16(a)(b) statement が S12_E に未露出 (§13 全体が gate)

## ✅ CLOSED (2026-06-13): de-axiom 完了

Lane F が issue 0065 で S12_E に faithful sorry'd statement
(`sigma_subgroup_pRank_normalizer_le_one` / `sigma_subgroup_not_mem_primeFactors_derived_of_tau1`,
commit `e876f29b`) を露出 → main 同期後、G が forward axiom 2 本
(`cor1216_pRank_normalizer_le_one` / `cor1216_not_mem_primeFactors_derived_of_tau1`) を削除し
cite 先を S12_E の 2 定理へ差し替え (de-axiom handshake step 2)。Lemma 13.1・Cor 13.2 とも
**新規 axiom 0**、footprint は `[propext, sorryAx, Classical.choice, Quot.sound]`
(sorryAx は S12_E Cor 12.16 由来 = repo 標準 scaffold-sorry)。AxiomsCheck の cor1216 island 削除、
13.1(a) は S12_E 非依存ゆえ `#assert_only_allowed_axioms` 維持。full build + AxiomsCheck green。
**HOLD 解消**: G の forward axiom が消えたので merge ブロッカー無し。

## 背景

Lane G (`bg-s13`) の着工前 STATEMENT AUDIT (LAUNCH.md 手順 3) で発覚。

§13 は **全結果が Lemma 13.1 を根に持つ DAG** (13.1 → Cor 13.2 → Cor 13.3 / Thm 13.4 → … →
13.5/13.6/13.7/13.8/13.9/13.10/13.11)。Cor 13.2 は mmd L3554「our assertions follow directly
from Lemma 13.1」で 13.1 に完全依存し、以降全結果が 13.2 か 13.4 を経由する。

**Lemma 13.1** (mmd L3528, 3 結論 (a)(b)(c)) の証明 (mmd L3534-3546) は BG **Corollary 12.16(a)
と (b)** を本質的に使う:
- (b) `p ∉ τ₂(M*)`: 「`r_p(N_{M*}(Y))=2` ∧ `p∉β(G)` (Lemma 12.1(g)) は **Cor 12.16(a)**
  (`r_p(N_H(Y))≤1`) に矛盾」(mmd L3538)。
- (c) `p∈τ₁(M) ⟹ p∈β(G)`: 「`p∈π(N_{M*}(Y)')` ゆえ **Cor 12.16(b)**
  (`p∈τ₁(M) ⟹ p∉π(N_H(Y)')`) の対偶が (c) を与える」(mmd L3540)。
- (a) も `p∈σ(M*)∪τ₃(M*)` (= (b) で τ₂ 除外して得る) に依存し、Sylow `S⊆M*'` を使うので
  (b) 経由。**13.1 の 3 結論すべてが 12.16(a) を要する。**

## 問題 (ズレ)

repo に **Cor 12.16(a)/(b) の statement が存在しない** (grep 確認済)。

- `S12_E.lean:64` `sigma_subgroup_conj_into_Msigma` は docstring が「**BG Corollary 12.16(a)**」
  だが、実際に述べているのは mmd Cor 12.16 の**前置節**「`Y` is conjugate to a subgroup of `M_σ`」
  (`∃ g ∈ M, Y^g ≤ M_σ`) のみ。BG が (a)/(b) と番号付けする **rank bound / π-bound は未述**。
  → **誤ラベル + 不完全** (statement 自体は前置節として faithful・unsound ではない)。
- `S12_E.lean:29` のコメントも「Corollary 12.16(b) remains a deferred proof obligation」と認める。

依存ポリシー上、§13 は §12 の sorry'd statement を cite してよいが、**cite すべき statement が
無い**。新規 forward axiom 禁止・S12_E 編集禁止・実 sorry 増加禁止のため、Lane G 単独では
unblock 不能。→ LAUNCH.md「§12 側に補題が欲しくなったら issue 起票 + hub に依頼」に従い起票。

## 解消方針 (2026-06-12 ユーザー裁可: **forward axiom で即着工**)

`S13_Lemma131.lean` に Cor 12.16(a)(b) を **provisional forward axiom** として宣言
(`cor1216_pRank_normalizer_le_one` / `cor1216_not_mem_primeFactors_derived_of_tau1`、
user-approved 2026-06-12)。G はこれを cite して §13 を実証明する。**Lane F が S12_E に
faithful な statement (下記「提案署名」) を入れ次第、本 axiom を de-axiom し cite 先を
S12_E へ差し替える** (この issue は de-axiom 完了で closed)。本 axiom を使う §13 定理は
`AxiomsCheck.lean` の `#assert_axioms_island … expecting [cor1216_…]` で pin する。

## やること

- [ ] S12_E (または §12 leaf) に **BG Cor 12.16(a)/(b) の faithful な statement を追加** (proof は
      `sorry` でよい — G は black box として cite する)。下記「提案署名」参照。実施 owner は
      **hub / Lane F** (S12_E は Lane F の active ファイル; G は編集禁止)。
- [ ] (副次) Cor 12.14 `maximalContaining_centralizer_eq_singleton` に `ℳ(P) = {M}`
      (P = Sylow p of M_σ) 結論を追加 — Lemma 13.6 (mmd L3608) が `ℳ(C_G(X))=ℳ(S)={M}` の
      `ℳ(S)` 側に要する。現状 `ℳ(C_G(X))={M}` のみ。**13.6 着工時まで遅延可**。
- [ ] (任意) `sigma_subgroup_conj_into_Msigma` の docstring「12.16(a)」表記を「Cor 12.16 前置節」へ
      訂正 (混乱回避)。

## 提案署名 (drop-in spec; 正確な repo idiom は S12_E 側で調整)

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

(注: H ∈ ℳ(Y) と N_H(Y) の正確な型は S12_E の `maximalSubgroupsContaining` / `pRank` 慣用に
合わせること。`pRank ↥M p = 2` の用例 = `S12_Lemma1211.lean:301`。)

## 完了条件

- 上記 Cor 12.16(a)(b) の statement が repo に存在し (sorry'd 可)、Lane G が `exact`/`apply` で
  cite して Lemma 13.1 を証明できる。
- `lake build` 緑・実 sorry 数 net 不変 (statement 2 個 sorry'd 追加なら +2; ただし proof 進行で
  相殺される設計)。

## 参照

- 監査記録: `notes/bg/s13_prime_action.md`「2026-06-12 Lane G session 1: STATEMENT AUDIT」
- mmd: `references/bg/local-analysis.mmd` L3453-3476 (Cor 12.16), L3528-3546 (Lemma 13.1)
- repo: `S12_E.lean:64` (誤ラベル 12.16(a)), `:29` (deferred obligation コメント),
  `S12_ECore.lean:487` (Lemma 12.1(g)), `S13_PrimeAction.lean:34` (scaffold dep note)
