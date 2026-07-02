---
id: 8008
slug: lemma151-gated-upstream
title: "typeP_auxiliary_structure_gated — Lemma 15.1 の §14/§12 cross-lane gate"
created: 2026-06-15
---

# typeP_auxiliary_structure_gated — Lemma 15.1 の §14/§12 cross-lane gate

## 背景

BG Lemma 15.1 (`typeP_auxiliary_structure`, S15_MF) は conjuncts 3,4 + assembly を proven
(`97d2efe1`)。substantive content は forward lemma `typeP_auxiliary_structure_gated`
(S15_MF:682, sorried) に isolate 済。これを埋めるには **未形式化の cross-lane upstream** が要る:

- **§14 `M' = U M_σ`** (Thm 14.7(h) の specific 分解形): 現 `typeP_duality` は K-complement 形
  (`IsComplement' (derivedInG M) K`) のみ露出、`M' = U⊔M_σ` は未露出。**Lane H に露出要請**
  (Cor 15.6 の Thm 14.7(h) 露出 = issue 8006 と同型)。
- **§14 Corollary 14.3** (σ'-元が M_σ# を centralize ⟹ κ or τ₂; conjunct 6 の核): repo に
  未形式化(grep 不発)。**Lane H 領域**。
- **§12 Theorem 12.12(a)(b)** (C_E(S)=E 構造 / A_0 abelian / E_0 Frobenius; conjuncts 7,8 の核):
  repo に未形式化(grep 不発)。**§12 領域**。conjunct 8 K≠⊥ は componentwise Frobenius 構成も要す
  (notes/bg/s15_1_chatgpt_answer.md 参照)。

## やること

- [ ] Lane H: `typeP_duality` (or 別 §14 補題) に `K≠⊥ → M' = U⊔M_σ` を露出。
- [ ] Lane H: Cor 14.3 を形式化(or cite 可能な等価を露出)。
- [ ] §12: Thm 12.12(a)(b) を形式化。
- [ ] それらが揃ったら `typeP_auxiliary_structure_gated` の sorry を埋める(notes の per-conjunct
  plan に従う)。conjunct 8 K≠⊥ の componentwise 構成は要手当て。

## 完了条件

`typeP_auxiliary_structure_gated` の sorry が消え、`typeP_auxiliary_structure` (Lemma 15.1) が
cite 先のみ(proven upstream)に gated な本体になる。

## 参照

- 検証済証明: `notes/bg/s15_1_chatgpt_answer.md` (ChatGPT Pro 拡張, per-conjunct)。
- mmd Lemma 15.1 = L4166 (proof L4174)。
- 同型先例: issue 8006 (Thm 14.7(h) 露出要請, Lane H が `1243d4c6` で対応)。
- **広い文脈**: §15 deep core (Lemma 15.1, Thm 15.2) はすべて cross-lane-gated
  (§3 Lane A / §12 / §14 Lane H)。Lane G の genuinely-closeable §15 は connective + M_F Hall で尽きた。

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

gate 全解消・証明済: `typeP_auxiliary_structure_gated` (S15_MF.lean:1640) proven、AxiomsCheck.lean:4248-4249 に
assert 登録 (検証 2026-07-02)。
