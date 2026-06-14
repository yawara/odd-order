---
id: 8002
slug: cor1214-faithful-sylow
title: "S12 Cor 12.14 faithful化: ℳ(Sylow q of M_σ)={M} を expose (BG Lemma 13.6 用)"
created: 2026-06-14
---

# S12 Cor 12.14 faithful化: ℳ(Sylow q of M_σ)={M} を expose (BG Lemma 13.6 用)

## 背景

BG Lemma 13.6 (`S13_PrimeAction.maximalContaining_eq_singleton_of_E1`) の結論は
`ℳ(C_G(X)) = ℳ(S) = {M}` (S = M_σ の Sylow q-部分群)。証明冒頭は
「By Corollary 12.14, we can assume q∉β(M) and X⊄M_σ'」= **Cor 12.14 が
q∈β(M)∨X⊆M_σ' の場合に結論 (両 conjunct) を直接供給**する reduction。

ところが repo の `S12_Corollary1214.maximalContaining_centralizer_eq_singleton`
は **`ℳ(C_G(X)) = {M}` のみ**を結論し、原典 BG L3401 の `= ℳ(P) = {M}`
(P = M_σ の Sylow) を脱落している。Lemma 13.6 はこの Sylow 部分を要する。

## 核心観察 (再調査不要)

repo の Cor 12.14 証明は統一エンジン
`suffices ∃ U, IsUniquelyMaximal U ∧ U ≤ C_G(X) ∧ U ≤ M` で進む。
**この witness U は全ケースで `U ≤ S` を既に満たす** (S = 証明内で構成される
M_σ の Sylow p, line 130):

- central-product ケース (line 317): U = P₁、`hP₁S : P₁ ≤ S`。
- rank ≥ 3 ケース (line 391): U = CPX = C_G(X) ⊓ S、`inf_le_right : CPX ≤ S`。

よって `suffices` に `U ≤ S` を 1 つ足すだけで `ℳ(S)={M}` が同じ witness から出る。
private consumer `eq_singleton_of_uniquelyMaximal_le` は `C_G(X)` を任意 `Y` に
一般化すれば ℳ(S) にも流用可 (証明本体は字面が変わるだけ)。

## やること

- [ ] §12 (`S12_Corollary1214.lean`, 最小追加 — **S12_E は触らない**):
  - [ ] private `eq_singleton_of_uniquelyMaximal_le` を `{Y U M}` に一般化 (C_G(X)→Y)
  - [ ] hSMσ (S≤M_σ) を rcases 前に hoist (両ブランチで使う)
  - [ ] `suffices` を `… ∧ U ≤ (S:Subgroup G) ∧ U ≤ M` に強化、witness 2 箇所に U≤S 追加
  - [ ] 新 theorem `maximalContaining_centralizer_and_someSylow_eq_singleton`:
        `ℳ(C_G(X))={M} ∧ ∃ S₀, X≤S₀ ∧ S₀≤M_σ ∧ IsPGroup p S₀ ∧ (Sylow-maximality) ∧ ℳ(S₀)={M}`
  - [ ] 旧 `maximalContaining_centralizer_eq_singleton` は `(… ).1` の 1 行 projection に
        (型不変 → AxiomsCheck 登録不変)
  - [ ] AxiomsCheck.lean に新 theorem 登録
- [ ] §13 (`S13_PrimeAction.lean`, Lemma 13.6 内): conjugacy transfer
      (任意の Sylow q of M_σ `S` と内部 S₀ は M_σ-共役 → ℳ(S)=ℳ(S₀)^m={M}; m∈M_σ≤M)。
      ℳ-conj-equivariance の idiom は `S12_Corollary1216.lean:355` を参照。

## 完了条件

`maximalContaining_eq_singleton_of_E1` の Cor 12.14 reduction 部 (q∈β∨X⊆M_σ' 分岐) が
新 §12 theorem + transfer で埋まり、build-green。残りの contradiction 分岐 (q∉β∧X⊄M_σ')
は別途 (issue 8003 予定)。

## 参照

- BG L3399-3413 (Cor 12.14), L3604-3624 (Lemma 13.6)
- `S12_Corollary1214.lean:47` (consumer), `:130` (Sylow 構成), `:150` (suffices),
  `:317`/`:391` (witness sites)
- `S12_Corollary1216.lean:355` (ℳ conj-equivariance idiom)
