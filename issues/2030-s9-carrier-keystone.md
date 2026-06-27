---
id: 2030
slug: s9-carrier-keystone
title: "Pf §9 Clifford counts (9.8)-(9.10) + Section11CharacterData redesign — W3 keystone"
created: 2026-06-27
---

# Pf §9 Clifford counts + `Section11CharacterData` redesign — the W3 keystone

> lane-b (W3). This is the **single deep keystone** the entire W3 frontier converges on: both
> on-path obligations — (10.8)`no_typeV` (via (10.7)) and **(11.8)** (the bare `feitThompson` sorry
> residual `card_kappaHall_lt_of_isTypeIIIorIV`) — bottom out here.

## 背景: W3 が単一 keystone に de-risk された (2026-06-27)

本セッションで **(10.8) の機械的・算術 spine 全体**を実証明 (§7 入力 + line 81→83 + line-87 算術 +
ℚ chain + closer; issue 2020 / `notes/peterfalvi/s12_10_8_noncoherence.md`)。(10.8)・(11.8) の残りは
正確に §9 Clifford 指標理論のみ。

## architectural finding (精密)

`S11.Section11CharacterData data chief` (`S11_MaximalII_III_IV.lean:1479`) は **scaffold-by-design**:
- subgroup/numeric field は constrained: `C ≤ U`, `Uprime ≤ U`, `Cprime ≤ C`, `u_eq_card_quotient`。
- **character field は全て FREE** (property field 無し): `X`, `S`, `XOf`, `SOf`, `H0CprimeSupport`,
  `tau`, および `Prop` の `quotientSemidirectFrobenius`。

ゆえに §9 指標カウント定理は**全て `sorry`** で、現 carrier に対しては genuine に証明不可
(free な `chars.SOf`/`chars.S` 等に量化しているため):
- (9.8) `caseA_character_counts` — `sorry` (S11:2505)
- (9.9) `caseB_character_counts` — `sorry` (S11:2516)
- (9.10) `exceptional_case_frobenius_realization` — `sorry` (S11:2532)
- (9.11) `coherent_H0C_commutator` — (6.8) に wired (witness `sibleyTarget_H0C` が `sorry`, §14-gated)

## なぜ両 W3 obligation を塞ぐか

- **(10.8) `hB` / (10.7) `typeII_derived_frobenius`**: Pf (10.7) 証明 (04.12 line 71) は partner の
  chief factor に (9.10)/(9.8.b)/(9.9.b) を cite。`[S,S]=H⋊U` Frobenius (ゆえ `|U|≥7`,
  `|S|=|H||U|w₂`, TI-counting `hB` の `G₁ ⊆ (H#)^G ∪ V^G`) がこれを要する。
- **(11.8) `exists_zeta_residual_not_orthogonal`**: `S(HC)=S₁` の materialize (定数次数 w₁ の
  `(u−1)/q` 既約、`(U/C)⋊W₁` Frobenius) + (9.8)/(9.9)/(9.11) を要する
  (`notes/peterfalvi/s13_11_8_orthogonality.md`)。
- **(7.8.b)** ((10.8) 最後の §7 gate、`Hypothesis78` for `(M,A(M))`, `H=M'`): その *family* `T` 列挙
  (`Hypothesis76.zeta : Fin (n+1) → …` の degree-ratio 構造) 自体が同じ §9 chief-factor Clifford
  構造に支配される。

## やること (research-grade, multi-session)

- [ ] **A: carrier 再設計** — character field を genuine 化 (`S = S(HC)` 等を kernel-restricted
      induced family + `data`/`chief` に紐づく property field で; または producer を持つ genuine な
      `S12.Hypothesis` + `ChiefFactorData` (S11:1408) に対して定義). `U` の chief factor `H̄=H/N`
      への作用とその既約成分が核心対象。**S11/S12/S13 consumer に波及する signature 変更ゆえ landing
      前に HUB 確認を検討** (cross-file)。
- [ ] **B: case-(b) (9.9)/(9.10)** — Singer field model (`Ū ⊂ 𝔽_{p^q}^×`)。既存の
      `chiefFactor_caseB_image_*` (S11:2092/2189/2376, unconditional: `|Ū| ∣ (p^q−1)/(p−1)`,
      `Coprime |Ū| (p−1)`) を活用。
- [ ] **C: case-(a) (9.8)** — `H̄ = ⊕ q` 個の order-`p` 因子 + `W₁`-置換カウント。
- [ ] **D: (9.11) `sibleyTarget_H0C`** 構造 witness。

## 完了条件

(9.8)/(9.9)/(9.10) が genuine な carrier に対し sorry-free。これで (10.7)→(10.8)`hB` と (11.8) の
§9 依存が外れ、W3 の両 on-path obligation が char-content 的に閉じうる状態になる。

## 参照

- carrier: `OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean:1479`; counts 2495/2507/2518;
  case-(b) Singer infra 2092/2189/2376; `ChiefFactorData` producer 1408。
- consumers: `S12.typeII_derived_frobenius` (5765), `S12.exists_zeta_residual_not_orthogonal` (~6580),
  S13 type III/IV。
- 原典: Pf §9 = `references/peterfalvi/04.11` + (9.7)-(9.11); (10.7) 証明 = `04.12` line 71。
- 関連: issue 2020, `notes/peterfalvi/s13_11_8_orthogonality.md`,
  `notes/peterfalvi/s12_10_8_noncoherence.md`。
