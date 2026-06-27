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

## 2026-06-27 lane-b (W3): task A の character-family 部分 COMPLETE (commit `9c41978a`)

**`Section11CharacterData` の character field を genuine 化** (full build 3884 green)。issue 冒頭の
「character field は全て FREE → §9 counts は genuine に証明不可」を直接解消した:

- **genuine families 新規** (S11, all sorry-free, `S12.inducedFamily` パターン):
  `huSub` (HU=H⊔U を ↥M 内に realise) / `hInHu` (H の HU 内表現) / `xiSet` (𝒳={χ∈Irr(HU)|H⊄Ker χ}) /
  `xiOf` (𝒳(Y)={χ∈𝒳|Y⊆Ker χ}) / `induceHU` (Ind_{HU}^M, canonical Invertible bake-in で desync 回避) /
  `induceHU_apply_one` (degree [M:HU]·χ(1)) / `sSet` (𝒮=Ind 𝒳) / `sOf` (𝒮(Y)=Ind 𝒳(Y))。
  基礎 API: `xiOf_subset_xiSet`/`mem_xiOf`/`xiOf_antitone`/`mem_sSet`/`mem_sOf`/`sOf_subset_sSet`/`sOf_antitone`。
- **carrier 再設計**: free な `X`/`S`/`XOf`/`SOf` field を削除 → genuine namespace defs
  (`X=xiSet`,`XOf=xiOf`,`S=sSet`,`SOf=sOf`) + `X_eq`/`XOf_eq`/`S_eq`/`SOf_eq` (rfl simp)。
  ⟹ (9.8)/(9.9)/(9.10) と (9.11) coherence consumer は Peterfalvi の **honest families** を参照
  (以前は free field ゆえ原理的に証明不能)。consumer (S12 `typeII_section11_coherence`,
  `sibleyTarget_H0C`) は `chars.S`/`tau`/`H0CprimeSupport` のみ使用で signature 不変、producer 不在ゆえ
  field 削除も安全。

**残 task A (carrier の部分群)**: `C=C_U(H̄)` (= U-action map `(quotientMulAutHom chief.N_aInvariant).comp
(U.subgroupOf(U⊔W1)).subtype` の `MonoidHom.ker` を G の部分群へ map-down、`u_eq_card_quotient` の range
と双対) / `Uprime=[U,U]=derivedInG U` / `Cprime=[C,C]=derivedInG C` を free field → genuine def 化。
counts が `chars.C`/`chars.Uprime`/`chars.Cprime` に量化するため、これらを pin しないと (9.8)/(9.9) は
genuine families に対しても未証明。pinning 自体は count を unlock しない (count は下記 B/C の deep Clifford)
が、count 証明の prerequisite。**fiddly だが honest-architecture prerequisite、次 brick**。

## やること (research-grade, multi-session)

- [x] **A (character-family 部分)**: families genuine 化 + carrier 再設計 (commit `9c41978a`)。
- [ ] **A (subgroup 部分)**: `C`/`Uprime`/`Cprime` を genuine def 化 (上記)。
- [ ] **B: case-(b) (9.9)/(9.10)** — Singer field model (`Ū ⊂ 𝔽_{p^q}^×`)。既存の
      `chiefFactor_caseB_image_*` (unconditional: `|Ū| ∣ (p^q−1)/(p−1)`, `Coprime |Ū| (p−1)`) を活用。
      (9.9.a) の `u ∣ qu` は `dvd_mul_left` で trivial、残りは Clifford。
- [ ] **C: case-(a) (9.8)** — (9.8.a) `a ∣ χ(1)` = Clifford 誘導 (irred component θ of Res_H χ,
      χ=Ind_{I(θ)∩HU}, I(θ)∩U⊆C_U(H_i) ゆえ a=|U:C_U(H_i)| ∣ χ(1)); (9.8.b,c) = (8.4.d)+(4.5)/(4.7)
      Dade for L=M/H₀; (9.8.d) = degree-qa 構成。Clifford 誘導は `Clifford.lean`/`InducedIrreducible.lean`
      (`IrreducibleCharacter.LiesOver`/inertia) を要する deep multi-step。
- [ ] **D: (9.11) `sibleyTarget_H0C`** 構造 witness。

## 完了条件

(9.8)/(9.9)/(9.10) が genuine な carrier に対し sorry-free。これで (10.7)→(10.8)`hB` と (11.8) の
§9 依存が外れ、W3 の両 on-path obligation が char-content 的に閉じうる状態になる。

## 参照

- carrier: `OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean` `Section11CharacterData` (~1578);
  genuine families `xiSet`/`xiOf`/`sSet`/`sOf` (~1486-1570); counts `caseA_character_counts`(~2626)/
  `caseB_character_counts`(~2638)/`exceptional_case_frobenius_realization`(~2651);
  case-(b) Singer infra `chiefFactor_caseB_image_*` (~2092/2189/2376); `ChiefFactorData` producer
  `exists_chiefFactorData` (~1406)。
- consumers: `S12.typeII_derived_frobenius` (5765), `S12.exists_zeta_residual_not_orthogonal` (~6580),
  S13 type III/IV。
- 原典: Pf §9 = `references/peterfalvi/04.11` + (9.7)-(9.11); (10.7) 証明 = `04.12` line 71。
- 関連: issue 2020, `notes/peterfalvi/s13_11_8_orthogonality.md`,
  `notes/peterfalvi/s12_10_8_noncoherence.md`。
