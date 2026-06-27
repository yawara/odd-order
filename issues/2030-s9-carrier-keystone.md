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

## 2026-06-27 lane-b (cont.): task A 完了 (subgroups genuine 化) + 文字基盤 (commits `153e866a`+本)

- **subgroup genuine 化** (commit `153e866a`): carrier の free な `C`/`Uprime`/`Cprime` (+ `_le_`) を
  削除し genuine def へ: `uActionHom` (U の H̄ 作用 hom) / `cSub` = C_U(H̄) = uActionHom の kernel を G へ
  map-down (`cSub_le_U`、first iso で |U:C|=u) / `uprimeSub`=derivedInG U / `cprimeSub`=derivedInG C +
  le 定理。⟹ **task A (carrier 再設計) 完了** = families + subgroups 全 genuine。
- **文字基盤** (本 commit): `induceHU_mem_ZIrr` (𝒮-member ∈ ℤ[Irr M]) + `sSet_subset_ZIrr` — counts が
  𝒮 を character として扱う foundation (`ClassFunction.induce_mem_ZIrr` cite)。
- **count 用 infra を特定**: Clifford inertia-induction が `InducedIrreducible.lean` に実在 =
  `isIrreducibleCharacter_induce_of_inertia_eq` (inertia=H ⟹ Ind irreducible) /
  `induce_eq_induce_iff_conj` (Ind 一致 ⟺ 共役) / `card_filter_induce_eq_index_inertia` /
  `sum_div_normSq_induce_image_eq`。§4 Dade は `S06_CertainType*` に (4.3)-(4.9) 実在。

## 2026-06-27 lane-b (cont.²): genuinization が露呈した count 文の imprecision (重要)

carrier を genuine 化したことで、free-field 時代に **vacuous だった (9.8)/(9.9)/(9.10) の文**が実内容を
持ち、Peterfalvi に対する **imprecision** が露呈した (build は green = `sorry` body ゆえ; ただし文が
不正確だと proof 不能)。count 証明前に Peterfalvi (`04.11`) に対し**文の再導出**が必要:

- **(9.9) conjunct 2** `∃ χ ∈ SOf Cprime, χ 1 = u` ⚠: SOf=𝒮 は induced family ゆえ member の degree は
  `[M:HU]·(source) = q·u = qu`((9.8.c) と同じ、(9.10) の "degree qu" とも整合)。Peterfalvi (9.9.a)
  「χ(1)=u」は **𝒳(H₀C')**-member (HU 文字) の degree であり、𝒮-member ではない。⟹ **`u` → `data.q*u`
  (qu)** に修正、または XOf(𝒳) を参照すべき ((9.8) は両所 qu で consistent)。
- **(9.10) hypothesis** `¬∃ χ ∈ SOf C, χ 1 = qu` ⚠: Peterfalvi (9.10) は **𝒮(H₀C')** (=Cprime) で記述。
  Lean は `SOf chars.C` (=C)。⟹ C/Cprime 要確認。
- **(9.8.c)/(9.8.d)/(9.9) の `SOf` 引数が H₀ join を省略** ⚠ (systematic): Peterfalvi は 𝒮(H₀C)/
  𝒮(H₀U')/𝒮(H₀C') (H₀ との join) を使うが、Lean は `SOf chars.C`/`SOf chars.Uprime`/`SOf chars.Cprime`
  (C/U'/C' 単独)。`sOf data Y` = {χ | Y⊆Ker} ゆえ H₀⊆Ker を要求しない → 別物。⟹ `SOf (chief.H0 ⊔ chars.C)`
  等に修正すべき (`chief.H0`/`chars.C` は共に `Subgroup G` ゆえ `⊔` 可)。((9.8.b) の `SOf chief.H0` は
  H₀ 単独で正しい。)
- 一般に SOf(𝒮, degree q·src) と XOf(𝒳, degree src) の使い分け・H₀ join・C/Cprime 引数を Peterfalvi
  (9.5)-(9.10) に対し総点検すること。これは genuine carrier 化の正の副産物 (scaffold 時代は検出不能)。
  **A' は count 証明 (B/C) の前提**: 文が正確になって初めて Clifford/Dade 証明が意味を持つ。

## やること (research-grade, multi-session)

- [ ] **A': count 文監査** — 上記 imprecision を Peterfalvi に対し総点検・修正 (count 証明の前提)。
- [x] **A**: carrier 再設計 = families (commit `9c41978a`) + subgroups (commit `153e866a`) 全 genuine。
      残 free field = u (pin 済) / tau・H0CprimeSupport (S12-Dade layer) / quotientSemidirectFrobenius
      ((9.10) output)。
- [ ] **B: case-(b) (9.9)/(9.10)** — Singer field model。`chiefFactor_caseB_image_*` (|Ū|∣(p^q−1)/(p−1),
      Coprime) 活用。(9.9.a) `u∣qu` は trivial。(9.9) の `∃χ∈𝒮(C'), χ1=u` = Ind_{HC}^{HU}(linear, inertia=C)
      irreducible (degree |U:C|=u) を `isIrreducibleCharacter_induce_of_inertia_eq` で構成; `|𝒮(H₀)|=p−1`
      = (4.5)/(4.7) Dade on L=M/H₀ (S06 cite + 商 inflation)。
- [ ] **C: case-(a) (9.8)** — (9.8.b,c) = (8.4.d)+(4.5)/(4.7) Dade for L=M/H₀ + θ=θ₁…θ_q1_C 構成;
      (9.8.d) = degree-qa 構成 + inertia counting (`card_filter_induce_eq_index_inertia`)。
      case-(a) factor 構造 (`CliffordCaseAData.Hpart`/`a`) を使う。
- [ ] **D: (9.11) `sibleyTarget_H0C`** 構造 witness (現状 (6.8)/Sibley 経由で §14-gated)。

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
