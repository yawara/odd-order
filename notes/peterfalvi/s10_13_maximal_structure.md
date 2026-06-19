# Peterfalvi §10–§13 — maximal-subgroup structure (Lane H 計画正本)

> Lane H = worktree `odd-order-pf-s10` / branch `pf-s10` / issue base **2000** / model Opus 4.8 (1M)。
> 本ノートは Lane H 所有。LAUNCH.md の STATEMENT AUDIT 成果物。
> **対象**: `S10_MinimalSimpleStructure` (12) / `S11_MaximalII_III_IV` (8) /
> `S12_MaximalIII_IV_V` (10) / `S13_MaximalIII_IV` (9) = **実 sorry 計 39**
> (LAUNCH の「40」は docstring 行を誤カウントした grep 由来; 実体は 39)。

---

## 0. ヘッドライン（session 1 AUDIT の結論）

§10–13 は **2 つの構造ゲート**の下流に分かれる。素朴な「実証明しやすい節」ではないが、
**S10 には新規 axiom 不要の実 wiring プログラムがある**(LAUNCH の悲観的前提を上方修正)。

- **G1 = BG §16(Thm A–E / Prop 16.1 / Thm I–II)**。
  ⚠ **S10 docstring の「BG §16 は Lean に未 scaffold」は STALE**。実際は
  [`OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean`](../../OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean)
  に Thm A–E / Prop 16.1 / Thm I–II の **statement が完全に存在**(全 sorry, faithful signature,
  Peterfalvi から import 可)。⟹ S10 の (I) 群は **新規 axiom 不要**で、この sorried statement を
  **cite**(= Lane G の S12_E 引用パターン)できる。BG §16 完成時に自動 unconditional 化。
  **承認ゲート不発**(既存 sorried statement の cite は新規 axiom でない)。
- **G2 = Pf §3–§8 character API**(Lane B の active frontier)。coherence producer
  ((6.8) `sibleySetup_is_coherent` = S08 sole sorry)+ 指標 index 族 ω/η/μ/ν/σ の S03/S04
  未材料化(= [`scaffold_opaque_prop_convention.md`](../meta/scaffold_opaque_prop_convention.md)
  の「gate #3」)。S11–13 の 27 sorry はここに gate。**Lane H からは触れない**(B の領域)。

**Lane H の near-term 実作業 = S10 → BG §16 wiring**(辞書補題 + cite, axiom 0)。
S11–13 は G2 解消(Lane B)待ちで defer。空 scaffold 量産はしない([[scaffold-sorry-free-not-done]])。

---

## 1. 分類表(R / I / C)

凡例: **R**=今すぐ実証明可(上流が main; 数論/自己完結) ／ **I**=BG §16 interface(cite で解決) ／
**C**=Lane B character API gate(G2)。`Iₛ` = BG §16 statement 既存 ⟹ cite 可(axiom 不要)。

### S10 — 全 12 が `Iₛ`（BG §16 cite + 辞書補題）

| 行 | Pf番号 | theorem | 分類 | cite 先(BG §16)/ 要 bridge |
|---|---|---|---|---|
| 75  | (8.2.a) | `typeF_card_U0_eq_exponent` | Iₛ | Thm B の `∃U0, exp U0 = exp U` 条項 / BG Prop 3.9(要確認) |
| 85  | (8.2.b) | `typeF_frobenius_of_card_eq_exponent` | Iₛ/R | type F=I の Frobenius 崩壊; Thm A extreme + Isaacs Frobenius |
| 103 | (8.8) | `maximalSubgroup_type_dichotomy` | **Iₛ ★** | `theoremI_…` 第2連言(既に shared predicate 言語)。**最有望初手** |
| 125 | (8.11) | `hall_maxNilpotentNormalHall_and_mainSubgroup` | Iₛ | Thm A(`Msigma` Hall)+ 辞書 `maxNilpotentNormalHall↔MF`,`mainSubgroup↔Msigma` |
| 138 | (8.12) | `typeI_or_typeII_centralizer_unique` | Iₛ | `theoremII_tame_embedding` + Thm B 第4連言(unique max) |
| 154 | (8.13) | `escapingCentralizers_control` | Iₛ | `theoremII_…` D-set + `theoremD_…` R(x) |
| 169 | (8.16) | `typeII_A_sets_TI` | Iₛ | Thm B(ASet TI)/`aSets_support_slice` + 辞書 `A1/typePA0↔ASet/A0Set` |
| 179 | (8.16) | `typeII_A_sets_normalizer` | Iₛ | 同上 + normalizer 形 |
| 234 | (8.15) | `dadeSupportHypotheses_typeI` | Iₛ+R | (8.16) の `N_G(A)=M` + **§4 Dade(main 在, sorry-free)**で構成 |
| 245 | (8.15) | `dadeSupportHypotheses_typeP` | Iₛ+R | 同上 |
| 335 | (8.17) | `bgTheoremE_cover_data` | Iₛ | `theoremE_sigma_partition_and_counting`(大 translation)+ 辞書 `thickenedA1↔tildeM` |
| 347 | (8.18) | `support_mutual_exclusion` | Iₛ | Thm E covering + `Supports` |

### S11 — 全 8 が C（type II/III/IV; G2 gate）

(9.1) Wielandt fixed-point は `GroupTheory.CoprimeAction` に**既出・done**(factored out)。

| 行 | Pf番号 | theorem | 分類 | gate |
|---|---|---|---|---|
| 116 | (9.3) | `typeII_III_IV_order_relations` | C(R寄り) | card 等式は genuine; Wielandt(done)使うが (9.4) chief factor + type 構造に依存 |
| 123 | (9.4) | `exists_chiefFactorData` | C | chief factor 存在は `GroupTheory.ChiefFactor` に実 API 在。但し `ChiefFactorData` が opaque Prop + card p^q が (9.3) 依存 |
| 186 | (9.6) | `chiefFactor_basic` | C | opaque `quotient_chiefFactor` |
| 194 | (9.7) | `clifford_dichotomy` | C | Clifford 二分; CaseA/B carrier(opaque 重) |
| 208 | (9.8) | `caseA_character_counts` | C | §7 `SOf` 指標数え |
| 219 | (9.9) | `caseB_character_counts` | C | 同上 |
| 235 | (9.10) | `exceptional_case_frobenius_realization` | C | Frobenius realization + opaque |
| 248 | (9.11) | `coherent_H0C_commutator` | **C ★** | coherence producer。**Lane B coherence の直 gate**(S12 (10.11) が exact で消費) |

### S12 — 全 10（9 が C, 1 が Iₛ）

| 行 | Pf番号 | theorem | 分類 | gate |
|---|---|---|---|---|
| 139 | (10.2) | `exists_zeta_degree_w1` | C | `∃ params`(指標 carrier 構成)= gate #3 |
| 148 | (10.3) | `w2_prime_and_parameter_independence` | C | `∃ params`; w2 prime は R-数論だが param 構成に bundle |
| 160 | (10.5) | `alpha_support_and_image` | C | Dade image, gate #3 |
| 171 | (10.6) | `tau1_values_and_norm_bound` | C | 同上 |
| 192 | (10.7) | `typeII_derived_frobenius` | C | [S,S] Frobenius/kernel S_F; type-II 構造依存 |
| 201 | (10.8) | `S_not_coherent` | **C ★** | 非 coherence(§10 keystone); coherence 理論 gate |
| 211 | (10.9) | `orthogonality_of_w1_lt_w2` | C | opaque rider |
| 221 | (10.10.x) | `typeV_forces_coherence` | C | type V param |
| 226 | (10.10) | `no_typeV_maximal` | C | (10.8)+(10.10.x) 依存 |
| 249 | (10.11) | `theorem88_caseB_prime_orders` | I | \|W1\|,\|W2\| prime; BG case-B 構造(`theoremI_…` の W data)から |

`typeII_section11_coherence` (260) は **sorry でない**(`exact ⟨coherent_H0C_commutator⟩`)= (9.11) に委譲(中身は空)。

### S13 — 9 sorry + (11.1) done

| 行 | Pf番号 | theorem | 分類 | gate |
|---|---|---|---|---|
| —   | (11.1) | `prime_pow_gt_four_mul_sq_add_one` | **R done** | p^q>4q²+1; 完全証明済(自己完結数論) |
| 168 | (11.3) | `S_H0C_not_coherent` | C | 非 coherence |
| 180 | (11.4) | `coherent_quotient_bound` | C | Thm(6.2)量子化 bound; opaque rider |
| 186 | (11.5) | `secondDerived_eq_HC` | C(opaque) | `→ hyp.secondDerived_eq_HC`(opaque field)= de-opaque まで**証明不能** |
| 196 | (11.6) | `core_structure` | C(opaque) | opaque `U_centralizes_H0/H0_eq_Hprime/C_eq_Uprime` + 実 IsPGroup |
| 204 | (11.7) | `H_elementaryAbelian` | C | **結論は実型**(IsElementaryAbelian p^q ∧ H0=⊥)だが (11.5)(11.6) commutator 鎖依存 |
| 232 | (11.8.x) | `orthogonality_setup` | C | `∃ data`; gate #3 |
| 240 | (11.8.5) | `orthogonality_coefficient_zero` | **R-triv** | `exact data.coefficient_zero`(carrier field で即閉; **vacuous**, 内容は (11.8.x) 構成側) |
| 248 | (11.8) | `not_orthogonal_mu0_sub_zeta` | C(opaque) | opaque `notOrthogonalFormula` |
| 260 | (11.9) | `final_typeIII_conclusions` | C | opaque + IsTypeIII M; 全依存 |

---

## 2. opaque carrier の 2 下位パターン(重要)

[`scaffold_opaque_prop_convention.md`](../meta/scaffold_opaque_prop_convention.md) 準拠。S11–13 の (C) は
**carrier 材料化**(gate #3, Lane B)に gate されており、二態:

1. **存在結論** `∃ params/data/chief, …rider…`(例 (10.2)(10.3)(9.4)(11.8.x))。opaque rider 連言は
   vacuous(構成側で witness を選べる)。真の負荷 = **実型 field(`zeta`,`mu`,`omegaSigma`,`alpha`,
   chief factor の card p^q 等)の構成** ⟹ 指標 API(σ/τ₁/ω 族)が要る = gate #3。
2. **全称・opaque field 結論** `(hyp) → hyp.foo`(`foo : Prop` opaque, `_holds` 無)。例 (11.5)
   `→ hyp.secondDerived_eq_HC`。任意 `Prop` を被仮定者が選ぶので **de-opaque まで literally 証明不能**
   (field を `False` で実体化すれば反例)。cleanup = `foo : Prop` を実 `ClassFunction`/群恒等式に置換。

⟹ **S11–13 の sorry 除去 ≠ 進捗**。doneness は carrier 材料化で判定。Lane H はここを量産しない。

---

## 3. 攻略順(Lane H near-term)

### Phase A — S10 → BG §16 wiring(axiom 0, in-scope, build-green)

**辞書補題層**(独立定義間の橋; 一部は定義的、一部は Prop 16.1[sorried] / BG §14-15 依存):

- `maxNilpotentNormalHall M = S15.MF M`(両者「M_F」; 別ファイル別定義 → bridge 要)
- `mainSubgroup M tau ↔ Msigma M`(I/II/V: M_F=Msigma は Prop 16.1; III/IV: M'=derivedInG)
- `A1 M tau / typePA0 M data ↔ ASet M U / A0Set M K`(support set 辞書)
- `thickenedSupport / thickenedA1 ↔ tildeM`(thickened 辞書)
- `S14.IsConjugateSubgroup M N ↔ ∃ g, MulAut.conj g • M = N`(conjugacy 辞書; おそらく定義的=易)
- type predicate ↔ BG taxonomy: **`proposition_type_classification`(Prop 16.1)が辞書本体**(sorried)

**初手 = (8.8) `maximalSubgroup_type_dichotomy` ← `theoremI_…`**。BG Thm I 第2連言は既に
`GroupTheory.IsTypeI/II/NonI` + `S14.IsConjugateSubgroup` 言語 ⟹ conjugacy 辞書 1 本で wiring。
S10 版は W1/W2/W data を落とした弱形ゆえ derivable。**最小 friction で 1 sorry 実減 + 辞書 1 本確立**。

次 = (8.12)/(8.13) ← `theoremII_tame_embedding` → (8.16) → (8.15)[+§4 Dade] → (8.11) → (8.17)/(8.18)。
辞書補題が Prop 16.1 / BG §14-15 の sorried 内部に bottom-out する箇所は cite で sorry を BG 側に局所化
(Lane H 側 theorem は「BG §16 modulo」の実証明 = axiom 0)。bottom-out が**新規** axiom を要する形
(例: BG Prop 3.9 が main に無い場合の (8.2.a))は **issue 起票 → STOP → 承認**(LAUNCH §🚦)。

### Phase B — S11–13 は defer(G2=Lane B 待ち)

coherence producer((6.8))と指標 index 族材料化(gate #3)が Lane B で landing するまで
S11–13 の (C) は実証明不能。Lane B の sorried statement を cite して S11–13 の依存を**明示配線**する
のは可(carrier 構造の opaque field を Lane B 完成形に置換)だが、near-term の主作業ではない。

### (R) harvest(微小)

- (11.1) done。
- (11.8.5) `orthogonality_coefficient_zero` は `exact data.coefficient_zero` で即閉可だが **vacuous**
  (a=0 の実内容は (11.8.x) 構成側 = C)。単独 commit 価値薄。Phase A の wiring commit に同梱可。

---

## 4. 上流の事実(再調査不要メモ)

- BG §16 statements: `OddOrder.BG.Ch4.S16.{theoremA_maximal_structure, theoremB_U_and_A_tame,
  theoremC_paired_structure, theoremD_msigma_conjugacy_and_centralizers,
  theoremE_sigma_partition_and_counting, aSets_support_slice, proposition_type_classification,
  theoremI_nilpotentHall_conjugacy_and_type_dichotomy, theoremII_tame_embedding}` — **全 sorry, cite 可**。
- §4 Dade: main 在・sorry-free(`S04_DadeIsometry`)。(8.15) の Dade 部材料。
- chief factor: `GroupTheory.ChiefFactor`(`isChiefFactor_maxProperNormalOrBot` 等, 実 API)。
- `IsCoherent`: `S07_Coherence.lean:1557`(実 structure)。producer/操作子は S08 在。但し
  maximal-subgroup 族の `Nonempty (IsCoherent …)` producer は (6.8) = Lane B 未完。
- shared notation 定義: `GroupTheory/MaximalSubgroupType.lean`(`mainSubgroup`:239, `A1`:248,
  `supportKernel`:64, `thickenedSupport`:74, `thickenedA1`:269), `MaxNilpotentNormalHall.lean`:34。
  いずれも **BG notation とは独立定義** ⟹ 辞書補題が要る(§3)。

## 5. session 1 計測結果 — 残 11 を 3 tier に + interface gap

**✅ (8.8) 完了**(commit 6de1edea, axiom 0)。`theoremI_…` 第2連言が shared predicate 言語 +
`S14.IsConjugateSubgroup M N := ∃ g, conj g•M=N`(**defeq**)ゆえ辞書不要で wiring。S10 12→11。
**この clean さは (8.8) 固有**(BG Thm I だけが shared 言語で pre-translate 済)。

**辞書実体**(grep 確定):
- `S15.MF M := maxNilpotentNormalHall M`(**abbrev = defeq・無料**)。S14 も `K = maxNilpotentNormalHall M`。
- `Msigma M := opiCoreInG (sigma M) M`(σ-Hall, **MF と別物**)。Prop 16.1[sorried] が I/II/V で `MF=Msigma`。
- `escapingCentralizerSet M X = {x|x∈X ∧ ¬C{x}≤M}`(BG ThmII の D は `+x≠1`; near-defeq)。
- `maximalSubgroupsContaining H = {N|IsCoatom N ∧ H≤N}`,`IsUniquelyMaximal H = H<⊤ ∧ ∃!coatom⊇H`
  ⟹ `IsUniquelyMaximal ↔ maximalSubgroupsContaining=singleton ∧ H<⊤`(provable)。
- `A1 M tau = sharpSubgroup(mainSubgroup)` vs BG `ASet/A0Set = hatMsigma ∩/∖ …` = **実際に異なる集合。
  等式を与える citeable BG statement が無い**(← 壁)。

| tier | sorry | 状態 |
|---|---|---|
| **T1 wireable**(tighten + cite) | (8.12),(8.11) | `theoremB`/`theoremA` cite。但し `theoremB` 仮説 `hU : IsHallSubgroup ((kappa∪sigma)ᶜ) U` が BG-internal ⟹ S10 を BG notation に結合する要(↓ gap) |
| **T2 blocked**(support-set 等式不在) | (8.16),(8.13),(8.17),(8.18) | `typePA0=A0Set` / `A1⊆…` / `thickenedA1=tildeM` の citeable 等式 無し。sorried BG §14-15 構造に bottom-out |
| **T3 別ゲート** | (8.2.a)(8.2.b),(8.15) | (8.2)=BG Prop 3.9(main 在否要確認)/ThmA,B extreme; (8.15)=(8.16)[T2]依存 |

### ⚠ interface gap(session 1 の主発見)

BG §16 file docstring 明記:「Peterfalvi §10+ should consume these BG endpoints **through the shared
type predicates**」。しかし `theoremB/C/E` は仮説・support-set とも **BG-internal notation**
(`kappa`/`sigma`/`ASet`/`A0Set`/`tildeM`)で露出。S10 は shared notation で書かれ、両者を繋ぐ
**shared-notation 消費層が不在**。⟹ T1/T2 の wiring は「S10 を BG-internal に結合」か「BG §16 に
shared-notation wrapper/bridge を足す(BG spine 編集)」の**設計・所有権判断**を伴う。
**独断で結合させない → ユーザー裁可待ち。**(8.8) 以降の自動 wiring は gap 解消後。

### 6. consumption-layer 構築済み(`S10_BGInterface.lean`, 2026-06-12〜13)

interface gap の設計裁可 = **Lane-H 所有 wrapper file 方式**(ユーザー裁可)。以下を実証明(axiom 0、
sorry は BG Prop16.1 へ局所化のみ):

- `maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`(MF=Msigma, Prop16.1 cite)
- `isTypeI_iff_isTypeF` / `isTypeII_iff_isTypeP2`(type 辞書, Prop16.1 cite — §14/§16 の結論
  `IsTypeF/P2` を shared `IsTypeI/II` へ翻訳; wiring (8.13)/(8.16) で確実に要る)
- `isHall_primeFactors`(一般: π-Hall ⟹ π(|H|)-Hall)
- `maxNilpotentNormalHall_isHall_of_typeI_or_II`(= **(8.11) 第1連言の type I/II 部**)
- **`A1_eq_sigmaSharp_of_typeI_or_II`**(= support-set bridge `A1 M tau = M_σ#`, type I/II)
  — ⚠ §5 表の「A1↔ASet 等式不在」を訂正: **A1↔sigmaSharp(=M_σ#)は I/II で証明可**。
  不在なのは `A0Set/ASet = hatMsigma ∩/∖ …`(別構造)の bridge。
- `isUniquelyMaximal_of_maximalSubgroupsContaining_eq_singleton`(maximality bridge, 一般)
- S13 (11.8.5) `orthogonality_coefficient_zero` close(carrier field; S13 sorry 9→8)

### 7. 残 TODO / 頭打ちの正確な所在(2026-06-13)

**§14/§15 を実地調査**(全 proved 補題を grep): §14=11 / §15=9 sorry、**主結果は全て sorried** で
shape も BG-internal(`kappa`/`piSet`/`tau2`/`IsTypeF/P2`/`hatMsigma`)。S10 の (8.11)-(8.18) は
**universally-typed・multi-branch** で、上記 bridge により **type I/II の部分**は wiring 可能だが、
- III/IV 部(`M_s=M'≠M_σ`)・`A0Set/ASet` 部 = §14/§15 の sorried 構造に bottom-out、
- 全 branch を要する 1 定理ゆえ**部分 wiring では closure しない**。

⟹ **clean な consumption-layer foundation は概ね構築完了**。これ以上の §10-13 foundation は
(a) thin wrapper(規約違反)、(b) §14/§15-gated 定理の部分片(speculative)、(c) type V(空)拡張、
のいずれかで**逓減**。実質的な S10 closure の唯一のレバー = **BG §14/§15 が *proved* になること**
(BG spine = Lane F/G の下流; Lane H scope 外)。
- [ ] T2/(8.11)III-IV/(8.13)(8.16)-full = BG §14-15 landing 待ち。
- [ ] (8.2.a) BG Prop 3.9 在否(T3; 未確認、優先度低)。
- [ ] §14/§15 が landing したら本 bridge 群で S10 を一気に wiring。

### 8. faithful-(10.1) Hypothesis + honest (10.10) (2026-06-19, commit `26c1a9f0`)

cite-split で H を §10-13 char track に再配向後の実作業。**(10.10)/(10.11) は当初想定より深く gated**
と判明(調査): (10.10)=B の §10 coherence char 全体 + faithful Dade 設定、(10.11)=(10.10)+lane-f の
BG↔Pf W1=κ bridge(gap B)+ `Theorem88CaseBData` 構造強化(FeitThompson.lean consumer 影響)。
S10/S11/S12/S13 の ~39 sorry は全て `Hypothesis M`(loose char carrier)の opaque field 経由で、
clean な純群論 win は無し。

ユーザー裁可で **(10.1) `Hypothesis` の faithful 化**(scaffold cleanup step 3 = carrier 非空化):
- 旧: `Sset`/`A0`/`tau` が**無制約 data field**(garbage 構成可 ⟹ `IsCoherent 0 ∅ ∅`(false)依存の
  brittle proof が書けてしまう = やってはいけない)。
- 新: 3 つを **genuine projection** に pin:
  - `A0 := S04.supportInSubgroup (typePA0 M typeP) M` (= A_0(M) of (8.10))
  - `Sset := inducedFamily M` (= {Ind_{M'}^M θ | θ∈Irr M', θ≠1} of (10.1)、新 def)
  - `tau := S07.dadeIntegralCharacterMap dadeData.dade (… hconj)` (= genuine Dade isometry rel (A_0(M),M,G))
  - carrier に `[finiteG : Finite G]`(S15 `FiniteInduce` パターン、scoped Fintype/Invertible)+
    `dadeData : S10.DadeSupportHypothesisData M (typePA0 M typeP)`(= (8.15) Dade support)+ `hconj`。
- **構成サイト不在ゆえ downstream 無破壊**(full build 3868 jobs green; S13 が `base` 経由で消費するが OK)。
- producer `exists_hypothesis_of_typeIIIorIVorV`(type III/IV/V 極大 → faithful Hypothesis、
  `S10.dadeSupportHypotheses_typeP` cite + own residual = `hconj` のみ = issue 2011、gated でない群論)。
- **(10.10) `no_typeV_maximal` を honest 化**(bare sorry → proof): faithful な `hyp` 上で
  `(10.8) S_not_coherent` ∧ `(10.10.1-4) typeV_forces_coherence` の矛盾に還元。**同一の genuine
  `hyp.tau/Sset/A0`** を両者が参照 ⟹ B が faithful 化したら通る(brittle でない真の reduction)。

real sorry 136→136(10.10 の bare sorry が producer の hconj に置換)。**gain = carrier 非空化 +
§10 capstone (10.10) honest 化**。残 §10 materialization は **carrier bundling 壁**((10.2)/(10.3) の
`CharacterParameters` が `w2_prime`/`d_gt_one` を bundle)+ B の §3-§6 char API 待ちで逓減。
(10.11) は (10.10) cite + `Theorem88CaseBData` faithful 化(cross-lane, gap B)で別途。
