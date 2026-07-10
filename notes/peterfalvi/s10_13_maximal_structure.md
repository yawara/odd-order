# Peterfalvi §10–§13 — maximal-subgroup structure (Lane H 計画正本)

> ⚠ **2026-07-02 再編**: Lane H は消滅、§10–13 = **lane a** (正本 [`ft_lane_reallocation_2026_06_28.md`](../meta/ft_lane_reallocation_2026_06_28.md))。
> ただし S10 の §8 Dade-support 宣言群 (`typeII_A_sets_TI`/`typeII_A_sets_normalizer`・
> `dadeSupportHypotheses_typeI`/`typeP`・`support_mutual_exclusion`) は issue
> [0096](../../issues/0096-s10-section8-dade-support-carveout-lane-b.md) carve-out で **lane b** —
> 本 note の「S10→BG§16 wiring を実作業」指示はこの範囲では無効。`support_mutual_exclusion` は
> **PROVEN** (2026-07-02, lane b)。(8.2.a)/(8.2.b)/(8.8) proven。S08 は sorry-free ((6.8) gate 閉)。
> census (2026-07-02, comment-strip): S10 8 / S11 4 / S12 4 + Core 0 / S13 10。
> 本 note の S12:NNNN 行番号は 07-02 prefix-split (95fc7ade) 前のもの。

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

**追記 (2026-06-19, commit `e9c37da7`)**: producer の own residual `hconj` を discharge(issue 2011 closed)。
新 private helper 2 本: `conj_smul_centralizer_singleton`(`g·C_G(a)·g⁻¹=C_G(gag⁻¹)`、calc+`group`)+
`supportKernel_conj_invariant`(`supportKernel M M X (gxg⁻¹)=g·supportKernel·g⁻¹`、escaping 不変 + M_F の M-normal
`maxNilpotentNormalHall_le_normalizer` + `smul_inf`)。`hconj`=`H_eq_supportKernel`+`typePA0` の M-invariance
(`dade.L_normalizes_A` の l/l⁻¹)。**producer 完全 honest 化**(legit upstream のみ cite)、**real sorry 136→135**。
⟹ **H-only clean win 出尽くし**: 残り (10.11)=cross-lane(F+gap B)/ materialization=carrier bundling+B-gated。

**追記 (2026-06-19, commit `64472a63`) — (10.11) 完全 unconditional 化 + 用語訂正**: (10.11) を支える
「κ-Hall が derived を complement する」事実は **既に証明済**(`BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall`、
BG Thm 14.7(h)、AxiomsCheck 登録、axiom-clean)。私が原文/既存機構を確認せず sorry'd 重複 `kappaHall_isComplement_derived`
を切り出し「gap B/lane-f obligation」と誤ラベルしたのを訂正(ユーザー指摘: 「gap」は書籍の行間/誤りに限る; cross-book
対応・未形式化既知事実は形式化労力)。重複削除 + consumer で既存定理を直接 cite → **(10.11) は (10.10)+(8.6.a)+
proven typeP_derivedInG_isComplement_kappaHall で完全 unconditional**(FT 消費される primality 完全証明、real sorry 135)。
issue 2012 RESOLVED。教訓: obligation 化の前に grep + AxiomsCheck を確認。

### 9. §10-13 残 sorry 監査 (2026-06-19) — citeable vs gated 分類

(10.11) が「既存 proven 定理 cite」で閉じた後、残 sorry を**精読して**分類(gated と決めつけず原文確認):

**citeable に見えて実は gated(精読で判明)**:
- `hall_maxNilpotentNormalHall_and_mainSubgroup` (8.11) — `maxNilpotentNormalHall_isHall`(S15_MF:279 proven）は
  **Hall-in-M**(`.subgroupOf M`)。target は **Hall-in-G**。別物。G-level は sorried BG §16(theoremE/I）経由 ⟹ gated。
- `typeF_card_U0_eq_exponent` (8.2.a) — `|U0|=exp(U0)` に U0 の cyclic-Sylow(BG Prop 3.9 = 奇 Frobenius 補元）要。
  **TypeFData は U0 を Frobenius 補元として carry せず** ⟹ gated（structure 不足）。

**character-theory-gated(B の §3-§6 char API 待ち、~11 本)**: `typeI_or_typeII_centralizer_unique` /
`escapingCentralizers_control` / `dadeSupportHypotheses_typeI`/`_typeP` / `support_mutual_exclusion`（S10）;
`clifford_dichotomy` / `caseA`/`caseB_character_counts`（S11）; `S_H0C_not_coherent` / `coherent_quotient_bound` /
`orthogonality_setup` / `not_orthogonal_mu0_sub_zeta` / `final_typeIII_conclusions`（S13）。

**opaque-carrier materialization（murky、~8 本）**: `typeII_III_IV_order_relations` / `exists_chiefFactorData` /
`chiefFactor_basic` / `exceptional_case_frobenius_realization`（S11）; `secondDerived_eq_HC` / `core_structure` /
`H_elementaryAbelian`（S13）。結論が S11/S13 Hypothesis carrier の opaque Prop field ゆえ「証明」が vacuous/要材料化で murky。

⟹ **§10-13 の clean な H-only win は (10.10)/(10.11) で出尽くし**。残りは (a) BG §16 G-level Hall（sorried BG 下流）、
(b) B の §3-§6 char API、(c) opaque carrier 材料化（B 寄り）に gated。faithful (10.1) tau は §4 Dade proven 補題
(`dadeIntegralCharacterMap_inner_eq_on_supported_span` 等)を cite する土台になるが、(10.5)/(10.8) 等の materialization は
Peterfalvi 原文の長い算術論法ゆえ substantial。

### 10. §13 (`S13_MaximalIII_IV` = Pf §11 types III/IV) de-opacify (2026-06-23, lane-h relane #2, commit `81b633cc`)

relane #2 (issue 8018+2017) で lane-h = **`S13_MaximalIII_IV`** (active) に再配置。hub 指定の着手口
= 構造 leaf (11.5)/(11.6)/(11.7)。**重要: repo `S13` ファイルは Pf §11 (types III/IV, results (11.x), pp.64-68)**
(file 番号は Pf §番号 -2; Pf §13 の (13.x) は repo `S15_SAndT`)。

**診断**: `S13.Hypothesis` は「結論を opaque `Prop` field として*仮定*する」scaffold だった
(`secondDerived_eq_HC`/`U_centralizes_H0`/`H0_eq_Hprime`/`C_eq_Uprime` opaque + `H_is_pgroup`/
`H_elementaryAbelian`/`H_order_prime_power`/`H0_eq_bot` が (11.6)/(11.7) の結論を field で仮定)
⟹ 定理は vacuous。**構成サイトは repo 全体に皆無、S14 は 8 定理を 1 つも消費しない** (grep 確認) ⟹ 改変安全。

**landed (de-opacify + 2 unconditional fragment, axiom-clean, AxiomsCheck 登録)**:
- `C_eq_centralizer` opaque → 実 (11.2) `C = U ⊓ C_G(H)` (assumption field、残す)。
- conclusion-as-field 8 個削除。(11.5)/(11.6) を実ステートメントに:
  - (11.5) `secondDerived_eq_HC` → `M'' = HC`。`≤` を **`secondDerived_le_HC`** (sorry-free) で load-bearing 証明、`≥` のみ char gate。
  - (11.6) `core_structure` → `IsPGroup p H ∧ U ≤ C_G(H₀) ∧ H₀=H' ∧ C=U'` (実 conjunction、body sorry)。
  - (11.7) `H_elementaryAbelian` 実ステートメント不変、冗長 carrier field 除去。
- **`Hypothesis.secondDerived_le_HC`** : `M'' ⊆ HC` ← `TypePData.secondDerived_le_fitting` (=(8.5.a)) + `C_eq_centralizer`。
- **`Hypothesis.derivedU_le_C`** : `U' ⊆ C` ← `S11.typeP_commutator_U_centralizes_H` (=(8.5.b)) + `map_subtype_le`。

**追加 de-opacify (commit `04eb6f32`)**: (11.4) `coherent_quotient_bound` も実ステートメント化 —
opaque `quotientBoundFormula` field 削除、結論を実 index 不等式 `|M':H₁| ≤ 2q|U:C| + 1`
(`Subgroup.relIndex`、Pf `|M'/H₁|-1 ≤ 2q|U/C|` の減算回避形) に。証明は Thm (6.2)/(6.3) coherence (char) gate ゆえ sorry。
**∴ §13 で char API 無しに faithful に STATE できる定理は全 de-opacify 完了**。残 opaque field =
(11.8)/(11.9) char rider (`notOrthogonalFormula`/`finalOrthogonalityFormula`/`caseB_of_97`、σ/ω/(Irr W) API 要) のみ。

**追加 (commit `558619f2`): (11.6) `U ≤ C_G(H₀)` clause の Wielandt 部分を landing** —
`U_centralizes_H0_of_W1_fpf` (axiom-clean, AxiomsCheck 登録): `C_{H₀}(W₁)=1` ∧ `U≠1` ⟹ `U ≤ C_G(H₀)`,
lane-h の (9.1) `frobenius_kernel_centralizes_of_complement_fpf` を `U W₁` Frobenius (`typeP_uW1_frobenius`)
が `H₀ ≤ M_F` に coprime 作用する形で適用。**残 gate = fpf 入力 `C_{H₀}(W₁)=1`** に縮小 = `|W₂|=p`
(§8 `typeIIIorIV_W2_prime`←(8.8)) + coprime-quotient (`C_H(W₁)=W₂` [TypePData] + Cor 3.28 + (9.6)`|W̄₂|=p`)。
∴ (11.6) clause 2 の substantive な群論核は済み、§8 prime fact 待ちに。

FT-path sorry **122 不変** (vacuous opaque → 実ステートメント + 2 proven sublemma; CLAUDE.md「sorry≠進捗」)。

**残 §13 gate (= cross-lane char、精密化済)**:
| 結果 | 残 gate | 担当 |
|---|---|---|
| (11.5) `≥` (`HC ⊆ M''`) | (11.4) quotient bound → Thm (6.3) coherence + (10.8) `S12.S_not_coherent` | lane-b char |
| (11.6) 残 3 conjunct | (9.3) `U cent O_{p'}(H)` + (9.6) `C_{H₀}(W₁)=1`(+(9.1)✓ Wielandt) + [BG]1.6(d) + (11.5) | S11 sub-facts (未 export) + char |
| (11.7) | (11.5)+(11.6) | 上記下流 |
| (11.3) `S(H₀C)` not coh / (11.4) bound | Thm (6.3) + (10.8) | lane-b char |
| (11.8.x)/(11.8)/(11.9) | σ/ω/μ/(Irr W) char API (gate #3) + (9.7)(9.8)(9.11) | lane-b char |

**lane-b への signature 依頼 (issue 起票)**: (10.8) `S_not_coherent` の faithful signature (S12 export 済か要確認) +
§6 coherence (Thm 6.3) の citeable 形。char API (gate #3) landing 時に §13 char 方向を一気に wiring。
**lane-h 次手**: (11.6) の §9 sub-fact ((9.3)/(9.6) の正確な carrier 形) が S11 に未 export ⟹ S11 (driver) に
追加するか lane-b 依頼。これらは §8-free 群論寄りなので lane-h で attemptable な可能性 (要 (9.1) Wielandt 適用調査)。

**追記 (cite-reduction, ユーザー指示「cite して進められる」, commits `5a212bc4`/`0adb8560`)**:
char leaf を sorried 上流の cite で sorry-free 化 ([[feedback-cite-sorried-lemmas-if-signature-correct]])。
**重要発見: (10.8) `S12.S_not_coherent` は clean signature で citeable だが、Thm (6.3)「部分族 coherent
⟹ S coherent」は repo に standalone 形が無い** (§6 coherence は `SibleyDadeHypothesis` filtration
machinery `S08_Theorem63` 経由)。⟹ Thm (6.3) 適用を **named obligation** に切り出す方式:
- **(11.3) `S_H0C_not_coherent` sorry-free**: `coherent_S_of_coherent_SH0C` (Thm 6.3 obligation) +
  `S12.S_not_coherent` ((10.8)) cite → 矛盾。
- **(11.5) `secondDerived_eq_HC` (`M''=HC`) sorry-free**: `secondDerived_le_HC` (proven ≤) +
  `HC_le_secondDerived` (≥ obligation, (5.7)+(11.4)) の `le_antisymm`。
残 gate = 2 named obligation (`coherent_S_of_coherent_SH0C`/`HC_le_secondDerived`) = lane-b §6 char。
両定理は sorried 上流 cite ゆえ axiom-clean でない (登録せず、honest cite reduction)。FT-path sorry 122 不変。
**残: (11.4)(=Thm 6.2 そのもの)/(11.6)残/(11.7)/(11.8)/(11.9) は char-gated or §8(|W₂|=p)。** §13 の構造側
(11.3/11.5) は cite-reduce 完了、(11.6) clause2 Wielandt 核 landed、残りは genuinely lane-b char / §8 待ち。

---

## relane #4 (2026-06-23, issue 2019+4009): Pf (13.2.a) 配線 — `IsTypeP2 mp.S` 供給

> ※ (13.2.a) は **Pf §13** ("The Subgroups S and T", `04.15_*.mmd`) = **repo S15**。本 note は本来 Pf §8-11
> だが、relane #4 の lane-h タスクゆえ handoff をここに記録 (s14_maximalI と並ぶ lane-h frontier 記録)。

**経緯**: §13 (repo S13 = Pf §11) clean work 完遂で lane-h starve (issue 2019) ⟷ lane-c の POLE-1
TypePData carrier 機構 (`exists_typePData_W1_eq_of_isTypeP2`) 完成で残る唯一 gate = `IsTypeP2 mp.S`
(issue 4009)。ユーザー裁可で **lane-h が (13.2.a)「q<p ⟹ S は Type II (=type-P₂)」を担当** (relane #4)。

**landed (`OddOrder/FeitThompson.lean`, commit `87068c22`)**:
- `isTypeP2_of_typeP_kappaHall_lt` (character obligation 以外 sorry-free): S type-P + `|K|<|K*|`
  ⟹ `IsTypeP2 S`。skeleton = `isTypeP_iff_isTypeP1_or_isTypeP2` で P₁∨P₂、P₁ 枝を下記 obligation で
  排除、P₂ 残す。BG Thm 14.7 の disjunction (`IsTypeP2 S ∨ IsTypeP2 T`、**順序情報なし**) を
  `K_lt_Kstar` で確定側に pin。
- `Section16MaximalPair.S_typeP2 : IsTypeP2 S` field 新設 + producer fill ⟹ **`mp.S_typeP2`
  available** ⟹ **lane-c §15 carrier wiring (step 3) unblock** (issue 4009 完了条件達成)。

**重要な routing 訂正 (LAUNCH の想定と相違)**: LAUNCH は「BG §16 type API を cite / 必要なら lane-f BG」
を想定したが、**調査の結果 BG は disjunction を density argument で導き順序を使わない** (`exists_typeP2_member`、
`card_kappaHall_ne_card_Kstar` は `≠` のみ)。**順序による型決定 = Pf §10-11 character 理論** (Thm (10.10)
[no Type V] + (11.9.b) [type III/IV ⟹ q>p via `S(HC)` coherence/norm bound])。⟹ 残 character 核は
**lane-f (BG) でなく lane-b (Pf char)** に routing。faithful obligation `card_kappaHall_lt_of_isTypeP1`
(型-P₁ ⟹ `|K*|<|K|`) に clean isolate → **issue 2020 で lane-b へ**。

**lane-h frontier 状況**: relane #4 の in-lane 部 (型判定 skeleton + 配線) 完遂。残 (13.2.a) character 核は
lane-b (issue 2020)、step 3 wiring は lane-c。S13/S14 は依然 char/Prop16.1 gated。
full AxiomsCheck build 3881 green、FT-path sorry 122 不変 (disjunction→determinate `IsTypeP2 mp.S` の
de-opacify、sorry 数でない [[scaffold-sorry-free-not-done]])。

---

## 11. Coherence-free (10.9) landed — unblocks (11.9.b) `q > p` (2026-06-25, lane-b W3, relane #9)

W3 (= lane-b, 正本 `notes/meta/ft_frontier_remap_2026_06_25.md`) の臨界路最狭点 = `card_kappaHall_lt_of_isTypeIIIorIV`
(FeitThompson.lean:426, Pf (11.9.b) = "type III/IV ⟹ q>p")。textbook (11.9.b) の証明 = "follows from (10.9)
and (11.8)"。

**問題 (coherence carrier 障害)**: 既存 `orthogonality_of_w1_lt_w2` (S12) は `coh : CoherentHypothesis hyp params`
を要求するが、(10.8) `S_not_coherent` により S は coherent でない ⟹ `CoherentHypothesis` は uninhabitable
⟹ (11.9.b) に**直接使えない**。textbook (10.9) の証明 (04.12 lines 105-109) は実は **coherence-free**:
χ は (μ₀-ζ)^τ の (Irr W)^σ 直交補にすぎず、ζ^{τ₁} 同定 (coh 依存) は不要。

**landed (commit この commit)**:
- `S05.TICyclicHypothesis.ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast` — 一般 **Bessel NC bound**
  `sigmaNC ψ ≤ ‖ψ‖²` (ψ∈ZIrr G, ⟨ψ,ψ⟩=(N:ℂ) ⟹ NC≤N)。norm-1/2 特殊版 (`…le_one`/`…le_two`) の一般化。
  証明 = χ=∑c_a·a の per-constituent support (各 ≤1) で被覆 + #supp ≤ ∑c_a²。**fully axiom-clean、AxiomsCheck 登録済**。
- `S12.inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2` — **coherence-free (10.9)** σ-coeff 形:
  w₁<w₂ ⟹ ∀ i j, ⟨(μ₀-ζ)^τ, ω_{ij}^σ⟩ = if j=0 then 1 else 0 (ζ∈inducedFamily, irreducible, ζ(1)=w₁)。
  既存 (10.9) の coherence-free core を抽出 + 2 置換: (i) NC bound を Bessel 化
  (‖ψ‖²=‖μ₀-ζ‖²=w₁+1<2w₁、Dade `tau_inner_eq_of_supported` + `muGrid_column_sum_inner_self` + 次数不一致
  `⟨μ_{i0},ζ⟩=0`)、(ii) row-branch 排除を `NC≥w₂>w₁+1` で (full row が w₂ 個の非零係数; coh の ‖ζ^{τ₁}‖²=1 不要)。
- `S12.residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2` — **直交補形**: residual `(μ₀-ζ)^τ - ∑ω_{i0}^σ`
  が (Irr W)^σ に直交。これが (11.9.b) が (11.8) と矛盾させる直交性。
- sorryAx は既存 §10 carrier 機構由来 (既存 (10.9) も同一 taint、`tau_apply_of_mem_typePV` 等は clean) で
  **新規 sorry 導入なし** ([[feedback-cite-sorried-lemmas-if-signature-correct]])。full build 3884 green。

**残 Part 3 ((11.9.b) `q>p` reduction → `card_kappaHall_lt_of_isTypeIIIorIV`)**: 以下が要 (issue 2020):
1. **∃ ζ ∈ S(HC) of degree w₁** ((10.2) の S(HC)=`{χ∈S|HC⊆Ker χ}` 版、genuine §11 fact)。
   (10.2) producer `exists_zeta_in_inducedFamily_degree_w1` は S∩Irr の degree-w₁ ζ を供給するが、S(HC) 制約付きは別途。
2. **genuine (11.8)** — 現 `S13.not_orthogonal_mu0_sub_zeta` は opaque `notOrthogonalFormula` field 結論。
   de-opacify して "residual NOT ⊥ (Irr W)^σ" の実 ClassFunction 形に。証明は (11.8.1)-(11.8.6) 経由
   (deep: (9.11)/(5.8)/(4.9)/σ-grid; **これが Part 3 の主負荷**)。
3. **reduction** ✅ **landed** (`S12.w2_lt_w1_of_residual_not_orthogonal`): ζ (degree-w₁) + genuine (11.8)
   仮説 `h118` (residual ¬⊥ の実 ClassFunction 形、opaque でない explicit obligation) ⟹ `hyp.w2 < hyp.w1`。
   証明 = lt_trichotomy: w₁<w₂ なら coherence-free (10.9) [residual ⊥] が h118 と矛盾、w₁=w₂ は coprime+w₁≥3
   で排除、∴ w₂<w₁。**(11.9.b) の reduction 論理は完成**、残 = `h118` (= genuine (11.8)) の discharge (step 2)。
4. **carrier 構成 + 翻訳**: type III/IV maximal S → `exists_hypothesis_of_typeIIIorIVorV` で S12.Hypothesis、
   q=w₁=|K|, p=w₂=|K*| に翻訳 → `card_kappaHall_lt_of_isTypeIIIorIV` (FeitThompson:426)。

---

## 12. Lane A (α) 立ち上げ 2026-06-28 — §9 keystone `caseB_degree_qu` (9.9.a) 進行中

新体制 (lane a/b/c/d, 正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`) で Lane A = クラスタ α
(Pf §10–13 中央指標核) を立ち上げ。最上流 §9 (repo `S11`) の keystone から着手。

**⚠ stale 訂正**: §1 の「§9 carrier `Section11CharacterData` は opaque/never-constructed」は **stale**。
実コードでは carrier は materialize 済 (`S11:1477`「formerly free fields are pinned to genuine
constructions」、`C := cSub`, `X := xiSet`, `S/SOf` も genuine def)。`clifford_dichotomy` (9.7) も
sorry-free。⟹ §9 counts (9.8/9.9/9.10) は genuine に証明可能 (carrier gate は消滅済)。

**`caseB_degree_qu` (9.9.a, `S11:3454`)** = 「𝒮(H₀C') の各元は degree qu」。Clifford degree
`χ(1)=[HU:HC]` を `apply_one_eq_index_of_liesOver_linear_inertia` で出す skeleton は既存。3 obligation:

- ✅ **obligation 1 (θ₀ 抽出)** DONE (commit `46e474d9`): χ∈𝒳(H₀C') から nontrivial chief-factor
  constituent θ を `exists_constituent_not_subset_characterKernel` で抽出 → kernel 継承 (新 helper
  `liesOver_mem_characterKernel`、S08 `characterKernel_subset_of_isCharacter_of_inner_ne_zero` cite)
  で θ が N-trivial → `exists_compHom_eq_of_subset_characterKernel` で θ=compHom(hInHuEquivH)(inflate θbar)
  に同定 → inertia=HC は既証明 `inertia_eq_hcInHu`、θ₀(1)=1 は H̄ 可換 ⟹ θbar linear。
- ✅ **obligation 4 の数学核** DONE (commit `62fce025`): `hInHu_inf_uInHu_le_cInHu` (`H⊓U≤C_U(H̄)`、
  H̄ 可換ゆえ H 元の共役は H̄ 上自明) + `uInHu_inf_hcInHu_eq_cInHu` (`U⊓HC=C`)。これが `[HU:HC]=[U:C]`。
- ⬜ **obligation 4 残 (index 代数, `S11:3557` `hidx`)** = `(hInHu⊔cInHu).index = chars.u`。機械的:
  (A) `HC.index = cInHu.relindex uInHu` (第2同型 `quotientInfEquivProdNormalQuotient` + `uInHu⊔HC=⊤`
  (`hInHu_sup_uInHu_eq_top`+sup_comm) + `relindex_top_right`、`uInHu⊓HC=cInHu` で LHS 商を書換);
  (C) `cInHu.relindex uInHu = chars.u` (card-cancel: `card_mul_index`+`subgroupOfEquivOfLe` で
  `|cSub|·relindex=|U|`、first-iso `quotientKerEquivRange`+`equivMapOfInjective`×2 で `|U|=u·|cSub|`、
  `Nat.card cSub>0` で消去)。`chars.u_eq_card_quotient` が `u=|range uActionHom|`。
- ⬜ **obligation 3 (ψ linearity, `S11:3551` `hψdeg`)** = `ψ(1)=1` (ψ=`exists_liesOver` の HC-constituent)。
  `apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient` (N=`commutator ↥HC`) で、
  `[HC,HC]⊆ker ψ` を kernel 継承 (`liesOver_mem_characterKernel`) + `[HC,HC]⊆ker χ` から。後者は
  `⁅HC,HC⁆≤H₀C'` (構造: `⁅H,H⁆≤H₀` [H̄ 可換], `⁅H,C⁆≤H₀` [C cent H̄], `⁅C,C⁆=C']) — `Subgroup.commutator_le`
  で生成元ごとに ([[lean-normal-closure-good-elements]]: sup 上の commutator 分配は直接不可、generator 経由)。

**次手 (上流順)**: obligation 4 残 (機械的、すぐ) → obligation 3 (構造 commutator) → caseB_degree_qu
sorry-free。その後 (9.9) `caseB_character_counts` / (9.8) `caseA_character_counts` → (11.8)/(10.7) へ。

### §12 追補 (lane-a /loop): obligation 4 完了 + obligation 3 精密化

- ✅ **obligation 4 完了** (commit f522c634): `[HU:HC]=u`。(A) `index_hcInHu_eq_relindex_cInHu`
  (第2同型 `quotientInfEquivProdNormalQuotient` + card 分解、`U⊓HC=C`) + (C)
  `index_cInHu_subgroupOf_uInHu_eq_u` (第1同型 `quotientKerEquivRange`、`u=[U:C]`) + card 補題群
  (`card_uInHu_eq`/`card_cInHu_eq`/`card_cSub_eq_card_ker`)。crux+B (62fce025) を消費。
- ⬜ **obligation 3 (ψ linearity)** = `caseB_degree_qu` 唯一の残 sorry。`apply_one_eq_one_of_subset_
  characterKernel_of_isMulCommutative_quotient` (N=`commutator ↥HC`) + kernel 継承 (`liesOver_mem_
  characterKernel`) で、核心は **`⁅HC,HC⁆ ⊆ realized-(H₀ ⊔ C')`** (⊆ ker χ ∵ χ∈𝒳(H₀C'))。
  - ✅ fact 1 `derivedInG_H_le_H0` (`⁅H,H⁆≤H₀`, commit bf689bc7)。
  - ⬜ fact 2 `⁅C,H⁆≤H₀`: c∈C=ker(uActionHom) ⟹ c が H̄ 中心化 ⟹ `c h c⁻¹ ≡ h (mod N)` ⟹ ⁅c,h⁆∈H₀。
    `quotientMulAutHom_apply_mk'` + `QuotientGroup.eq` で N-membership を G に transport。
    ⚠ mk-coset 方向 (`y⁻¹h∈N` vs `yh⁻¹∈N`) は N 正規で両立 (conj_mem)。
  - ⬜ fact 3 `⁅C,C⁆=C'` (= `derivedInG cSub` = `cprimeSub`、ほぼ定義)。
  - ⬜ **assembly**: 鍵洞察 = **K=H₀C' は HC で正規** (`[H,C']⊆[H,C]⊆H₀` ⟹ H が K を正規化、
    C は C'◁C で K 正規化)。C' 単独は HC-正規でないが H₀C' は正規。⟹ HC/K で生成元 H,C の像が
    可換 (fact1/2/3 が mod K で commute) ⟹ HC/K abelian ⟹ `⁅HC,HC⁆≤K`。
    sup 上の commutator 直接分配は不可 ([[lean-normal-closure-good-elements]]) ゆえ商可換経由。
- caseB_degree_qu 完了で → (9.9) caseB_character_counts (9.9.b/c) → (9.8) → (11.8)/(10.7)。

### §12 追補² (lane-a /loop iter2): obligation 3 facts 1,2 完了 + assembly full path

- ✅ fact 1 `derivedInG_H_le_H0` (commit bf689bc7)、✅ fact 2 `commutator_cSub_H_le_H0` (`⁅C,H⁆≤H₀`,
  commit abbfb1d7、`quotientMulAutHom_apply_mk'` で W=conj·h·h⁻¹∈N transport)。
- fact 3 `⁅C,C⁆≤C'` = `derivedInG cSub` で定義的 (= `cprimeSub`)。
- **assembly full path (次反復で実装、~120行)**: 目標 = `⁅HC,HC⁆ ⊆ ker χ` (HC=hInHu⊔cInHu, huSub level)。
  ⚠ **正規性レベル**: K=H₀⊔C' は **G で非正規** (H₀ は M でのみ正規) ⟹ 商論法は **↥(H⊔C) level** で。
  1. **K◁(H⊔C)** (G-level group `data.H⊔cSub`): `H⊔C ≤ normalizer K`、`sup_le` で H,C 各々が K 正規化。
     h∈H: `(conj h)•K = (conj h)•H₀ ⊔ (conj h)•C'` (map_sup)、`(conj h)•H₀=H₀` (H₀◁M)、
     `(conj h)•C'≤K` (`h c' h⁻¹=⁅h,c'⁆·c'`、⁅h,c'⁆∈⁅cSub,H⁆⊆H₀ [fact2,comm,C'≤cSub]、c'∈C')。
     c∈cSub: `(conj c)•H₀≤K` (同様 fact2)、`(conj c)•C'=C'` (C'=⁅cSub,cSub⁆◁cSub)。
  2. **⁅H⊔C,H⊔C⁆≤K**: mk:=mk' (K.subgroupOf(H⊔C))、`map_commutator`+`map_sup` で
     `⁅H̄⊔C̄,H̄⊔C̄⁆=⊥`、`commutator_eq_bot_iff_le_centralizer`+`centralizer_sup` (repo `OddOrder.Mathlib.Subgroup`)
     +`sup_le`/`le_inf` で 4 facts (mapped) に帰着 (⁅H̄,H̄⁆=⁅C̄,C̄⁆=⁅H̄,C̄⁆=⊥ ⟸ facts 1/3/2 ≤K)。
     `Subgroup.map_eq_bot_iff`/`ker_mk'` で `⁅H⊔C,H⊔C⁆≤K`。
  3. **realized 転送**: huSub-level `⁅hInHu⊔cInHu,·⁆⊆realized-K`: `commutator_le`+各 commutator の
     G-coord が ⁅H⊔C,H⊔C⁆ に入る (`map_commutatorElement` 2 coe) → step2 適用。
  4. **obligation 3**: `apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`
     (N=`commutator ↥HC`、商可換 instance) + `liesOver_mem_characterKernel` で
     commutator ↥HC ⊆ ker ψ (← (g:huSub)∈⁅HC,HC⁆⊆realized-K⊆ker χ [hχker])。

### §12 追補³ (lane-a /loop iter5): obligation 3 assembly — lemma 名確定 + closure_induction 注意

facts 1,2 + bridge `derivedInG_eq_commutator` (⁅H,H⁆=derivedInG H) committed。assembly
`commutator_HsupC_le_H0Cprime : ⁅data.H ⊔ cSub, data.H ⊔ cSub⁆ ≤ chief.H0 ⊔ cprimeSub` を試作したが
下記 friction で revert (clean 状態は green、obligation 3 のみ sorry)。**次反復で完遂**:

確定 lemma 名 (build で検証済): `Subgroup.normal_subgroupOf_iff_le_normalizer (hKle : K≤HC)`、
`Subgroup.subgroupOf_sup le_sup_left le_sup_right` (A,A',B 全 implicit)、`Subgroup.subgroupOf_self`、
`Subgroup.map_top_of_surjective mk hmk_surj`、`Subgroup.commutator_eq_bot_iff_le_centralizer.mp`
(`..` 不可、引数なし)、`OddOrder.Mathlib.Subgroup.centralizer_sup` (Set 形)、
`Subgroup.subgroupOf_map_subtype : (K.subgroupOf H).map H.subtype = K⊓H`、`Subgroup.map_eq_bot_iff`、
`QuotientGroup.ker_mk'`、`Subgroup.map_commutator`、`Subgroup.commutator_comm` (=)、
`Subgroup.commutator_mem_commutator`。facts in ⁅⁆形: hHH=⁅H,H⁆≤K (bridge+fact1), hCH (fact2),
hHC' (commutator_comm), hCC=⁅C,C⁆≤K (bridge, =cprimeSub)。

**残 friction (次反復の要対処)**:
1. **conj fact `∀x∈HC,∀k∈K, xkx⁻¹∈K`**: `closure_induction` (k∈K=closure(↑H₀∪↑C') を
   `← closure_eq ×2, ← closure_union` で) は **dependent-motive** で binder 不一致 +
   `chief.H0_lt_H.le hy0` が Set→Subgroup mem 強制要 (`SetLike.mem_coe`)。**代替**: pointwise
   `MulAut.conj x • K = •H₀ ⊔ •C'` (`smul_sup`) で各 ≤K を示す方が clean かも。
2. quotient hcomm: `commutator ↥HC ≤ K.subgroupOf HC` を `← ker_mk', ← map_eq_bot_iff, commutator_def,
   map_commutator, map_top_of_surjective` → `⁅⊤,⊤⁆=⊥` → `← hAB (⊤=A⊔B)` → `commutator_eq_bot_iff_le_centralizer,
   centralizer_sup` → `sup_le (le_inf ..) (le_inf ..)` で 4 facts (hsub helper: ⁅P,Q⁆≤K → 商で⊥)。
3. obligation 3 wiring: `apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`
   (N=commutator ↥HC) + `liesOver_mem_characterKernel` で commutator ↥HC ⊆ ker ψ
   (← (g:huSub) G-coord ∈ ⁅H⊔C,H⊔C⁆≤K [assembly] ⊆ ker χ [hχker]; map_commutatorElement で transport)。

### §12 追補⁴ (lane-a /loop iter6): obligation 3 assembly 障害確定 + ↥M-level 修正案

obligation 3 (`caseB_degree_qu` ψ linearity = `⁅HC,HC⁆ ⊆ ker χ`) の assembly を複数アプローチで試行、
全て revert (clean 状態 green、committed 進捗保持)。**確定した障害**:
- `Subgroup.mem_sup` (積形 `∃y∈s,z∈t, y*z=x`) は **可換性必須** (Lattice.lean:586 は CommGroup 節)。
  ⟹ K=H₀⊔C' の元 k を `k=h₀·c'` 分解できない (G 非可換、H₀/C' は G-非正規)。
- `closure_induction` (k∈closure(↑H₀∪↑C')) は正しいツールだが case body で "failed to synthesize
  instance" (未解明、motive dependent + bracket/coercion 絡み)。
- ∴ commutator-over-sup (非正規 summand) は [[lean-normal-closure-good-elements]] の gap 直撃。

**次反復の修正案 (↥M-level)**: H₀ ◁ M (`H0_normalized_by_M`) ⟹ `chief.H0.subgroupOf M` は **↥M で正規**。
⟹ ↥M レベルで `mem_sup_of_normal_left` 使用可で k=h₀·c' 分解が通る。assembly を ↥M-subgroup
(`(data.H).subgroupOf M` 等) で証明し huSub へ transport (huSub ≤ ↥M)。OR `closure_induction` の
real error を live で特定して修正。確定 lemma 名は §12追補³ 参照。

**進捗総括 (この /loop セッション)**: caseB_degree_qu (Pf 9.9.a) の obligation 1 (θ₀抽出)・obligation 4
([HU:HC]=u)・obligation 3 facts 1,2 + bridge を committed (6 commits)。残 = obligation 3 assembly のみ
(機械的だが mathlib gap で高コスト)。難所の数学は全完了、残りは群論 plumbing。caseB_degree_qu は
signature 正しく cite 可。

### §12 追補⁵ (lane-a /loop iter7): caseB_degree_qu (9.9.a) SORRY-FREE 達成 🎉

obligation 3 (ψ linearity) を完成し **caseB_degree_qu (𝒮(H₀C') の各元 degree qu) が完全 sorry-free**。
obligation 1 (θ₀ inflation 抽出)・3 (linearity)・4 ([HU:HC]=u) 全完了。full build 3886 green。

**6 反復の obligation 3 struggle の真因 (重要教訓)**:
1. **`commutatorElement` (element commutator `⁅x,y⁆` の `Bracket G G`) は scoped instance** —
   `open scoped commutatorElement` が必要 (subgroup commutator `⁅H,K⁆` は別 instance で常用可)。
   fresh な element bracket を書くと `failed to synthesize Bracket G G`。
2. **`Subgroup.normalizer` は Set 引数** (`normalizer (S : Set G)`) — `normalizer (A ⊔ B)` は
   Subgroup の A,B を Set-sup (union) に解釈。Subgroup-sup の normalizer は `normalizer (↑(A⊔B):Set)` と書く。

**完成した補題群** (全 axiom-clean candidate、AxiomsCheck 未登録):
- `derivedInG_eq_commutator` (⁅H,H⁆=derivedInG H)、`HsupC_le_normalizer_K` (K=H₀C' は HC で正規、
  closure_induction on k で ⁅x,k⁆∈K、帰納共役は K の部分群閉性)、`commutator_HsupC_le_H0Cprime`
  (G-level ⁅HC,HC⁆≤K、商/中心化子)、`commutator_hcInHu_le_realized` (huSub 転送、comap 経由)。
- 構造的 commutator facts: `derivedInG_H_le_H0` (⁅H,H⁆≤H₀)、`commutator_cSub_H_le_H0` (⁅C,H⁆≤H₀)。

**次手**: (9.9) `caseB_character_counts` の (9.9.a) conjunct を proven caseB_degree_qu で wire
(残 (9.9.b)/(9.9.c))、(9.8) `caseA_character_counts`、→ (11.8)/(10.7) → card_kappaHall。

### §12 追補⁶ (lane-a /loop iter8): (9.9) に (9.9.a) wire + 残 §9 counts frontier 評価

(9.9.a)=caseB_degree_qu を `caseB_character_counts` の第1 conjunct に wire (honest)。残 §9 counts の評価:

**残 §9 counts (全て深い Peterfalvi character-counting、次反復の deep 着手対象)**:
- **(9.9.b)** `caseB_character_counts` 第2/3 conjunct: `{φ∈𝒮(H₀)|¬irr}.ncard = p-1` (reducible count) +
  reducible は degree qu かつ 𝒮(H₀C) に入る。Clifford counting (どの θ̄∈Irr(H̄) が reducible Ind を生むか)
  + inflation 機構 (obligation 1 で構築済) で着手可か要分析。
- **(9.9.c)** 第4 conjunct: `(𝒮(H₀C') に irr 無) → C=⊥ ∧ u=(p^q-1)/(p-1)` (exceptional case)。
- **(9.8)** `caseA_character_counts` (S11:3479): case (a) の counts ((9.8.b/c/d))、parallel to (9.9)。
- **(9.10)** `exceptional_case_frobenius_realization` (S11:3913): ⚠ 第1 conjunct
  `chars.quotientSemidirectFrobenius` は **opaque Prop field** ([[scaffold-sorry-free-not-done]]、
  de-opacify 要)。第2/3 は exceptional u + HU Frobenius (深い)。
- **(9.11)** `sibleyTarget_H0C` (S11:3936): §14-gated ((6.8) + Sibley Dade witness)、lane-b/d 寄り。

これらは (10.7) typeII_derived_frobenius / (11.8) を unblock する (両者 §9 counts 依存)。次反復は (9.9.b)
reducible count を deep 分析 (tractable か §3-§7 char API gate か、原文 04.13 (9.8.b)/(9.9.b) 読んで判定)。

### §12 追補⁷ (lane-a /loop iter9): 残 §9 counts は §4 Theorem (4.5)/(4.7) gated (要判断)

原文 04.11 (9.8.b,c)/(9.9.b) 精読の結論: **§9 の reducible COUNT 系は §4 Dade framework gated**で、
(9.9.a)=caseB_degree_qu (純 Clifford, DONE) とは本質的に異なる。
- **(9.9.b)** `𝒮(H₀) は exactly p-1 reducible μ_j` の証明 = 「By (4.7) and Theorem (4.5), 𝒮(H₀)/𝒮(H₀C)
  contain exactly p-1 reducible characters」。⟹ **§4 Theorem (4.5) + (4.7)** (Dade family の
  reducible/exceptional count = |W₂|-1 = p-1) + **(8.4.d)** (Hypothesis (4.2) for M/H₀) に依存。
- **(9.8.b)** 同様 ((4.7)+(4.5))。**(9.10)** = (9.8.c)+(9.9.a,c)+(9.7)、(9.9.c) は (9.9.b) 依存。
- **repo 確認**: §4-§7 (S04-S07) に Theorem (4.5)/(4.7) の reducible-count 定理は **citeable な形で不在**
  (Dade isometry・omega/muGrid・certain-type Clifford はあるが「p-1 reducible」count 定理は無い)。
  (8.4.d) (Hypothesis 4.2 for M/H₀) も S10 に不在。

**⟹ lane-a の §9 char 内訳**: 純 Clifford な (9.9.a) は DONE。reducible counts ((9.9.b)/(9.8.b)/(9.10))
は §4 Theorem (4.5)/(4.7) (Dade reducible-count, 未形式化) gated。これは lane-a の S10-13 cluster の
**上流** (§4 = S04 Dade foundational)。(10.7)/(11.8) も §9 counts 経由でここに bottom-out。

**要判断 (ユーザー/hub)**: (a) §4 Theorem (4.5)/(4.7) を formalize (上流優先だが S04 で大物・scope 外気味)、
(b) §4 signature を pin して (9.9.b) で cite (policy 可、但し (4.5) statement は複雑)、(c) lane-a を
§4-gated でない別 FT-path 作業へ redirect。lane-a の非-§4-gated な §9 char 内容 ((9.9.a)) は完了済。

### §12 追補⁸ (lane-a /loop iter10): §9 counts の gate を §6 Theorem (4.5)/(4.7) + (8.4.d) に精密特定

Theorem (4.5)/(4.7) の所在確定 (mmd 04.6 = 書籍 §6 "Dade Isometry for Certain Type of Subgroup"):
- **(4.5)** (04.6:39): Hypothesis (4.2) 下、μ_j = ∑_{0≤i<w₁} μ_{ij} (0≤j<w₂) の reducible 構造。
- **(4.7)** (04.6:67): Hypothesis (4.6) 下、Supp χ ⊂ A∪{1} 等。
- ⟹ (9.9.b) の「p-1 reducible」count = w₂-1 (w₂=p)。**repo S06** に `Hypothesis46`/`CertainTypeHypothesis`/
  omegaProdChar 機構は存在するが、**μ_j reducible-count 定理 (4.5)/(4.7) は citeable な形で未完**。
- **(8.4.d)** (Hypothesis (4.6) for M/H₀, M/H₀C) は **§8 = S10 = lane-a scope** (S10:451,588 に
  「Hypothesis (4.6)/(5.2) specializations ... kept as ...」言及 = 部分的)。

**⟹ (9.9.b)/(9.8.b)/(9.10) の path**: (8.4.d) [S10/lane-a] Hypothesis(4.6)-for-M/H₀ 構成 →
S06 Theorem (4.5)/(4.7) reducible-count (要 formalize/拡充) → (9.9.b) instantiate。**substantial な
§6/§8 char-framework 作業** (multi-step、複数ファイル)。

**lane-a frontier 総括 (honest)**: 純 Clifford な §9 主結果 (9.9.a)=caseB_degree_qu は DONE。残る
§9 counts + endgame ((10.7)/(10.8)/(11.8)) は **§6/§8 char-framework endgame** (Dade reducible-count
+ §7 norm-counting + coherence) gated = 本プロジェクトで「最難・最高コスト」と記された指標終盤。
lane-a がこれを担うのは FT 経路・上流優先で妥当だが quick win でなく multi-session 級。

**次手 (concrete)**: (8.4.d) Hypothesis(4.6)-for-M/H₀ 構成 (S10、lane-a scope、上流優先の entry point)。
S10:445-595 の既存 specialization を土台に。

### §12 追補⁹ (lane-a /loop): 「(4.5)/(4.7) 未完」評価は STALE — §6 reducible-count を完結

追補⁷⁸ の「§6 Theorem (4.5)/(4.7) の reducible-count 定理は citeable な形で未完」は **STALE だった**
([[verify-port-state-by-number-not-coq-name]] / [[grep-sorry-docstring-contamination]] 系)。実コード
を grep/Read で検証した結果:

- **(4.5)(a),(b) の Clifford 分類は 2026-06-11 に完成済** (`S06_CertainTypeClifford.lean`、commit
  `1091b8f7`〜`a1679621`): `exists_eq_certainType_or_induce` = 「Irr(L) = {μ_{ij}} ∪ {Ind^L_K χ}」
  (χ∉{χ_j})、支持補題 `card_fixed_irr_le_W2` (Brauer count ≤ w₂) / `inertia_eq_K_of_forall_chiRestrict_ne`
  (I_L(χ)=K) / `chiRestrict_injective` / `card_charGroup_W2` (|Ŵ₂|=w₂) すべて axiom-clean。
  追補⁷⁸ は (4.5.b) 完成後に書かれたのに「未完」と誤評価していた。
- **不在だったのは reducible-COUNT corollary のみ** (分類の上の数え上げ)。これを本セッションで実証明・追加
  (`S06_CertainTypeClifford.lean`、全 axiom-clean [3 標準公理]、leaf build green):
  - `induce_chiRestrict_not_isIrreducible`: `Ind^L_K χ_j = μ_j = ∑_i μ_{ij}` は reducible (w₁≥2 個の相異
    既約の和; 既約と仮定すると μ_{0j}/μ_{1j} 両方に等しくなり矛盾)。
  - `induce_not_isIrreducible_iff`: χ∈Irr(K) で `Ind^L_K χ` reducible ⟺ χ=χ_j (∃χ₂, chiRestrict χ₂=χ)。
  - **`card_reducible_induce_eq_W2`**: `|{χ∈Irr(K) | Ind^L_K χ reducible}| = w₂` (= 相異 χ_j の数
    = |Ŵ₂|)。`chiRestrict` の bijection で。

**⟹ §9 reducible counts の残ゲートは純粋に (8.4.d) bridge のみ**: 「(4.5)/(4.7) 未完だから gated」は
誤りで、§6 count は **citeable** (`card_reducible_induce_eq_W2`)。残るのは「§9 の `chars.SOf chief.H0`
(HU から M への induced family) を L=M/H₀ の §6 induction-family と同一視する (8.4.d) 商 bridge」。
w₂=p で count は p、H̄-nontriviality で j=0 column を除いて **p-1** = (9.9.b) の主張。**次手は変わらず
(8.4.d) bridge** だが、ゲートが 2 つ (§6 count + bridge) から 1 つ (bridge) に縮小し、§6 count は完了。

### §12 追補¹⁰ (lane-a /loop cont.): §6 side を完全クローズ — H-nontrivial count = w₂-1、bridge も「構造のみ」と判明

**重要な簡約 2 件**:
1. **count は STRUCTURAL Hypothesis のみ要 (Dade isometry 不要)**: `card_reducible_induce_eq_W2` /
   (4.7) structural は全て `S06.Hypothesis L` (= K/W₁/W₂ + complement) 上で動き、`Hypothesis46` の
   Dade τ/dade0 は不要。⟹ (8.4.d) bridge は **`S06.Hypothesis (M⧸H₀)` (構造のみ) の構成 + 文字対応**で
   足り、商上の Dade 等長写像構成 (最重量級) は **不要**。
2. **(4.7) structural も既存だった** ([[verify-port-state-by-number-not-coq-name]] 再び):
   `not_subset_characterKernel_chiRestrict_of_ne_one` (S06_CertainTypeSupport、χ₂≠1 ⟹ W₂⊄Ker χ_j、
   `Hypothesis L` 構造のみ) が (4.7) j≥1 核を既に供給。

**本セッションで §6 side を完全クローズ** (commit 次、2 lemma axiom-clean [3 標準公理]、leaf build green):
- `Hypothesis.chiRestrict_one_eq_trivial` (S06_CertainTypeSupport): trivial column χ₂=1 ⟹
  chiRestrict 1 = 1_K (anchor `certainType_zero_column_anchor.2`)。j=0 列が唯一の H-trivial reducible。
- **`Hypothesis.card_reducible_Hnontrivial_induce_eq_W2_sub_one`**: 任意の `W₂ ≤ H ≤ K` に対し
  `|{χ∈Irr(K) | Ind^L_K χ reducible ∧ H⊄Ker χ}| = w₂ - 1`。reducible↔Ŵ₂ bijection から χ₂=1 列
  (=1_K, H⊆Ker) を除外、χ₂≠1 列は (4.7) で H⊄Ker。**これが (9.9.b) "p-1 reducible" の §6 side 完全形**
  (H=H̄、w₂=p で p-1)。

**⟹ §6 side は 100% 完了。残る唯一のピース = §9↔§6 character bridge** (構造のみ):
- (B1) `S06.Hypothesis (↥M ⧸ H₀')` 構成 (K=HU/H₀, W̄₁, W̄₂; `typePData_toS06Hypothesis` (S12:1062, L=M版)
  が template、商 transport が要点)。**H₀ ◁ M 要確認** (chief factor data から)。
- (B2) `chars.SOf chief.H0` (§9 induced family, HU→M) ↔ §6 induction-family {Ind^L_K χ} on M/H₀ の
  同一視 ((1.6): H₀⊆Ker の M-文字 = M/H₀-文字)。その下で reducibility + H̄-nontriviality 対応。
- (B3) `card_reducible_Hnontrivial_induce_eq_W2_sub_one` を H=H̄, w₂=p で instantiate → (9.9.b) count。
次手 = B1 (S10、`typePData_toS06Hypothesis` 商版)。

## 2026-07-11 (lane a): (8.11) 閉鎖 + (8.17) type-I branch の mis-layering 決着

- **(8.11) `hall_maxNilpotentNormalHall_and_mainSubgroup` は完全証明済** (6b08f22d、
  axiom-clean)。上の表の「Iₛ / BG endpoint 待ち」は解消 — BG 側 (Msigma_isHall /
  mainSubgroup_eq_Msigma / primeFactors_Msigma_eq_sigma / maxNilpotentNormalHall_isHall)
  は全て landed 済だった。消費: S14 WitnessSylowCyclic ×4 + (10.8) hB。
- **(8.17) type-I branch**: cover_nonidentity + pairwise_disjoint は実証明 (f4140838)。
  `cover_subset_kernels` は **§8 では証明不能な mis-layered claim** と判明 (BG Thm E は
  R(x)-thickening を保持; collapse は (12.17) 証明内で (12.7) から)。migration 計画 =
  **issue 9080** (S14 側で typeI_frobenius + 新 collapse lemma
  `Mtilde_eq_sigmaSharp_of_forall_centralizer_le` を使う; その後 field 削除)。
