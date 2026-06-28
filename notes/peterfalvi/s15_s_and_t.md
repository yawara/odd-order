# Peterfalvi §15: The Subgroups S and T — mini-roadmap (本文最大規模)

**スコープ**: Peterfalvi §15 (pp.75-86, 12 ページ), mmd `04.15_pp_75_86_The_Subgroups_S_and_T.mmd` (365 行).  
**結果数**: 17 結果 ((13.1)-(13.17)) + 1 補足 ((13.18)-(13.19)) = 計 19 個の番号付き内容.  
**形式化先** (予定): `OddOrder/Peterfalvi/S15_SAndT.lean` (将来 subdirectory 分割可能性大)  
**ROADMAP 上の位置**: **Phase 2b 第 6 波** (§10-§14 完成必須, §16 直前).  
**役割**: 最小反例 G の 2 つの特殊最大部分群 S, T の **位数・正規化群・指標論的詳細**. 指標演算を極限まで詰めて §16 の最終矛盾を導く直前準備.

---

## ✅ LIVE STATUS (2026-06-29, 正本 — ゲートなし方針で再開, lane c /loop)

> **下の 2026-06-23 ブロックの「§15 lane-c ungated closable work 枯渇 / 全 cross-lane gated」は
> stale な待ち文化フレーミング** ([[ft-four-fronts-w1-w4]] の 2026-06-28 再配分が明示的に却下した症状)。
> 実際には「上流 sorried を cite する」「genuine な arithmetic core を抽出する」だけで closable work は在る。
> 技術的な carrier 診断 (U/W₂ reconciliation の所在) は今も有効な参照。

### 本セッション成果 (2026-06-29, **5 commits** — carrier-free norm toolkit を構築中)
1. **(13.2.b) 位数 `|P|=p^q` = 実証明** (`Hypothesis.card_P_eq`, commit `a1e59e84`):
   §11 の Wielandt 順序関係 `typeII_III_IV_order_relations` (type-II 側) を `typeP := Sdata` の
   `TypesIIIIIIVSetup` に適用。nontrivial-core (U≠⊥ via 不変 index / |W₁| prime / A₀(S) TI) は type-II
   witness から read off。唯一の non-derivable 入力 = `Sdata.W2 = W2` reconciliation を**明示仮説に隔離**
   (= `Sdata_U_eq`/`Sdata_W1_eq` の W₂ 版; **issue 3001** で carrier threading)。`P_elementaryAbelian`
   と `u_bound` は genuine §10/§11/§9 (lane a) content ゆえ未着手。
2. **(13.12)/(13.15) 数値核 = 抽出** (`caseB_numeric_forces_q_three`, commit `389650dd`):
   `m < qp/((2q+1)(p-1))` + (13.11) 下界 ⟹ `q=3` の純 ℚ-arithmetic (3 ケース)。`m_value_*` 族と同様の
   self-contained 補題、(13.12) c=1 と (13.15) u 値の両者が consume する再利用核。
3. **(13.5.c) inflation norm bound = 実証明** (`sum_normSq_erase_one_ge_of_const_on_subgroup`, commit `c038fc59`):
   `∑_{x∈H#}|α(x)|² ≥ (|P|−1)α(1)²` (α が P 上 α(1) に定値 = P が α の全 constituent の kernel に入る inflation
   状況)。**任意有限群 H + 部分群 P の carrier-free 一般補題** — Dade 機構も Hypothesis carrier も不要
   (α=α(1) on P + 二乗ノルム非負 only)。`H=↥hyp.H`, `P=S_F` で (13.5) に特化。
4. **innerSum self-identity = 実証明** (`innerSum_self_eq_sum_normSq`, commit `56886c1c`):
   `ClassFunction.innerSum α α = ↑(∑_g ‖α g‖²)` — 抽象 inner-product API と具体 `∑|α|²` の**橋**
   (API に欠けていた)。`RCLike.mul_conj` 経由、任意有限群 H。norm cascade 全 step が依存。
5. **(13.6) quadratic 非負 = 実証明** (`caseB_quadratic_nonneg`, commit `54a1784f`):
   `0 ≤ (|P|−1)b² − 2ub` (u ≤ (|P|−1)/2)。`α(1)=qb` 代入で (13.6) の補正項
   `q²((|P|−1)b²−2ub) ≥ 0` を与える、純 ℤ-arithmetic 核。`(|P|−1−2u)b² + 2u·b(b−1)` 分解。

### ★ 生産的手法 (2026-06-29) — **carrier-free core 抽出** (9 commit で実証、arithmetic toolkit ≈完成)
norm cascade ((13.5)-(13.10)) は「Hypothesis の opaque grid が τ-isometry/直交性/次数を carry しない」ため
**wrapper 定理 (∃ data, opaqueProp 形) は carrier-gated**。だが **各 cascade step の genuine な数学的核は
carrier-free な一般補題として抽出・実証明できる**。これが**待たずに本丸を進める正攻法**
(reallocation §2 の consumer-side prescribed path; STOP(c) の sorry-shuffle でない — 実定理・実証明・再利用可)。
**着地済 toolkit** (§15 norm-cascade + endgame の arithmetic は網羅):
- `caseB_u_bound_arith` = 13.2.c 橋 `(p−1)^{q−1}≤(p^q−1)/(p−1)` (9.7 FPF 下界 → u≤(|P|−1)/2)
- `sum_normSq_erase_one_ge_of_const_on_subgroup` = 13.5.c (inflation 下界 `∑_{H#}|α|²≥(|P|−1)d²`)
- `innerSum_self_eq_sum_normSq` = innerSum↔∑‖·‖² の橋 + `sum_normSq_eq_card_mul_inner` = Parseval `∑_H=|H|⟨α,α⟩`
- `caseB_quadratic_nonneg` = 13.6 quadratic 非負 `0≤(|P|−1)b²−2ub` (**13.8 も `b↦±b` で被覆**)
- `caseB_eta_norm_core` = 13.7 不等式核 `∑_{H#}|η₁₀|²≥|H#|` (Parseval + 13.5.c + n≥1/abelian)
- (既出) `caseB_numeric_forces_q_three` = 13.12/13.15 数値核、`card_P_eq` = 13.2.b 位数

**⟹ cheap carrier-free arithmetic cores はほぼ枯渇** (starved でなく「土台が建った」)。**残る genuine work は 2 系統**、
いずれもより重い/cross-lane:
1. **重い character-theoretic core** (carrier-free): 13.18.b Frobenius induced-trivial norm
   `‖Ind_A^F 1‖²=(|N|−1)/|A|+1`。**✅✅ 完成** (`norm_induce_one_frobenius`, commit `d15bb4fc`)。
   value 3 piece (`induce_one_apply` / `induce_one_eq_zero_of_mem_normal_inf_bot` (γ=0 on N#) /
   `induce_one_eq_one_of_mem_complement` (γ=1 on A#、repo の `IsFrobeniusGroup.trivialIntersection` cite))
   + reciprocity assembly (`inner_induce_eq_inner_restrict` + star-drop `invOf_eq_inv`/`star_inv₀` +
   sum-split)。**§13 で `‖β_j‖²=(u-1)/q+2` を組むときに直接 cite 可** (A=W̄₁, N=Ū, |N:A|=u, |A|=q)。
   **残る重い carrier-free core**: 13.9.b の [Is] Lemma 3.14 (∑_{⟨x⟩-class}|χ|²≥count、代数的整数論/Galois、
   より重い)。13.18 の他 part (13.18.a support / 13.18.c,d Γ 分解) は grid/Dade 依存 (carrier-gated)。
2. **carrier/grid enrichment** (cross-lane、**issue 3002 で hub escalate 済**): 全 cascade wrapper を
   Hypothesis の grid τ₃-isometry/ω-orthonormality field から faithful 化 (toolkit 完成済ゆえ field が入れば
   組める)。FeitThompson constructor + §16 carrier (lanes B/D) に波及。consumer-side で contract pin も可。
   **次 /loop**: 1 の Frobenius reciprocity step を継続 (solo)。

### frontier (ゲートなし方針)
- **(A) Dade norm cascade ((13.5)-(13.10) + (13.3)/(13.4))** = §15 hard core。wrapper は carrier-gated だが
  **carrier-free core は上記手法で抽出可** (13.5.c 着地)。完全な wrapper 化には Hypothesis enrich
  (FeitThompson 2 constructor + §5 性質補題に波及、cross-lane = issue で hub escalate)。
- **(B) 後半 arithmetic ((13.12)/(13.13)/(13.15))** = (A) の (13.10) に gated だが数値核抽出済 (上記 2)。
  abstract `caseX_for_S : Prop` 仮説が残課題 (scaffold design)。

---

## ✅ LIVE STATUS (2026-06-23 再開², ⚠ framing stale — 上ブロック参照) — step-3 wiring 着地後の carrier consumer

> 以下が現状の正本。下の「🔑 carrier 診断」「🔧 POLE-1 carrier 構築」節は **step-3 wiring 着地前の
> 歴史的経緯** (carrier wall の診断・解消過程)。carrier は既に sorry-free 完成 (`exists_typePData_W1_eq_of_isTypeP2`)
> + `Sdata` thread 済 + lane-h が `mp.S_typeP2` 着地 (commit `6ba0bce5`) で step-3 gate 解消済。

### carrier consumer 成果 (本セッション)
1. **`exists_typeI_maximal_overNormalizer_U` 本体 = sorry-free** (commit `7eeb4555`): 2 本の bare sorry を
   `Sdata` carrier から実証明。F-ask `P⊓U=⊥` = `Sdata.derived_complement` の disjoint から; Hall-faithfulness
   `|U|⟂[S:U]` = `[S:U]=|P|·|W₁|` index 分解 (`Sdata.card_W1_eq_derived_index`/`card_U_eq_index`) + `hcop` +
   `coprime_card_kernel_complement` (U⋊W₁ Frobenius)。
2. **`basic_structure` (13.2.a-c,e) = gated-endpoint skeleton 化** (commit `b0a60fbe`):
   - **`S_typeP2 : IsTypeP2 S` を S15.Hypothesis に追加** (mp.S_typeP2 → Section16Inputs → S15.Hypothesis、
     sorry-free thread)。型決定 (13.2.a) を `isTypeII_of_isTypeP2` (lane-f, axiom-clean) で **sorry-free 実証明**
     (`S_typeII_or_typeIII`/`q_lt_p_forces_typeII` を type-II 側で)。
   - **(13.2.b,c,e) M_F-構造を faithful producer `basic_structure_gated` に localize** (P が p^q el-ab、
     U abelian + U⋊W₁ Frobenius、u-bound、A_0(S) TI)。§16 σ-structure (M_σ=M_F el-ab p^q、**repo 未形式化**) に gated。
   - `basic_structure` 本体は sorry-free assembly。

### 現フロンティア分類 (残 21 sorry、全て他レーン/未形式化 gated)
- **char (lane-b §3-13 char API): 10** — `sibleyTarget_S`/`character_degree_analysis`/`lambda_forces_T_caseB`/
  `tiSubset_character_orthogonality`/norm cascade 4本/`analytic_inequality`/`beta_support_norm_and_remainder`/
  `typeI_orthogonality_dichotomy`。
- **numeric (char-determined / 抽象 Prop scaffold): 4** — `numeric_bounds` q=3 (u/c は analytic 待ち + p≥5 不在)、
  `c_eq_one`、`caseA_parameters`/`caseB_order_u` (`caseX_for_S : Prop` 抽象仮説ゆえ u の値は char が決定、honest 不可)。
- **§13 counting / BG Thm E: 3** — `card_Q_eq`(|Q|=q^p)、`tConjugate_fitting_data`、`card_LF_coprime_pq`(BG Thm E=lane-f)。
- **§16 σ-structure (未形式化): 2** — `basic_structure_gated` (P el-ab p^q + Frobenius、ユーザー裁可で skeleton 化、
  本体は lane-f BG§14-16 領域)、`complement_inf_Q_structure`。
- **T 側構造: 1** — `normalizer_W1` (Q⊔W2 = T 側 §16 構造)。

⟹ **§15 の lane-c 単独 ungated closable work は枯渇** (carrier consumer は完遂、型決定は sorry-free)。
残りは lane-b char / lane-f §16 σ-structure (ユーザーが新規形式化を保留) / §13 counting 待ち。
次手 = 要 hub/ユーザー判断 (基準: [[lanes-are-equivalent-no-specialty]]、再配置 or gate 待ち self-resume)。

---

## 🔑 lane-c carrier 診断 (2026-06-23, relane §11→§15 後の最初の精査)

**owner = lane-c** (`S15_SAndT.lean`、2026-06-23 に H→C 移譲、issue 4007)。最初に文書順最上流
`basic_structure` (13.2) を精査して判明した **carrier 設計の核心課題** (次 session の着手前提):

### 課題: `Hypothesis` が type-P 分解を pinning していない
- `Hypothesis` は S, T, U, V, W1, W2, P, Q を **raw subgroup** として持ち、`S_deriv_eq_PU :
  derivedInG S = P ⊔ U` は **join のみ**で `U ⊓ P = ⊥` (complement 性) を持たない。
- `typePData_of_isTypeNonI hyp.S_nonI` で `TypePData S` は取れる (public) が、その `.U`/`.W1` は
  **新 witness** で `hyp.U`/`hyp.W1` と一致保証なし。complement は一意でないため、抽出 `TypePData.U`
  ↔ `hyp.U` の **reconciliation は現フィールドから導出不能**。
- ⟹ `basic_structure` の `UW1_frobenius` (= `typeP_uW1_frobenius` は `data.U`/`data.W1` 上) /
  `U_commutative` が `hyp.U`/`hyp.W1` に転送できず **blocked**。
- これは (13.1.b)「S = (P⋊U)⋊W₁」の**形式化が不完全** (型-P witness を carry していない) のが原因。

### ⚠️ 訂正 (2026-06-23 lane-c 再開時、main マージ後の精査): enrich は **lane-local でなく cross-lane**
**上の数学的洞察 (U-reconciliation が必要) は正しい。が、当初の「`Hypothesis` は producer 無しゆえ
field 追加は C 所有・安全」は誤り。** 実際には `S15.Hypothesis` は
`sectionSixteenHypothesis_of_inputs` ([`OddOrder/FeitThompson.lean:655`]) で **record literal として
明示構成**され、各フィールドを `inp : Section16Inputs G` (= lane-f の POLE-1, issue 7005) から取る。
よって `S15.Hypothesis` に `Sdata : TypePData` を足すと:
1. `FeitThompson.lean:655` の record literal が壊れる (**lane-c 非所有**);
2. ソースとして `Section16Inputs` / `Section16TypePStructure` / `section16TypePStructure_of_components`
   にフィールド追加が必要 (**すべて lane-f 所有 = FeitThompson.lean**);
3. discharge には「**指定した complement `U` を持つ `TypePData mp.S` を構成する**」実作業が要る
   (`typePData_of_isTypeNonI` は自前の `U` を作るので使えない)。`hyp.U` の源
   `exists_kappaHall_invariant_complement_to_MF` ([`S14_TypePComplement.lean:85`]) は内部で
   Schur–Zassenhaus complement (`M_F ⊓ U = ⊥`) を作りながら**返り値型で破棄** (`obtain ⟨U, -, …⟩`)
   している。露出 + `TypePData` 化が lane-f の作業。

⟹ **honest fix = cross-lane carrier enrich** (lane-f の `Section16TypePStructure` に
`Sdata : TypePData mp.S` / `Tdata : TypePData mp.T` を reconciliation 付きで carry させ、
`S15.Hypothesis` へ thread)。lane-f の POLE-1 producer は既に sorry なので obligation は吸収されるが、
TypePData の complement 指定構成は実作業。**lane-c が独断で触れない (cross-lane judgment)** ⟹ HUB issue
4008 で escalate。当初案の reconciliation 設計 (`Sdata.U = hyp.U`, `Sdata.W1 = hyp.W1`, T-side 対称)
自体は正しい — 配置先が lane-c の `Hypothesis` でなく lane-f の `Section16TypePStructure`。

### `basic_structure` (13.2) = 5 部 capstone (単一 leaf でなく複数 session)
1. **carrier reconciliation** (上記 enrich; `hyp.U`=type-P U の pinning) → UW1_frobenius / U-side facts。
2. **type II/III 判定** = 型 IV/V 除外。V= `no_typeV_maximal` (10.10, lane-b S12 sorried, cite 可)。
   IV 除外 + 型確定は §15 解析 (cross-lane 寄り)。`one_typeII : IsTypeII S ∨ IsTypeII T` は片側のみ。
3. **P el-ab 位数 `p^q`** = §15 固有 (chief factor = 全 Fitting, H₀=1; §11 の H=p^q·|H₀| より強い)。
4. **u 上界** `u ≤ (p^q-1)/(p-1)` = (9.7) Singer (lane-c が 2026-06-23 に `clifford_dichotomy` で
   `|Ū| ∣ (p^q-1)/(p-1)` を確立済 → u=|Ū| で landable)。
5. **U_commutative** = type II/III の `TypeIIData`/`TypeIIIData.U_commutative` から (型確定後)。

### 既に証明済 (sorry なし、再着手不要)
`not_conj_of_isTypeI_of_isTypeNonI` (1179)、`isHall_subgroupOf_primeFactors_of_coprime_index` (1085)、
`le_kernel_of_isMulCommutative_of_inf_ne_bot` (1162)、`typeI_U_le_fitting_of_coprime` (1196,
basic_structure の sorried signature を cite)、`typeI_overNormalizer_U_le_fitting` (1267)、
`q_not_dvd_kernel` (1645) 等。

### frontier 全評価 (2026-06-23 lane-c, main マージ後) — 実 sorry 23 本は**全て cross-lane gated**
clean な lane-local win は無い。内訳:
- **基盤 (cross-lane carrier, lane-f)**: `basic_structure` (245, 上記訂正)、`sibleyTarget_S` (258, §14)、
  `card_LF_coprime_pq` (1154, BG Thm E = F)、`exists_typeI_maximal_overNormalizer_U` の `hdisj`/`hUhall_cop`
  (1303/1352, carrier faithfulness = F-ask)。
- **char-theory (lane-b §3-13 char API)**: `character_degree_analysis` (300)、`lambda_forces_T_caseB` (309)、
  `tiSubset_character_orthogonality` (332)、norm cascade (349/356/363/370)、`analytic_inequality` (379)、
  `numeric_bounds` q=3 conjunct (523, p≥5 不在)、`c_eq_one` (529)、`caseA_parameters` (536)、
  `caseB_order_u` (700)、`beta_support_norm_and_remainder` (1744)、`typeI_orthogonality_dichotomy` (1841)。
- **§15 固有 Fitting 構造 (`|Q|=q^p` / chief factor、type-P carrier に bottom out)**: `card_Q_eq` (1115)、
  `tConjugate_fitting_data` (1135)、`complement_inf_Q_structure` (1539)。`TypePData` は Fitting **位数**を
  pin しない (`H = maxNilpotentNormalHall M` のみ) ので、これらは Singer rank + chief-factor 論を要し、
  basic_structure の `P_order` と同じ carrier reconciliation に依存。
- **§13 multi-obligation (lane-h 確認済)**: `normalizer_W1` (831, card_Q_eq + W₁⊆Q + Q# TI + d=1 + KW₂ Frobenius)。

⟹ **lane-c の S15 frontier は現在 ungated closable Lean work が無い。要 HUB/ユーザー判断** (cross-lane enrich
を誰が所有するか、または lane-c を別 FT-path セグメントへ再配置)。正本 = この節 + issue 4008。

### ✅ 確定 (2026-06-23 続, lane-c 再開 deep dive、ユーザー裁可 option 1): carrier wall を**原文+signature で厳密再確認**
上の診断は憶測でなく確定。Pf (13.2) 証明本文 (`04.15_...mmd:35`) を読み、各 cite を repo 追跡:
- (13.2.a) type II/III 分類 = (10.10)/(11.9.b,c); U abelian = 型定義; UW₁ Frobenius = (8.4.d)。
- (13.2.b) P 基本可換 `p^q` = (10.11)/(11.7)。**(11.7)=`S13.H_elementaryAbelian` は `S13.Hypothesis M` 入力**
  (rich carrier: `base.typeP`/`s11Setup`/`chief`)。「IsTypeII M → |M_F|=p^q」の直接 lemma は無く、必ず §13.Hyp 経由。
- (13.2.c) `u≤(p^q-1)/(p-1)` = (9.7) `clifford_dichotomy` (sorry-free 既出, `|Ū|∣(p^q-1)/(p-1)`) + 算術。
  hyp.u=|Ū| は Hypothesis field (`card_U_eq_uc`/`C_eq`) から def 上成立だが、(9.7) を hyp.S に適用するには
  §11 chief-factor setup の reconciliation 要 → wall。
- (13.2.e) TI-subset = (8.13)/(12.7) char/structural。
**核心 = reconciliation wall**: `typePData_of_isTypeNonI hyp.S_nonI` で `TypePData hyp.S` は取れるが
intrinsic `.U`/`.W1` が `hyp.U`/`hyp.W1` と一致する保証が bare Hypothesis に無い (`P_eq_SF` で `.H=hyp.P` だけ一致)。
全上流が rich carrier 入力を要し、それを §15 Hypothesis から構成するには step-3 wiring = **lane-h の (13.2.a)
`IsTypeP2 mp.S` 着地**が必要。**数学は全存在 (Pf 原文 + repo sorried) = 形式化順序の問題、研究 gap でない**
([[feedback-dont-mislabel-formalization-as-research]])。⟹ deep dive は「§15 に lane-c sorry-free closable work
無し」を厳密確定。**4 回目の再 deep-dive は不要** — 次手は lane-h 待ち (self-resume) か別作業再配置。

---

## 🔧 POLE-1 TypePData carrier 構築 (2026-06-23 relane #3, issue 4008 = option A 裁定)

hub が issue 4008 を **option A** で裁定 → lane-c が POLE-1 tp producer carrier を引き取り
(`FeitThompson.lean` tp系 + `S14_TypePComplement.lean` complement 露出)。目標 = `Section16TypePStructure`
に `Sdata`/`Tdata : TypePData` を carry させ、`basic_structure` の U-side 結論を carrier から実証明。

### ✅ step 1: complement 性露出 (commit `1a807071`)
`exists_aInvariant_complement_within_normal` (AInvariantComplement.lean) / `exists_kappaHall_invariant_complement_to_MF`
(S14_TypePComplement.lean) の返り値に `M_F ⊓ U = ⊥` を追加 (内部 `IsComplement'` から、従来 `obtain ⟨U,-,…⟩` で破棄)。
→ `typePData_of_isTypeP_of_inputs` の `hDcompl` 入力に必要。

### ✅ step 2: sorry-free engine (commit `a82ca82a`)
`typePData_of_kappaHall_hallComplement` (FeitThompson.lean):
type-P M + cyclic κ-Hall K + K-invariant (κ∪σ)'-Hall complement U → `TypePData M` (`.W1 = K`, `.U = U` を
definitionally 露出 = projection lemma `_W1`/`_U`)。全フィールドは lane-f の `typeP2_mf_internal_fitting_decomposition`
/`isTypeP2_of_hall_subgroupOf_ne_bot`/`typeP_hall_derived_eq_and_abelian`/`typePData_of_isTypeP_of_inputs` で
sorry-free に discharge (cite)。**`.W1=K` の rfl は term-mode 構成必須** (obtain/have の casesOn が lane-f の
tactic-built def の projection reduce を阻む、[[lean-coupled-engine-fields-and-beta]])。

### ✅ step 2.5: hUhall discharger (commit `f1d710a4`)
`isHall_kappaSigmaCompl_of_isTypeP2_complement` (FeitThompson.lean, sorry-free): type-P2 M で carried U
(M'=M_F⊔U, M_F⊓U=⊥) が (κ∪σ)'-Hall。証明: type-P2⟹M_F=M_σ; `typeP_exists_hall_derived_eq` が (κ∪σ)'-Hall
U₀ (M'=U₀⊔M_σ) 供給; U と U₀ は共に normal M_σ を M' で complement ⟹ |M_σ|·|U|=|M'|=|M_σ|·|U₀| ⟹ |U|=|U₀|;
IsHallSubgroup は order 決定 (`isHallSubgroup_of_card_eq` 新 helper) ⟹ U も (κ∪σ)'-Hall。支持 helper:
`card_mul_card_of_complement_normal` (normal complement の card 積、`normal_mul`+`isComplement'_of_disjoint_and_mul_eq_univ`)。
**Lean 知見**: `subgroupOf` は regular def ゆえ `← comap_inf` rw 不発 → `show … from (comap_inf _ _ _).symm` で
defeq 強制; `hMFeq ▸ hUinf` を rw 引数にすると motive 不定 → `← hMFeq` で戻して `hUinf`。

**⟹ carrier 核心機構 (engine + hUhall + helpers) 完成・全 sorry-free。** engine は type-P2 input で
完全に invocable (step 1 が hUsup/hKnorm/hUinf 供給、step 2.5 が hUhall)。

### ✅ step 2.7: carrier capstone (commit `a6faa39c`、main 同期で lane-f Prop 16.1 hP2II 取り込み済)
**carrier 構成を単一 sorry-free lemma に集約完了。**
- engine `typePData_of_kappaHall_hallComplement` を **`hP2` 直接入力に refactor** (旧 hP+hUne →
  hP2; type-P2 input なら `isTypeP2_of_hall...` 不要ゆえ hUne wart 除去、`typeP2_mf_internal` は hP2 直取り)。
- **compose lemma `exists_typePData_W1_eq_of_isTypeP2`** (sorry-free): `type-P2 M + cyclic κ-Hall K →
  ∃ data : TypePData M, data.W1 = K` = exists_kappaHall_invariant_complement_to_MF + step 2.5 hUhall + engine。
  **step 3 wiring が consume する「ready」形** (指定 κ-Hall を W1 に持つ matched TypePData)。

⟹ **diagnosis が特定した U-reconciliation (元の blocker) の構成機構が完全に sorry-free で完成。**

### 🚧 残 step 3 gate = (13.2.a) producer type 判定 (deep、要 hub/lane-f 判断)
**唯一の gate**: producer (`section16TypePStructure_of_isMinimalSimpleOdd`) で `exists_typePData_W1_eq_of_isTypeP2`
を mp.S に適用するには **mp.S が type-P2** が要る。pair 構成 (`exists_section16MaximalPair_data`, lane-f) は
`IsTypeP2 S ∨ IsTypeP2 Mstar` (FeitThompson.lean:356) **disjunction のみ**で、どちらか不明。q<p (mp.K_lt_Kstar)
で「smaller κ-Hall member = S が type-P2」を resolve するのが **Pf (13.2.a)「q<p ⟹ S type II」**だが、これは:
- producer 文脈で必要 (basic_structure の上流ゆえ basic_structure では供給不可、循環)、かつ
- 証明に §15-16 type 構造を要する deep result (現状未形式化)。
**⟹ (13.2.a) は lane-f の §16 pair 構成 (disjunction を ordering で resolve) で閉じるのが自然か、
lane-c §15 か = cross-lane 判断。lane-f が Prop 16.1 を進行中ゆえ、その完成で resolve する可能性。**
**carrier 機構は完成・consume 待ち; (13.2.a) landing で step 3 wiring は機械的。**

### 🔜 step 3 wiring (gate 解消後)
1. **compose**: `exists_typePData_W1_eq_of_isTypeP2 (hP2) (K κ-Hall) : ∃ data : TypePData M, data.W1=K`
   = exists_kappaHall_invariant_complement_to_MF + step 2.5 hUhall + engine。残 sub-gate = `hUne` (U≠⊥;
   type-P2 ⟹ M_σ≠M' ⟹ U≠⊥、要小 lemma)。
2. **(13.2.a) type 判定 (producer gate)**: producer で engine を mp.S に適用するには **mp.S が type-P2 (=type II)**
   が要る。§16 carrier は q<p (`q_lt_p`) を持ち Pf (13.2.a)「q<p⟹S type II」だが、これは `BasicStructureData.q_lt_p_forces_typeII`
   field = basic_structure 自身。**producer で独立に「q<p (= smaller κ-Hall member) ⟹ type-P2」を要する**
   (Prop 16.1(b) の `IsTypeP2 S ∨ IsTypeP2 Mstar` disjunction を ordering で resolve、BG §16 の deep result、要調査)。
3. **wiring**: `Section16TypePStructure` に `Sdata`/`Tdata : TypePData` (+ `.U=U`/`.W1=K` reconciliation、
   engine `_W1`/`_U`) → producer で compose 呼び出し → `Section16Inputs`+`sectionSixteenHypothesis_of_inputs`+
   `S15.Hypothesis` に thread → `S15.basic_structure` の `UW1_frobenius`/`U_commutative` を carried `Sdata` から
   実証明 (`typeP_uW1_frobenius`)。**注意**: basic_structure の他 field (type 判定, P el-ab p^q, u 上界) は
   carrier と別の deep obligation; carrier は U-side (UW1_frobenius/U_commutative = 診断が特定した元の blocker) を解く。
4. **co-edit 境界** (FeitThompson.lean は F/B/C 共有、def 単位): C=tp系 / F=mp+Prop16.1 / B=cd。互いに別 def。

---

## 実装状況 (2026-06-05 更新, peterfalvi worktree)

**注意**: 以下の大計画は 2026-05-22 の初版 (stale)。実体は `S15_SAndT.lean` の scaffold (18 sorry)。`Hypothesis` は **opaque-Prop convention** (m/u/c 等の値は usable な等式で pin されていない field 群) で、多くの数値結果は値の不透明性ゆえブロックされる。`Hypothesis` は **どこからも構成されない** (S16 が `base : S15.Hypothesis` で参照するのみ) ので field 改変は安全。

### ✅ 実証済 (real, axiom-clean)
- **(13.14) cyclotomic number theory 一式** — `cyclotomic_divisor_facts` + 7 helper (odd / dvd_of_modEq_one / coprime / not_dvd_self / prime_dvd_modEq_one / dvd_modEq_one / modEq_one_of_forall_primeFactors)。純数論、完全証明済。
- **(13.11) m-bounds 部分** (2026-06-05, commit 987392d): opaque `m_formula : Prop` を `m_eq : m = 1 - 1/(q-1) - (q-1)/q^p + 1/((q-1)q^p)` (= (13.10) の値) に置換して **m を pin**。新 arithmetic lemma `m_value_ge_aux` (m ≥ 1-1/(q-1)-1/q², p≥3 で可) / `m_value_gt_seven_tenths` (5≤q⇒m>7/10) / `m_value_gt_four_fifths` (7≤q⇒m>8/10)。`numeric_bounds` の **q≥7, q≥5 conjunct は real** (m_eq + three_le_p 経由)。

### 🔴 残ブロッカー
- **`numeric_bounds` の q=3 conjunct** (narrow sorry): m-bound (m>49/100) は **p≥5 が要** (q=p=3 で m=4/9<49/100 と破綻)。§15 は q<p も p≠q も field に持たず (§16 は (14.1) の `q_lt_p` から p_ne_q/five_le_p を導くが §15 には無い)。p≠q は (13.1) mmd に明示されず §10-§12 由来。u/c bound (u/c>(p²-1)/6) は **analytic_inequality (13.10) 待ち** (character theory)。→ **p≠q (or q<p) を Hypothesis に追加すれば q=3 m-bound は landable** (u/c は別途)。
- **character-theoretic norm 系 (13.5)-(13.10)**: lambda/eta norm lower bounds, global_character_bound, analytic_inequality — §3-§8 (Dade/coherence/TI) の深い指標論依存。`m` は pin 済だが norm cascade 本体は未。
- **c_eq_one (13.12)**: numeric_bounds + analytic + caseA に依存、blocked。
- **caseB_order_u (13.15)**: §16 の `caseB_for_S` が `CaseBOrderUData` 経由で消費。u の値確定は (13.14) facts + character-theoretic な u 下界が要 (blocked)。
- **normalizer_W1 (13.16) / typeII_overNormalizer (13.17) / 18,19**: group/character theory, blocked。

**次の tractable 候補**: p≠q を (13.1) field 追加 (mmd 由来要確認だが FT 設定で valid) → q=3 m-bound 完成 + 他 §15 proof も恩恵。それ以外の実前進は §3-§8 character theory のスキャフォールド解消が必要。

---

## TL;DR — Peterfalvi 本文最大規模, §16 直前の最終仕込み

§15 は Peterfalvi 著作の中で **最も計算が過密** な節. §14 で確立した Type I 最大部分群 (13 個の補題) に続き、§15 は **Type II/III の 2 つの最大部分群 S, T** に焦点を絞る. 両者の位数・正規化群・Dade 等距写像を組合せ、最終的に「S, T の存在は矛盾を導く」という結論に到達させる. これが §16 の 11 個の結果による「G 非存在」の直接的な前提となる.

**本文規模**: 365 行（全 16 節中最大、§10-§14 の平均 150 行を大きく上回る）  
**指標論の深さ**: §3-§8 で確立した Dade isometry / Coherence / TI-subset 理論の **全パイプラインを§15 1 節で集約**  
**形式化上の懸念**: 17 結果 × 大規模 × 指標論特化 → **Lean コード 1500+ 行** の見込み. 2-3 ファイルへの分割戦略が必須.

---

## §15 全 17 結果 + 補足 2 (表形式)

| # | 結果 | 型 | 頁 | 主張 | 依存 | 指標論度 |
|---|------|------|------|------|------|---------|
| 0 | (13.1) | **仮説** | 75 | S, T 定義. W=S∩T=W₁×W₂, P=S_F, Q=T_F. (a)-(e) 5 条件: S=(P⋊U)⋊W₁, T=(Q⋊V)⋊W₂, Dade τ, character ω_ij, η_ij, μ_ij, ν_ij, 集合 𝒮, 𝒯 | (12.1)-(12.13) | **複雑な setup** |
| 1 | (13.2) | Prop | 75-76 | (a) S Type II or III, q<p ⇒ S Type II. UW₁ Frobenius. (b) P elementary abelian rank q. (c) u ≤ (p^q-1)/(p-1). (d) 𝒮 coherent. (e) A₀(S) is TI-subset with normalizer S, τ = Ind_S^G | (10.10), (11.9), (8.4.d), (9.11), (12.7), (8.13) | **structure + coherence** |
| 2 | (13.3) | Prop | 76-77 | (a) j≥1 ⇒ μ_j induced from linear char of PC, μ_j(1)=uq. (b) If 𝒮 has no uq-degree char from PC, then case (9.7.b) holds. (c) δ_j=δ'_i=1. μ_j^{τ₁} = Σ_{i} η_{ij} or (p=3, sign flip) | (9.8), (9.9), (4.3), (4.4), (4.9), (5.8) | **character degree analysis** |
| 3 | (13.4) | Prop | 77 | If 𝒮 has λ of degree uq from PC, then case (9.7.b) for M=T, D=1, v=(q^p-1)/(q-1) | **key case split** | (9.7.b), (13.3.b) | **character orthogonality** |
| 4 | (13.5) | Prop | 77-78 | TI-subset 上の character orthogonality formula. (a) χ(x) = (a/‖ζ₁‖²)ζ₁(x) + α(x) for x∈H^#, a=(ζ₁^τ, χ). (b), (c) norm inequality on α | (7.7.a), (1.5) | **linear algebra on character** |
| 5 | (13.6) | Prop | 78 | Σ_{x∈H#} \|λ^{τ₁}(x)\|² ≥ \|S\| - λ(1)² | (13.5), (13.2.c) | **norm lower bound** |
| 6 | (13.7) | Prop | 78-79 | Σ_{x∈H#} \|η₁₀(x)\|² ≥ \|H^#\| | (5.3.b), (5.5), (13.3.c), (1.10) | **norm lower bound** |
| 7 | (13.8) | Prop | 79 | Σ_{x∈H#} \|η₀₁(x)\|² ≥ \|S'\| - u² | (13.3.c), (13.3.a), (13.5) | **norm lower bound** |
| 8 | (13.9) | Prop | 79-80 | G₀ = G# - ((H#)^G ∪ (Q#)^G). (a) x∈G₀ ⇒ λ^{τ₁}(x) ≠ 0 or η₁₀(x) ≠ 0. (b) Σ_{x∈G₀} (\|λ^{τ₁}(x)\|² + \|η₁₀(x)\|²) ≥ \|G₀\| | (13.3.c), (3.9.b), (3.2.c), (3.4), (1.9.b) | **global character bound** |
| 9 | (13.10) | Prop | 80 | m = 1 - 1/(q-1) - (q-1)/q^p + 1/((q-1)q^p). If 𝒮 has λ, then u/c > mp^{q-1}/q | (13.9), (13.6), (13.7), (13.8), (13.4) | **analytic inequality** |
| 10 | (13.11) | Prop | 80-81 | (a) q≥7 ⇒ m > 8/10. (b) q≥5 ⇒ m > 7/10. (c) q=3 ⇒ m > 49/100 and u/c > (p²-1)/6 | (13.10) | **numeric bounds** |
| 11 | (13.12) | **Main** | 81 | **c = 1** (最重要結果) | (13.3.b), (13.10), (13.11) | **contradiction via bounds** |
| 12 | (13.13) | Prop | 81-82 | If case (9.7.a) for M=S, then q=3 and u=(p-1)²/4 | (13.3.b), (13.10), (13.12), (13.11.b) | **case elimination** |
| 13 | (13.14) | Prop | 82 | (p^q-1)/(p-1) is odd. Divisor arithmetic: if p≡1 (mod q), q divides ratio; if not, ratio is coprime to p-1 | — | **number theory** |
| 14 | (13.15) | Prop | 82 | If case (9.7.b) with M=S, then u = (p^q-1)/(p-1) [if p≢1(q)] or (p^q-1)/(q(p-1)) [if p≡1(q)] | (13.14), (13.3.b), (13.10), (13.12) | **divisor analysis** |
| 15 | (13.16) | Prop | 82-83 | **N_G(W₁) = C_G(W₁) = QW₂** | (13.12), (8.6.a), (9.1) | **normalizer determination** |
| 16 | (13.17) | Prop | 83-84 | If S is Type II, L is maximal with N_G(U)⊆L, H=L_F. Then (a) L is Frobenius group. (b) U⊆H. (c) L=H⋊W₁ or L=H⋊(W₁W₂^y) for y∈Q | (13.2.a), (13.16), (8.8.b4), (12.7), (8.17.a) | **Frobenius structure** |
| 17 | (13.18) | Prop | 84-85 | β_j = Ind_{PW₁}^S 1_{PW₁} - μ_{0j}. (a) Supp(β_j) ⊆ P# ∪ (W-(W₁∪W₂))^S ⊆ A₀(S). (b) ‖β_j‖² = (u-1)/q + 2. (c) Γ = β_j^τ - 1_G + η_{0j} independent of j, orthogonal to 1_G, real. (d) ‖Y‖² ≤ (u-1)/q where Y is orthogonal to η_{ik} | (4.5.a), (4.3.c), (13.3.c), (13.12), (1.6.b), (4.8) | **virtual character decomp** |
| 18 | (13.19) | Prop | 85-87 | L maximal Type I, H=L_F, e=\|L:H\|. (a) Ã(L)∩(P^G∪W^G)=∅. (b) ℒ^{τ₁} orthogonal to η_{ij}. (c) (β_L^τ, η_{0j}) independent of j. Two cases: (c1) (β_S^τ, φ^{τ₁})≡1(2) and (|H|-1)/e ≤ (u-1)/q, or (c2) (β_L^τ, η_{0j})≡1(2) and p ≤ e | (13.18.a), (7.8), (7.8.b), (13.18.d) | **Type I vs (S,T) orthogonality** |

**合計**: 17 結果 (13.1)-(13.17) + 2 補足 (13.18)-(13.19) = **計 19 個**.

---

## §15 の構造: 4 つのフェーズ

### Phase A: Setup と基本構造 ((13.1)-(13.2))

**役割**: 仮説の精密化. §14 の Type I 分析から §15 の (S, T) 分析への転換.

**(13.1) 仮説 (5 条件)**:
- (a) S, T: maximal subgroup pair satisfying (8.8.b conditions). W = S ∩ T = W₁ × W₂ (cyclic direct product)
- (b) P = S_F, Q = T_F. S = (P⋊U)⋊W₁, T = (Q⋊V)⋊W₂. W₁ normalizes U, W₂ normalizes V.
- (c) 𝒮 = {Ind_W^S θ | θ ∈ Irr S', P ⊄ Ker θ}, 𝒯 = similar for T. Dade isometry τ for A₀(S), A₀(T).
- (d) ω_{ij} (as in (3.3)), η_{ij} = ω_{ij}^τ.
- (e) μ_{ij}, ν_{ij}: characters from (4.3) with specific reduction properties.

**mathlib 上の課題**: (13.1) 全体が 1 つの大型 `structure` または `class` になると見込まれる. 10-15 個のフィールド.

**(13.2) 基本事実 (5 項)**:
- (a) S is Type II or III. q < p ⇒ S Type II. UW₁ is Frobenius with abelian kernel U.
- (b) P is elementary abelian of order p^q.
- (c) u ≤ (p^q - 1)/(p - 1).
- (d) 𝒮 is coherent.
- (e) A₀(S) is TI-subset of G with normalizer S. τ = Ind_S^G.

**意義**: §14 の Type I 定理群を (S, T) に特化. Coherence が明示的に現れる最初の箇所.

---

### Phase B: Character-Theoretic Analysis ((13.3)-(13.10))

**役割**: Dade isometry + Coherence を駆使した, S の指標の詳細解析. 8 個の補題で段階的に制約を積み重ねる.

**(13.3) Character Degrees**:
- μ_j (j ≥ 1) は PC の linear character から induced
- μ_j(1) = uq
- δ_j = δ'_i = 1
- μ_j^{τ₁} = Σ η_{ij} (or sign-flipped if p=3)

**ポイント**: Character の度数が (1.1.e) 内で完全に決定される → degree freedom の除外.

**(13.4) Key Case Split**:
- If 𝒮 contains λ of degree uq from PC, then **case (9.7.b) holds for M=T** with D=1, v=(q^p-1)/(q-1).

**意義**: (13.3)-(13.4) は **"Either ... or ..."** 分岐の開始. (13.3.b) で (9.7.b) の可能性を示唆, (13.4) で逆方向を固定.

**(13.5)-(13.8) Norm Lower Bounds** (4 個の補題):
- (13.5): TI-subset 上の character orthogonality (一般型). χ(x) = (a/‖ζ₁‖²)ζ₁(x) + α(x).
- (13.6): Σ |λ^{τ₁}(x)|² ≥ |S| - λ(1)².
- (13.7): Σ |η₁₀(x)|² ≥ |H^#| (H = PC).
- (13.8): Σ |η₀₁(x)|² ≥ |S'| - u².

**手法**: Frobenius-type inner product と Dade image の norm decay を逐次追跡.

**(13.9) Global Character Bound**:
- G₀ = G# - ((H#)^G ∪ (Q#)^G) (intermediate element set)
- (a) x ∈ G₀ ⇒ λ^{τ₁}(x) ≠ 0 OR η₁₀(x) ≠ 0 (完全カバー)
- (b) Σ_{x∈G₀} (|λ^{τ₁}(x)|² + |η₁₀(x)|²) ≥ |G₀|.

**意義**: 「G の generic 元は λ または η₁₀ で非自明」→ character の global 支配権確立.

**(13.10) Analytic Inequality**:
- m = 1 - 1/(q-1) - (q-1)/q^p + 1/((q-1)q^p)
- **u/c > mp^{q-1}/q**

**ポイント**: norm 計算の集約. (13.6)-(13.9) の結果を組合せて, 位数と normalizer サイズの関係式を導出.

---

### Phase C: 位数決定 ((13.11)-(13.15))

**役割**: Analytic inequality (13.10) を数値分析 + case elimination で進める. 最終的に **c=1 決定** と u の明示形を得る.

**(13.11) Numeric Bounds** (3 項):
- (a) q ≥ 7 ⇒ m > 8/10
- (b) q ≥ 5 ⇒ m > 7/10
- (c) q = 3 ⇒ m > 49/100 and u/c > (p²-1)/6

**手法**: 初等不等式 (f(x) monotonicity など)

**(13.12) MAIN RESULT: c = 1**

**Proof Strategy**:
1. (13.3.b) より λ existence 仮定
2. (13.10), (13.12) より m < uq/(p^{q-1}) ≤ q(p^q-1)/((p-1)cp^{q-1})
3. c ≠ 1 ⇒ c ≥ 2q+1 (W₁ acts fixed-point-freely on C, c odd)
4. 3 つの case (p=3, p≥5) で numerically 矛盾導出
   - p=3: m < 3/4 < 8/10, (13.11.a) と矛盾
   - p≥5: m < p/(2(p-1)) < 7/10, (13.11.b) と矛盾

**結論**: c = 1 is forced.

**形式化上の注**: この証明は **case-by-case numeric 検証**. Lean での numeric tactic (omega, norm_num 等) の活躍場.

**(13.13) Case (9.7.a) Analysis**:
- If case (9.7.a) for M=S, then q=3, u=(p-1)²/4.

**意義**: (13.3.b) の (9.7.b) assumption に対して, 逆に (9.7.a) を仮定すると矛盾 → (9.7.b) forced.

**(13.14) Number-Theoretic Facts on Cyclotomic**:
- (p^q-1)/(p-1) is always odd
- If p ≡ 1 (mod q), q divides ratio
- If p ≢ 1 (mod q), ratio is coprime to p-1, and divisors ≡ 1 (mod q)

**目的**: (13.15) の分母分析の準備.

**(13.15) u の最終形**:
- **If case (9.7.b)**:
  - p ≢ 1 (mod q): **u = (p^q-1)/(p-1)**
  - p ≡ 1 (mod q): **u = (p^q-1)/(q(p-1))**

**ポイント**: (13.14) の divisor 性質を使い, (p^q-1)/(p-1) の factorization を決定 → u の一意性.

---

### Phase D: 正規化群と Frobenius 構造 ((13.16)-(13.19))

**役割**: S, T の外部 (G 内での) normalizer 構造と, Type I との相互作用を分析.

**(13.16) KEY FACT: N_G(W₁) = C_G(W₁) = QW₂**

**Proof**: 
1. TI-subset 性質 (13.2.e) より N_G(W₁) = N_T(W₁)
2. QW₂ ⊆ C_G(W₁) は定義より
3. Maschke → Q = W₁ × Q₁ with KW₂ normalizes Q₁ (K = N_V(W₁))
4. K ≠ 1 → contradiction by (13.12) and (9.1)
5. **K = 1** ⇒ N_G(W₁) = QW₂

**意義**: W₁ の正規化群が (S の外で) exactly QW₂ に等しい → geometric constraint on T.

**▶ 2026-06-23 lane-h 着手 — §8-free Wielandt step landed, full assembly は §13-gated (再調査不要)**:
深掘りの結果、(13.16) full は当初の見立てより gating が深い。`normalizer_W1` (S15:827, `:= sorry`) は以下に bottom-out:
- **Q elem-ab order q^p (Q abelian)** = `card_Q_eq` (S15:1113, sorried 残差 B1, **lane-f/b cross-lane gate**) + basic_structure T-side。Maschke (step 3) に必須。
- **W₁ ⊆ Q** — Hypothesis field に無し (構造的 obligation 要)。
- **Q# TI-subset with normalizer T** — step 1 の核、Hypothesis に無し (§13 obligation)。
- **d = 1 (T-side of (13.12))** — `c_eq_one` は S-side のみ、T-side 不在 (obligation)。step 4 の K=1 に必須。
- **KW₂ Frobenius kernel K** — step 4 の Wielandt 入力 (§13 obligation)。
- **BG Lemma 3.2** — step 5 (K ⊆ C(W₁))。✅ **2026-06-23 完全版 landed** (`S03_FrobeniusActions.lean`,
  axiom-clean): `isFrobeniusGroup_quotient_of_normal_not_le_kernel` (= 3.2(a)(b): `N◁G`, `K⊄N` ⟹ `N<K`
  ∧ `Ḡ=G/N` Frobenius) + crux `inf_complement_eq_bot_of_normal_not_le_kernel` (`N⊓R=⊥`) +
  `normal_le_kernel_of_not_le` (`N⊆K`)。repo は Lemma 3.2 の `N≤K` 枝のみ既存だった、未実装の `K⊄N`
  枝を補完。⟹ step 5 obligation は解消 (残 5 obligation は依然 cross-lane gate)。
- **module Maschke** = `OperatorMaschke.lean` ✓ (available)。
⟹ full assembly は残 ~5 obligation の large scaffold (うち card_Q_eq は cross-lane) ゆえ「scaffold ≠ done」回避で full は保留。
**✅ 但し step 4 の genuine §8-free Wielandt 核を landing** (commit `d11f7fe9`, axiom-clean):
`OddOrder.GroupTheory.frobenius_kernel_centralizes_of_complement_fpf` (WielandtFixedPoint.lean) —
Frobenius `U⋊E ≤ N_G(N)` coprime, `C_N(E)=1` ⟹ `U ≤ C_G(N)`。`wielandt_fixedPoint_trivial_E_fixed` の
ambient form (= step 4 の「K centralizes Q₁」)。reusable。**(13.16) full は §13 structural facts (上記) 着地待ち。**

**(13.17) Type II Frobenius Structure**:
- If S is Type II, L = maximal ⊃ N_G(U), H = L_F. Then:
  - (a) **L is Frobenius group with kernel H**
  - (b) **U ⊆ H**
  - (c) **L = H⋊W₁** or **L = H⋊(W₁W₂^y)** for some y ∈ Q

**Proof Idea**:
1. L ≠ S (S は Type II → non-Frobenius)
2. L ≠ T (|H| = q^p, but W₁ ⊆ N_G(U) ⊆ L, W₁ ⊆ H, [U, W₁] ⊆ H ∩ U = 1 → contradiction with (13.2.a))
3. L は Type I → Frobenius (by (12.7))
4. Structure of L.complement via (13.16)

**形式化上の注**: L, M の 2 つの maximal subgroup を導入. これが §16 の (14.3), (14.10) に対応.

**(13.18) Virtual Character Decomposition** (補足):
- β_j = Ind_{PW₁}^S 1_{PW₁} - μ_{0j}
- (a) Supp(β_j) ⊆ P# ∪ (W-(W₁∪W₂))^S ⊆ A₀(S)
- (b) ‖β_j‖² = (u-1)/q + 2
- (c) Γ = β_j^τ - 1_G + η_{0j} independent of j, orthogonal to 1_G, real
- (d) ‖Y‖² ≤ (u-1)/q (Y orthogonal to η_{ik})

**意義**: (13.18) は (13.19) の前置き. β_j の Dade norm と support 構造を確定.

**(13.19) Type I との Orthogonality** (補足):
- L: maximal Type I, H=L_F, e=|L:H|
- ℒ = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}
- (a) Ã(L) ∩ (P^G ∪ W^G) = ∅ (A₀(L), A₀(S), A₀(T) disjoint in fixed-point-set sense)
- (b) ℒ^{τ₁} orthogonal to η_{ij}
- (c) **Two alternative cases**:
  - (c1) (β_S^τ, φ^{τ₁}) ≡ 1 (2) and (|H|-1)/e ≤ (u-1)/q
  - (c2) (β_L^τ, η_{0j}) ≡ 1 (2) for j ≥ 1 and p ≤ e

**意義**: Type I (L) と Type II (S, T) の character family が "orthogonal" → dimension analysis へ. (c1), (c2) は §16 の key case split.

---

## S, T の定義と役割

### S, T は何か?

**定義** (from (13.1), (8.8.b)):
- G: minimal odd-order non-solvable group (極小反例)
- **S, T**: maximal subgroup pair of G, both solvable, satisfying:
  - W = S ∩ T (分解 W = W₁ × W₂, cyclic)
  - |W₁| = q (prime), |W₂| = p (prime), q < p
  - W₁ cyclic Hall subgroup of S, W₂ cyclic Hall subgroup of T
  - S, T are **conjugate-free** (no S ≅^conj T in typical case, see (13.17.c) exception)

### 構造

**S の構造** (from (13.1.b), (13.2)):
- S = (P⋊U)⋊W₁ (nested semidirect product)
- P = S_F (Fitting subgroup, elementary abelian, rank q)
- U: abelian (from (13.2.a)), order u
- W₁: cyclic of order q
- U, W₁ complement P with specific action properties
- S' = PU, C = C_U(P), S'/P ≅ U/C

**対称性**:
- T は S と同じ構造で, P ↔ Q, U ↔ V, W₁ ↔ W₂, q ↔ p を交換した形.

### 指標論的特徴

**集合 𝒮, 𝒯** (from (13.1.c)):
- 𝒮 = {Ind_W^S θ | θ ∈ Irr S', P ⊄ Ker θ}
- 𝒯 = {Ind_W^T ψ | ψ ∈ Irr T', Q ⊄ Ker ψ}
- **Coherent** (from (13.2.d)): Dade isometry τ̃: Z[𝒮] → Z[Irr G] の拡張が存在

**主要指標族**:
- μ_{ij}, ν_{ij}: S, T 上の character famiglia, degree u
- η_{ij} = ω_{ij}^τ: Dade image (virtual character on G)

---

## 17 結果のグループ化

### Group 1: Type Determination (13.3)-(13.4)

**内容**: S, T の Type (II or III) 決定, character degree structure.  
**キー結果**: (13.3.a) μ_j(1) = uq, (13.4) case (9.7.b) for T with v=(q^p-1)/(q-1).  
**mathlib 上**: character degree の列挙 (finite list, Lean で直接?).

### Group 2: Norm Inequalities (13.5)-(13.10)

**内容**: Dade norm, character support, analytic inequality.  
**キー結果**: (13.10) u/c > mp^{q-1}/q (m parameterized by q, p).  
**mathlib 上**: `ℝ` 不等式の cascade. `norm_num` tactic 多用.  
**形式化量**: **最大** (6 補題 × 詳細計算 = 300-400 行?)

### Group 3: Order and Centralizer Determination (13.11)-(13.15)

**内容**: c=1 証明, u の明示形.  
**キー結果**: (13.12) c=1, (13.15) u = (p^q-1)/(p-1) [or divided by q].  
**mathlib 上**: numeric case analysis + divisor theorem.  
**形式化量**: **大** (case split 多い, 150-200 行)

### Group 4: External Structure (13.16)-(13.19)

**内容**: G 内での normalizer, Frobenius structure, Type I との orthogonality.  
**キー結果**: (13.16) N_G(W₁) = QW₂, (13.17) L Frobenius, (13.19.c) case (c1)/(c2).  
**mathlib 上**: Group theory (normalizer, Frobenius定義).  
**形式化量**: **中程度** (100-150 行)

---

## §14 (Type I) からの継承

**§14 全 13 結果** (12.1)-(12.13) は Type I 最大部分群 L の詳細分析.  
**§15 の依存**: 
- (13.1) の仮説は (12.1)-(12.13) の **逆側 (non-Type I case)**
- (13.2.a) "S is Type II or III" = **not Type I**
- (13.17) "L is Type I Frobenius" = §14 の type classification を再利用

**継承構造**:
```
§14: Type I (M) の 13 補題
    ↓ (exhaustion)
§15: Type II,III (S,T) の 17 補題 + Type I 例外 (13.17.c)
    ↓
§16: G non-existence (11 補題)
```

---

## §16 (Non-existence G) への橋渡し (final input)

**§16 全 11 結果** (14.1)-(14.11) + (14.12)-(14.17):

| §15 Result | § 16 usage | Purpose |
|------------|-----------|---------|
| (13.1) Hyp | (14.1) Hyp | Setup (q < p variant) |
| (13.2.e) τ=Ind | (14.2) FT Main | Dade simplification |
| (13.3), (13.4) char degree | (14.4) case (9.7.b) | Type constraint |
| (13.10) ineq | (14.8) key ineq | u/c bound |
| (13.12) c=1 | (14.12)-(14.16) | Simplification |
| (13.16) N_G(W₁)=QW₂ | (14.5.c) L structure | Frobenius complement |
| (13.17) L Frobenius | (14.5.a) | Type I analysis |
| (13.18)-(13.19) | (14.14.c) case (c1)/(c2) | Orthogonality switch |

**Key Mechanism**:
- §15: (13.1)-(13.19) で S, T の完全記述を達成
- §16: その記述を (14.1)-(14.11) で矛盾導出に使用
- **結論**: S, T 共存不可 ⇒ G 존재不可 (by exhaustion with Type I (13.17))

---

## BG §15 (M_F) との関係

**BG Notation**: M_F = Fitting subgroup of M (maximal Hall odd-order normal subgroup)

**Peterfalvi vs BG**:
| 項目 | BG §15 | Peterfalvi §15 |
|------|--------|-----------------|
| **焦点** | M_F の局所構造 (Frobenius action, cohomology) | S, T の指標論的詳細 (Dade, coherence, norm) |
| **手法** | Group cohomology H²(U, M_F), Maschke | Character theory, Dade isometry |
| **結果** | Type 𝓕 definition | c=1, u = (p^q-1)/(p-1) |
| **規模** | ~60 行 | ~365 行 |

**統合点**:
- BG §15 で M_F の structure 決定
- Peterfalvi §15 で M_F (= P or Q) を S_F, T_F と呼び, 指標論で再分析

---

## ファイル分割の検討 (s15_s_and_t subdirectory 戦略)

**規模見積**: 365 行 (本文) → **1500-1800 行 (Lean)**

**理由**: 
- 17 結果各々 80-120 行の Lean code (proof density 高)
- 指標論計算 (norm, character degree) の detailed lemma化
- case split 多い ((13.12), (13.13), (13.15) 等)

**分割案 A (フェーズベース)**:
```
s15_s_and_t/
  ├─ A_setup_and_types.lean       (~200 行: 13.1-13.4)
  ├─ B_norm_and_analytics.lean    (~500 行: 13.5-13.10)
  ├─ C_order_determination.lean   (~350 行: 13.11-13.15)
  ├─ D_normalizers_and_frobenius.lean (~300 行: 13.16-13.19)
  └─ S15_SAndT.lean               (imports + index)
```

**分割案 B (グループベース)**:
```
s15_s_and_t/
  ├─ Normalizers.lean             (13.16)
  ├─ TypeDetermination.lean       (13.3-13.4)
  ├─ NormInequalityMain.lean      (13.5-13.10) — **最大ファイル**
  ├─ OrderDetermination.lean      (13.11-13.15)
  ├─ FrobeniusStructure.lean      (13.17-13.19)
  └─ S15_SAndT.lean
```

**推奨**: **分割案 A** (フェーズ順に development → より readable)

---

## mathlib カバレッジ

### 完全新規 (Peterfalvi 固有)
- `DadeIsometry` API (§4 から継続)
- `Coherence` 定義・主定理 (§7 から継続)
- Virtual character norm inequality (§5-§8 application)
- Type II/III 定義と properties (from BG §11, but Peterfalvi-specific formulation)

### 部分既存 (mathlib+補強)
- `Character.degree`, `Character.induced`: existing in `Mathlib.RepresentationTheory.Character`
- Frobenius group structure: existing in `Mathlib.GroupTheory.Frobenius` (but (13.17.a)-(c) may need extension)
- Numeric inequality: `norm_num`, `omega` tactic

### 依存関係 (§15 独自)
- **§3 Preliminary** (character orthogonality, Frobenius, TI-subset)
- **§4 Dade Isometry** (全体の backbone)
- **§5 TI-Cyclic Normalizer** (13.16 preparation)
- **§7-§8 Coherence** (13.2.d, 13.3.c application)
- **§14 Type I** (13.2.a, 13.17 structure)

---

## Phase 2b 形式化着手順

### 予備調査 (準備期間, 1-2 週)
1. mmd ファイル全 365 行を Lean code 密度で分類 (proof vs setup vs lemma)
2. mathlib Character/Frobenius API の詳細確認
3. (13.12) c=1 の numeric case split strategy を mock-up

### 第 1 pass: Setup + Type (1 週)
- (13.1)-(13.4): structure 定義 + basic properties
- **形式化量**: 200-250 行

### 第 2 pass: Norm Inequalities (2-2.5 週) ← **最長**
- (13.5)-(13.10): 6 個の norm lemma, analytic inequality
- **難所**: (13.6)-(13.9) の nested character bound, (13.10) の analytic formula
- **形式化量**: 500-600 行

### 第 3 pass: Order & Divisor (1.5 週)
- (13.11)-(13.15): numeric bounds, case (9.7.a)/(9.7.b), divisor arithmetic
- **難所**: (13.12) c=1 の exhaustive case analysis (p=3 vs p≥5)
- **形式化量**: 350-400 行

### 第 4 pass: Normalizers & Frobenius (1 週)
- (13.16)-(13.19): normalizer determination, Frobenius structure, Type I orthogonality
- **形式化量**: 300-350 行

### 統合テスト (0.5 週)
- Full file build
- Cross-reference check with §16 (14.1)-(14.11)

**総所要期間**: **6-7 週** (依存コンポーネント §3-§14 完成後)

---

## 未解決 / TODO

### Theory-Level
1. **c=1 決定の formal 手法**: (13.12) の proof は numerically exhaustive (case p=3, p≥5). Lean での `interval_cases` 的な tactic の適用可能性?
2. **Divisor arithmetic の mathlib**: (13.14)-(13.15) で (p^q-1)/(p-1) の divisor properties. `Nat.dvd` + congruence `Nat.ModEq` で formalize?
3. **Frobenius complement の一意性**: (13.17.c) で "L = H⋊W₁ or L = H⋊(W₁W₂^y)" の either/or structure. Lean で case-by-case proof design?

### Formalization-Level
1. **Virtual character space Z[Irr G]**: §5 では virtual character を informal に扱う. Lean type を設計する際, `Z-Module ℂ` か, それとも custom type か?
2. **Dade isometry の norm 計算**: (13.5)-(13.8) の norm lower bound が本体. mathlib `‖·‖` notation との統一?
3. **TI-subset orthogonality** ((13.5.a) etc.): inner product (·, ·) on CF(L, A^#) の定義が (7.1) Hypothesis に依存. dependency handling?

### Integration-Level
1. **§15 → §16 引き継ぎ**: (13.19.c) の two cases が (14.14) の case (a)/(b) に対応するが, formal mapping を明確化?
2. **BG App.C との overlap check**: BG でも M_F (type 𝓕) と U の関係が扱われるが, 重複部分の elimination strategy?

---

## Summary

**Peterfalvi §15** は Phase 2b の最終直前準備として、**17 個の結果 (365 行) を使い, S, T 部分群の位数・正規化群・指標を極限まで詳細化する**.

**Key achievements**:
- (13.12) **c = 1** (C_U(P) が自明)
- (13.15) **u = (p^q-1)/(p-1)** (order 決定)
- (13.16) **N_G(W₁) = QW₂** (external normalizer)
- (13.17) **Type II ⇒ L is Frobenius** (structure)
- (13.19) **(c1)/(c2) dichotomy** (§16 key case split)

**形式化規模**: 1500-1800 行 (4 ファイル分割推奨)

**所要期間**: 6-7 週 (§3-§14 完成後, §16 前)

**最大の挑戦**: 
- Norm inequality cascade (13.5-13.10) の formal proof
- Numeric case analysis (13.12) の exhaustiveness guarantee
- Character family orthogonality (13.19) の dimensional argument

---

**作成**: 2026-05-22. **出典**: `references/peterfalvi/04.15_pp_75_86_The_Subgroups_S_and_T.mmd` (365 行, 17 結果). §14, §16 ノートのクロス参照確認済.

