---
id: 9079
slug: typep-pair-grid-transpose
title: "shared-infra claim: (8.8) typeP-pair grid transpose + (10.7) pair-witness route — S-grid = M-grid swap"
created: 2026-07-10
---

# shared-infra claim: (8.8) typeP-pair grid transpose + (10.7) pair-witness route — S-grid = M-grid swap

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

# shared-infra claim (lane a): (8.8) typeP-pair の grid transpose + (10.7) pair-witness route

**claim-before-build (CLAUDE.md (C))**。lane a が (10.7) obligation 2(b) のために claim:

## Scope
1. **(10.7) の pair-witness 再構成** (Coq `Frob_der1_type2` PFsection10:549-560 の忠実 route):
   任意 type-II L に対する直接証明でなく、**M の pair partner S** (`FTtypeP_pair_witness`
   相当) に対して cross-isometry を証明し、`L = S^x` (pair の type-2 分類 clause) の
   **共役転送**で一般 L に拡張。lane-a 既存の T2/dichotomy 機構 (S12_TypeIIColumnPin、
   S-generic) は partner 上でそのまま再利用。
2. **S-grid = M-grid transpose**: partner S は M と W = W₁×W₂ を共有 (役割 swap)。
   S-side certainTypeOmegaSigma (typeIIHypothesis46-S) と M-side alignedOmegaSigmaGrid の
   同定。**鍵候補 = Dade-map 一意性** (`IsDadeMap.unique`): 両 σ は同じ (G, V-TI) の
   Dade isometry ⟹ 同一 map、grid は index の swap 翻訳のみ。
3. repo 既存資産: `Section16MaximalPair` (FeitThompsonSetup:292、W-structure +
   certainTypeS/certainTypeT 済) — coverage 精査から着手。

## 非重複確認
- 9076 (lane c) = §3 rigidity `eq_signed_sub_cTIiso` + `prDade_sub_TIirr` — **別物**
  (norm-2 rigidity; 本 claim は pair-witness + σ-同一視)。9076 成果物は将来 (10.5)-系で
  相互参照の可能性のみ。
- 9014 (primeTI residue API) とも独立。

owner: lane a / 起点 note: notes/peterfalvi/s10_7_derived_frobenius.md 進捗⁸

## 2026-07-10 coverage 調査結果 (Explore agent、実装前提の確定)

**既存資産 (全て確認済)**:
- `Section16MaximalPair` (FeitThompsonSetup:292-334): S/T + `theorem88_caseB`
  (**分類 clause 有**: ∀ M maximal, IsTypeI ∨ conj•M = S ∨ conj•M = T) + `S_typeP2` +
  K/K* (= W₁/W₂)。producer `section16MaximalPair_of_isMinimalSimpleOdd` (726-760、本体 sorry-free;
  推移依存に §11/§13 残 sorry — 本レーンが現在埋めている (5.8)/(10.8) 系そのもの、sorried-cite で可)。
- `certainTypeS`/`certainTypeT` (1132-1153): S06.Hypothesis を **W₁/W₂ swap** で両側構成済。
- `W_structure` (1180-1196): S ⊓ T = K ⊔ K* + cyclic。`Section16TypePStructure.W1_eq_K_and_W2_eq_Kstar` (1203)。
- `typeP_duality` (= pair_witness 相当、∃! partner) + `theoremC_paired_structure` covering。
- `IsDadeMap.unique` (S04_DadeIsometry:651、sorry-free)。

**足りない部品 (優先順、全て exists_typeIICrossIsometryData の単一 sorry に集約)**:
1. **σ-grid pair transpose bridge** (核心新規): certainTypeOmegaSigma (S-side、certainTypeT の
   W-swap 基盤) = alignedOmegaSigmaGrid (M-side) の transpose。材料 = 共有 W + (3.2) σ 一意性
   (IsDadeMap.unique — 両 σ は同一 (G, V-TI) の Dade map)。S05_SignedTripleGrid の
   `IsSignedTripleGrid.transpose` (1489) は grid primitive として再利用可。
2. **pair 対称化** (`typeP_pair_sym` 相当の `.swap`): 現状不在 — S↔T/K↔K*/W₁↔W₂。
3. **type-II L → canonical partner 還元 glue** (組立のみ、新規部品不要):
   theorem88_caseB + typeP_duality + type 排他。
4. **行和 pin 変換**: 1 が入れば dichotomy (typeII_nu_tau2_dichotomy、landed) の
   S-列和 → M-行和変換で nu_tau2_eq が従う。

## 2026-07-10 part 1 LANDED (1dedff44): σ-一致 bridge — `S12_TypeIIGridTranspose.lean`

全 9 宣言 sorry-free / axiom-clean ([propext, Classical.choice, Quot.sound])。
namespace `OddOrder.Peterfalvi.S12`、import = S12_TypeIIColumnPin。

### 宣言一覧
1. `dadeHypothesis_eq_of_forall_H_eq_bot` — 同一 (A,L) 上の H≡⊥ な 2 つの S04.Hypothesis
   は**構造として等しい** (H が唯一の data field、他 8 fields は全て Prop → destructure +
   funext + subst + rfl (定義的 proof irrelevance))。
2. `dadeMap_unique_of_forall_H_eq_bot` — cross-hypothesis 版 (2.5) 一意性 (k-generic)。
   1 の等式で h₂ を書き換え `IsDadeMap.unique` (S04:651) 一撃。
3. `ticyclic_toDadeMap_apply_eq` — 同一 hyp の任意の 2 つの FullDadeApplication は同じ
   Dade map (`IsDadeMap.unique` の congrFun、packaging 非依存)。
4. **`ticyclic_toDadeMap_eq_of_V_eq` (核心)** — hV : hyp₁.V = hyp₂.V のみで、V 上の値が
   等しい supported 引数対 (α₁, α₂, hα pointwise) について full Dade map が一致。
5. `ticyclicSupportedOnVCongr` (def) + `ticyclicSupportedOnVCongr_coe_apply` (@[simp] rfl)
   — CF(W,V) transport (hV, hW)。
6. `ticyclic_toDadeMap_congr_eq` — transported 形 (hα 側は `fun _ _ _ => rfl` で閉じる)。
7. `ticyclic_sigma_eq_of_V_eq` / 8. `ticyclic_sigma_congr_eq` — σ-一致 (sigma_eq_tau 経由、
   CF(W,V) 上、pointwise / transported の 2 形)。

### statement 設計 (採用した transport 形式)
- **核心 lemma は pointwise-agreement 形** (brief の「hV ▸ transport 形」でなく): 引数を
  α₁ : SupportedOnV hyp₁ / α₂ : SupportedOnV hyp₂ の対で取り、
  `hα : ∀ v hv₁ hv₂, α₁ ⟨v,_⟩ = α₂ ⟨v,_⟩` で結ぶ。**型 transport / HEq / Eq.rec 完全ゼロ**。
  副産物: **hW : hyp₁.W = hyp₂.W すら不要** (TI-特殊化 (2.5) map は V と α|_V のみに依存
  — 値は conj(V) 上 α(v)、外 0)。証明は `full_map_eq_of_mem_V` +
  `full_map_eq_zero_of_not_mem_conjugatesOfSet_V` + `of_isConj` の 10 行 (IsDadeMap.unique の
  引数を V-共有 2-hyp に開いた形)。
- **transport def は Eq.rec でなく値制限**: `ClassFunction.compHom (Subgroup.inclusion hW.ge)`
  (membership proof だけを hW で運ぶ) → apply が literal rfl、congr 系列の hα も
  `fun _ _ _ => rfl` (定義的 proof irrelevance)。cast unfold 補題が一切要らない。
- instance 規律: FiniteInduce scoped でなく **S05 流の明示 instance binder**
  ([Fintype G] [Fintype hyp.W] [Invertible …]) — S05 lemma 側と同じ流儀で、FiniteInduce
  scope の呼び出し側 (S12) からも従来通り埋まる (ColumnPin が S05 lemma を呼べているのと
  同型)。scoped instance を statement に焼き込まない。

### 設計境界 (重要、part 2 への引き継ぎ)
**σ-一致は V-supported 引数上に限る**。σ は chiFam ((3.5) family) の `choose` で構成され
(S05_SigmaIsometry:24-28)、Dade map が pin するのは CF(W,V) への制限のみ (sigma_eq_tau)。
**非 supported な grid 指標 ω_{ij} 自体の σ-像同定** (certainTypeOmegaSigma ↔
alignedOmegaSigmaGrid の per-index 対応) は
(a) chiFam の (3.5)-determination (一意性、repo 未形式化)、または
(b) notes 進捗⁸系の (3.7)-式係数 rigidity route
のどちらかが必要 — transpose part 2 の本体はここ。part 1 の bridge は「両側の τ が
CF(W,V) 上で同一 map」を無 cast で供給するので、(b) の rigidity 比較の共通土台になる。

### 残り (scope items、未着手)
- item 2: pair 対称化 `.swap` (S↔T/K↔K*/W₁↔W₂)。swap 構成なら V/W が **defeq** で
  共有されるため、`IsDadeMap.unique`/lemma 3 が cast なしで直接効く見込み。
- item 3: type-II L → canonical partner 還元 glue。
- item 4: 行和 pin 変換 (dichotomy の S-列和 → M-行和)。

## 2026-07-10 part 1.5 LANDED (7354b626): item (ii) pair 対称化 / V-W 共有 packaging

S12_TypeIIGridTranspose に 12 宣言追加 (432 行)。全て sorry-free / axiom-clean
(3-standard のみ — **BG S16 の centralizer law / W_structure 連鎖は上流 sorry なし**を
axiom check で実証確認)。import に `OddOrder.FeitThompsonSetup` 追加 (cycle なし:
FTS 閉包は S12_TypeII* leaf を含まない — S13_CoreStructure/S13_Orthogonality 経由確認済)。

### 宣言一覧 (part 1 の 9 宣言に追加)
**Generic 層** (S05-generic、`section GenericBridge` [Fintype G]):
- `ticyclic_Vdiff_eq_of_swap` — Vdiff = W ∖ (W₁ ∪ W₂) の W₁↔W₂ swap 不変性
  (Set.union_comm 一撃)
- `ticyclic_V_eq_of_swap` — Vdiff-形 (hVeq₁/hVeq₂) + W 共有 + swap ⟹ V 一致

**Pair 層** (`section PairPackaging`、[Finite G] + open scoped FiniteInduce per-decl):
- `typePData_toTICyclicHypothesis_{W,W1,W2,V}` (@[simp] rfl) + `_V_eq_Vdiff` (rfl) —
  §10→§5 bridge の projection 補題。**注**: bridge の hVeq は rfl (V := typePV は
  Vdiff と definitional) — CharacterParameters の `chiFam rfl` precedent と整合。
- `section16_partner_typePData_W2_eq` — **T-side W₂ 強制**: dataT.W1 = mp.Kstar なら
  dataT.W2 = mp.K。証明 = dataT.centralizer_W1 (x ∈ K*#) +
  `BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq` (mp.K_eq を pairing に)。
  K* ≠ ⊥ は `S14.card_kappaHall_ne_one`。
- `section16_partner_typePData_W_eq` — dataT.W = mp.K ⊔ mp.Kstar (W_eq + sup_comm)
- `section16_pair_tic_V_eq` — S-side `tp.Sdata` bridge と T-side bridge の **V 同一**。
  S-side W-block: Sdata_W1_eq/Sdata_W2_eq + `W1_eq_K_and_W2_eq_Kstar hG` で (K, K*)、
  T-side (K*, K) → swap 不変性で V 一致。
- `section16_pair_toDadeMap_eq` / `section16_pair_sigma_eq` — canonical pair の
  Dade map / σ の CF(W,V) 上一致 (part-1 核心 lemma の pair instance、pointwise hα 形)

### ★ 2a 調査結果: 両側 TypePData の所在 (構造的 gap 1 点)
- **S-side: 完備**。`Section16TypePStructure.Sdata : TypePData mp.S` が reconciled
  (Sdata_W1_eq/Sdata_W2_eq + W1_eq_K_and_W2_eq_Kstar で W-block = (K, K*) に pin 済)。
- **T-side: 構造的に欠落**。Section16TypePStructure は **Tdata を持たない** (field
  docstring 明記: "Only S is determinate — T need not be type-P₂, so no symmetric
  Tdata")。W₁-prescribing producer `exists_typePData_W1_eq_of_isTypeP2`
  (FeitThompsonSetup:857) は **IsTypeP2 gate** — mp は `S_typeP2` のみ供給
  (T_typeP2 は保証されない)。`typePData_of_isTypeNonI mp.T_nonI` は
  Nonempty (TypePData T) を出すが **W₁ が uncontrolled** (T′ の任意 complement —
  複数 witness 間で W₁ は共役までしか一致しない)。
- **packaging の設計対応**: pair 層は T-side を仮説対
  `(dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar)` で受ける —
  `exists_typePData_W1_eq_of_isTypeP2` が emit する exact な形。W₂ = K / W = K⊔K* /
  V-共有 / σ-一致は全部そこから**導出済**なので、T-side producer が閉じれば無変更で
  plug in。
- **T-side producer の closing 経路 (次 iteration 以降の選択肢)**:
  (a) P₂-gate の精査 — 実際に P₂ が要るのは供給 lemma 3 本
  (`typeP2_mf_internal_fitting_decomposition` / `typeP_hall_derived_eq_and_abelian` /
  `isHall_kappaSigmaCompl_of_isTypeP2_complement`)。underlying engine
  `BG.Ch4.S16.typePData_of_isTypeP_of_inputs` は IsTypeP + 分解 inputs 駆動 —
  T 用に inputs を P₂ なしで供給できるか (BG §14/15 の T-side 構造) が本体。
  (b) (10.7) の実消費形の再確認 — gate `exists_typeIICrossIsometryData`
  (S12_TypeIIFrobenius:1206) の M-side は既に `hyp.typeP : TypePData M` を持つ。
  pair-witness route では M = partner なので、**M-side typeP の W₁ を mp.Kstar に
  reconcile する** (conjugacy adjust / TypePData conjugation transport) 路が (a) の
  代替。なお S12_TypeIIFrobenius は FeitThompsonSetup を import しない (逆も無い) —
  gate の pair-witness 再構成時は gate 側 (or 新 leaf) が FTS を import する方向で
  cycle なし (確認済)。

## 2026-07-10 part 1.6 LANDED (d5809411): T-side producer — sourcing gap CLOSED

`exists_section16_partner_typePData (hG) (mp) : ∃ dataT : TypePData mp.T,
dataT.W1 = mp.Kstar ∧ dataT.W2 = mp.K` — sorry-free / axiom-clean (3-standard)。
**P₂ 不要**。pair 層の仮説対 (dataT, hTW1) はこれで完全 discharge 可能。

### route (a)/(b) の判定根拠
- **(a) は P₂ 必須と確定**: 供給 lemma 3 本のうち `typeP_hall_derived_eq_and_abelian`
  (BG 15.1(b)) は実は **P₂-free** (K ≠ ⊥ のみ) だが、
  `typeP2_mf_internal_fitting_decomposition` (BG Cor 15.5) は冒頭で
  `M_F = M_σ` (⟸ `msigma_isNilpotent_of_isTypeP2`) を本質使用。非 P₂ の partner T では
  M_σ が nilpotent でなく M_F < M_σ となりうるため、(κ∪σ)'-Hall U は M_F を T′ 内で
  補完しない (hDcompl が偽) — U を Hall で選ぶ (a) 型の構成は T-side では成立しない。
- **(b) を採用**: 任意 witness data₀ (typePData_of_isTypeNonI mp.T_nonI) の
  **complement U/構造 field を作り直さず丸ごと共役移送**。data₀.W1 と mp.Kstar は
  どちらも T′ の補群 (data₀.M_complement / `typeP_derivedInG_isComplement_kappaHall`
  — 後者は IsTypeP のみで ungated) → Schur–Zassenhaus 共役
  (`IsComplement'.exists_conj_of_coprime`、coprime |T′| [T:T′] は
  `coprime_card_derived_kappaHall_of_isComplement'`、T′.subgroupOf T normal は
  = commutator ↥T via comap_map_eq_self_of_injective) → conjugator n ∈ T →
  G-level lift (subtype-comp 橋 + map_subgroupOf_eq_of_le ×2) →
  `TypePData.conj` (MaximalSubgroupTypeConj:462、全 20 field 移送済の既存資産!) +
  `hgT ▸` cast-back (hgT : conj g • T = T、projection は fresh-index subst 補題) 。
  S15 CountingLayer:340-385 の `exists_typePData_U_eq_V` が同型 pattern の precedent。

### 発見した既存資産 (調査で判明、再構築を回避)
- `TypePData.conj (φ : MulAut G) : TypePData M → TypePData (φ • M)` — 完全な
  automorphism-equivariance が **既に formal 化済** (GroupTheory/MaximalSubgroupTypeConj)。
- S15 の `reconciled_typePData_T` (CountingLayer:757) は S15-Hypothesis 文脈の
  同型ゴール (data.W1 = hyp.W2 等) を Fact A/B (κ-Hall + Msigma⊓C 同定) 経由で組む —
  ただし S15 文脈では Fact B (`W1_eq_Msigma_T_inf_centralizer_W2`) が別途 gated。
  **mp 文脈では Fact A = mp.Kstar_hall / Fact B = mp.K_eq が structure fields** ゆえ
  本 producer は完全 ungated で閉じた (これが mp-文脈の決定的アドバンテージ)。
- ⚠ 唯一の実装ハマり: `MulAut G` の `Subgroup` への smul は `open scoped Pointwise` 必須
  (HSMul synth 失敗で発覚)。

### 残 (part 2 本体、次 iteration)
1. **grid 指標レベルの σ-同定** ((3.5)-determination or (3.7) 係数 rigidity) —
   certainTypeOmegaSigma (S-side) ↔ alignedOmegaSigmaGrid (M-side) の per-index 対応。
   pair 層の CF(W,V)-一致 (完成) が土台。
2. scope item 3 (type-II L → canonical partner 還元 glue、theorem88_caseB +
   typeP_duality) + item 4 (行和 pin 変換)。
3. gate `exists_typeIICrossIsometryData` の pair-witness 再構成時は gate 側が
   FeitThompsonSetup (or 本 leaf) を import する (cycle なし確認済)。

## 2026-07-10 part 1.7 LANDED (98fb466d): item 3 還元 glue — disjunction 版

3 宣言 sorry-free / axiom-clean (3-standard):
- `section16_S_isTypeII` — IsTypeII mp.S (S_typeP2 + `isTypeII_of_isTypeP2` dictionary)
- `conj_eq_S_or_conj_eq_T_of_isTypeII` — 任意 type-II maximal L について
  (∃g, conj g • L = mp.S) ∨ ((∃g, conj g • L = mp.T) ∧ **IsTypeII mp.T**)。
  theorem88_caseB → type-I 枝は `not_isTypeI_of_isTypeNonI` (IsTypeNonI = 4-or の
  Or.inl) で排除、T-枝は `isTypeII_pointwise_smul` で type-II 証明書付与。
- `exists_conj_eq_S_of_isTypeII` — 条件付き strong 形 (仮説 ¬IsTypeII mp.T)。

### ★ T-枝の排除可否判定 (調査結果): 無条件 strong 版は成立しない
- **Peterfalvi (13.2.a) は片方向**: mmd 原文 "S is of Type II or Type III.
  If q<p, then S is of Type II" — 小さい側の type-II を保証するだけで、大きい側
  T の type-II を**排除しない** (T が type II の可能性は理論上 open)。
- **Coq も同様**: PFsection10 `Frob_der1_type2` の M-枝 kill は
  `rewrite defL FTtypeJ` + **文脈仮説 notMtype2** (§10 の ambient M が type 2 でない
  という section hypothesis) — 無条件の排除は Coq にも無い。
- **設計対応**: disjunction + 証明書 + 条件付き strong の 3 段 API。T-枝が発火した
  場合は IsTypeII mp.T 証明書付きで、pair 機構は S/T 対称
  (exists_section16_partner_typePData で T-side TypePData も取れる) ゆえ消費側
  ((10.7) gate の pair-witness 再構成) で対称に処理できる。gate 側が
  notMtype2-相当の文脈 (M-side は §10 の Hypothesis M で type III/IV/V) を持つ
  場合は strong 形が直接効く。

### issue scope 総括 (part 1–1.7 で landed 済 / 残)
- ✅ item 1 (σ-grid pair transpose bridge の CF(W,V) 層): part 1 + 1.5
- ✅ item 2 (pair 対称化 / V-W 共有): part 1.5 + 1.6 (T-side producer)
- ✅ item 3 (type-II L → canonical partner 還元): part 1.7 (disjunction 版)
- ⏳ item 4 (行和 pin 変換) + **part 2 本体** (grid 指標 per-index σ-同定 =
  (3.5)-determination or (3.7) 係数 rigidity) — 次 iteration。

## 2026-07-10 part 2 第一陣 LANDED (6dfc4e9e): (3.5)-determination core

### route 判定: (a) 採用、(b) は不要と確定
- **書籍 (3.5) は存在文のみ** (mmd 04.5 確認: "There is an orthonormal family (χ_ij) …" —
  一意性 clause 無し)。証明の交叉組合せ論 ((3.5.2)/(3.5.4)) が実質 family を pin する。
- **Coq の形式化が正解形**: `eq_in_cycTIiso` (PFsection3.v:1750) =
  「φ ∈ dirr G が V 上 ω と一致 ⟹ φ = σω」— **σ-像は V-制限だけで pin される**。
  pair transpose 同定 `cycTIisoC` (1849) はこれ + V の swap 不変性 (setUC =
  自分の ticyclic_Vdiff_eq_of_swap!) + (3.2.c) restrict で **2 行**。
  PFsection10:632 の `etaC i j : sigS (w_ j i) = eta_ i j` が (10.7) での消費形。
- **(b) との関係**: 本 route が消費する (3.7)/(3.8) は S05_SigmaTrichotomy の自レーン
  既存 engine (`sigmaCoeff_eq_zero_of_vanishOnV`) のみ — **9076 (lane c、§3 rigidity
  eq_signed_sub_cTIiso) への依存ゼロ**。境界侵犯なし。

### landed (3 宣言、S05-generic、GenericBridge 節)
- `inner_intCast_of_mem_ZIrr` — ZIrr×ZIrr 内積整数性 (右 slot span 帰納)。
  ⚠ upstream hoist 候補 (ZIrrFourier.lean が自然な家)。
- `ticyclic_V_nonempty` — V ≠ ∅ (supportInVdiffEquiv.symm、W₁/W₂ 非自明)。
- **`ticyclic_eq_sigma_omega_of_eqOn_V`** (eq_in_cycTIiso の Lean 版) —
  φ ∈ ZIrr、⟨φ,φ⟩ = 1、φ|_V = ω(ξ)|_V ⟹ φ = σ(ω(ξ))。
  Coq mirror 証明: c = ⟨φ,σω⟩ ∈ ℤ; ‖σω∓φ‖² = 2∓2c ≥ 0 → c ∈ {-1,0,1};
  c=1 → 正定値性で φ = σω / c=0 → ‖ψ‖²=2 + ψ|_V=0 → 全 σ-係数 0
  (sigmaCoeff_eq_zero_of_vanishOnV) が ⟨ψ,σω⟩=1 と矛盾 / c=-1 → ω が非空 V 上
  0 (linear char の unit 値と矛盾)。

## 2026-07-10 part 2 第二陣 LANDED (3d6df7c2 + 5a521768 + ea13fb44): per-index 同定 + 列和→行和 transpose

**3 commit で cycTIisoC assembly + item 4 の generic/pair 層が完成** (全宣言 sorry-free /
axiom-clean 3-standard):

1. **per-index σ-同定** (3d6df7c2): `ticyclic_sigma_omega_eq_of_V_eq` (generic、V/W 共有で
   σ₁(ω(ξ)) = σ₂(ω(ξ∘incl))) + `section16_pair_tic_W_eq` + `section16_pair_sigma_omega_eq`
   (pair instance)。ξ-transport は MonoidHom.comp (Subgroup.inclusion hW.ge)、cast ゼロ。
2. **列和→行和 transpose generic core** (5a521768): `subgroupOfTransport` (2 層 subgroupOf
   value-transport、mathlib hoist 候補) + `subgroupOfTransportCharEquiv` (逆合成 = rfl) +
   `ticyclic_wFstSnd_inclusion_of_swap` (W=W₁×W₂ 分解の swap 転置、wProdEquiv.injective) +
   `ticyclic_omegaProdChar_comp_inclusion_of_swap` (index 翻訳 ω_{(p,kcol)}∘incl =
   ω_{(kcol∘τ,p∘τ')}) + ★`ticyclic_chiFam_columnSum_transpose` (∑_p chiFam₁(p,kcol) =
   ∑_q chiFam₂(kcol∘τ,q)、Fintype.sum_equiv reindex)。
3. **S-side rfl 同定** (5a521768): ★`ticVdiff_typeIIHypothesis46_eq` —
   `ticVdiff (typeIIHypothesis46 hG hSmax hSII data) = typePData_toTICyclicHypothesis data hodd`
   が **rfl** (tic field がその bridge そのもの + 全 data field rfl + proof irrelevance)。
   「要確認」だった S-side V/W 一致は無料で決着 — **dichotomy の chiFam と pair 機構が無変換で接続**。
4. **pair instance** (ea13fb44): swap 等式の抽出 (`section16_pair_tic_W1_eq_W2`/`W2_eq_W1`) +
   ★`section16_pair_chiFam_columnSum_transpose` (S-grid 全列和 = T-grid 全行和 at pair)。

**M-side 発見 (次段の鍵、コード確認済)**: `Hypothesis.toHypothesis46` (M-side、
S12_MaximalIII_IV_V_Core/Hypothesis.lean:1057) も `tic := typePData_toTICyclicHypothesis
hyp.typeP hodd` を field に持つ (S-side と完全同型) → M-side ticVdiff too = rfl。
`alignedOmegaSigmaGrid` の σ も同 bridge 上 (CharacterParameters.lean:138) — pair 機構の
T-side は `dataT := hyp.typeP` で直結。

### ✅ M-side fiber 変換 LANDED (3de82514)
`Hypothesis.exists_alignedOmegaSigmaGrid_row_sum_eq_chiFam_fiber` — 設計どおり
(e = ticWEquivSdiffW pointwise (双方 coe-rfl/coe_ticWEquivSdiffW) + ColumnPin
IndexComponents + Pontryagin counting)。**item 4 の変換チェーンが全リンク閉じた**:
dichotomy 列和 →(pair transpose)→ T-grid 行和 →(fiber lemma)→ aligned 行和 = gate 消費形。
⚠ 実装 crumb: `Nat.bijective_iff_injective_and_card` + card 等式は defeq (`rfl`/hcardW1) /
haveI `NeZero (Nat.card h46.W1)` は h-版と別に要 (syntactic instance) / step1 は
change + `congr 1` (compHom↔linearIrred-comp は defeq、congr が閉じる)。

### gate 組立第一陣 LANDED (910419f5): M-seed 前提 2 本
`isHallSubgroup_of_card_eq` + ★`typePData_W1_isHallSubgroup_kappa` (W₁ 自身が κ(M)-Hall;
typePData_W1_hall_coprime の proof mirror + card-transfer) + `not_isTypeP2_of_isTypeIII_or_IV_or_V`
(P₁/P₂ 排他)。これで下記設計 1 の duality seed (K := hyp.typeP.W1) と、強形 reduction の
¬IsTypeII discharge / K_lt_Kstar 導出の材料が揃った。
**✅ P3/P4 LANDED (5422d724)**: `exists_section16MaximalPair_data_around` +
`exists_section16MaximalPair_around` — `∃ mp, mp.T = M ∧ mp.Kstar = W1` 形。
relabel case-split なし (M 非 P₂ ⟹ 強制)。⚠ producer は tactic-def + rfl-projection
不可 (obtain の casesOn が簡約塞ぐ) → ∃-theorem 形が正。
⚠ axiom: isTypeP2_of_typeP_kappaHall_lt 経由の既存 sorryAx taint 継承 (canonical
data lemma と同一、新規 sorry ゼロ、typeP_duality 自体 clean)。
**✅ P5 確定**: `section16TypePStructure_of_isMinimalSimpleOdd (hG) (mp)` は
**mp-generic** (FTS:953) — M-seeded pair に直接適用可、tp.Sdata 無料
(U-side residual menu の既知 local sorry 1 点、sorried-cite 可)。

**次 = gate field threading** (設計 2/3 の実行)。gate 文脈 (hyp : Hypothesis M) での組立:
```
hP      := hyp.bgTypeP hG (要確認: 名称)
hnotP2  := not_isTypeP2_of_isTypeIII_or_IV_or_V hG hyp.maximal hyp.type_alt
hW1hall := typePData_W1_isHallSubgroup_kappa hG hyp.maximal hP hyp.typeP
⟨mp, hT, hKstar⟩ := exists_section16MaximalPair_around hG … hyp.typeP.W1_le hW1hall
tp      := section16TypePStructure_of_isMinimalSimpleOdd hG mp
dataT   := hyp.typeP / hTW1 := hKstar.symm 形 (hT : mp.T = M を ▸ で調整)
¬IsTypeII mp.T := hT ▸ (classification .2.1 + hnotP2)
S-reduction := exists_conj_eq_S_of_isTypeII
```
残る本体 = aux (S12_TypeIIFrobenius:1332) の WLOG 再構成 (mp.S 上での S11 data
instantiate — TypesIIIIIIVSetup 4-field 組立 + 結論 Frobenius の conj 転送) +
dichotomy→pair transpose→fiber lemma の連結 + c.extension→tau2 packaging + 符号。

**✅ threading 前半 LANDED (8908ee50 + 7cc90fb7)**:
- `Hypothesis.exists_seeded_pair_conj_typeII` — WLOG entry: 任意 type-II S ↦
  ∃ mp g, mp.T = M ∧ mp.Kstar = hyp.typeP.W1 ∧ conj g • S = mp.S (T-枝 kill 込み)。
- `exists_typesIIIIIIVSetup_Sdata` — TypesIIIIIIVSetup mp.S with typeP = tp.Sdata
  (axiom-clean; nontrivial core は TypePNontrivialCore.transfer)。
**次 (残り 2 段)**:
1. **pair-instance gate 変種** (本丸): (mp.S, Sdata-setup) 文脈で gate fields 1-3 を
   実生産 — tau2 := typeII_T2_coherent の c.extension packaging (IntegralCharacterMap 化)、
   nu_tau2_eq := typeII_nu_tau2_dichotomy (ticVdiff rfl 接続)
   → section16_pair_chiFam_columnSum_transpose (dataT := hyp.typeP、hTW1 := hKstar.symm、
   appT := hyp.canonicalFullDadeApp) → exists_alignedOmegaSigmaGrid_row_sum_eq_chiFam_fiber
   (r'char := kcol∘τ)。obligation-3 fields (cross_zero 系) は sorried-cite で前倒し可。
   ⚠ 要設計: dichotomy の ±δ dichotomy 形 → gate の (r', delta') 存在形への整形
   (delta'_pm ✓ sign ± どちらでも)。χ₂/hkeq 供給 = typeII_reducible_inducedKernelFamily_
   eq_columnSum 系 (aux の hred_ne pattern 参照)。
2. **結論 conj-転送**: IsFrobeniusGroup (derivedInG mp.S) H' U' → (derivedInG S) H U。
   H = S_F canonical (maxNilpotentNormalHall の conj равивариantность) + U complement
   conjugacy flexibility。aux 差し替えはこの後。

### 残 = gate 組立 (次 iteration)。★設計確定 (2026-07-10 調査、conj-transport 不要 route):
**発見**: `BG.Ch4.S14.typeP_duality` (TypePDuality.lean:982) は**任意の type-P maximal M**
に対し stated (K = κ-Hall seed) — canonical pair を「conj で寄せる」のでなく
**§10 の M の周りに直接 pair を建てる**:
1. **W1-seeded pair producer** `section16MaximalPair_around_M` (新規、
   `section16MaximalPair_of_isMinimalSimpleOdd` FTS:726 の proof を M-seed で mirror):
   typeP_duality hG hyp.maximal (bgTypeP) (K := κ-Hall containing story: hyp.typeP.W1 が
   κ(M)-Hall — typePData_W1_hall 系で supply) ⟹ mp with **mp.T = M (literal)**、
   **mp.Kstar = hyp.typeP.W1 (rfl by construction)** ⟹ pair 機構の (dataT, hTW1) =
   (hyp.typeP, rfl)。IsTypeP2 M ∨ IsTypeP2 Mstar + M は III/IV/V (hyp.type_alt) ⟹
   mp.S := Mstar が P₂-member。
2. **S-side WLOG (consumer restructure、char-data conj-transport 完全回避)**:
   `typeII_HU_frobenius_of_coherent_aux` (S12_TypeIIFrobenius:1332) の側で、任意 type-II
   (S, data) を `exists_conj_eq_S_of_isTypeII` (hT := ¬IsTypeII M ⟸ hyp.type_alt +
   type 排他) で mp.S に reduce し、**S11 setup/chars/coherence を mp.S 上で新規
   instantiate** (TypesIIIIIIVSetup = {maximal, typeP, nontrivial, type_alt} の 4-field
   組立; typeP = tp.Sdata、nontrivial = (8.6) TypePNontrivialCore producer、
   type_alt = Or.inl (section16_S_isTypeII))。Coq PFsection10 が §10 で char data を
   on-demand 構築するのと同型 — **char-theoretic 対象は一切 conj しない**。
   結論 (IsFrobeniusGroup (derivedInG S) H U) のみ conj g で S へ transport
   (H = S_F は canonical ⟹ conj-image 一致; U は complement conjugacy flexibility)。
3. **gate field threading**: mp.S 上で dichotomy (`typeII_nu_tau2_dichotomy`、
   ticVdiff_typeIIHypothesis46_eq で pair 機構に直結) → pair transpose
   (appT := hyp.canonicalFullDadeApp) → fiber lemma → nu_tau2_eq。
   c.extension → tau2 packaging + 符号 (columnFamily sign → delta')。
4. obligation 3 ((8.18.b) disjointness → cross_zero/zeta_lam_ortho/*_ortho_grid) は別線
   (s10_7 note update⁵)。

### 残 assembly (part 2 第二陣、fresh agent 向け設計) — ↑で実施済み (履歴として保存):
Coq `cycTIisoC` の Lean 版 = **pair 両側 σ の per-index 同定**:
```
σ_T (ω_T(ξ')) = σ_S (ω_S(ξ))   (ξ' = ξ の swap-transport)
```
手順 (全部品 landed 済):
1. hyp_S := typePData_toTICyclicHypothesis tp.Sdata hodd / hyp_T := 同 dataT
   (dataT := exists_section16_partner_typePData で取得)。
2. ξ' : hyp_T.W →* ℂˣ を ξ : hyp_S.W →* ℂˣ から W-同一性 (section16_pair 系の
   hW : hyp_S.W = hyp_T.W、derivable) で transport — **MonoidHom.comp
   (Subgroup.inclusion hW.ge)-流の値レベル transport を推奨** (part-1 の
   ticyclicSupportedOnVCongr と同型、cast ゼロ)。
3. apply `ticyclic_eq_sigma_omega_of_eqOn_V` (hyp := hyp_T, ξ := ξ',
   φ := σ_S(ω_S(ξ))): hφZ = sigma_mem_ZIrr (ω ∈ ZIrr)、hφ1 = sigma_inner +
   irr norm 1 (or chiFam_spec 対角)、hφV = (3.2.c) sigma_apply_irreducible… on
   S-side + V-同一 (section16_pair_tic_V_eq) + ω_S/ω_T の V 上一致 (値レベル、
   transport の rfl-性)。
4. 帰結: alignedOmegaSigmaGrid (M-side) と certainTypeOmegaSigma (S-side、
   typeIIHypothesis46 の ticVdiff — こちらの V/W と typePData bridge の V/W の
   一致 lemma が追加で要る可能性 → 要確認) の per-index 翻訳、そして item 4
   (行和 pin 変換) へ。
注意: ω_S(ξ) の IrreducibleCharacter norm: hφ1 は
`sigma_inner_irreducibleCharacter` + `irreducibleCharacter_inner_eq_ite` (対角) で
1 行のはず。

### 2026-07-10 loop 続報: R1 (pair cluster 一般化) LANDED (f1b48365)
pair lemmas 7 本を (dataS, hSW1 : dataS.W1 = mp.K, hSW2 : dataS.W2 = mp.Kstar) 形へ。
理由 = row-pin で S-side は S11 setup の data.typeP (tp.Sdata と propositional 等価のみ)
— 依存型 rewrite (χ₂ 型が data.typeP 依存) を回避する正しい一般性。
**次 = R2 row-pin theorem** `exists_nu_extension_eq_alignedRow_at_pair`:
`∃ r' delta', pm ∧ c.extension nu = δ' • ∑_j aligned r' j`。組立 (全 interface 確認済):
1. hnuIKF := typeII_sOf_subset_inducedKernelFamily data Y hnu_mem →
   ⟨χ₂, hne1, hkeq⟩ := typeII_reducible_inducedKernelFamily_eq_columnSum (data.typeP)
2. hdich := typeII_nu_tau2_dichotomy … c hne1 hkeq 0 (2 枝: ±sign • ∑_p chiFam (p, kcol±))
3. 各枝: section16_pair_chiFam_columnSum_transpose (dataS := data.typeP、hSW1/hSW2 :=
   hdata ▸ tp-式、dataT := hyp.typeP、hTW1 := hKstar.symm、appS := ticVdiffFullDade…、
   appT := hyp.canonicalFullDadeApp hG hG.odd) — ticVdiff rfl で型 defeq
4. Hypothesis.exists_alignedOmegaSigmaGrid_row_sum_eq_chiFam_fiber (r'char := kcol±∘τ)
5. delta' := ±(columnFamily χ₂).sign、pm := .sign_eq (neg 枝は ∓)
註: tau2 := c.extension は既に IntegralCharacterMap (packaging 不要)。
gate 全 fields 組立 (obligation-3 sorried) は row-pin 後、gate file 側で。

### ★★ R2 row-pin LANDED (31856bed) — nu_tau2_eq 消費形が完全閉鎖
`Hypothesis.exists_nu_extension_eq_alignedRow_at_pair` — **完全 axiom-clean (sorryAx なし)**。
(9.8)分類 → (5.8)dichotomy → pair transpose → fiber sweep の全 chain。
技術 crumbs: hT は subst (M 自由変数、cast ゼロ) / kcol は明示項渡し (metavar+defeq
同時解決は unifier 放棄) / 負枝符号 = Int.cast_neg。
**⚠ leaf 1492 行 — 次の追加前に prefix-split 必須** (GenericBridge 節 (~85-614、凍結) を
新 upstream leaf (例 S12_TicyclicSigmaBridge) へ、transpose leaf が import。module 名
不変で下流無変更)。
**残 (9079 tail)**: (a) leaf 分割 → (b) gate-package assembly (TypeIICrossIsometryData
at pair — nu_tau2_eq/tau2 (= c.extension)/r'/delta' は row-pin で実、obligation-3 の
4 fields (lam_ortho_grid/zeta_ortho_grid/zeta_lam_ortho/cross_zero) は sorried-cite
skeleton) → (c) aux WLOG 差し替え + Frobenius 結論 conj 転送 (obligation 3 と並行)。
接続部品は全て landed: hSW1/hSW2 := hdata ▸ (tp.Sdata_W1_eq.trans
(tp.W1_eq_K_and_W2_eq_Kstar hG).1) 等 (Subgroup-level、依存なし)。

### tail 続報: (a) split + (b) pair-package producer LANDED (00bb893f + 9f944c66)
- (a) `S12_TICyclicSigmaBridge.lean` (574 行、generic 層) ← `S12_TypeIIGridTranspose`
  (966 行、pair 実体化) の 2-leaf 構成へ。namespace/下流不変。
- (b) `S12_TypeIICrossIsometryPair.lean` (新 leaf): `exists_typeIICrossIsometryData_at_pair`
  — tau2 (= c.extension) + r'/delta'/nu_tau2_eq (= row pin) を**実生産**、
  obligation-3 の 4 fields (lam_ortho_grid/zeta_ortho_grid/zeta_lam_ortho/cross_zero)
  のみ sorry (単一 discharge 点)。gate 本体は import cycle で cite 不可 — aux 差し替えは
  本 leaf 下流。
**残 (優先順 = 上流+文書順)**:
1. **obligation 3-(5.3.b)**: lam_ortho_grid / zeta_ortho_grid — coherent image ⊥ σ-grid
   (Coq coherent_ortho_cycTIiso)。§5 章内容、s10_7 note update⁵ の部品survey参照。
2. **obligation 3-(8.18.b)**: zeta_lam_ortho / cross_zero — support disjointness
   (disjoint_conjugatesIntoSet_of_centralizer 等 landed 部品あり)。
3. **(c) aux 差し替え**: 新 leaf (S12_TypeIICrossIsometryPair 下流) に aux の pair-witness
   版 — WLOG entry (exists_seeded_pair_conj_typeII) + setup 組立 (exists_typesIIIIIIVSetup_
   Sdata、hSW1/hSW2 := hdata ▸ tp-式) + §9 counts 再 instantiate + package.elim →
   IsFrobeniusGroup (derivedInG mp.S) → conj 転送 (maxNilpotentNormalHall equivariance +
   complement flexibility) → 旧 aux/gate の deprecate。

### 2026-07-10 obligation 3-(5.3.b) 調査結果 (次 iteration の実装設計)
**Coq 証明構造** (`coherent_ortho_cycTIiso` PFsection8:839): τ₁(irr χ) = R(χ)-列の
signed 部分和 (`mem_coherent_sum_subseq`、(5.5)) + R-元 ⊥ σ-grid (`FTtypeP_base_ortho`、
R 構成時に焼き込み)。Coq の R-構成は prDade 機構 (9014 chain: cyclicTIiso → primeTIred →
uniform_prTIred_coherent → FTtypeP_coherent_TIred) 経由。
**repo 資産**: (5.5)-engine は lane-b が本日 landed
(`coherent_extension_mem_span_Rset_of_mem`、S14_MaximalI/PairCoherence:400 —
S07.CharacterPsiDecomposition.ofProjection + eq_sum_of_psi_eq_zero の S07-generic 核心を
S14-文脈で instantiate した worked template。同 pattern を T2-R-family で再演すれば
τ₂(λ) ∈ ℤ[R(λ)] が出る)。
**★ base-ortho の constituent trick** (新規設計、prDade 焼き込みを回避):
R(λ) = {χ₊, χ₋} (dadeOrthonormalCharacterImageFamilyOfDiff、orthonormal irr、
τ_S(λ−λ̄) = χ₊ − χ₋)。grid 元 η = chiFam-member は ±irreducible。
⟨τ_S(λ−λ̄), η⟩ = 0 が示せれば ⟨χ₊,η⟩ = ⟨χ₋,η⟩ =: c ∈ {0,±1}; c = ±1 なら
χ₊ = ±η = χ₋ で orthonormal 対に矛盾 ⟹ c = 0 ⟹ 各 R-元 ⊥ η。
**⟹ (5.3.b) の残 kernel = 単一 cross-inner**: ⟨τ_side(φ−φ̄), σ-grid 元⟩ = 0
(S-side: τ_S = h46.tau vs M-grid / M-side: hyp.tau vs 自 grid)。
- 注: zeta 側を `orthogonality_of_w1_lt_w2` (Prop109:100、zeta_ortho_grid そのもの) で
  討とうとするのは**不可** — gate 文脈は type III/IV で w2 < w1
  (card_kappaHall_lt_of_isTypeIIIorIV) ⟹ hw : w1 < w2 が偽側。(10.9) は別 dichotomy。
  両 fields とも (5.5)+constituent trick で対称に討つのが正。
- cross-inner の証明素材: (2.6)/(4.6) Dade 随伴 (inner_induce/restrict 系) +
  σ-grid の V-side 挙動 (sigma_apply_…of_mem_V / vanish off conj(V))、または
  (8.18.b)-disjointness 系。Prop109 の STEP-1 機構 (tau_muColumnZero_sub_zeta_eq 等)
  が M-side の類似計算 precedent。
実装順: (i) T2-R-family での (5.5) 再演 (lane-b template mirror) → (ii) cross-inner
kernel (S-side から) → (iii) constituent trick 組立 → lam_ortho_grid / zeta_ortho_grid
discharge (S12_TypeIICrossIsometryPair の sorry 2 本)。

### ★ (5.3.b) 完全写像 (Coq oS1sigma 精読、全部品 landed 確認) — 次 iteration は組立のみ
Coq の base-ortho kernel は support 論法でなく **(3.8) NC-カウント**だが、その実体は:
ψ = φ−φ̄ は A(L)-supported (A₀ の V-part に触れない) ⟹ **τψ は conj(V) 上 vanish**
⟹ norm² = 2 + V-vanishing ⟹ 全 σ-係数 0 (= 各 grid 元と直交)。
**repo 対応 (全 landed)**:
- V-vanishing anchor = `typeII_tau_apply_eq_zero_of_mem_ticVdiffV` (S-side、update⁸ landed)
- 係数消滅 engine = `sigmaCoeff_eq_zero_of_vanishOnV` (S05_SigmaTrichotomy:69、
  hψZ + ‖ψ‖²=2 + V-vanish → 全 sigmaCoeff 0; sigmaCoeff = ⟨·, chiFam P⟩ rfl)
- **lam_ortho_grid の S-side 還元**: aligned_M(i,j) = σ_S-grid 元 (per-index 同定
  section16_pair_sigma_omega_eq + fiber/haligned 系) ⟹ ⟨aligned, τ₂λ⟩ は
  ⟨chiFam_S P, τ₂λ⟩ に等しい — **全て S-side で閉じる**
- (5.5): τ₂λ = R(λ)-constituents の signed 和 — lane-b template
  (coherent_extension_mem_span_Rset_of_mem の ofProjection/eq_sum_of_psi_eq_zero
  pattern) を typeII_T2_memberRFamily で再演
- constituent trick: ⟨τ_S(λ−λ̄), chiFam P⟩ = 0 + R(λ) = {χ₊,χ₋} orthonormal ±irr +
  chiFam P = ±irr ⟹ ⟨χ±, chiFam P⟩ = 0 (c=±1 なら χ₊=±grid=χ₋ 矛盾)
- zeta 側 = 同型を M-side で (τ_M(ζ−ζ̄) の V_M-vanishing anchor は S-side anchor の
  M-mirror — hyp.tau + typePV M; 要 1 lemma、同 pattern)
組立順: (k1) S-side kernel ⟨τ_S(λ−λ̄), chiFam_S P⟩ = 0 (anchor + norm2 + engine) →
(k2) (5.5) 再演 → (k3) constituent trick → lam_ortho_grid (per-index 還元込み) →
(k4) M-mirror で zeta_ortho_grid。

### k1 LANDED (44ea7140): (5.3.b) base-ortho kernel — axiom-clean
`typeII_tau_diff_inner_chiFam_eq_zero` (S12_TypeIICrossIsometryPair)。crumbs: dade0 の
A は A₀-形 (明示型注釈で monotone 拡張) / mem_ZIrr_of_supported は (hsupp)(hZ) 順 /
hconj は typeIIHypothesis46_dade0_hConjInvariant。
**次 = k2**: τ₂λ ∈ ℤ[R(λ)]-form ((5.5) 再演)。lane-b template
(PairCoherence:400 の ofProjection (ψ:=0) + eq_sum_of_psi_eq_zero) を
typeII_T2_memberRFamily の R(λ)-block (dadeOrthonormalCharacterImageFamilyOfDiff) で。
c := typeII_T2_coherent の extension、hsupp/inner 部品は k1 と共通。
その後 k3 (constituent trick: k1 + orthonormal ±irr 対 + grid=±irr) → lam_ortho_grid
(per-index 還元込み、pair leaf の sorry 1 本目 discharge) → k4 M-mirror。

## 2026-07-10 obligation 3 LANDED (4 fields 全 discharge、(8.18.b) 単一 sorry 化)

producer `exists_typeIICrossIsometryData_at_pair` の obligation-3 sorry 4 本を全て実 route で
discharge (69dd1bda + 9733220f + ef1396e2 + 2d110469 + 本 commit)。leaf 残 sorry =
`cross_dade_inner_eq_zero_at_pair` (Coq oST、(8.18.b)) の **1 本のみ**。

### landed 構造
- **lam_ortho_grid** = (5.5) k2 span (`typeII_T2_extension_lam_mem_span_RFamily`、ofProjection
  (ψ:=0) template) + k3 constituent trick + per-index transpose chain
  (`ticyclic_chiFam_transpose` generic / `section16_pair_chiFam_transpose_T` pair /
  `exists_alignedOmegaSigmaGrid_chiFam_family` M-side) + span 帰納 (要素変数化必須 —
  compound 要素への direct induction は "Index not variable")。
- **zeta_ortho_grid** = `Hypothesis.tau1_zeta_inner_alignedGrid_eq_zero` —
  `tau1_zeta_vanishes_on_typePV` (Isometry106) の中間形を full-𝒮 coherence で standalone 抽出。
- **zeta_lam_ortho** = 共役対差分 trick → `orthonormal_vchar_diff_ortho` (S09 port)。
  差分 = Dade 像 (`tau_zeta_sub_conj_eq_tau1` M-side / `extends_on_supported` + map_sub S-side)、
  1-消滅 = `dadeIntegralCharacterMap_apply_one_eq_zero`。
- **cross_zero** = α = μ_s − d·ζ の span/degree/support plumbing
  (`muGrid_column_sum_mem_inducedFamily` + degree_independent + 新 helper
  `mem_zSpan_inducedFamily_support_sharp_derived` / `supportInSubgroup_sharp_derived_subset_A0`)
  → 同じ (8.18.b) 核心。producer に (hζ1 : params.zeta 1 = w₁) 追加 (Coq zeta1w1 対応;
  CharacterParameters は ζ-degree を field に持たない)。

### ★ 残 = (8.18.b) 本体 `cross_dade_inner_eq_zero_at_pair` の honest 証明 (次 iteration)
**構造的発見**: A₀ 全体の thickened 支持は pair で disjoint に**ならない** (両側が V-共役類を
共有)。正しくは M-side (M′)^# = A₁(M)-restricted thickening vs S-side A(S)-closure。
honest 経路 (Coq PFsection10:563-576 + PFsection8 FT_Dade_support_disjoint):
1. **支持制限 Dade 像 bound** (新規、S04 plumbing): supp(τφ) ⊆ ⋃_{a ∈ A ∩ supp φ}
   conj(a·H(a)) (dadeValue_eq: 値は φ(a))。S-side は H ≡ ⊥ (8.16 TI-route) で bare closure。
2. **(8.13.c4) clause** (未 port): supporting maximal L が type II なら M は Frobenius with
   kernel M_F (Coq FTsupport_facts (c4)、BGsummaryII)。既存 `escapingCentralizers_control`
   (S10_StructureSetup:509、sorried) は (b)+type-clause のみで c4 条件文を欠く → 忠実拡張
   statement を §8 側に追加 (sorried-cite、(8.13) は独立上流 obligation)。
3. **typePF exclusion**: type-P₁ M (III/IV/V) は Frobenius with kernel M_F でない
   (kappa ≠ ∅ / isTypeI_iff_isTypeF 経由、要 port 確認)。
4. 組立: 共有点 → supporting 配置 → c4 → Frobenius → exclusion 矛盾。
参考: type-I pair 版 `ftThickenedSupport_mixed_disjoint_of_nonconjugate`
(S10_MinimalSimpleStructure:574、同型 assembly の precedent)。

### その後の残り (9079 tail)
- (c) aux 差し替え: WLOG entry (exists_seeded_pair_conj_typeII) + setup 組立 + producer 接続 +
  結論 Frobenius conj 転送。producer の hζ1 は (10.2) ζ-構成 (exists_zeta_in_inducedFamily_
  degree_w1) から供給。

## 2026-07-10 loop 続報: (8.18.b) の段階的実証明化 — 残 2 点の §8 instance に narrowing

3 commit (c0c58ee4 → 42cb3909 → 5d3c1188) で opaque だった (8.18.b) sorry を分解:

1. **oST character plumbing 実証明** (c0c58ee4): 支持制限 Dade 抽出
   (`IsDadeMap.exists_base_of_map_apply_ne_zero`) ×2 + S-side H≡⊥ + disjoint-support
   内積消滅 → 共役幾何 `typeP_pair_base_not_isConj` に還元。
2. **thickening 還元実証明** (42cb3909): h ∈ H(a) は (2.2) で a と可換・互いに素位数 →
   CRT で a = (a·h)^k → b^k が再び A(S)-点 → bare case へ。
3. **bare-case landing analysis 実証明** (5d3c1188、Coq part_a2):
   b は (κ∪σ)′(S)-元 (κ: S′ = W₁-complement / σ: (P1)) → BG 15.1(c)
   `uniqueMaximal_of_kappaSigmaCompl_element` (**type-generic と判明**、
   hall_E_exists で κσ′-Hall は type-data 不要) → ℳ(C(b)) = {S} →
   C(a) ≤ M 枝は mp.S_T_not_conj (pair field!) で kill / 脱出枝は (S2) へ。

### 残 = §8 instance 2 点 (いずれも忠実 statement + 経路 docstring 済)
- **(P1)** `typeP_pair_core_order_coprime`: Coprime |a| |Mσ(S)| for a ∈ (M′)^# —
  (8.17.a) FTcore-π-partition (Coq FT_Dade_support_partition) の pair instance。
  σ(M)-部は sigma_disjoint_of_nonconjugate (BG 13.9、証明済) で落ちるが、
  M′ の U-部 ((κ∪σ)′(M)-primes) × σ(S) の排除が partition の本体。
- **(S2)** `typeP_pair_escaping_centralizer_not_le_conj_partner`: M-脱出 A₀-点の
  C(a) ≤ S^g → False — (8.13.b/c4) (Coq FTsupport_facts、BGsummaryII) +
  typePF exclusion。上流 `escapingCentralizers_control` (S10:509) は既存 sorried。

axioms: 全 chain の sorryAx はこの 2 点 (+既知上流) 経由のみ。

## 2026-07-10 ★★ obligation 3 完全閉鎖 — (8.18.b) 全 chain 実証明 (sorryAx ゼロ)

(P1)/(S2) の残 2 sorry を同 loop 内で実証明 (8eac1c21 + 6376a9b2):

- **(P1)**: (8.17.a) partition は不要と判明 — type-P₁ collapse
  `isTypeP1_derivedInG_eq_Msigma` (M′ = M_σ、TypeP1Criteria:208) で |a| は σ(M)-数、
  BG 13.9 `sigma_disjoint_of_nonconjugate` + Mσ-Hall で即決着。
- **(S2)**: (8.13.c4) は **BG Theorem D(4) が完全 package 済**
  (`theoremD_msigma_conjugacy_and_centralizers`、sorry-free) — D(4) の
  P₂-supporter 節 (IsTypeP2 N → IsTypeF M ∧ …) + ℳ(C(b))={S} の conj 移送 +
  Prop 16.1(b) (II↔P₂) + 型排他で False。

★★ **`exists_typeIICrossIsometryData_at_pair` = [propext, Classical.choice, Quot.sound]**
— (10.7) cross-isometry package の producer が完全 axiom-clean。4 fields 全て honest。

### 残 (9079 tail、最終項目) = (c) aux 差し替え
`typeII_HU_frobenius_of_coherent_aux` (S12_TypeIIFrobenius:1332) の pair-witness 再構成:
WLOG entry (`Hypothesis.exists_seeded_pair_conj_typeII`) + setup 組立
(`exists_typesIIIIIIVSetup_Sdata`、hSW1/hSW2 := hdata ▸ tp-式) + §9 counts 再
instantiate + 新 producer 接続 (hζ1/hμd は (10.2)/(10.3) canonical 構成から供給) +
package.elim → IsFrobeniusGroup (derivedInG mp.S) → conj 転送
(maxNilpotentNormalHall equivariance + complement flexibility) → 旧 gate deprecate。

## 2026-07-10 (c) 前半 LANDED (a239c479): pair member 上の (10.7) 完全証明

`typeII_HU_frobenius_of_coherent_at_pair` — **axiom-clean [propext, Classical.choice,
Quot.sound]**。旧 aux の dichotomy assembly を honest producer で mirror
(hleft = exists_typeIICrossIsometryData_at_pair + elim; hz1/hμd は
exists_charParameters_full から)。§9 dichotomy/counts/例外 (9.10) は全て sorry-free
上流と実証確認。**Peterfalvi (10.7) が pair member 上で完全に閉じた。**

### (c) 後半の設計 (次 iteration、部品全て存在確認済)
一般 type-II (S, data) → 結論 IsFrobenius (derivedInG S) (data.typeP.H) (data.typeP.U):
1. WLOG: `exists_seeded_pair_conj_typeII` → mp, g, conj g • S = mp.S。
2. **Hall 調整**: conj g • data.typeP.W1 と mp.K は共に mp.S の κ-Hall (cyclic) →
   Hall-C 共役で n ∈ mp.S、u := n·g として conj u • data.typeP.W1 = mp.K。
3. **data forward-conj**: data₃ := data.typeP.conj (MulAut.conj u) : TypePData mp.S
   (TypePData.conj = 全 field 移送済既存資産; H₃ = conj u • H、U₃ = conj u • U、
   H_eq は maxNilpotentNormalHall_pointwise_smul で再確立済 @ MaximalSubgroupTypeConj:469)。
   hSW1 : data₃.W1 = mp.K ✓ (2 の調整)。hSW2 : data₃.W2 = mp.Kstar — **S-side W₂ 強制
   lemma が必要** (T-side 版 section16_partner_typePData_W2_eq の mirror:
   TypePData mp.S with W1 = mp.K → W2 = mp.Kstar; centralizer_W1 + pair の
   Kstar-側 field で導出)。
4. setup₃ := ⟨mp.S_maximal, data₃, nontrivial-transfer, Or.inl (section16_S_isTypeII)⟩。
5. at_pair → IsFrobenius (derivedInG mp.S) (H₃-sub) (U₃-sub)。
6. **transport back は自明化**: H₃/U₃ = conj u • (元の H/U) なので
   `IsFrobeniusGroup.mapEquiv` (FrobeniusGroupQuotient:104) を conj u⁻¹-制限 iso
   ↥(derivedInG mp.S) ≃* ↥(derivedInG S) に適用 → H/U がそのまま戻る
   (U-complement flexibility 不要!)。carrier 橋 = map_subgroupOf_eq_of_le ×2 +
   subtype-comp (S15 CountingLayer exists_typePData_U_eq_V の precedent)。
7. 新 aux を typeII_HU_frobenius_of_coherent に配線 → 旧 gate deprecate。

## 2026-07-11 (c) part B LANDED (2aa6da12): 一般 type-II の (10.7) 完成

`typeII_HU_frobenius_of_coherent'` (pair leaf 末尾) — 任意 type-II (S, setup) の
(10.7) Frobenius。part A の WLOG engine + at_pair + IsFrobeniusGroup.mapEquiv
(conj-制限 iso、carrier 橋は defeq show + pointwise-smul mem lemmas)。
sorryAx = 既知上流 isTypeP2_of_typeP_kappaHall_lt (13.2.a) のみ。

### 配線の知見と残タスク
- ⚠ **S12_MaximalBasic は pair leaf の上流** (FTS ← S13_CoreStructure ←
  S12_MaximalIII_IV_V ← Props109To1011 ← Prop109 ← MaximalBasic) — 旧
  `typeII_derived_frobenius` の frobenius field を直接 repoint すると cycle。
  **`typeII_derived_frobenius` に実 consumer は現状ゼロ** (S07/S11 の docstring
  言及のみ) → 将来の実消費側が pair leaf の `typeII_HU_frobenius_of_coherent'`
  (または新 packaging) を直接 cite する方針。旧 gate `exists_typeIICrossIsometryData`
  + 旧 aux は consumer 不在確認後に hub deprecation 対象。
- ⚠ pair leaf 1570 行 (>1500) — 分割対象: 候補 = (8.18.b) 支持幾何 cluster
  (typeP_pair_* 5 定理) を新 sibling `S12_TypeIIPairSupportGeometry.lean` へ
  prefix-split (下流 import 不変、hub 委任可)。
- 9079 の主要 arc はこれで **全項目完了** (item 1-4 + part 1-2 + obligation 3 +
  (c))。残 = 上記 2 整理タスクのみ。
