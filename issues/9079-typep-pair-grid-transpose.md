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
