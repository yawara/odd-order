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
