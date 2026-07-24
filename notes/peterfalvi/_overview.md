# Peterfalvi: Character Theory for the Odd Order Theorem — overview

**スコープ**: T. Peterfalvi, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000).
原典: `references/peterfalvi/04.*.mmd` (本体 §1-§16, 計 1718 行) と `05-09.*.mmd` (5 つの付録, 計 1183 行).
形式化先 (予定): `OddOrder/Peterfalvi/S{NN}_*.lean` + `Appendices/*.lean`.
ROADMAP 上の位置: **Phase 2b** (Phase 1 Isaacs 完了後着手, Phase 2a BG と並行可).

## Audit log (2026-05-23 audit 訂正, §3-§8 範囲)

統合 doc: [`notes/meta/log/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md).

**結果数の systematic 誤認 (本文表 L28-44)** — §3 のみ正確、§4-§8 で 2-5 結果欠落:

| § | 既存 _overview | 実際 (audit) | 欠落 |
|---|---|---|---|
| §4 | 6 | **11** | (2.7)-(2.11) |
| §5 | 5 | **9** | (3.6)-(3.9) (特に (3.8) NC trichotomy = forward 最多 hub) |
| §6 | 5 | **10** | (4.6)-(4.10) (特に (4.6) Hypothesis = 実は中核) |
| §7 | 6 | **9** | (5.7)-(5.9) (特に (5.7) degree-regular = forward 10 cites) |
| §8 | 4 | **8** | (6.5)-(6.8) (特に (6.8) Sibley main thm) |

L46 "本体合計 113 結果" → 数値再集計要 (per-section 漏れ加算で実数は **131** 程度).

**[BG] 依存 §3-§8 範囲 ゼロ**: §3-§8 character theory core は **BG 完全独立**. L31-37 (§3-§8) で "[BG] §1 軽", "[BG] §3" 等の記載は **全て overstated or false**. 実 [BG] dep は §9 (=App.C) 以降に集中.

**mathlib カバレッジ評価 overstated** (L36-37, L46): "§3 mid", "§4-§8 low" → 実は **全て (c) bucket dominant** (Wave 1a infra 11 modules ~1100 LOC 要). 既存「§4 mid Phase 1 Ch.6 完成下」「§5 low w/ Frobenius API」「§3 既存 wrapper」評価誤認.

**§8 fabrication 訂正** (per-section s08 ノート 該当): "Sibley 1984 Contemp. Math. 47" → **Sibley 1976 *Illinois J. Math.* 20** (Notes §SS6); "Reynolds 1965 Duke Math. J." → **存在しない (捏造)**.

詳細は統合 doc + per-section audit log 参照.

## TL;DR

Peterfalvi 本書は Feit-Thompson 定理の **指標理論パート**: BG (Phase 2a) で確立した最小反例 G の局所構造を、指標論で再分析し、最終矛盾を導出する. 全 16 節 + 5 appendix で **本文 113 個 + 付録 27 個 = 140 個の番号付き結果** ((N.M) 形式が本文、Proposition/Lemma/Theorem N. 形式が付録).

- **§1-§2** (80 行, 0 結果): 導入と記号 (前文相当、補強なし)
- **§3-§8** (978 行, **57 結果** ⚠️ audit 訂正; 旧 36 は §4-§8 grep 漏れ累積): 指標理論の道具袋. **§3 Preliminary** (10), **§4 Dade Isometry** (11), **§5 TI-Subset cyclic normalizer** (9), **§6 Dade Isometry for Certain Type** (10), **§7-§8 Coherence** (9+8). **新規概念 (Dade isometry, coherence) の中核**. **BG 完全独立で並行着手可** (§3-§8 範囲で [BG] cite ゼロ).
- **§9** (162 行, 6 結果): "Non-existence of a Certain Type of Group of Odd Order". **BG App.C と並行内容**. Phase 2a App.C と統合.
- **§10-§15** (1087 行, 60 結果): 最小単純群 G の最大部分群 (Type I, II, III, IV, V) の **指標論的分析**. **BG Ch.3-Ch.4 の出力を入力にする**. §15 (365 行, 17 結果) が最大規模で、S, T 部分群を最終矛盾向けに詰める.
- **§16** (184 行, 11 結果): **G の非存在**. FT 局所部 + 指標部の最終結合.
- **付録 (05-09)** (1183 行, 27 結果): A Suzuki 二重推移群定理 (713 行, Ch.5.0-5.6 まで分割; 主要本体), B Huppert 特例 (26 行), C Near-Fields (44 行), D Suzuki 2-Groups (130 行), E Feit-Sibley (228 行).

**FT クリティカル経路**: §3-§8 (指標論コア) → **§9** (= BG App.C) → §10-§15 (型分析) → **§16** (非存在). 全節が ☆ (FT 必須). 付録は **△ (FT 経路外)** — Suzuki/Huppert/Near-fields は Peterfalvi 自身の独立再録、Phase 2b 完成度のためのオプション.

**mathlib カバレッジ** ⚠️ audit 訂正 (旧記載「§3 mid」「§4-§8 low」評価 overstated): §3-§8 範囲は **全節 (c) bucket dominant** で、Wave 1a 共有 infra **11 modules ~1100 LOC** 要 (`OddOrder/RepresentationTheory/` 配下 `ClassFunction`, `InducedCharacter`, `ZIrr`, `Clifford` (BG §2 と共有), `Inertia`, `SchurCenterBound`, `BrauerPermutation`, `IsReal`, `IsometryDifferencePair`, `SecondOrthogonality` + `OddOrder/GroupTheory/TISubset`). (6.7) 専用 `ClassSumAlgebraHom` + `AlgInt.cong` 別途. §10-§16 (構造分析) は **low** (BG 結果の指標論的再解釈で 100% 新規). **Phase 2b の中核は §4-§8 の Dade isometry + Coherence の形式化** (mathlib 完全未収載).

## 本体節一覧

行範囲は per-file. **結果数** は `^\*\*\([0-9]+\.[0-9]+\)\*\*` (Peterfalvi の独自番号 `**(N.M)**` 形式) の grep 値.

| § | Type | ファイル | 頁 | 行数 | 題名 | 結果数 | mathlib | FT | BG 依存 | 一言 |
|---|------|----------|----|------|------|--------|---------|-----|---------|------|
| 1 | 序 | 04.1 | 1-2 | 40 | Introduction | 0 | n/a | △ | none | FT 証明戦略 + BG 依存性明示 |
| 2 | 記号 | 04.2 | 3-4 | 40 | Notation | 0 | n/a | △ | none | 指標論・加群記号定義. mathlib 移植先選定 |
| 3 | 基礎 | 04.3 | 5-9 | 140 | Preliminary Results from Character Theory | 10 | **mid** | ◯ | [BG] §1 軽 | Isaacs [Is] Ch.指標論 + Peterfalvi 補強 ((1.1)-(1.10)). mathlib 既存と橋渡し |
| 4 | 中核 | 04.4 | 10-14 | 127 | The Dade Isometry | **11** ⚠️ | **low** | ☆ | **0** ⚠️ | **(2.1)-(2.11) Dade isometry 定義 + 主定理 + (2.7)-(2.11) sub-lemmas**. TI-subset 上の virtual character isometry. audit 訂正: 旧 6 結果は (2.7)-(2.11) 欠落 |
| 5 | 中核 | 04.5 | 15-20 | 174 | TI-Subsets with Cyclic Normalizers | **9** ⚠️ | low | ☆ | **0** ⚠️ | **(3.1)-(3.9)** cyclic normalizer 特殊化. **(3.8) NC trichotomy = forward 8 cite 最多 hub**. audit 訂正: 旧 5 結果 → 9 |
| 6 | 中核 | 04.6 | 21-24 | 108 | The Dade Isometry for a Certain Type of Subgroup | **10** ⚠️ | low | ☆ | **0** ⚠️ | **(4.1)-(4.10)** Dade 拡張. (4.6) Hypothesis が §9-§16 で named hyp. audit 訂正: 旧 5 結果 → 10; **§5 dep が §4 より重い (8 vs 3 cites)** |
| 7 | 中核 | 04.7 | 25-29 | 136 | Coherence | **9** ⚠️ | low | ☆ | **0** ⚠️ | **(5.1)-(5.9) Coherence 定義 + 基本性質**. **(5.5) ×11 + (5.7) ×10 が forward 最多 hub**. audit 訂正: (5.1) def に rider なし (character difference は (5.9.b) 結論) |
| 8 | 中核 | 04.8 | 30-37 | 243 | Some Coherence Theorems | **8** ⚠️ | low | ☆ | **0** ⚠️ | **(6.1)-(6.8) Coherence 応用定理**. **(6.8) のみ** が Sibley 1976 *Illinois J. Math.* 20 寄与; **(6.3),(6.5) は [FT] §11 から** (Sibley 無関係); **(6.7) は無名 lemma** (Reynolds 帰属は audit 訂正で削除) |
| 9 | 最終 | 04.9 | 38-43 | 162 | Non-existence of a Certain Type of Group of Odd Order | 6 | low | ☆ | §3-§8 + [BG] §3 | **(7.1)-(7.6) ≡ BG App.C Theorem C**. Frobenius family の非存在 |
| 10 | 構造 | 04.10 | 44-49 | 166 | Structure of a Minimal Simple Group of Odd Order | 6 | low | ☆ | **[BG] §10-§16 全面** | **(8.1)-(8.6) G の Type I-V 分類定義**. BG Theorem A-E 翻訳 |
| 11 | 構造 | 04.11 | 50-57 | 202 | Maximal Subgroups of Types II, III and IV | 9 | low | ☆ | §10 + [BG] §11-§13 | **(9.1)-(9.9) 型 II/III/IV 詳細**. (9.1) Wielandt 作用, (9.2) Frobenius kernel cohomology |
| 12 | 構造 | 04.12 | 58-63 | 136 | Maximal Subgroups of Types III, IV and V | 7 | low | ☆ | §11 | **(10.1)-(10.7) 型 III/IV/V**. (10.7) [S,S] が Frobenius (Frobenius group with kernel の中核) |
| 13 | 構造 | 04.13 | 64-68 | 108 | Maximal Subgroups of Types III and IV | 8 | low | ☆ | §12 | **(11.1)-(11.8) 型 III/IV 核構造** |
| 14 | 構造 | 04.14 | 69-74 | 110 | Maximal Subgroups of Type I | 13 | low | ☆ | §13 + [BG] §12 (E) | **(12.1)-(12.13) 型 I (最複雑)** |
| 15 | 構造 | 04.15 | 75-86 | 365 | The Subgroups S and T | 17 | low | ☆ | §14 + [BG] §15 (M_F) | **(13.1)-(13.17) S, T の位数・正規化群・指標**. **§16 直前の最終仕込み**. 本文最大規模 |
| 16 | 最終 | 04.16 | 87-92 | 184 | Non-existence of G | 11 | low | ☆☆ | §3-§15 + [BG] §16 | **(14.1)-(14.11) G の非存在 = FT 完了**. 指標論計算が中心 |

**本体合計**: 1718 行, **131 程度結果** ⚠️ audit 訂正 (旧「113 結果」は §4-§8 grep artifact で (2.7)-(2.11), (3.6)-(3.9), (4.6)-(4.10), (5.7)-(5.9), (6.5)-(6.8) 欠落の累積). per-section 再集計: §3=10, §4=11, §5=9, §6=10, §7=9, §8=8, §9=6, §10=6, §11=9, §12=7, §13=8, §14=13, §15=17, §16=11 → 合計 **134** (§1+§2 が 0 結果). mathlib カバレッジ: **全節 (c) bucket 多数** (audit 訂正で旧「§3 mid」「§7-§8 low」評価 overstated; (6.7)/(6.8) は実 0%). **§4-§8 のコア理論 (Dade + Coherence) が形式化の山場** (audit 訂正: 47 結果, 全 35%) + Wave 1a infra ~1100 LOC 別途.

## 付録一覧

Peterfalvi の付録は **05-09 prefix で 11 ファイル**. 番号付き結果は `^\*\*?(Theorem|Lemma|Proposition|Corollary) [0-9]` 形式 (Roman 章節別ナンバリング).

| App | ファイル | 頁 | 行数 | 題名・主要結果 | 結果数 | mathlib | FT | 内容 |
|-----|---------|----|------|----------------|--------|---------|-----|------|
| A Intro | 05.0, 05.1 | 97-98 | 73+57 | A Theorem of Suzuki: Introduction | 0+1 | low | △ | Suzuki 1962 主結果の概観 (3 つの 2-trans 群) |
| A §2 | 05.2 | 99 | 33 | Notation | 0 | n/a | △ | |
| A §3 | 05.3 | 100-107 | 191 | General Properties of G | 16 | low | △ | **Proposition 1-16**. Suzuki 仮説下の G の構造. **付録最大** |
| A §4 | 05.4 | 108-114 | 168 | The First Case | 1 | low | △ | Case A 分析 |
| A §5 | 05.5 | 115-121 | 178 | The Structure of H | 1 | low | △ | H 部分群構造 |
| A §6 | 05.6 | 122-134 | 313 | Characterization of PSU(3,q) | 2 | low | △ | PSU(3,q) 特性化 |
| B | 06.0 | 135-136 | 26 | A Special Case of a Theorem of Huppert | 1 | low | △ | Huppert 1957 定理の Peterfalvi 流再証明 |
| C | 07.0 | 137-138 | 44 | On Near-Fields | 2 | low | △ | Near-field (Wedderburn 系) の基本 |
| D | 08.0 | 139-143 | 130 | On Suzuki 2-Groups | 4 | low | △ | Higman 分類 Suzuki 2-群 |
| E | 09.0 | 144-150 | 228 | The Feit-Sibley Theorem | 2 | low | △ | Feit-Sibley 1976 定理 |

**付録合計**: 1183 行, **27 結果**. 全 △ (FT 本筋外) — Suzuki/Huppert/Near-fields/Suzuki 2-groups/Feit-Sibley は本書独立トピックで、Peterfalvi の **完成度のため** に再録. **Phase 2b 必須は本体 §1-§16 のみ**, 付録は Phase 2b 完了後の発展材料.

## 主要概念と mathlib カバレッジ

### 1. Dade Isometry (§4, (2.5)-(2.6))

**内容**: TI-subset `A ⊂ G`、その正規化群 `L = N_G(A)` に対し、`L` 上 `A` で支持された virtual character `CF(L, A^#) → CF(G, ...)` の **isometry** `τ` (内積保存). 仮想指標 `Z[Irr L, A]` から `Z[Irr G]` への線形写像.

**mathlib 状況**:
- 直交関係 (内積保存): `Mathlib/RepresentationTheory/Character.lean` 既存
- TI-subset: Peterfalvi 流定義は mathlib 未収載 (basic な disjoint conjugate 系のみ)
- **Dade isometry 自体**: 完全新規
- 仮想指標 `Z[Irr H]`: 既存. ただし `Z[Irr H, A]` (support 制限) は要拡張

**予想**: **low** — Dade isometry の主定理は完全新規. mathlib 基礎 API の上に `Dade.isometry` 抽象型を新規定義する形が自然.

### 2. Coherence (§7-§8, (5.1)-(5.6))

**内容**: 等距写像 `τ: Z[S, A] → Z[Irr G]` が **coherent** ⟺ `Z[S]` 全体への拡張 `τ̃` が存在し、各 `χ ∈ S` で `τ̃(χ - 1)` が **virtual character の差** で書ける.

**mathlib 状況**: **未収載**. Peterfalvi 独自概念で mathlib に対応物無し.

**予想**: **low** — `OddOrder.Peterfalvi.Coherence` 名前空間で完全新規実装. §4-§6 (Dade) と並行設計.

### 3. TI-Subset (§5, (3.1)-(3.5))

**内容**: Trivial Intersection subset `A ⊂ G` — `A^g ∩ A ≠ ∅ ⇒ g ∈ N_G(A)`. Isaacs Ch.6 (Frobenius) と Ch.5 (Transfer) の境界概念. Peterfalvi §5 は cyclic normalizer 特殊化.

**mathlib 状況**: 基本概念は周辺 API (disjoint conjugate) で部分被覆だが、Peterfalvi 流 `TI(G, A)` を 1 つの型として定義は無し.

**予想**: **mid** — 基本部分は mathlib で組める. cyclic normalizer 特殊化部分は新規補題 4-5 個.

### 4. Virtual Character Space `CF(H, A^#)` (§3, (1.1)-(1.10))

**内容**: 集合 `A ⊂ H` で支持された複素類関数 (virtual character integer combination の前段). `H^# = H - {1}` で支持されるものは「**character vanishing at identity**」.

**mathlib 状況**:
- `RepresentationTheory.Character` 既存
- 部分空間 `CF(H, A)` の明示型は無し (関数 + support 制限で代用可)
- `Z[Irr H]` (virtual character の Z-module 構造) は既存

**予想**: **mid** — 既存 API の薄いラッパー + Peterfalvi 流 notation で OK.

## FT クリティカル経路

```
Phase 2a 完成 (BG)
       ↓
[Peterfalvi §1-§2] (記号・前文)
       ↓
[§3 Preliminary] (指標論の前提 = Isaacs [Is] 経由)
       ↓
[§4 Dade Isometry]     ←─ Phase 2b の山場 (新規概念)
       ↓
[§5 TI-cyclic norm]
       ↓
[§6 Dade for certain type]
       ↓
[§7 Coherence]         ←─ Phase 2b の中核
       ↓
[§8 Coherence Theorems]
       ↓
[§9 Non-existence of Certain Type] ≡ BG App.C
       ↓
[§10 Structure of Minimal Simple] (Type I-V 定義) ← BG Ch.3-§16 from Phase 2a
       ↓
[§11-§14 Type II/III/IV/V/I 分析]
       ↓
[§15 S and T] ← 最大規模、最終仕込み
       ↓
★ [§16 Non-existence of G]
       ↓
    FT 完了
```

## BG との関係

| 項目 | BG | Peterfalvi | 関係 |
|------|-----|------------|------|
| **App.C (Final Contradiction)** | App.C (L4759-5005, 246 行, 3 結果) | §9 (162 行, 6 結果) | **重複内容**. BG App.C = Peterfalvi 1984 paper 改訂版を Carlip-Wheeler が再編. Phase 2b §9 を一次、BG App.C を二次 |
| **§10 入力 Theorem A-E** | §16 Main Results (Ch.4 最終) | §10 (8.1)-(8.6) Type 分類 | **逐次依存**. BG Ch.4 の主結果が §10 の前提 |
| **§11-§14 構造** | §10-§13 (Ch.3 Maximal) + §14-§15 (Ch.4 Type 𝒫, M_F) | §11-§14 各 Type 分析 | **逐次依存**. BG 局所構造を Peterfalvi が指標論で再分析 |
| **§15 S, T** | §15 M_F | §15 (13.1)-(13.17) S, T | Peterfalvi 独自詳細 (BG では片付かない部分の指標論的完成) |
| **§16 Non-existence** | §16 Main Results | §16 (14.1)-(14.11) | BG が局所部の矛盾を、Peterfalvi が指標論の矛盾を導く. **両者合わせて FT** |

**統合**: Phase 3 (最終結合) で BG App.C ≅ Peterfalvi §9, BG §16 + Peterfalvi §16 → FT メイン定理ステートメント. Phase 4 で `FeitThompson : ∀ (G : Type*) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G` を完成.

## Phase 2b 着手順の提案

### 第 1 波 (Phase 1 Isaacs 完了直後、Phase 2a と並列可)
- **§1** (Introduction): 記号集約のみ. 形式化対象は 0 結果、`OddOrder.Peterfalvi.S01_Introduction.lean` に空ファイル + 大規模 docstring
- **§2** (Notation): 同上. notation 定義のみ. mathlib との notation 対応を docstring に
- **§3** (Preliminary): Isaacs [Is] 表現論 + Peterfalvi 補強. mathlib `Character.lean` API + 新規補題 5-6 個

### 第 2 波 (§3 完了後、Phase 2a 中盤と同期)
- **§4** (Dade Isometry): **新規型 `Dade.Isometry` 設計** + 主定理 (2.6)
- **§5** (TI-cyclic norm): §4 後すぐ
- **§6** (Dade for certain type): §4-§5 拡張

### 第 3 波 (§6 完了後)
- **§7** (Coherence): **新規型 `Coherence` 設計** + 基本性質
- **§8** (Coherence Theorems): §7 応用

### 第 4 波 (§8 完了 + BG Ch.4 完了後、Phase 3 準備)
- **§9** (Non-existence Certain Type): **BG App.C と同期形式化**

### 第 5 波 (Phase 2a 完了後)
- **§10** (Structure Minimal Simple): BG Theorem A-E 翻訳. 並行不可 (BG 完成必須)
- **§11-§14** (Type 分析): §10 後. **§11 → §12 → §13 → §14 の線形チェーン**

### 第 6 波 (§14 完了後)
- **§15** (S and T): 最大規模. 1 節で 365 行. 形式化期間長め
- **§16** (Non-existence G): §15 直後、Phase 3 結合の直前

### 第 7 波 (Phase 2b 本体完成後、独立)
- 付録 A Suzuki (05.*) : 独立トピック. Phase 1 Ch.8 (permutation group) の活用先. Phase 2b 必須ではない
- 付録 B Huppert / C Near-Fields / D Suzuki 2-groups / E Feit-Sibley: 各独立. Phase 2b 完成度のため

## ROADMAP リンク

- Phase 2b チェックリスト: [ROADMAP.md#phase-2b--peterfalvi-本体](../../ROADMAP.md)
- BG overview: [`notes/bg/_overview.md`](../bg/_overview.md)
- 3 冊間クロス参照マップ: [`notes/meta/phase2_cross_refs.md`](../meta/phase2_cross_refs.md)
- Phase 1 Isaacs Ch.6 (Frobenius) — Peterfalvi §11-§14 で多用: [`notes/isaacs/ch06_frobenius_actions.md`](../isaacs/ch06_frobenius_actions.md)
- Phase 1 Isaacs Ch.8 (Permutation Groups) — Peterfalvi 付録 A Suzuki で前提: [`notes/isaacs/ch08_permutation.md`](../isaacs/ch08_permutation.md)

## 未解決事項 / TODO

- **§4 Dade isometry の Lean 表現方針**: `def Dade.isometry : (CF(L, A) ≃ₗ[ℂ] CF(G, ...))` か、`structure Dade where ...` か. mathlib `LinearIsometry` API との接続要設計
- **§7 Coherence の formalize 戦略**: Peterfalvi 流 `coherence triple (τ, S, A)` を 1 つの structure として捉える方針 vs. ad-hoc な predicate. §8 の応用補題見てから決める
- **§3 Preliminary が mathlib [Is] (Isaacs Character Theory 1976) のどこまでカバーするか**: Peterfalvi が引く [Is] Thm 6.32, 6.5, 2.21, Cor 6.28, 2.30, Lem 7.7 は mathlib `Character.lean` / `Induced.lean` に対応物がある可能性. §3 着手前に [Is] ↔ mathlib 対応表を作成 (TODO)
- **付録 A Suzuki が PSU(3,q) を含む意義**: BG 本文 (§3 Frobenius Actions) でも PSU(3,q) が現れるが、Peterfalvi 付録 A は完全に独立証明. Phase 2a §3 形式化時に PSU(3,q) 周辺の API 整備が App.A の前提にもなるか要確認
- **Peterfalvi 04.17 Notes (L1-26)** の中身を per-section ノート (§1 着手時) で確認. 編集者注 + bibliography 補強. Phase 4 で重要かも

---

*作成: 2026-05-22. 出典: `references/peterfalvi/04.*.mmd` (本体 1718 行) + `05-09.*.mmd` (付録 1183 行). Phase 1 Isaacs ノート (Ch.1-10) のクロス参照確認済. 各節 per-section ノートは `notes/peterfalvi/sNN_*.md` で詳細化していく.*
