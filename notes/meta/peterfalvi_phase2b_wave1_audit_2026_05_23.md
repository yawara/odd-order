# Peterfalvi Phase 2b 第1波 audit (2026-05-23)

Peterfalvi 第 1 波 (character theory core, FT-critical) の **§3-§8 6 節**を **4 視点** (forward / internal hub-and-spoke / mathlib status incl. proof-internal API / preceding [BG]/[Is]/[H]/[HB] cites) で並列再調査した結果の統合メモ. 既存の per-section ノート (`notes/peterfalvi/s{03-08}_*.md`, 2026-05-22 作成) の上にかぶせる **sharp findings + 補正 + 設計提案** のみを記述. 各節の TL;DR / 結果一覧は per-section ノート参照.

## 統合観点での最重要 6 点

1. **5/6 節で結果数誤認 (§3 のみ正確)**: 既存 per-section ノートの「結果数」は §4 (6→**11**), §5 (5→**9**), §6 (5→**10**), §7 (6→**9**), §8 (4→**8**) と systematic に **2-5 結果欠落**. 原因: overview の `^\*\*\([0-9]+\.[0-9]+\)\*\*` grep が top-bolded label のみ拾い、Hypothesis / sub-lemma / 派生結果を漏らす. **欠落結果は下流で最多 cite**になっていることが多い: §5 (3.8) NC trichotomy = §6 (4.6) Hypothesis = §7 (5.7) degree-regular = §8 (6.8) Sibley. これらは全て FT-critical 下流入力.

2. **mathlib character theory は既存 per-section ノートの主張より遥かに薄い**:
   - **`ClassFunction G` 型不在** (only `RepresentationTheory.Character.character : G → k`, conj-invariant submodule なし) — §3, §4, §5, §7 全て依存
   - **Classical induced character (numerical formula) 不在** — `Mathlib.RepresentationTheory.Induced` は **`IndV` coinvariants** (Rep レベル)のみ. classical `(Ind χ)(g) = (1/|H|) Σ ...` 式は無し — §3, §4, §5, §6 全て
   - **`ZIrr G` / `VirtualChar G` 不在** (free Z-module of irreducible characters)
   - **Brauer permutation lemma ([Is] Thm 6.32) 不在** — §3 (1.1), §6 (4.5.b) で必要、§6 (4.5.b) の単一最大 blocker
   - **Character-level Frobenius reciprocity 不在** (only `indResAdjunction_homEquiv` categorical) — §3, §4, §6 全て
   - **`IsTISubset` 不在** (`MulAction.IsBlock` ≠ TI-subset; existing notes が混同)
   - 既存ノート「mathlib 30%」「`ClassFunction` 既存」「Induced 既存」「ZIrr 既存」等 **全て誤り**.

3. **§8 で重大な fabrication 2 件**:
   - 既存 s08 ノート L18, L137, L142, L257: "**Sibley 1984 Contemp. Math. 47**" → **捏造**. 実際は **Sibley 1976 *Illinois J. Math.* 20:434-442 [Si1]**. (6.4)-(6.5) は実は [FT] §11 (Notes §SS6 明示) であり Sibley と無関係. Sibley の貢献は **(6.8) のみ**.
   - 既存 s08 ノート L20, L261-273: "**Reynolds 1965 Duke Math. J.**" attribution for (6.7) → **完全捏造**. Reynolds は Peterfalvi 参考文献 (`04.18`) + Notes (`04.17`) 双方に **存在しない**. (6.7) は無名 internal lemma. **L261-273 sub-section 全削除要**.

4. **Coherence (5.1) 定義に rider 混入** (§7): 既存 s07 ノート TL;DR L10 + コード L46-69 が「`τ̃(χ - 1)` virtual character の差」を (5.1) 定義に含む. **正は (5.1) に rider なし** — extension 存在のみ. "character difference" property は **(5.9.b) の結論** (under (2.2) Hypothesis). さらに L62 コード `χ - 1` → 正は `χ - χ̄` (複素共役).

5. **`OddOrder/RepresentationTheory/` 新規 shared module 群** (Phase 2b 真の前提条件, BG audit 16 modules の Peterfalvi 版):
   - `ClassFunction.lean` (~150 LOC, `CF G`, `CF(H, A)` support, inner product, ZIrr) — §3-§8 全て
   - `InducedCharacter.lean` (~200 LOC, classical formula `(Ind χ)(g)` + numerical Frobenius reciprocity + isometry on `CF(H, A)`) — §3 (1.3)/(1.4), §4 (2.6), §5 (3.5), §6 全て
   - `BrauerPermutation.lean` (~80 LOC, [Is] Thm 6.32, # real Irr = # real classes) — §3 (1.1), §6 (4.5.b)
   - `Clifford.lean` (~150 LOC, Clifford decomposition) — **§3 (1.7), §6 (4.5.b), BG §2 Prop 2.2 共有** (BG audit 既述)
   - `Inertia.lean` (~100 LOC, `I_G(θ)` + induction from inertia, [Is] Thm 6.11) — §3 (1.5), (1.7)
   - `SchurCenterBound.lean` (~50 LOC, [Is] Cor 2.30 `χ(1)² ≤ |G:Z(χ)|`) — §3 (1.8), §8 (6.6), (6.8.3)
   - `IsReal.lean` (~80 LOC, real character predicate + `# real Irr = # self-inv classes`) — §3 (1.1)
   - `IsometryDifferencePair.lean` (~80 LOC, (1.4)/(3.2)/(4.5)/(5.6) 共通 orthonormal-pair 抽出 induction) — §3 (1.4), §5 (3.2), §6 (4.5), §7 (5.6)
   - `SecondOrthogonality.lean` (~50 LOC, column orthogonality `∑_χ |χ(g)|² = |C_G(g)|`) — §3 (1.2)
   - `ClassSumAlgebraHom.lean` (~80 LOC, `ω : ZC[G] → C` algebra hom, [Is] p.35) — §8 (6.7) のみ但し critical
   - `AlgInt.cong.lean` (~50 LOC, algebraic integer congruence `α ≡ β mod n`) — §8 (6.7)
   - `OddOrder/GroupTheory/TISubset.lean` (~80 LOC, `IsTISubset A`) — §4 (2.3), §5 全節, §6 (4.7), §8 (6.7), (6.8)
   
   合計 ~1150 LOC 共通 infra **before** §3-§8 本体 (~2500-3500 LOC).

6. **Pet → BG 依存は ほぼゼロ** (§3-§8 範囲): §3 (0 [BG] cite), §4 (0), §5 (0), §6 (0), §7 (0), §8 (0). 既存 s04 ノート "[BG] §1 軽" / s05 "[BG] §3 dep" / s06 "[BG] App.C 関連" 等 **全て overstated or false**. §3-§8 character theory core は **BG 完全独立**で並行着手可. **BG 依存は §9 以降に集中** (§9 = BG App.C, §10-§16 = Type 分析で BG §10-§16 出力受け取り).

---

## 1. Forward (per-result, 集計)

各節下流引用カウント (§7-§16 mmd grep の集計):

### §3 (Preliminary Character) — flat, no internal hub

| Result | 下流 cites | Top citers |
|---|---|---|
| (1.6) | **7** ★最多 | §8 ×3, §11 ×3, §15 |
| (1.1) | 5 | §8 ×3, §9, §15 |
| (1.4) | 5 + §4 prose | §8 ×2, §14 ×2, §6 |
| (1.9) | 3 | §5 ×2, §8 |
| (1.3) | 3 | §5, §6 |
| (1.2) | 2 | §6, §14 |
| (1.5)/(1.7)/(1.8)/(1.10) | 0 explicit | (used 内部 / via (1.5.e) once) |

既存 s03 "(1.4) hub" → 訂正: **(1.6) hub**. (1.5)/(1.7)/(1.8) 既存「◯ §10-§15」評価は overstate.

### §4 (Dade Isometry) — 11 結果, 既存 6 結果

| Result | 下流 cites | Top |
|---|---|---|
| (2.5) τ Def | "Dade isometry relative to (A,L,G)" 全節 (§6-§16 ほぼ全て) | concept |
| (2.1) Coprime decomp | §6, §10, §12 ×2, §15, §16 = 6 | structural, → `OddOrder/GroupTheory/CoprimeAction.lean` |
| (2.7) Adjoint formula | §7, §9, §12 ×2, §13, §16 ×2 = 7 | heavy externally |
| (2.6.a) Isometry | §7, §16 ×2, §12 | foundation |
| (2.2) Hypothesis | §6, §7, §8, §15 etc | named structure |
| (2.3) TI ⇔ H(a)=1 | §8, §14 | TI bridge |

既存 s04 「6 結果 (2.1)-(2.6)」→ **11 結果 (2.1)-(2.11)**. (2.7) は最も外部 cite が多い "stand-alone observation".

### §5 (TI Cyclic Normalizer) — 9 結果, 既存 5 結果

| Result | 下流 cites | Notes |
|---|---|---|
| (3.8) NC trichotomy | **8** ★最多 (§6×多, §7, §12×2, §15×2) | combinatorial hub, 既存 note 欠落 |
| (3.9) Galois | 4 (§6×2, §12, §13, §15) | (3.9.b) σ-rationality |
| (3.2) | §6, §7, §12, §15 | core σ |
| (3.5) | §6 | classical Case I/II |
| (3.7) | §16 final-contradiction | **§16 直接消費** |

既存 「(3.5) hub」→ 実は **2 hub**: (3.5) (Case I/II 内部) + (3.8) (外部 forward). 既存「§6-§8+§10-§16 全面」→ 実測 §6, §15, §12, §7, §13, §16 のみ; §8, §9, §10, §11, §14 = **0 direct cite**.

### §6 (Dade Certain Subgroup) — 10 結果, 既存 5 結果

41 cites total downstream (§7-§16 中 §6 が **最大 forward footprint**):

| Result | 下流 cites | Top |
|---|---|---|
| (4.1) orthogonality crit | **9** ★最多 | §7×2, §12, §14, §15, §16 |
| (4.3) | 9 | §7×2, §12×3, §15×2 |
| (4.7) Supp | **7** | §7×3, §11×2, §8, §12 |
| (4.6) Hypothesis | 5 | §7×2, §8, §12 |
| (4.5) Ind decomp | 5 | §7, §11×2 |
| (4.4) Kernel | 5 | §12×3 |
| (4.9) τ-isometry | 4 | §12, §13, §15 |

**最大消費**: §12 = 13 cites, §7 = 11, §15 = 11, §11 = 7.

既存 s06 「§4 の application/extension」→ **§5 への依存が遥かに重い** (§5 → §6: **8 cites**, §4 → §6: **3 cites**).

### §7 (Coherence) — 9 結果, 既存 6 結果

| Result | 下流 cites | Notes |
|---|---|---|
| (5.5) Coherent extension | **11** ★最多 | §8, §11, §12, §13, §14×4, §15×2, §16 |
| (5.7) degree-regular | **10** | §8, §11×3, §12×2, §13, §14×2, §16 — gateway to "all of S coherent" |
| (5.2) Hypothesis | 6 | §8×2, §11, §12, §14×2 |
| (5.8) reducible μ_k | 5 | §12×2, §13×2, §15 |
| (5.9) Galois/μ-μ̄ | 5 | §9, §14, §15, §16×2 |
| (5.3) suff cond | 4+ | §8×2, §13, §15 |
| (5.6) composition | 3 | §8×2, §11 |

既存 s07 「(5.5) Coherence main thm」→ 実は **(5.1) Definition + (5.2) Hypothesis + (5.6) Sibley composition + (5.7) degree-regular + (5.8)/(5.9) reducible-μ** の 6-tier 構造. (5.7)-(5.9) 既存「bonus」評価は誤り.

### §8 (Coherence Theorems) — 8 結果, 既存 4 結果

| Result | 下流 cites | Role |
|---|---|---|
| **(6.8) Sibley Coherence** | 4 (§9, §12, §14 + (6.5) internal) | **FT-critical, "Type V case eliminator"** |
| (6.4) | §12 ×2 | Type V (a) hypothesis |
| (6.3) | §13 ×3 | nilpotent descent |
| (6.2) | §13 ×3 | inequality lemma |
| (6.5.b)(c) | §12, §14 | Type I TI-dispatch |
| (6.7) | (6.8) only | character-class congruence, **Sibley's apparatus** |

§9-§16 合計 11 cites (§13=6, §12=3, §9=1, §14=1).

**(6.8) は §9, §12 (Type V), §14 (Type I) の各章 single decisive use** — eliminates an entire type each time.

---

## 2. Internal hub-and-spoke (sharpened)

| 節 | hub | 内部 self-cites | Notes |
|---|---|---|---|
| §3 | **flat** (only 2 self-cites) | (1.1)→(1.5.e), (1.5.a)→(1.6.a) | 10 results essentially **unordered toolbag** |
| §4 | **(2.4)** + **(2.1)** | 内部 tie | (2.4) → τ steps; (2.1) → (2.10) engine |
| §5 | **(3.5)** + **(3.8)** dual hub | 22 + 5 self-cites | 既存「(3.5) only」誤認 |
| §6 | **(4.3.b)** (logical center) + **(4.5)** | 6 + multi | 既存 (4.3) hub OK |
| §7 | **(5.4)** technical + **(5.5)** surface API | 3+3 | 既存 認識 OK |
| §8 | **(6.5)** internal + **(6.8)** export | 5+sink | 既存 認識 OK |

物理 vs 論理順序: 全節で一致 (mismatch なし). §4 (2.7) は中間配置だが外部 forward 7 cite — Lean では (2.5) Def 直後に public theorem 置く推奨.

---

## 3. Mathlib status (proof-internal) — DEEPEST

### 3.1 mathlib v4.29.1 で本質的に欠けている前提

| 概念 | 状態 | 必要箇所 | 新規 LOC |
|---|---|---|---|
| **`ClassFunction G`** (conj-invariant submodule) | 完全に無し (`Character.character : G → k` のみ) | §3-§8 全て | ~150 |
| **Classical `Ind χ` (numerical formula)** | 完全に無し (only categorical `IndV` `Induced.lean:59`) | §3 (1.3), §4 (2.5), §5 (3.5), §6 (4.3.c) 全て | ~80-200 |
| **`ZIrr G` / `VirtualChar G`** | 完全に無し | §3 (1.5), §4 (2.6.b), §5 (3.5), §7 (5.4) | ~30-80 |
| **`Irr(W₁ × W₂) ≃ Irr(W₁) × Irr(W₂)` cyclic** | 完全に無し | §5 (3.3), §6 (4.3) | ~60 |
| **Character-level Frobenius reciprocity** (numerical `⟨Ind χ, ψ⟩ = ⟨χ, Res ψ⟩`) | 完全に無し (categorical のみ) | §3 (1.3), §4 (2.7), §5, §6, §7, §8 全て | ~40-80 |
| **Brauer permutation lemma** ([Is] Thm 6.32) | 完全に無し | §3 (1.1), **§6 (4.5.b) 最大 blocker** | ~80 |
| **Inertia subgroup `I_G(θ)`** + induction from inertia ([Is] Thm 6.11) | 完全に無し | §3 (1.5), (1.7) | ~100 |
| **Clifford theorem** ([Is] Thm 6.5) | 完全に無し | §3 (1.7), §6 (4.5.b), **+ BG §2 Prop 2.2** | ~150 (BG audit 共有) |
| **Schur center bound** ([Is] Cor 2.30) | 完全に無し | §3 (1.8), §8 (6.6), (6.8.3) | ~50 |
| **`# real Irr = # real classes`** ([Is] Thm 6.32 Brauer permutation 系) | 完全に無し | §3 (1.1) | ~80 |
| **Galois auto `Q_n / Q`** decomp ([Is] Lem 3.2 / Cor 3.5) | mid (`IsCyclotomicExtension`, `Cyclotomic.Gal` 部分) | §3 (1.9), (1.10), §5 (3.9), §7 (5.9.a) | ~30-60 |
| **Second orthogonality** (column form `∑_χ \|χ(g)\|² = \|C_G(g)\|`) | 完全に無し (row のみ `char_orthonormal`) | §3 (1.2) | ~30-50 |
| **`IsTISubset A`** | 完全に無し (`MulAction.IsBlock` ≠ TI; 既存ノート混同) | §4 (2.3), §5 全, §6 (4.7), §8 (6.7), (6.8) | ~80 |
| **`IsHallSubgroup`** | mathlib v4.29.1 に **無し** (grep 確認) | §6 (4.2) Hypothesis | (Phase 1 Ch.3 既存 OddOrder?) |
| **Class-sum algebra hom `ω : ZC[G] → C`** ([Is] p.35) | 完全に無し (`MonoidAlgebra.center` あり、explicit map なし) | §8 (6.7) のみ critical | ~80 |
| **Algebraic integer congruence** `α ≡ β (mod n)` | 完全に無し (`IsIntegral`, `RingOfIntegers` あるが congruence wrapper なし) | §8 (6.7) | ~50 |

### 3.2 Per-section バケット summary

| 節 | (a) exact match | (b) wrap | (c) new | 既存ノート評価 | 実評価 |
|---|---|---|---|---|---|
| §3 | 0 | 4 ((1.5.b-e), (1.9.a-b), (1.10.b)) | 7 ((1.1), (1.2), (1.3), (1.4), (1.5.a), (1.6.a-b), (1.7), (1.8), (1.10.a)) | "mid" | **mostly (c)** |
| §4 | 0 | 4 ((2.1), (2.4.a), (2.6.a), (2.6.b)) | 7 | "~20% mathlib" | **正** |
| §5 | 0 | 2 ((3.4)で orthonormal, (3.7) trivial) | 7 | "30%" | **30-35% w/ infra** |
| §6 | 0 | 4 ((4.3.a),(4.3.d),(4.4),(4.10)) | 6 | "30%" | **20% w/o Brauer** |
| §7 | 0 | 3 ((5.3.a),(5.5),(5.9.b)) | 6 | "10%" | **正** |
| §8 | 0 | 1 ((6.2)) | 7 | "5%" | **0% for (6.7)/(6.8)** |

### 3.3 既存 per-section ノートの mathlib 評価訂正リスト

| 節 | 既存 claim | 訂正 |
|---|---|---|
| §3 | "(1.5)-(1.8) mid" | 全て (c) bucket, new helpers 要 |
| §3 | "[Is] Lem 7.7 → §3 (1.4) context" | 実は **§8 L150** (Coherence) |
| §3 | "Frobenius API 既存" | mathlib `indResAdjunction_homEquiv` categorical のみ |
| §4 | "ClassFunction 既存" | **誤り** |
| §4 | "MulAction.IsTrivialIntersection あり" | **誤り** (`IsTrivialBlock` 別概念) |
| §4 | "Phase 1 Ch.6 必須" | overstate; `Subgroup.piCore` で十分 |
| §4 | "[BG] §1 軽" | **誤り** (0 [BG] cite) |
| §5 | "Induced character 既存" | **誤り** (only `IndV` coinvariants) |
| §5 | "Class function CF 既存" | **誤り** |
| §5 | "ZIrr 既存" | **誤り** |
| §5 | "[BG] §3 dep" | **誤り** (0 [BG] cite) |
| §5 | "§4 (Frobenius) TI-subset dep" | §5 mmd で §4 (2.X) cite 0 |
| §6 | "(4.5.b) Phase 1 Ch.指標論で fixed point theory 確認" | Phase 1 計画に無し; 新規 `BrauerPermutation.lean` 要 |
| §6 | "§5 と独立" | 8 cites of §5 (3.X) (大誤り) |
| §6 | "§4 application" | §4 より §5 dep が重い (3 vs 8) |
| §7 | "(5.1) def に virtual char difference rider" | **誤り** ((5.1) は extension 存在のみ) |
| §7 | "mathlib ~10%" | 正だが infra 600 LOC 別途要 |
| §8 | "Sibley 1984 Contemp. Math. 47" | **捏造** (実は Sibley 1976 Illinois) |
| §8 | "Reynolds 1965 Duke" | **完全捏造** (Reynolds 不在) |
| §8 | "mathlib ~5%" | (6.7)/(6.8) は実 0% |

---

## 4. Preceding [BG]/[Is]/[H]/[HB] dependencies — per-section

### 4.1 [BG] cites

**全節 0 件 (proof body, prose 双方)**. §3-§8 character theory core は **BG と完全独立**.

既存 per-section ノート [BG] 主張 → 全て訂正対象:
- s04 "[BG] §1 軽" → 0
- s05 "[BG] §3 dep" → 0
- s06 "BG App.C 関連" → 0
- s07/s08 — claim なし (OK)

### 4.2 [Is] cites (Isaacs *Character Theory of Finite Groups* 1976 — 本プロジェクト Isaacs FGT とは別書)

全 §3-§8 で **proof body cite のみ** (prose だけの言及なし). 一覧:

| §3 | [Is] Thm 6.32 (1.1), Lem 2.21 (1.6.a), Thm 6.11 (1.7.a), Thm 6.5 Clifford (1.7.b), Cor 6.28 (1.7.c), Cor 2.30 (1.8), Lem 3.2/Cor 3.5 (1.10.b), Lang [L] Ch.VIII Thm 3.1 (1.9.a) | 8 cites |
| §4 | [Is] Lem 7.7 (intro prose, motivation only — proof body cite なし) | 0 hard |
| §5 | [Is] Ch.7 (3.1 prose), [Is] Cor 2.23 + Thm 4.21 (3.3 prose) | 2 cites |
| §6 | **[Is] Thm 6.32 Brauer permutation** (4.5.b) | 1 cite (最大 blocker) |
| §7 | 0 cite | — |
| §8 | [Is] Lem 7.7 ×2 (6.8 L150), [Is] Thm 6.34 ×3 (6.8 L150, L156, L160), [Is] Cor 2.30 ×2 (6.6, 6.8.3), [Is] p.35 ω (6.7), [Is] Lem 2.27 (6.8.2.3) | **8 cites** |

合計 [Is] cite: **19 件** ([Is] Thm 6.32 は §3 + §6 で重複). mathlib v4.29.1 で対応**ゼロ**, 全て新規 helper 要.

### 4.3 [H], [HB] cites

§3-§8 範囲で **0 件** (§4 mmd intro prose の "[1s]" は OCR typo of "[Is]"). 既存 _overview L50-55 が [H]/[HB] 言及するのは §11+ から.

### 4.4 Peterfalvi internal dependencies (per-target sharpened)

§6 = **§5 への heaviest consumer** (8 §5 cites vs 3 §4 cites). 既存 _overview "§6: §4-§5 dep" → 順序逆.

§8 = §3 + §4 + §6 + §7 **fully integrated** ((6.8) のみ):
- §3 (1.x): 5 cites
- §4 (2.x): 2 cites
- §6 (4.x): 4 cites
- §7 (5.x): 7 cites

§7 = §6 (4.x) も呼ぶ ((5.3.b) で (4.7) ×1 etc.) — 既存「§4 のみ」誤認.

---

## 5. Per-section ノート corrections (最小 Edit 推奨)

### s03_preliminary_character.md
- L18, L72 (1.5)/(1.7) "mid (Clifford)" → **low** (no Clifford in mathlib)
- L76 [Is] Lem 7.7 "(1.4) context" → **"§8 (Coherence) L150"**
- L25 (1.8) "◯ §14-§15" → "0 explicit forward cite; background tool only"
- L100 "§3 → §4 strict dep" → **正しく forward 1位 (1.6), 1.4 は §4 prereq**
- 行数 350-400 → **~1000-1200 LOC** (infra ~600 LOC 含む)

### s04_dade_isometry.md
- **L3, L7, L16, L18 "6 結果 (2.1)-(2.6)"** → **"11 結果 (2.1)-(2.11)"** (重大欠落)
- L141 "ClassFunction 既存" → **誤り**
- L150 "MulAction.IsTrivialIntersection" → **誤り** (実は `IsTrivialBlock`)
- L213 "20% mathlib + 10% Ch.6" → **Ch.6 寄与ゼロ**, `Subgroup.piCore` で十分
- L254 "Phase 1 Ch.6 完成必須" → **不要**
- "[BG] §1 軽" 削除 → **0 [BG] cite**

### s05_ti_cyclic_normalizer.md
- **L3, L12 "5 結果 (3.1)-(3.5)"** → **"9 結果 (3.1)-(3.9)"**
- L18 (3.5) "§6-§8+§10-§16 全面" → 実: §6×9, §15×3, §12×2, §7×2, §13, §16; §8/§9/§10/§11/§14=**0**
- L53 "Phase 1 §4 dep" → §5 mmd で §4 (2.X) cite **0**
- L294-319 mathlib eval → "Induced/CF/ZIrr 既存" **全て誤り**
- "350-400 LOC" → **700-850 LOC**

### s06_dade_certain_subgroup.md
- **L3 "5 結果 (4.1)-(4.5)"** → **"10 結果 (4.1)-(4.10)"**
- L12 "§4 の応用・拡張" → **"§5 σ + §4 Dade τ; §5 dep 重い (8 cites)"**
- L14 "30% mathlib" → "20%; Brauer permutation 最大 gap"
- L60 (4.2.a) "K の Hall subgroup" → **"L の Hall subgroup"**
- L181 (4.5.b) "Phase 1 で確認" → **Brauer 不在; 新規 `BrauerPermutation.lean` 要**
- L213 "§5 と独立" → **8 §5 cites**
- L218-237 §7 bridge → (5.3.b) は (4.7)+(4.9) 経由

### s07_coherence.md
- **L3 "6 結果 (5.1)-(5.6)"** → **"9 結果 (5.1)-(5.9)"**
- **L10 TL;DR / L46-69 / L408-413 coherence def** → **rider 削除** ((5.1) は extension 存在のみ; "character difference" は (5.9.b) 結論)
- L62 `χ - 1` → **`χ - χ̄`**
- L329 "Inner product 既存" → partial (irreducible のみ; CF 全体 inner product なし)
- L334 "TI-subset → Coherence.Hypothesis 内定義" → **§4-§5 work, §7 内では不要**
- L470 "(5.9.b)以降 omitted?" → No; mmd L136 で終了, omitted 内容なし

### s08_coherence_theorems.md
- **L3, L13, L37 "4 結果 (6.1)-(6.4)"** → **"8 結果 (6.1)-(6.8)"**
- **L18, L137, L142, L257 "Sibley 1984 Contemp. Math. 47" → 訂正: "Sibley 1976 *Illinois J. Math.* 20:434-442 [Si1]"**; (6.4)-(6.5) は **[FT] §11** (not Sibley); only **(6.8)** is Sibley's
- **L20, L158, L181, L261-273 "Reynolds 1965" → 完全削除** (Peterfalvi 参考文献に存在せず)
- L24 "mathlib ~5%" → (6.7)/(6.8) は **0%**
- L267-273 Korean-mixed section → 削除 (Reynolds fabrication 関連)
- L84 (6.2) → (6.5), (6.6) cite なし; (6.3) のみ
- L405-408 "30 days" → **35-45 days realistic**

### `_overview.md` corrections
- 表行 結果数: §4 6→11, §5 5→9, §6 5→10, §7 6→9, §8 4→8 訂正要
- L46 "本体合計 113 結果" → 数値再集計要 (per-section 漏れ加算)
- L31 (§3 "mid") → "(c) bucket 多数; new helpers 要"
- L36-37 (§7-§8) "low" → **0% for (6.7)/(6.8)**

### `phase2_cross_refs.md` corrections
- §3 [BG] 引用「**多数**」(L51) → §3-§8 範囲では **0**. §9 以降に集中.
- L113 "(7.6) ↔ BG Thm 6.2" — 既述 OK
- §3 (1.X) cite 表 [Is] Lem 7.7 (1.4) → §8 (Coherence) L150 へ移動

---

## 6. Implementation order revisions (Phase 2b 第 1 波)

### 6.1 Wave 1a: `OddOrder/RepresentationTheory/` shared modules (Phase 1 不要)

並列実装可、~3-5 日 each:

```
OddOrder/RepresentationTheory/
  ClassFunction.lean             (~150 LOC, §3-§8 全て)
  InducedCharacter.lean          (~200 LOC, classical formula + numerical Frobenius)
  ZIrr.lean                      (~80 LOC, virtual character lattice)
  SecondOrthogonality.lean       (~50 LOC, §3 (1.2))
  IsReal.lean                    (~80 LOC, §3 (1.1))
  Clifford.lean                  (~150 LOC, **BG §2 共有**)
  Inertia.lean                   (~100 LOC, §3 (1.5)(1.7))
  SchurCenterBound.lean          (~50 LOC, §3 (1.8) + §8)
  BrauerPermutation.lean         (~80 LOC, §3 (1.1) + §6 (4.5.b))
  IsometryDifferencePair.lean    (~80 LOC, §3 (1.4) + (3.2)/(4.5)/(5.6) 共通)
OddOrder/GroupTheory/
  TISubset.lean                  (~80 LOC, §4-§8 全)
```

合計 ~1100 LOC infra.

### 6.2 Wave 1b: §3 + §4 (Wave 1a 後)

- §3: ~250-400 LOC (10 結果 + Wave 1a 経由)
- §4: ~300-500 LOC (11 結果; 既存 6 結果想定の約 2 倍)
- 並列可 (§4 は §3 (1.X) 多用だが Wave 1a で代用)

### 6.3 Wave 1c: §5 + §6 (Wave 1b 後)

- §5: ~700-850 LOC (9 結果, (3.5) Case I/II は 300 LOC)
- §6: ~600-800 LOC (10 結果)
- 順序: §5 → §6 (strict, §6 が §5 (3.X) を 8 cite)

### 6.4 Wave 1d: §7 + §8 (Wave 1c 後)

- §7: ~250-400 LOC (9 結果, infrastructure 大半 Wave 1a で吸収済)
- §8: ~800-1200 LOC (8 結果, **(6.7) 単独 ~200 LOC + (6.8) ~400 LOC**)
- §7 → §8 strict, §8 は §7 (5.x) を 7 cite + §6 (4.x) を 4 cite

### 6.5 §3-§8 合計

| Item | LOC |
|---|---|
| Wave 1a shared infra | ~1100 |
| §3 | ~300 |
| §4 | ~400 |
| §5 | ~750 |
| §6 | ~700 |
| §7 | ~350 |
| §8 | ~1000 (含 (6.7)/(6.8) classifier modules) |
| **Total §3-§8** | **~4600 LOC** |

既存 _overview 「§4-§8 で 26 結果 = 23%」想定 → 実は **57 結果** (11+9+10+9+8 + §3 10 = 57). **2 倍以上の実装量**.

時間: ~3-4 ヶ月 (1 module/週 ペース).

---

## 7. 次のステップ

1. **本 audit doc を Phase 2b 着手前必読リスト** (ROADMAP Phase 2b に link).
2. **既存 per-section ノート 6 件に minimal correction** (audit log section + inline 訂正タグ).
3. **`_overview.md` 結果数訂正** + `phase2_cross_refs.md` §3-§8 [BG] dep ゼロ記載.
4. **Wave 1a 11 shared modules のスタブ作成** (docstring に audit link).
5. **§8 fabrication 訂正** (Sibley/Reynolds attribution 削除/置換).
6. **§9 (= BG App.C) audit を別途実施** (本 audit でカバーしていない; Phase 2b 第 2 波範囲).

---

*作成: 2026-05-23. 検証元: Peterfalvi mmd `04.{3-8}_*.mmd` per-section (合計 928 行). per-section ノート 6 件 (2026-05-22) を validate target. 6 並列 sub-agent + synthesis. 出力: per-section 訂正リスト + 横断観察 (mathlib gap 16 件 + Wave 1a 11 modules) + 着手順 revision.*
