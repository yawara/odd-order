# Peterfalvi §4: The Dade Isometry — mini-roadmap (Phase 2b の山場)

**スコープ**: Peterfalvi §4 (pp. 10-14), mmd `04.4_pp_10_14_*.mmd` (127 行), **11 結果 ((2.1)-(2.11))** ⚠️ audit 訂正 (旧記載「6 結果」は overview grep artifact; (2.7)-(2.11) 完全欠落).
形式化先 (予定): `OddOrder/Peterfalvi/S04_DadeIsometry.lean`.
ROADMAP 上の位置: **Phase 2b 第 2 波** (§3 完了後).
役割: **Dade isometry 新規概念の正式定義**, §5-§8 (Coherence) の全前提.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md).

- **L3, L7, L16, L18 "6 結果 (2.1)-(2.6)"** → **重大誤認: 実際 11 結果 (2.1)-(2.11)** + sub-lemmas (2.10.1)-(2.10.3). 既存表で **(2.7), (2.8), (2.9), (2.10), (2.11) 完全欠落**.
- (2.7) Adjoint formula は **外部 7 cite** (§7, §9, §12×2, §13, §16×2) で **最重要 forward-export 補題**. 既存「Helper」評価は overstate.
- (2.1) Coprime decomp は **外部 6 cite** で §4 内部用ではなく **shared primitive**. `OddOrder/GroupTheory/CoprimeAction.lean` (既存) 配置推奨.
- **L141 "mathlib `ClassFunction` 既存" → 誤り**. `ClassFunction G` 型不在 (only `FDRep.character : G → k`, conj-invariant submodule なし). 新規 `OddOrder/RepresentationTheory/ClassFunction.lean` 要.
- **L150 "`MulAction.IsTrivialIntersection` あり" → 誤り**. `Mathlib/GroupTheory/GroupAction/Blocks.lean` の `IsTrivialBlock` は別概念 (subsingleton/univ block, not TI-subset). TI-subset (`A^g ∩ A ≠ ∅ ⇒ g ∈ N_G(A)`) は **mathlib 完全不在**, 新規 `OddOrder/GroupTheory/TISubset.lean` 要.
- **L213 "Phase 1 Ch.6 (Frobenius) 完成必須" → overstate**. §4 で必要なのは `Subgroup.piCore` (= O_{π'}) facts のみで mathlib-native. **Frobenius kernel nilpotency は §4 で不使用** (Ch.6 dep ゼロ).
- **"[BG] §1 軽" → 0**. §4 mmd で [BG] cite **0** (intro prose の `[1s] Lem 7.7` は OCR typo of `[Is]`). §4 は **Phase 2a BG 完全独立**.
- **Encoding 推奨更新**: 既存 candidate 3 (predicate) → **bundled `structure DadeHypothesis` + named `def dadeMap`** (refined candidate 2). 理由: §6-§16 全節で「let τ be the Dade isometry relative to (A,L,G)」と named 形で参照される. predicate は existence elimination の冗長性を生む.
- 行数 "16-18h" → infra 8-10h 別途要; 実装 11 結果 = 既存 6 結果想定の **約 2 倍**.

## TL;DR — Phase 2b の山場, mathlib 完全新規

**Dade isometry は mathlib 未収載の Peterfalvi 独自概念**. TI-subset (Trivial Intersection) または一般化された仮説 (2.2) 下の virtual character 空間 `CF(L, A^#)` から `Z[Irr G]` への等距写像. **§5-§8 (Coherence), §9 (Non-existence), §10-§16 (構造分析) 全てが Dade isometry の上に構築される**.

**Phase 2b の最重要設計判断**: `Dade.Isometry` の Lean 型表現選択 (LinearIsometry API / structure / predicate). この選択が §5-§8 全体の形式化スタイルを決定. **推奨: candidate 3 (predicate-based)** で柔軟性確保.

**mathlib カバレッジ**: ~20% (周辺 API: TI-subset, induced character, inner product は存在). 主定理 (2.6) は完全新規. 補助 lemma (2.1)-(2.5) は Phase 1 Ch.6 (Frobenius) + Ch.指標論 完成下で 30-40% 既存.

## §4 全 11 結果 ⚠️ audit 訂正 (旧表「6 結果 (2.1)-(2.6)」は (2.7)-(2.11) 完全欠落)

| # | mmd 行 | 種別 | statement 概要 | 役割 | mathlib | §5-§16 被引用 |
|---|--------|------|-----------------|------|---------|---------------|
| **(2.1)** | 5-11 | Lemma | Coprime conjugacy decomposition of Hg in solvable | 補助 ((2.6) induction で使用) + **shared primitive** | mid | **外部 6 cite** (§6, §10, §12×2, §15, §16); `OddOrder/GroupTheory/CoprimeAction.lean` 配置推奨 |
| **(2.2)** | 13-24 | **Hypothesis** | 一般化された仮説 3 条件: (a) conjugacy equiv in L, (b) C_G(a)=H(a) ⋊ C_L(a), (c) coprime | **TI-subset 一般化** (核心 setup) | **low** | §4 内全結果の前提 |
| **(2.3)** | 20-22 | Theorem | Characterization: H(a)=1 ⟺ A is TI-subset | (2.2) の specialization | mid | §5, §6 |
| **(2.4)** | 26-32 | Lemma (3 部) | (a) H(a^x)=H(a)^x, (b) conjugate overlap ⇒ L-conjugacy, (c) N_G(aH(a))=C_G(a) | τ well-definedness | low | (2.5), (2.6) |
| **(2.5)** | 34-35 | **Definition** | **τ の定義**: `α^τ(g) = α(a)` if `g ~_G aH(a)`, else `0` | **Dade map の formal def** | low | §4-§16 全面 |
| **(2.6)** | 38-42, 120-124 | **Main Theorem** | (a) **Isometry**: `⟨α^τ, β^τ⟩_G = ⟨α, β⟩_L`, (b) **Preserves virtual**: `Z[Irr L, A] → Z[Irr G]` | **Dade 核心定理** | **low** | **§5-§16 全面 (☆☆☆)** |
| **(2.7)** | (proof body) | **Adjoint formula** | inner product を A 上 sum に reduce する手助け定理 | **stand-alone API edge** | low | **外部 7 cite** (§7, §9, §12×2, §13, §16×2) — §4 内最多 forward |
| **(2.8)-(2.9)** | (proof body) | helper lemmas | (2.6) 経路の inclusion-exclusion 補助 | 内部技術 | low | 内部 |
| **(2.10)** | (proof body) | **Inclusion-exclusion** | coprime + TI 経由の character 和計算 | (2.6) の中核 | low | 内部 + (2.10.1)-(2.10.3) sub-lemmas |
| **(2.11)** | (proof body) | conclusion | (2.6) bundled corollary | (2.6) 同等 | low | 内部 |

## 主要結果の詳細

### (2.2) Hypothesis — TI-subset の一般化

**主張**: G group, A ⊂ L ⊂ G (L = N_G(A) or subgroup). 以下 3 条件を満たすと仮定:

- (a) **Conjugacy equivalence**: `∀ a, b ∈ A: (∃ g ∈ G, a^g = b) ⟹ (∃ l ∈ L, a^l = b)`
- (b) **Centralizer factorization**: `∀ a ∈ A: C_G(a) = H(a) ⋊ C_L(a)` (where `H(a)` is a specific subgroup)
- (c) **Coprime condition**: `(|H(a)|, |C_L(b)|) = 1 for all a, b ∈ A`

**意義**: 古典的な TI-subset は H(a) = 1 case (= 結論 (2.3)). 仮説 (2.2) は **より一般な setting** (e.g., Frobenius 群の kernel 構造を許容) で Dade isometry を構築可能にする.

**Lean 表現**:
```lean
structure DadeIsometry.Hypothesis (G : Type*) [Group G] (A : Set G) (L : Subgroup G) where
  H : ∀ a : A, Subgroup G          -- 各 a に対する centralizer の正規部分
  cond_a : ∀ a b : A, (∃ g : G, a.val^g = b.val) → 
                       (∃ l : L, a.val^l.val = b.val)
  cond_b : ∀ a : A, C_G a.val = (H a ⋊ C_L a.val)
  cond_c : ∀ a b : A, Nat.Coprime (H a).card (C_L b.val).card
```

### (2.3) TI-subset characterization

**主張**: 仮説 (2.2) 下で H(a) = 1 ⟺ A は TI-subset (i.e., `A^g ∩ A ≠ ∅ ⇒ g ∈ N_G(A) = L`).

**意義**: 古典 TI-subset の場合に (2.2) が成立することを保証. Phase 1 Ch.6 (Frobenius) と Ch.5 (Transfer) の TI-subset 関連結果との橋渡し.

**Phase 1 Ch.6 との関係**: Isaacs Ch.6 で Frobenius group の TI-kernel が記述される. Peterfalvi (2.3) はその character-theoretic 翻訳.

### (2.5) τ の定義 — Dade map

**主張**: 仮説 (2.2) 下で `α ∈ CF(L, A^#)` (i.e., L 上の class function で A^# = A - {1} で支持されたもの) について

```
α^τ : G → ℂ
α^τ(g) = α(a)  if ∃ a ∈ A^#: g is G-conjugate to an element of aH(a)
α^τ(g) = 0     otherwise
```

(well-definedness は (2.4) で保証される)

### (2.6) Dade Isometry Main Theorem

**(a) Isometry property**:
```
⟨α^τ, β^τ⟩_G = ⟨α, β⟩_L for α, β ∈ CF(L, A^#)
```

**(b) Virtual character preservation**:
```
τ : Z[Irr L, A] → Z[Irr G]
(整係数 virtual character を整係数 virtual character に送る)
```

**証明戦略** (mmd L42-118):
1. 補題 (2.7): inner product を `Σ over A` に reduce
2. **補題 (2.10): inclusion-exclusion formula** — 主要技術. coprime + TI-property 経由で character 和を計算
3. (a) follows by (2.7) + (2.10) algebra
4. (b) follows from (a) + integrality of induced characters

**形式化の難所**: (2.10) inclusion-exclusion の長い計算 + 多変数 sum 操作.

## Lean 形式化方針: `Dade.Isometry` 型設計

### 候補 1: LinearIsometry 直接活用

```lean
def dadeIsometry (hyp : Hypothesis G A L) : 
    CF(L, A^#) →ₗᵢ[ℂ] (G → ℂ) := ...
```

- **長所**: mathlib `LinearIsometry` API 活用, isometry property が型に内包
- **短所**: dependent type で `CF(L, A^#)` 構築が複雑, Coherence (§7) で多重 isometry 比較がしにくい

### 候補 2: structure DadeIsometry

```lean
structure DadeIsometry (G L : Type*) [Group G] [Group L] (A : Set L) where
  map : CF L A → ClassFunction G
  isometry : ∀ α β, inner_product (map α) (map β) = inner_product α β
  virtual_pres : ∀ α ∈ Z[Irr L, A], map α ∈ Z[Irr G]
```

- **長所**: 明示 record, 後続 §5-§8 で field access 容易
- **短所**: 型クラス derivation が複雑

### 候補 3: Predicate + Existence Theorem (推奨)

```lean
namespace DadeIsometry

structure Hypothesis (G : Type*) [Group G] (A : Set G) (L : Subgroup G) where
  H : A → Subgroup G
  cond_a : ∀ a b : A, (a.val ~_G b.val) → (a ~_{L} b)
  cond_b : ∀ a : A, C_G a.val = (H a ⋊ C_L a.val)
  cond_c : ∀ a b : A, Nat.Coprime (H a).card (C_L b.val).card

def IsDadeIsometry (τ : CF L A → ClassFunction G) (hyp : Hypothesis G A L) : Prop :=
  (∀ α β, ⟨τ α, τ β⟩_G = ⟨α, β⟩_L) ∧
  (∀ α, α ∈ Z[Irr L, A] → τ α ∈ Z[Irr G])

theorem dadeIsometryExists (hyp : Hypothesis G A L) : 
    ∃ τ : CF L A → ClassFunction G, IsDadeIsometry τ hyp := by
  -- (2.5) で τ 構成, (2.6) で IsDadeIsometry を証明
  sorry

end DadeIsometry
```

- **長所**: 数学的表現に近い (「存在する τ で...」), Coherence で複数 τ の比較が自然, 最小実装コスト, mathlib 既存 API への依存最小
- **短所**: τ の具体性が低い (existence のみ), 計算には不便
- **Phase 2b § 5-§8 との整合性**: §7 Coherence は「coherent triple (τ_1, τ_2, τ_3)」を比較するので predicate が自然

**推奨**: **候補 3 (predicate-based)**. §5-§8 への移行が最も柔軟, Phase 2b 形式化期間短縮.

## TI-subset の Peterfalvi 流定義

**Peterfalvi §5 (3.1)-(3.5)** で cyclic normalizer 特殊化された TI-subset が扱われる:
- `A ⊂ L = N_G(A)`, `A^g ∩ A ≠ ∅ ⇒ g ∈ L`
- L は cyclic normalizer を持つ (e.g., Frobenius complement)

**mathlib 状況** ⚠️ audit 訂正 (旧記載「`MulAction.IsTrivialIntersection` あり」は誤り):
- `Mathlib/GroupTheory/GroupAction/Blocks.lean` の `IsTrivialBlock` は **別概念** (subsingleton/univ block, not TI-subset)
- Peterfalvi 流 TI-subset (`A^g ∩ A ≠ ∅ ⇒ g ∈ N_G(A)`) は **mathlib 完全不在**
- **新規 `OddOrder/GroupTheory/TISubset.lean` (~80 LOC) 要**

**Phase 2b 形式化**: 新規 `TISubset.lean` を Wave 1a で先行実装 (§4-§8 全節 + §11-§16 でも使用).

## Virtual character space `CF(H, A^#)` の Lean 表現

**Peterfalvi 流**: H 上の class function で集合 `A^# = A - {1}` で支持されたもの.

**Lean 形式化候補**:
```lean
def CF (H : Type*) [Group H] (A : Set H) : Submodule ℂ (H → ℂ) :=
  { f | ∀ h ∉ A, f h = 0 }  -- supported on A

-- または subtype
def CharacterSupport (H : Type*) [Group H] (A : Set H) : Type* :=
  { f : H → ℂ // ∀ h ∉ A, f h = 0 }
```

**mathlib**: `Submodule` API は既存, `Z[Irr H]` 構造は要追加.

## §5-§8 (Coherence) への橋渡し

```
§4 Dade Isometry
  ↓
§5 ((3.1)-(3.5)): TI-subset cyclic normalizer specialization
  ↓
§6 ((4.1)-(4.5)): Dade extension for certain subgroup type
  ↓
§7 ((5.1)-(5.6)): Coherence definition (Dade isometry が coherence triple として扱われる)
  ↓
§8 ((6.1)-(6.4)): Coherence theorems (Sibley/Reynolds 系)
  ↓
§9: Non-existence (Dade + Coherence の最初の応用)
  ↓
§10-§16: 構造分析 + 最終矛盾
```

**§7 Coherence の Dade 依存**: Coherence triple `(τ_1, τ_2, τ_3)` は 3 つの Dade isometry の整合性. Predicate-based 設計 (候補 3) では `IsDadeIsometry τ_i hyp_i` を 3 つ並べて比較可能.

## BG での関連 (App.C との比較)

**BG App.C** (L4759-5005, Final Contradiction = Peterfalvi 1984 paper 編集再録) は **character-free な generator-relation argument**. Dade isometry を使わずに Theorem C を証明.

**対して Peterfalvi 本体 §9** (= App.C 同等内容) は **Dade isometry + Coherence 経由**で同じ結論. 同じ Theorem C を 2 通りに証明.

**Phase 2b 方針**: §9 を Dade 経由で形式化 (Peterfalvi の道筋を尊重). BG App.C との対応は section docstring で明記.

## mathlib カバレッジ

| 結果 | mathlib | Phase 1 Ch.6 (Frobenius) | 新規実装 | 形式化コスト |
|------|---------|---------------------------|----------|--------------|
| (2.1) | mid (coprime, conjugacy) | 部分 | 40% | 短 (~30 行) |
| (2.2) | low (Hypothesis 構造) | TI-subset 概念 | 70% (def + cond) | 中 (~50 行) |
| (2.3) | mid (TI 概念) | Frobenius 関連 | 30% | 短 (~25 行) |
| (2.4) | low (3 部 lemma) | normalizer / centralizer | 60% | 中 (~50 行) |
| (2.5) | low (def map) | — | 70% | 中 (~30 行 + def) |
| **(2.6)(a)** | low (isometry) | virtual character | **80%** | 大 (~100 行) |
| **(2.6)(b)** | low (virtual pres) | virtual character | **80%** | 中 (~50 行) |
| (2.7) Helper | mid | — | 50% | 中 (~40 行) |
| **(2.10) Inclusion-exclusion** | low | — | **90%** | **大 (~100 行)** |

**全体カバレッジ**: ~20% (mathlib 周辺 API) + ~10% (Phase 1 Ch.6) = **§4 形式化は 70% 新規**.

## Phase 2b §4 形式化着手順

### Stage 1: Infrastructure (準備, 2-3h)
- Hypothesis structure 定義
- Phase 1 Ch.6 (Frobenius / TI-subset) からの import
- mathlib `inner_product`, `ClassFunction`, `Induced` API review

### Stage 2: Helper Lemmas (2-4h)
- (2.1) Coprime conjugacy decomp
- (2.4) τ well-definedness (3 部)

### Stage 3: Definition (2-3h)
- (2.5) τ の formal definition

### Stage 4: Main Theorem (4-6h, **山場**)
- (2.6.a) Isometry property
- 補題 (2.7) inner product reduction (1.5h)
- 補題 (2.10) **inclusion-exclusion formula** (4h, 計算量大)
- (2.6.b) Virtual character preservation (2h)

### Stage 5: Verification (1-2h)
- (2.3), (2.11) characterization 確認

**合計**: **16-18 時間** (経験ある Lean 形式化者), 行数 ~400-450 行.

## Phase 2b §4 着手前のチェックリスト

- [ ] **候補 3 (predicate-based)** 採用確定
- [ ] **Hypothesis structure 設計**: H field の parametrization (π global vs. explicit per a)
- [ ] **Z[Irr L, A] 表現**: `Submodule ℤ (ClassFunction L)` でラップ?
- [ ] **mathlib API レビュー**: `inner_product`, `ClassFunction`, `Induced` 現状確認
- [ ] **(2.10) Inclusion-Exclusion 戦略**: Peterfalvi 直接書き下し vs. tactic macro 設計
- [ ] **§5 preview review**: Coherence 互換性確認 (Predicate 設計が §7 で使える)

## 未解決 / TODO

1. **Hypothesis (2.2) の π parametrization**: BG/Peterfalvi で π = primes dividing |H(a)| を仮定する場合あり. global の `[Fact (...)]` vs. structure field か決定.
2. **CF(L, A^#) と Z[Irr L, A] の関係**: 前者は ℂ 線形, 後者は ℤ 加群. (2.6.a) は ℂ 内積, (2.6.b) は ℤ 構造. Lean では `Submodule ℤ` の coercion 必要.
3. **§4 → §7 Coherence の interface 設計**: §7 着手前に §4 完了が必須. Predicate-based なら interface 簡素.
4. ~~**Phase 1 Ch.6 (Frobenius) 完成日程**: §4 は Phase 1 Ch.6 完成 (Frobenius kernel nilpotent, TI-subset 関連) に依存.~~ ⚠️ audit 訂正 (2026-05-23): **Ch.6 dep ゼロ**. §4 で必要なのは `Subgroup.piCore` (= O_{π'}) facts のみで mathlib-native; Frobenius kernel nilpotency は §4 不使用. Phase 1 Ch.6 未完でも §4 着手可.
5. **BG App.C との対応**: §9 で Dade 経路 vs. App.C generator-relation 経路の Lean 統合戦略決定. Phase 3 結合時の整合性 lemma.

---

**作成**: 2026-05-22. **出典**: Peterfalvi `references/peterfalvi/04.4_pp_10_14_*.mmd` (127 行), Phase 1 Isaacs Ch.6 ノート (Frobenius), `notes/peterfalvi/_overview.md`, `notes/meta/phase2_cross_refs.md`.

**次ステップ**: §3 着手と並行して `Dade.Isometry` の Lean 型設計 review (候補 1-3 比較). §5 (TI cyclic normalizer) 設計の preview.
