# Peterfalvi §7: Coherence — mini-roadmap (Phase 2b の中核)

**スコープ**: Peterfalvi §7 (pp.25-29), mmd `04.7_pp_25_29_Coherence.mmd` (136 行), **9 結果 ((5.1)-(5.9))** ⚠️ audit 訂正 (旧 6 結果は (5.7) degree-regular, (5.8) reducible μ_k, (5.9) automorphism/μ-μ̄ 欠落; **(5.5) ×11 cite + (5.7) ×10 cite が forward 最多 hub**).
形式化先 (予定): `OddOrder/Peterfalvi/S07_Coherence.lean`.
ROADMAP 上の位置: **Phase 2b 第 3 波** (§4-§6 完成後).
役割: **Dade isometry の整合性条件**. Coherent triple の定義と基本性質. §8-§16 全面の前提.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md).

- **L3 "6 結果 (5.1)-(5.6)"** → **重大誤認: 実際 9 結果 (5.1)-(5.9)**. (5.7) degree-regular, (5.8) reducible μ_k, (5.9) automorphism/μ-μ̄ が完全欠落.
- **(5.5) と (5.7) が forward 最多 hub**: (5.5) ×11 cite (§8, §11, §12, §13, §14×4, §15×2, §16), (5.7) ×10 cite (§8, §11×3, §12×2, §13, §14×2, §16) — "all of S coherent" gateway. (5.8) ×5, (5.9) ×5. 既存「bonus/peripheral」評価は逆.
- **L10 TL;DR / L46-69 / L408-413 Coherence (5.1) 定義** → **重大誤り**: 「`τ̃(χ - 1)` virtual character の差」rider は (5.1) **に含まれない**. 正: (5.1) は extension `τ̃ : Z[S] → Z[Irr G]` の存在のみ (isometric + agrees with τ on Z[S, A]). "character difference" property は **(5.9.b) の結論** (under §4 (2.2) Hypothesis).
- **L62 コード `χ - 1`** → 正は **`χ - χ̄`** (複素共役); §7 全体で `χ - 1_L` ではなく `χ - χ̄` を扱う.
- **L46-69 candidate A code "(G → ℂ)"** → 正は `ClassFunction G` または `Z[Irr G]` codomain.
- **L329 "Inner product 既存"** → partial (`char_orthonormal` irreducible のみ; CF 全体 inner product, ZIrr inner product 不在).
- **L334 "TI-subset Coherence.Hypothesis 内定義"** → TI-subset は §4-§5 work, §7 内不要; shared `OddOrder/GroupTheory/TISubset.lean` 配置.
- **L464 "§4 Dade isometry 完成後必須"** → 実は §3 も必須 ((5.8), (5.9) が §3 (1.1), (1.5.c), (1.9) 利用).
- (5.6.1)-(5.6.3) microstructure (3-step Sibley) 正しく認識.
- **(5.7) は (5.6) の corollary ではない** (parallel proof, uses (5.4) directly).
- Encoding 推奨: **propositional predicate `IsCoherent`** (bundled structure ではなく); ただし **Hypothesis (5.2) は structure** で bundle. 既存 note の予感正しいが (5.1) def 訂正必要.
- 行数 "14-18h" → **18-22h realistic** + Wave 1a infra 別途.

## TL;DR — Coherence の正式定義, mathlib 完全新規

**Coherence は Dade isometry 完成後の "整合性チェック" 概念**. 等距写像 `τ: Z[S, A] → Z[Irr G]` が **coherent** ⟺ Z[S] 全体への isometric 拡張 `τ̃` が存在 (τ と Z[S, A] で一致). ⚠️ audit 訂正 (旧 TL;DR の rider「各 `χ ∈ S` で `τ̃(χ - 1)` が virtual character の差で書ける」は (5.1) **定義に含まれない**; 正は (5.1) は extension 存在のみ. "character difference" property は **(5.9.b) の結論** (under §4 (2.2) Hypothesis)). さらに §7 全体で扱うのは `χ - 1_L` ではなく **`χ - χ̄`** (複素共役). 

**核となる思想**: Dade isometry は部分空間 `Z[S, A]` で成立するが、Coherence は **その拡張性** を問う. 複数の coherent isometry (τ_1, τ_2, τ_3) の組が §9-§16 で矛盾導出に活用される.

**mathlib カバレッジ**: 0% (完全新規). Peterfalvi §7 の Coherence 概念は mathlib 未収載. 

**Phase 2b 形式化の方向性**: §4 (Dade isometry) で predicate-based 設計 `IsDadeIsometry τ hyp` を採択した場合、§7 Coherence は自然に `IsCoherent τ̃` predicate + extensionality lemma で表現可能.

---

## §7 全 9 結果 (抽出表) ⚠️ audit 訂正 (旧 6 結果は (5.7)-(5.9) 完全欠落)

| # | mmd 行 | 種別 | statement 概要 | 役割 | mathlib | §8-§16 被引用 |
|---|--------|------|-----------------|------|---------|---------------|
| **(5.1)** | 1-3 | **Definition** | Coherence の正式定義: isometry τ: Z[S,A] → Z[Irr G] が coherent ⟺ Z[S] 全体への **isometric 拡張 τ̃ 存在** (τ と一致). ⚠️ 旧記載の "τ̃(χ-1) character 差" rider は誤り (実は (5.9.b) 結論) | **核心** | **0** | **全面** |
| **(5.2)** | 5-11 | **Hypothesis** | 5 条件: (a) χ̄ = χ case禁止, (b) τ isometry on Z[S, L^#], (c) pairwise orthogonal, (d) (χ - χ̄)^τ が orthonormal set R(χ) に分解, (e) R(χ) ⊥ R(φ) if φ ⊥ {χ, χ̄} | **Coherence 応用の setup** | low | 6 cite (§8×2, §11, §12, §14×2) |
| **(5.3)** | 15-24 | Lemma (2 部) | (a) S ⊂ Irr L の場合 (5.2) 自動成立; (b) Hyp (4.6) (Dade 仮説) 下で induced char 系も (5.2) 満たす | Coherence 十分条件 | mid | 4+ cite (§8×2, §13, §15) |
| **(5.4)** | 31-53 | **Lemma** (2 部) | (a) ‖X‖² ≥ ‖χ‖²; (b) ‖Y‖² ≥ ‖ψ‖² なら ‖X‖² = ‖χ‖², ‖Y‖² = ‖ψ‖² かつ X ⊂ R(χ) (subset as sum) | **technical hub (内部 3 self-cite)** | low | (5.5), (5.6), (5.7) (5.6 経由せず direct) |
| **(5.5)** | 55-57 | Lemma | τ̃ 拡張下で χ^τ̃ ∈ Z[R(χ)] (χ の像が R(χ) の部分和) | **forward 最多 hub** | low | **11 cite** (§8, §11, §12, §13, §14×4, §15×2, §16) |
| **(5.6)** | 59-105 | **Main Theorem** | (5.1) 応用: 2 つの coherent set を統合. S_1 ∪ S_2 coherence 条件. (5.6.1)-(5.6.3) で 3 段階証明. 条件 (c): `2χ(1)χ_1(1) < Σ χ_i(1)²/‖χ_i‖²` が決定的 | **Coherence composition** | **low** | 3 cite (§8×2, §11) |
| **(5.7)** | (proof body) | **Theorem (degree-regular)** | S の各元 degree 一定なら S 全体 coherent. (5.4) を直接利用 (NOT (5.6) corollary) | "all of S coherent" gateway | low | **10 cite** (§8, §11×3, §12×2, §13, §14×2, §16) |
| **(5.8)** | (proof body) | Lemma (reducible μ_k) | (5.3.b) Dade 経路 + reducible μ_k decomp | (5.7) 補助 | low | 5 cite (§12×2, §13×2, §15) |
| **(5.9)** | (proof body) | Lemma (2 部) | (a) Galois auto compatibility (b) **χ-χ̄ → μ-μ̄ extension property** ((5.1) rider の正しい所在) | character Galois | low | 5 cite (§9, §14, §15, §16×2) |

---

## (5.1) Coherence の正式定義 — Phase 2b 形式化の中心

### 数学的 statement

**定義 (Peterfalvi §7 (5.1))**: `L` と `G` を有限群, `A ⊂ L`, `S ⊂ Z[Irr L]` (character set), `τ: E → Z[Irr G]` を Z-linear isometry. ここで `E` は `Z[S, A] ⊆ E ⊆ Z[Irr L]` を満たす Z-module.

**(S, A, τ) が coherent ⟺**
1. `Z[S, A] ≠ 0`
2. **∃ 拡張**: ∃ linear isometry `τ̃: Z[S] → Z[Irr G]` が τ と Z[S, A] で一致

⚠️ audit 訂正: 旧記載 3 「拡張が character 差で表現可能」は (5.1) **定義に含まれない**. これは (5.9.b) の結論 (under §4 (2.2) Hypothesis) であり、定義の rider ではない. (5.1) は extension 存在のみ.

### Lean 形式化候補: 2 つの設計

**候補 A: Predicate-based (推奨, §4 の predicate 設計と一貫)**

```lean
namespace Coherence

-- 仮説構造
structure Hypothesis (L G : Type*) [Group L] [Group G] 
    (S : Set (ClassFunction L)) (A : Set L) where
  nonzero : Z[S, A] ≠ 0
  tau : CF L (union S A) →ₗᵢ[ℂ] (G → ℂ)  -- τ: isometry on Z[S,A]
  -- (5.2) の 5 条件をここに encode

def IsCoherent (τ̃ : CF L S →ₗᵢ[ℂ] (G → ℂ)) (hyp : Hypothesis L G S A) : Prop :=
  -- ⚠️ audit 訂正: rider 削除. (5.1) は extension 存在のみ; character difference は (5.9.b) 結論
  ∀ x : Z[S, A], τ̃.comp (inclusion x) = hyp.tau x
  -- (codomain は `ClassFunction G` or `Z[Irr G]` 推奨; `(G → ℂ)` 直接は audit 訂正対象)
  -- "character difference" property は別 lemma (5.9.b):
  --   ∀ χ : S, ∃ (μ ν : Irr G), τ̃ (χ - χ.conj) = (μ : ClassFunction G) - (ν : ClassFunction G)
  -- これは χ - χ̄ (NOT χ - 1) を扱う点も注意

theorem coherenceExists (hyp : Hypothesis L G S A) :
    ∃ τ̃ : CF L S →ₗᵢ[ℂ] (G → ℂ), IsCoherent τ̃ hyp := by
  -- (5.1)-(5.6) で τ̃ 構成と同値性を証明
  sorry

end Coherence
```

**候補 B: Typeclass-based (柔軟性 ↑, 実装複雑度 ↑)**

```lean
class IsCoherentIsometry (τ̃ : CF L S →ₗᵢ[ℂ] (G → ℂ)) 
    (τ : CF L A →ₗᵢ[ℂ] (G → ℂ)) (hyp : Coherence.Hypothesis L G S A) : Prop where
  extends_tau : ∀ x : Z[S, A], τ̃ x = τ x
  char_decomp : ∀ χ, ∃ μ ν, τ̃ (χ - 1) = (μ : ClassFunction G) - ν
```

**推奨: 候補 A** — (5.1)-(5.6) の流れに直順応. Hypothesis の詳細化は (5.2)-(5.3) で段階的.

### (5.1) の数学的意義

- **Dade isometry との関係**: §4 (2.6) τ は Z[S, A] で isometry. (5.1) は「その拡張が存在できるか」を問う
- **Virtual character の差**: `τ̃(χ - 1) = μ - μ'` (μ, μ' ∈ Irr G) — character 評価での **well-definedness check**
- **Coherent triple**: (τ_1, τ_2, τ_3) が全て coherent ⇒ 整合性持つ ⇒ §9 で矛盾導出可能

---

## Coherence の Lean 形式化候補 — predicate vs. structure

§4 で採択した predicate-based 設計 `IsDadeIsometry τ hyp` との一貫性を優先.

### 設計 A: Predicate (推奨)

**長所**:
- §4 Dade isometry との interface 統一
- (5.6) で coherent triple (τ_1, τ_2, τ_3) を 3 つの predicate instance として並べられる
- Extensionality (§7 後半) が自然に predicate の conjunction 形式で表現
- mathlib LinearIsometry API と無理なく統合

**短所**:
- τ̃ の具体的構成は existence theorem に隠蔽

### 設計 B: Structure

**長所**:
- τ̃ を explicit に field として保持 (計算向け)

**短所**:
- dependent type の複雑度増加
- (5.6) で複数 structure の比較が noisy
- §8 応用 lemma で拡張が難

### 開発パターン (推奨順)

1. Hypothesis (5.2) を structure で定義
2. IsCoherent を predicate で定義
3. coherenceExists theorem で存在性保証
4. 各 lemma (5.3)-(5.6) を IsCoherent hypotheses 下で証明
5. (5.6) では「S_1 ∪ S_2 coherent」を `IsCoherent τ̃` (統合された τ̃) で主張

---

## §4 Dade isometry との関係 — coherent triple

**定義の依存関係**:

```
§4 (2.6) Dade isometry
  τ: Z[S, A] →ₗᵢ Z[Irr G]
          ↓
§7 (5.1) Coherence
  τ̃: Z[S] →ₗᵢ Z[Irr G] (extending τ)
          ↓
Coherent triple (τ_1, τ_2, τ_3)
  各 τ_i が coherent
  整合性条件を満たす
          ↓
§9 Non-existence で矛盾導出
```

**Coherent triple の具体例** (§8-§9 で多出現):
- `τ_1, τ_2, τ_3`: 異なる S_1, S_2, S_3 と A に対する Dade isometry
- 各 τ_i が coherent (∃ 拡張 τ̃_i)
- `τ̃_1, τ̃_2, τ̃_3` の compatibility 条件が満たされる
- ⇒ 指標 norm relation による矛盾

**§4 note での予測の検証**: 
§4 note の「Predicate-based 設計が自然」という予測が (5.1)-(5.6) で完全確認. (5.6.1)-(5.6.3) で複数 isometry の拡張を同時に操作するため、`IsDadeIsometry τ_i` と `IsCoherent τ̃_i` の predicate 形式が 3 つ並列で最も読みやすい.

---

## (5.2)-(5.6) 基本性質 — 詳細分析

### (5.2) Hypothesis — Coherence の応用仮説

**5 条件**:

- **(a)** `χ ∈ S ⇒ χ̄ ∈ S かつ χ̄ ≠ χ`
  - S は complex conjugation 下で閉じ、non-real character のみ (実指標禁止)
  
- **(b)** `τ : Z[S, L^#] →ₗᵢ Z[Irr G, G^#]`
  - τ は Z[S, A] より広い定義域で isometry (L^# = L - {1}, G^# = G - {1})
  - identity での評価を控除した "reduced" 指標空間
  
- **(c)** S の元が pairwise orthogonal
  - `(χ, φ) = 0` for distinct χ, φ ∈ S
  
- **(d)** `(χ - χ̄)^τ = Σ α∈R(χ) α` (R(χ) は orthonormal set)
  - character 差 χ - χ̄ が τ で orthonormal element の和に分解
  - |R(χ)| = ‖χ - χ̄‖² = 2 (非実指標なので)
  
- **(e)** `φ ⊥ {χ, χ̄} ⇒ R(φ) ⊥ R(χ)`
  - 異なる character pair に対する R 集合が直交

**Lean status (2026-05-26)**:
- `OddOrder.Peterfalvi.S07.IsCoherent.nonzero` now requires an actual nonzero
  witness `φ ∈ Z[S,A]`, matching (5.1)'s `Z[S,A] ≠ 0` condition rather than
  the vacuous existence of `0`.
- `mem_zSupportedSpan_iff`, `mem_zSpan_of_mem_zSupportedSpan`, and
  `support_subset_of_mem_zSupportedSpan` expose the two projections of the
  predicate-shaped `Z[S,A]`.
- `OddOrder.Peterfalvi.S03.conjugateDifference_eq_zero_iff_isReal` and
  `conjugateDifference_ne_zero_iff_not_isReal` identify the §7 expression
  `χ - χ̄` with the real-character obstruction.
- `OddOrder.Peterfalvi.S07.Hypothesis.conjugate_mem`,
  `not_isReal`, `ne_conj`, and `conjugateDifference_ne_zero` expose (5.2.a)
  as named, reusable API for later coherence proofs.
- `OddOrder.Peterfalvi.S07.CharacterDifferenceImage.imageSet` names the current
  two-element `R(χ)`, and `CharacterDifferenceImage.Orthogonal` plus
  `Hypothesis.difference_images_orthogonal` now encode the (5.2.e) image-set
  orthogonality condition.
- `CharacterDifferenceImage.signed_image_ne_zero` and
  `image_conjugateDifference_ne_zero` expose the immediate consequence of
  (5.2.d): the signed difference image of `χ - χ̄` is nonzero.

### (5.3) Lemma — Coherence の十分条件

**(a) 既存 character の場合**:
- S ⊂ Irr L (実指標を含まない既約 character 集合) なら (5.2) 自動成立
- Proof: Irr L の character は orthonormal, (5.2.c) 自明, (5.2.d) で ‖χ - χ̄‖² = 2 による

**(b) Dade 仮説 (4.6) 下の induced character**:
- S が `Ind_K^L θ` 型 (K < L, θ ∈ Irr K, H ⊄ Ker θ) なら (5.2) 満たす
- τ は Hypothesis (4.6) の Dade isometry の制限
- Bonus: φ ∈ S ∩ Irr L なら R(φ) ⊥ ω^σ (all ω ∈ Irr W)

**Lean 形式化**: (5.3.a) は Irr L の ortho-normality theorem, (5.3.b) は (4.6) 引用 + §3 preliminary results.

### (5.4) Lemma — Coherence extension の核技術

**主張**: Hypothesis (5.2) 下で χ ∈ S, ψ ∈ Z[S] に対し

```
(χ - ψ)^τ₁ = X - Y,  where X ∈ Z[R(χ)], Y ⊥ R(χ)
```

を満たす τ₁ が存在するとき:

- **(a)** `‖X‖² ≥ ‖χ‖²`

- **(b)** `‖Y‖² ≥ ‖ψ‖² ⇒ ‖X‖² = ‖χ‖², ‖Y‖² = ‖ψ‖², X = Σ_α∈E α (E ⊆ R(χ))`

**Proof sketch**:
- (a): Inner product 計算: `‖χ‖² = (χ - ψ, χ - χ̄) = (X - Y, Σ_α) = (X, Σ_α) ≤ ‖X‖²`
- (b): Norm additivity + (a) から等号条件 ⇒ projection が ±1 のみ

**形式化難所**: Inner product の多変量計算, Cauchy-Schwarz の等号条件.

### (5.5) Lemma — Character decomposition

**主張**: (5.2) 下で τ̃: Z[χ, χ̄] →ₗᵢ Z[Irr G] が τ|_{χ-χ̄} と compatible なら

```
χ^τ̃ = Σ_α∈E α   (E ⊆ R(χ))
```

**Proof**: (5.4) を ψ = 0 で適用.

**意義**: χ の像が R(χ) (character 差分解) の部分和 — coherence extension の key property.

### (5.6) Theorem — Coherence composition (最重要)

**主張**: (5.2) 仮説下で S_1 (n 元, real でない, 閉じている), S_2 = {χ, χ̄} (disjoint from S_1) について

- (a) S_1 が coherent
- (b) `χ_1(1) | χ(1)` (degree divisibility)
- (c) **`2χ(1)χ_1(1) < Σ_{i=1}^n χ_i(1)²/‖χ_i‖²`** (決定的条件)

⟹ **S_1 ∪ S_2 が coherent**

**証明の 3 段階** ((5.6.1)-(5.6.3)):

#### (5.6.1) 補題: Y の分解

```
(χ - aχ_1)^τ = X - Y,  X ∈ Z[R(χ)], Y ⊥ R(χ)
⟹ Y = aχ_1^τ₁ - λ Σ_i (a_i/‖χ_i‖²)χ_i^τ₁ + Z

where λ ∈ Z, Z ⊥ S_1^τ₁
```

**Key calculation**: (5.5) で χ_i^τ₁ ∈ Z[R(χ_i)], (5.2.e) で R(χ) ⊥ R(χ_i).

#### (5.6.2) 補題: Y = aχ_1^τ₁ (Z = 0, λ = 0)

**決定的**: 条件 (c) を使う. Norm bound

```
‖Y‖² ≤ a²‖χ_1‖²
```

と (5.6.1) の Y 形式を合わせ、λ² Σ_i (a_i²/‖χ_i‖²) の coefficient に対して 0 < b < 1 (from (c)) を得る. λ ∈ Z だから λ = 0.

#### (5.6.3) 定理: S_1 ∪ S_2 coherent

(5.6.2) から Y = aχ_1^τ₁ ⇒ ‖Y‖² = a²‖χ_1‖², 従って (5.4.b) の等号条件から X ∈ Z[R(χ)] orthonormal subset sum. これで χ^τ̃ = Σ α, χ̄^τ̃ = Σ (反対符号) の両立性確認. τ̃_2 (S_1 ∪ S_2 上の拡張) が isometry 保持.

**形式化注**: (5.6.2) の `0 < b < 1` 議論が最難. λ ∈ Z + quadratic 不等式の solver が必要.

---

## (5.7)-(5.9) 追加結果 — §8 への橋渡し

mmd に記載される結果 (5.7)-(5.9) も §7 の一部. 後の参照を整理:

### (5.7) Theorem

**仮説**: (5.2) + S の各元の degree χ(1) が χ に依らず一定.

**結論**: S 全体が coherent.

**Proof**: |S| = 2 base case + 帰納法 で (5.6) + degree 条件から.

**用途**: §9, §10 で degree regularity が成立する character set の coherence を直ちに結論.

### (5.8) Lemma

仮説 (5.3.b) (Dade 経由), S ∩ Irr L ≠ ∅, μ_k ∈ S (reducible) について

```
μ_k^τ̃ = ±δ_k Σ_i ω_{ik}^σ_k
```

의の場合, j, k のみが同じ degree を持つ.

**形式化**: (4.6), (5.5) 引用 + (3.7), (3.2.d) (Preliminary results).

### (5.9) Lemma (2 部)

**(a)** Automorphism compatibility: τ̃ が field automorphism u と交換可能.

**(b)** Character difference decomposition: χ ∈ Irr L, Supp(χ) ⊆ A ∪ {1} なら ∃ μ ∈ Irr G s.t. (χ - χ̄)^τ = μ - μ̄.

---

## §8 (Coherence Theorems) への橋渡し

§8 は (5.1)-(5.6) の Coherence를 活用して、より強い定理 (6.1)-(6.4) を導出.

| 関係 | (5.X) から (6.Y) | 内容 |
|------|-------------------|------|
| (6.1) Sibley's Theorem | (5.6) 応用 | Coherence composition を 3 族以上に拡張 |
| (6.2) Reynolds system | (5.2)-(5.6) | Character 족의 simultaneous coherence |
| (6.3), (6.4) | (5.1)-(5.7) | 特定 Dade 仮説下での coherence 判定 |

**§8 着手前に**: (5.1)-(5.6) の predicate/lemma が fully formalized であることを確認.

---

## §9-§16 での使用パターン

### §9: Non-existence of Certain Type

(5.1)-(5.6) の Coherence を using して Frobenius family の非存在を導出. 複数の coherent triple がチェーンを成す.

### §10-§15: Structure analysis

Type I-V の各類型で Coherence predicate が automatic に成立することを §10 で assert, §11-§15 で型別 analysis に活用.

### §16: Non-existence of G

最終矛盾: (5.6) 型の composition condition 違反を指摘.

---

## mathlib カバレッジ

| 概念 | mathlib | Phase 1 | 新規実装 |
|------|---------|---------|----------|
| Inner product (‖·‖²) | 既存 | — | — |
| Linear isometry | 既存 | — | — |
| Character orthogonality | 既存 | — | — |
| Virtual character Z[Irr] | 既存 (部分) | 補強 | subset/extension API |
| TI-subset A | 未収載 | §4, §5 参考 | Coherence.Hypothesis 内で定義 |
| **Coherence 全体** | **未収載** | — | **100% 新規** |

**§7 形式化**: mathlib 依存度 ~10% (基礎 inner product/linear isometry のみ), 本体は完全新規 (90%).

---

## Phase 2b 形式化着手順

### Stage 1: Infrastructure (1-2h)

- Coherence.Hypothesis structure 定義 ((5.2) の 5 条件)
- R(χ) orthonormal set 表現 (Set or Finset?)

### Stage 2: IsCoherent predicate (1h)

- IsCoherent τ̃ predicate 定義
- coherenceExists existence theorem statement

### Stage 3: Helper lemmas (3-4h)

- (5.2.a), (5.2.b) Hypothesis 特殊化
- (5.3) sufficient conditions (Irr L case, Dade case)

### Stage 4: Core lemmas (4-5h, **難所**)

- **(5.4)** Norm inequality (Cauchy-Schwarz 等号条件)
- **(5.5)** Character decomposition
- (5.6.1) Y decomposition (多変数 sum)
- **(5.6.2)** Norm bound から λ = 0 (quadratic 不等式)

### Stage 5: Main theorems (3-4h)

- **(5.6.3)** Coherence composition
- (5.7) degree regularity case
- (5.8), (5.9) additional results

### Stage 6: Verification (1-2h)

- coherenceExists の fullness 確認
- §8 §9 への interface test

**合計**: **14-18 時間**, 行数 ~350-400 行.

---

## Lean 形式化設計 — 詳細

### Coherence.Hypothesis 設計

```lean
namespace Coherence

structure Hypothesis (L G : Type*) [Group L] [Group G]
    (S : Set (IrrCharacter L)) (A : Set L) where
  -- (5.2.a) χ̄ ≠ χ, χ̄ ∈ S
  conj_closed : ∀ χ : S, χ.val.conj ∈ S
  conj_ne : ∀ χ : S, χ.val.conj ≠ χ.val
  
  -- (5.2.b) τ: Z[S, L^#] →ₗᵢ Z[Irr G, G^#]
  tau : CF L S →ₗᵢ[ℂ] (G → ℂ)  -- restrict to Z[S, A] ⊆ Z[S, L^#]
  tau_support : ∀ α : CF L A, tau (inclusion α) = ...
  
  -- (5.2.c) pairwise orthogonal
  pairwise_orthogonal : ∀ χ φ : S, χ ≠ φ → (χ.val, φ.val) = 0
  
  -- (5.2.d)-(e) R(χ) decomposition + orthogonality
  R : ∀ χ : S, Set (IrrCharacter G)
  R_decomp : ∀ χ : S, (χ.val - χ.val.conj)^τ = ∑ α : R χ, (α.val : ClassFunction G)
  R_norm : ∀ χ : S, ∑ α : R χ, 1 = ‖χ.val - χ.val.conj‖²
  R_orthogonal : ∀ χ φ : S, (φ.val, χ.val + χ.val.conj) = 0 → Disjoint (R χ) (R φ)

def IsCoherent (τ̃ : CF L S →ₗᵢ[ℂ] (G → ℂ)) (hyp : Hypothesis L G S A) : Prop :=
  -- (1) τ̃ extends tau on Z[S, A]
  (∀ x : Z[S, A], τ̃ x = hyp.tau x) ∧
  -- (2) ∀ χ, τ̃(χ - 1) is character difference
  (∀ χ : S, ∃ μ ν : IrrCharacter G, (τ̃ (χ.val : CF L) : ClassFunction G) - (1 : ClassFunction G) = 
                                      (μ.val : ClassFunction G) - (ν.val : ClassFunction G))

end Coherence
```

### Core lemmas の strategy

**(5.4) Norm inequality**:

```lean
lemma norm_bound_a (hyp : Hypothesis L G S A) {χ : S} {ψ : CF L S}
    {τ₁ : CF L S →ₗᵢ[ℂ] (G → ℂ)} {X Y : ClassFunction G}
    (hdecomp : (χ.val - ψ)^τ₁ = X - Y)
    (hX : X ∈ Submodule.span ℂ (R hyp χ))
    (hY : Y ⊥ (Submodule.span ℂ (R hyp χ) : Set (ClassFunction G))) :
    ‖χ.val‖² ≤ ‖X‖² := by
  -- Inner product trick: ‖χ‖² = (χ - ψ, χ - χ̄) ≤ (X, Σ_α) ≤ ‖X‖²
  sorry
```

**(5.6.2) Quadratic bound**:

```lean
lemma norm_bound_determines_zero (hyp : Hypothesis L G S A) {χ χ₁ : S}
    {a a₁ : ℕ} (h_div : χ₁(1) ∣ χ(1)) {λ : ℤ} (h_bound : ...)
    (h_cond_c : 2 * χ(1) * χ₁(1) < ∑ i, χ_i(1)² / ‖χ_i‖²) :
    λ = 0 := by
  -- 0 < b < 1 から λ ∈ ℤ ⇒ λ = 0
  sorry
```

---

## CLAUDE.md `feedback_no_mathlib_wrapper` との整合

§4 note で「Dade isometry は完全新規, 純粋リネーム懸念なし」と記述したが、§7 Coherence はさらに顕著:

- Coherence は **mathlib 完全未収載**
- Peterfalvi 独自概念で、他の形式化 (Lean 3 Feit-Thompson など) でも coherence 型が見当たらない
- predicate-based 設計により、「isometry τ̃ の properties」を記述 — mathlib `LinearIsometry` ラッパー不要

**結論**: Coherence は `feedback_no_mathlib_wrapper` 原則に完全準拠. 純粋新規実装として設計自由度最大.

---

## 未解決 / TODO

1. **R(χ) の Lean 表現**: Set か Finset か? Orthonormal set として index すべき? (5.4)-(5.6) で多出現するため, design choice は formalization の読みやすさを大きく左右.

2. **(5.6.2) λ = 0 の quadratic 불등식 solver**: `0 < b < 1` + `λ² ≤ bλ` から `λ ∈ ℤ ⇒ λ = 0`. これを tactic で組むか, lemma library 化か.

3. **§4 Dade isometry 完成日程**: §7 着手は §4 full formalization (특히 (2.6) inclusion-exclusion) 완료后 필수. Phase 2b timeline 확인.

4. **§8-§16 との interface design**: (5.6) Coherence composition を §8 で多重 apply する構造. Stage 6 (verification) で §8 preview lemma 작성이 필수.

5. **Hypothesis (5.2) の encode strategy**: 5 조건을 하나의 structure에 넣을지, "Hyp (5.2)" instance를 별도로 정의할지. Coherence.Hypothesis의 universe level 및 decidability.

6. **§7-(5.1)-(5.9) の mmd との gap 확認**: mmd 마지막 (L136) 이후 추가 내용이 있는지 (예: mmd file 끝 여부).

---

## 크로스참조

| 문서 | 내용 | 연관성 |
|------|------|--------|
| `s04_dade_isometry.md` | Dade isometry 정식 정의 | §7의 τ는 §4 (2.6) τ의 확장 |
| `s03_preliminary_character.md` | Character orthogonality, virtual char | (5.2)-(5.6)의 기초 |
| `s09_nonexistence_certain.md` | Non-existence Theorem C | (5.1)-(5.6) Coherence 활용 |
| `_overview.md` | Peterfalvi 전체 조감 | Phase 2b roadmap |
| `../bg/_overview.md` | BG App.C (character-free proof) | §9와 병렬 증명 경로 |

---

*작성: 2026-05-22. 출처: Peterfalvi `references/peterfalvi/04.7_pp_25_29_Coherence.mmd` (136 행), `references/peterfalvi/04.4_pp_10_14_*.mmd` (§4 Dade 참고), `notes/peterfalvi/_overview.md` (전체 구조), `notes/peterfalvi/s04_dade_isometry.md` (Dade 설계).*
