> ⚠️ **2026-06-17 STATUS 訂正**: (5.6)/(6.8.3)/case-B capstone の現状は [`s08_6_8_3_gap_resolution.md`](s08_6_8_3_gap_resolution.md) が正本。
> 本ロードマップ内（特に pass 3/4 の「main (5.6) 未着地 / 新 brick 必要 / IsCoherent.extension_isometry が唯一 gap」）は **stale**:
> norm-weighted (5.6) エンジン (`S08_CoherenceWeighted`: `coherentDegreeSqNormBound_of_not_coherentW`/`xChainCoherentW`) + (5.4)/(5.5)/(5.6.2)/(5.6.3) 計算は**既に sorry-free 着地済**。

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

## Lean status: (5.2.d) gateway + (5.4)/(5.5) norm 不等式 (2026-05-30, issue 1001, Round-9 Track B)

`OddOrder/Peterfalvi/S07_Coherence.lean` に (5.2.d) の一般 gateway + (5.4)/(5.5) を sorry-free 実装.

- **`OrthonormalCharacterImageFamily τ χ`** = (5.2.d) の R(χ): `imageSet : Finset (ClassFunction G ℂ)`
  (orthonormal subset of ℤ[Irr G]), `mem_ZIrr`, `orthonormal` (⟨α,β⟩=δ_{α,β}),
  `image_eq` ((χ-χ̄)^τ=∑_{α∈R(χ)}α). 既存 2 元 `CharacterDifferenceImage` は特殊例
  (R(χ)={ε·μ,-ε·ν}); 一般 gateway が真に subsume することを
  `CharacterDifferenceImage.toOrthonormalImage` で証明 (非空性 = scaffolding でない証拠).
  `Orthogonal` predicate = (5.2.e) disjoint-pair.
- **`CharacterPsiDecomposition τ χ ψ`** = (5.4) setup を bundle: imageFamily R(χ), 補助
  isometry τ₁ (χ-χ̄ で τ と一致), 分解 (χ-ψ)^{τ₁}=X-Y, X∈ℤ[R(χ)] (整数係数 coeff),
  Y⊥R(χ), 直交 (χ,ψ)=(χ̄,ψ)=(χ,χ̄)=0.
- **(5.4.a)** `inner_self_chi_re_le_inner_self_X`: (⟨χ,χ⟩).re ≤ (⟨X,X⟩).re. keystone は
  `inner_self_chi_eq_sum_coeff` (‖χ‖²=⟨χ-ψ,χ-χ̄⟩=⟨X-Y,∑α⟩=⟨X,∑α⟩=∑coeff).
- **(5.4.b)** `norm_eq_and_X_eq_sum_of_norm_Y_ge`: ‖Y‖²≥‖ψ‖² ⟹ ‖X‖²=‖χ‖², ‖Y‖²=‖ψ‖²,
  X=∑_{α∈E}α (E=filter(coeff=1)⊆R(χ)) **かつ `|E|=‖χ‖²`** (`(E.card:ℂ)=⟨χ,χ⟩`).
  total-norm Pythagoras + 整数 CS tightness. `|E|=‖χ‖²` は coeff∈{0,1} から
  ∑coeff=|E| で keystone identity に接続; (5.6.3) が `‖χ̄^{τ₂}‖²=|R(χ)|-|E|` で消費する形.
- **(5.5)** `eq_sum_of_psi_eq_zero`: ψ=0 特殊化. `‖ψ‖²=⟨0,0⟩=0≤‖Y‖²` が正半定値性で自動成立し
  (5.4.b) を起動; norm 等号 `‖Y‖²=0` から正定値性で **Y=0**, よって χ^{τ₁}=(χ-0)^{τ₁}=X=∑_{α∈E}α.
- norm 比較は repo 慣用の `(⟨·,·⟩).re` (S09 と整合).
- **infra (ZIrrFourier)**: 整数 CS (int_le_sq / int_eq_sq_iff / finset_sum_le_sum_sq /
  finset_sum_eq_sum_sq_iff), 任意 orthonormal Finset 族の Parseval
  (inner_orthonormalSum_eq_coeff / inner_self_orthonormalSum_eq_sum_sq /
  inner_orthonormalSum_sum_eq_sum_coeff), inner_conj_symm (⟨ψ,φ⟩=conj⟨φ,ψ⟩),
  **正(半)定値性** (inner_self_eq_realCast: ⟨φ,φ⟩=(|G|:ℝ)⁻¹·∑‖φ(g)‖² /
  inner_self_re_nonneg: 0≤(⟨φ,φ⟩).re / eq_zero_of_inner_self_re_eq_zero:
  (⟨φ,φ⟩).re=0→φ=0; ℂ 全体で一般, ZIrr 不要).
- AxiomsCheck 4 件登録 (all in allowlist): toOrthonormalImage / (5.4.a) / (5.4.b) / (5.5).
- **残 (別 issue)**: (5.6)/(5.7) は本 (5.4)/(5.5) gateway を消費する coherence 統合.
  (5.6.1) Y 分解, (5.6.2) `0<b<1⇒λ=0` quadratic forcing が未着手の主難所.
  `CharacterPsiDecomposition` の data 入力 (imageFamily/tau1/coeff) は実適用時に Dade
  文脈から構成要 (gateway は statement-level の道具).

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
- `zero_mem_zSupportedSpan`, `add_mem_zSupportedSpan`,
  `neg_mem_zSupportedSpan`, `sub_mem_zSupportedSpan`,
  `zSupportedSpan_mono_left`, and `zSupportedSpan_mono_right` provide the
  basic closure and monotonicity API for manipulating `Z[S,A]`.
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
- `CharacterDifferenceImage.difference`, `signedDifference`,
  `image_eq_signedDifference`, `difference_inner_self`,
  `signedDifference_inner_self`, `image_conjugateDifference_inner_self`,
  `Orthogonal.difference_inner_eq_zero`,
  `Orthogonal.signedDifference_inner_eq_zero`, and
  `Orthogonal.image_conjugateDifference_inner_eq_zero` now expose the norm
  `2` and orthogonal-image inner product `0` calculations for the two-element
  `R(χ)` interface without unfolding the underlying pair of irreducibles.
- `Hypothesis.difference_image_ne_zero` and
  `signed_difference_image_ne_zero` lift that nonzero image API to the §7
  hypothesis carrier, avoiding repeated unpacking of `difference_image hχ`.
- `Hypothesis.difference_image_inner_self` and
  `difference_images_inner_eq_zero_of_inner_pair` lift the same norm and
  orthogonality calculations to the §7 hypothesis carrier.
- `SignedIrreducibleDifferenceFamily.signedDifference_inner_self_of_ne_zero` and
  `signedDifference_inner_of_ne_zero_of_ne` provide the target-side norm/inner
  values needed when §7 reduces image differences to the shared §3 (1.4)
  isometry-difference structure.
- `IsCoherent.extension_inner_eq` exposes the inner-product preservation of
  the extension map, while `IsCoherent.inner_eq_on_supported` transfers it
  back to the original `τ` on `Z[S,A]` using `extends_on_supported`.
- `Hypothesis.tau_inner_eq` names the inner-product preservation field carried
  by the §7 hypothesis, so downstream files do not unpack `tau_isometry`.

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

## 형식화 진행 (Track A — 整數性/次数비 API)

### (2026-05-30) (5.6)(b) degree-ratio integrality landing — `exists_pos_natDegreeRatio_of_dvd`

(5.6) 증명 첫 줄 "Set `χ(1) = aχ₁(1)`"의 `a ∈ ℕ` 도출을 honest leaf로 형식화.
**위치**: `OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean` (`characterDegree` namespace,
`exists_natDegree_characterDegree_dvd_card` 직후). AxiomsCheck 등록 (3 axioms, all allowlist; sorry-free).

```
theorem exists_pos_natDegreeRatio_of_dvd [Finite G]
    (χ χ₁ : IrreducibleCharacter G)
    (hdvd : ∀ d d₁ : ℕ, (χ : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ) → d₁ ∣ d) :
    ∃ a : ℕ, 0 < a ∧ characterDegree (χ : ClassFunction G ℂ) =
      (a : ℂ) * characterDegree (χ₁ : ClassFunction G ℂ)
```

**중요 (honest-statement 訂正)**: 본 라운드 decomposition roadmap의 첫 leaf 후보 A3은
"χ(1) = a·χ₁(1) for some `a ∈ ℚ` ⟹ `a ∈ ℤ`"였으나 **이는 수학적으로 거짓** — 두 양의 정수 비가
정수일 필요는 없음 (degree 2, 3 → 2/3). Peterfalvi (5.6) 가설 **(b) `χ₁(1) ∣ χ(1)`** 가 바로 이
divisibility datum이며 (mmd 04.7, L60-67: "Set χ(1) = aχ₁(1) … this is compatible … if aᵢ ∈ **N**"),
`a`는 그 가설로 보장되는 **양의 자연수 몫**. 따라서 divisibility를 명시적 가설로 받는 형태가 honest이고,
roadmap의 무조건 ℚ→ℤ 형태는 채택하지 않음 (scaffolding/거짓 statement 회피).

증명: `χ.isIrreducible.exists_natDegree_charValue_one_dvd_card`로 두 양의 nat 차수 `d, d₁` 추출 →
`hdvd d d₁` 로 `d = d₁ * a` → `d > 0`에서 `a > 0` → `Nat.cast_mul` + `ring`.

**이후 leaf (미착수)**: (5.6.1) Y 분해, (5.6.2) `0 < b < 1 ⇒ λ = 0` quadratic forcing
(`a` 와 `a_i` 가 본 lemma 出力), (5.4.a/b) Cauchy–Schwarz. 모두 R(χ) 一般 orthonormal lattice (B1) 선행 필요.

### (2026-05-31) (5.6.2) integer-forcing + opening norm bound landing (S07)

(5.6) coherence-union 정리를 향한 **family-free honest sub-lemma 2개**를 `S07_Coherence.lean`에
landing (sorry/axiom 無). 둘 다 landed (5.4)/(5.5) API 위에 직접 구축, scaffolding 無.

1. **`int_eq_zero_of_sq_mul_le_of_two_mul_lt`** (`S07_Coherence.lean`, namespace `S07`) — (5.6.2)의
   integer-forcing core. division-free 형태: `0 < D` (rational), `0 ≤ z`, `0 ≤ a`,
   **strict** `2a < D` (텍스트의 `b < 1`, `b = 2a/D`), `λ : ℤ`에 대해
   `λ²·D - 2λa + z ≤ 0` ⟹ `λ = 0`. 부호별 trichotomy: `λ < 0`이면 `2λa ≤ 0 < λ²D` 모순;
   `λ > 0`이면 `λ` 약분해 `λ·D ≤ 2a < D` + `λ ≥ 1` 모순. slack `z = ‖Z‖²`를 들고 있어 caller가
   먼저 떨어뜨릴 필요 없음. **`λ` glyph는 식별자 불가** (lambda 예약) → 변수 `lam`, 가설 `hlamR`/`hlam1`.
2. **`CharacterPsiDecomposition.inner_self_Y_re_le_inner_self_psi`** — (5.6.2) 첫 줄 norm bound
   `‖Y‖² ≤ ‖ψ‖²` (적용 시 `ψ = a·χ₁` → `‖Y‖² ≤ a²‖χ₁‖²`). landed `inner_self_chi_add_psi_eq`
   (`‖χ‖²+‖ψ‖² = ‖X‖²+‖Y‖²`) + (5.4.a) `inner_self_chi_re_le_inner_self_X` (`‖χ‖² ≤ ‖X‖²`)에서 `linarith`로 즉시.

**미착수 잔여 (정밀)**:
- **(5.6.1) Y 분해** (`Y = a·χ₁^{τ₁} - λ·∑ᵢ(aᵢ/‖χᵢ‖²)·χᵢ^{τ₁} + Z`, `λ ∈ ℤ`): family
  `{χᵢ}` + degree ratio `aᵢ` + norm `‖χᵢ‖²` + cross-difference 직교
  `⟨(χ-aχ₁)^τ, (χᵢ-aᵢχ₁)^τ⟩ = a·aᵢ‖χ₁‖²`를 담는 **새 ambient bundle**가 필요.
  `CharacterPsiDecomposition`에는 family 데이터가 없음. (5.6.1) 결론을 가설로 패키징하면 scaffolding이라 금지 →
  bundle을 실제 구성하고 inner-product 관계를 §5.2 직교성에서 유도해야 함 (~150-250 LOC).
- **(5.6.3)/main `IsCoherent (S₁∪{χ,χ̄})`의 진짜 blocker**: `τ₂` extension은
  `IntegralCharacterMap L G` (전체 `ClassFunction L ℂ` 위 ℤ-linear) + **global** `IsIntegralIsometry`
  (`∀ φ ψ, ⟨τφ,τψ⟩=⟨φ,ψ⟩`)를 요구. 기저 `{χᵢ,χ,χ̄}` 위에서 정의해 ℤ-linear 확장해도 **전역 등거리**는
  보장 안 됨 (lattice 등거리 ≪ 전역 등거리). repo/mathlib에 orthonormal-basis → 전역 등거리 확장
  primitive **없음** (검색 확인: `grep LinearIsometry/extend` 무수확; `IsCoherent` 유일한 Type-level
  생성자는 `S08.sibleySetup_is_coherent`의 sorry). 이 확장 생성자가 §5.6 main의 단일 미착수 장애물.

### (2026-05-31, pass 2) (5.6.2) capstone end-to-end + (5.6.3) conjugate-image computations

pass 1의 sub-lemma 위에 (5.6.2)를 **완전히 닫고** (5.6.3)의 isometry 검증 계산을 landing
(전부 sorry/axiom 無, AxiomsCheck 등록, full `lake build OddOrder` 緑 3351 jobs).

**ZIrrFourier 일반 helper (Hilbert-space, 재사용)**:
- `inner_self_orthogonalSum_add_re` — **직교족 + 직교 잔차의 Pythagoras**:
  `‖(∑ᵢ cᵢ•vᵢ) + Z‖²(.re) = ∑ᵢ cᵢ²·mᵢ + ‖Z‖²(.re)` (gram `⟨vᵢ,vⱼ⟩ = δᵢⱼ·mᵢ` 실수, `Z ⊥ vᵢ`).
- `inner_self_sum_orthonormal_eq_card` — orthonormal 부분합 `‖∑_{a∈s} a‖² = |s|`.
- `inner_sum_orthonormal_eq_zero_of_disjoint` — disjoint 부분합 cross term `⟨∑_E, ∑_F⟩ = 0`.

**S07 (5.6.2)**:
- `CharacterPsiDecomposition.sum_sq_mul_add_normSq_Z_le` — (5.6.2) 기하 절반:
  `Y = (∑ᵢ cᵢ•vᵢ) + Z` (직교족) ⟹ `∑ᵢ cᵢ²·mᵢ + ‖Z‖² ≤ ‖ψ‖²`. Pythagoras + pass-1 opening bound.
- **`CharacterPsiDecomposition.lambda_eq_zero_and_Z_eq_zero`** — **(5.6.2) capstone** `λ=0 ∧ Z=0`.
  기하 절반 ∘ 대수전개 `∑(a·[i=i₁]-λrᵢ)²mᵢ = a²m₁ - 2aλ + λ²D` (`Finset.sum_ite_eq'` split + `ring`)
  ∘ pass-1 정수 forcing `int_eq_zero_of_sq_mul_le_of_two_mul_lt` (ℝ로 transcribe) ∘ 정정치성
  `eq_zero_of_inner_self_re_eq_zero`. 입력 = (5.6.1) 분해 데이터 + `‖ψ‖²=a²m₁` (`ψ=a·χ₁`) +
  `r₁·m₁=1` (`a₁=1`) + `2a<D` (가설 (c)) — 모두 §7 Hypothesis + (5.5)에서 **구성가능** (hoisting 아님).

**S07 (5.6.3) conjugate-image** (전부 (5.4.b)/(5.5)의 `E` 데이터에서, `τ₂` 구성 없이):
- `CharacterPsiDecomposition.conjImage_eq_neg_sum_sdiff` — `χ̄^{τ₂} = X - (χ-χ̄)^τ = -∑_{α∈R(χ)-E} α`
  (`Finset.sum_sdiff` telescoping).
- `inner_self_conjImage_eq_card_sdiff` — `‖χ̄^{τ₂}‖² = |R(χ)| - |E|` (= `‖χ-χ̄‖²-‖χ‖² = ‖χ̄‖²`).
- `inner_X_conjImage_eq_zero` — `⟨χ^{τ₂}, χ̄^{τ₂}⟩ = 0` (disjoint `E`, `R(χ)-E` cross term).

이 세 계산이 (5.6.3) `τ₂`의 `extension_isometry` 필드를 직접 공급 (`χ^{τ₂}`/`χ̄^{τ₂}` norm 보존
+ 상호 직교). **남은 단일 장애물은 변함없음**: (5.6.1) ambient bundle 구성 (~150-250 LOC) +
`τ₂`의 **전역** `IsIntegralIsometry` 확장 생성자 (orthonormal-basis → 전역 등거리 primitive,
repo/mathlib 부재). main `IsCoherent(S₁∪{χ,χ̄})`는 이 둘이 갖춰지면 위 landed 계산으로 즉시 조립 가능.

### (2026-05-31, pass 3) (5.6.3) re-targeting keystone + (5.6.1) family bundle landed

`S07_Coherence.lean` `namespace IntegralCharacterMap` / `CharacterFamilyBundle` (sorry/axiom 無,
AxiomsCheck 2 건 각 3 axiom 全 allowlist, full `lake build OddOrder` 緑 3351 jobs):

- **`retarget`** (구성): `τ₁ ∘ₗ orthoResidualMap χ χ̄ + (innerLeftℤ χ).smulRight X +
  (innerLeftℤ χ̄).smulRight X̄`. 곧 `τ₂ φ = τ₁ φ⊥ + ⟨φ,χ⟩·X + ⟨φ,χ̄⟩·X̄`,
  `φ⊥ = φ − ⟨φ,χ⟩χ − ⟨φ,χ̄⟩χ̄`. **결정적 미묘점**: 잔차를 `τ₁` *전에* 취한다 — `τ₁`은 ℤ-선형뿐이라
  복소 Fourier 계수를 통과시킬 수 없다. naive `τ₁ + ⟨·,χ⟩·(X−τ₁χ) + …` 형은 `τ₁(c•χ)≠c•τ₁χ`
  (c∈ℂ) 때문에 틀린다 (이번 라운드 실측 확인). `innerLeftℤ`/`orthoResidualMap` 도 ℤ-선형으로 구성.
- 일치 보조정리 (orthonormal pair 가정): `retarget_apply_left` (χ↦X), `retarget_apply_right`
  (χ̄↦X̄), `retarget_eq_of_orthogonal` ({χ,χ̄}^⊥ 위 τ₁ 일치). `inner_orthoResidualMap_left/right`
  (φ⊥ ⊥ {χ,χ̄}).
- **`retarget_isIntegralIsometry`** (CRUX): `τ₁` 전역 등거리 + {χ,χ̄}/{X,X̄} 동일 gram orthonormal
  + `∀ξ⊥{χ,χ̄}, ⟨τ₁ξ,X⟩=⟨τ₁ξ,X̄⟩=0` ⟹ `IsIntegralIsometry (retarget …)`. 증명: `inner_block_expand`
  (sesquilinear block normal form, 일반 `W`) 을 source/image 양변에 적용 → 둘 다
  `⟨φ⊥,ψ⊥⟩ + s·conj s' + t·conj t'` 로 환원, `τ₁` 등거리로 `⟨φ⊥,ψ⊥⟩=⟨τ₁φ⊥,τ₁ψ⊥⟩`.
- **`CharacterFamilyBundle`** (5.6.1, posit 無): family `{χᵢ}_{i∈s}⊆S₁` + ratio aᵢ∈ℕ (a₁=1) +
  degree scaling + `χ⊥S₁` + `{χᵢ}` pairwise 직교. **`crossDifference_inner`** (정리):
  `⟨χ−aχ₁, χᵢ−aᵢχ₁⟩ = a·aᵢ·‖χ₁‖²` (i≠i₁) 를 `χ⊥S₁`+pairwise 에서 도출 (비-posit).

**정밀 잔존 (main (5.6) 여전히 미착지, 새 brick 필요)**: repo `IsIntegralIsometry` 는 **전역**
(∀φ,ψ) 인데 Peterfalvi (5.6.3) `τ₂` 등거리는 격자 `ℤ[S₁∪{χ,χ̄}]` 위에서만 검증된다. keystone 의
가설 `∀ξ⊥{χ,χ̄}, ⟨τ₁ξ,X⟩=0` 은 `X∈ℤ[R(χ)]` 가 일반적으로 `span{τ₁χ,τ₁χ̄}` 밖이므로 주어진
S₁-coherence 확장 τ₁ (span 밖 값 비제어) 에 대해 **충족 불가**. ⟹ main (5.6) 은 추가 brick =
**"부분공간 등거리 → 전역 등거리 확장"** (유한차원 ℂ class-function 공간 Witt/Gram–Schmidt 확장)
또는 격자-상대 `IsCoherent` 재정식화 필요. keystone 자체는 R(χ)⊆span{τ₁χ,τ₁χ̄} (2-원소 (5.2.d)
base 등) 에서 직접 적용 가능하며 (5.6) 의 **대수적 심장**.

### (2026-05-31, pass 4) 격자-상대 keystone `retarget_inner_eq_on` + 大域 assembly bridge + span infra

`S07_Coherence.lean` (sorry/axiom 無, AxiomsCheck 7 건 신규 각 3 axiom 全 allowlist, full
`lake build OddOrder` 緑 3351 jobs; commits 63f7437 / e5ac588 / fede79c). Pass 3 의 정밀 잔존
("전역 vs 격자" + "格子-相対 재정식화 필요")의 **격자 측을 해결**.

- **`retarget_inner_eq_on`** (격자-相対 keystone, 진짜 충족가능형): 전역 keystone
  `retarget_isIntegralIsometry` 의 가설 `∀ξ⊥{χ,χ̄}, ⟨τ₁ξ,X⟩=0` 은 (5.6) 일반위치에서 충족불가
  (X=μ∉span{τ₁χ,τ₁χ̄}; τ₁=hS₁.extension 은 χ−χ̄ 위에서 τ 와 무관 — χ∉S₁). 대신 **ℂ-부분가군 `M`**
  ({χ,χ̄}-Gram–Schmidt 잔차 닫힘, χ,χ̄∈M) 위에서만 `⟨·,·⟩` 보존, `X,X̄⊥τ₁ξ` 도 `ξ∈M⊥{χ,χ̄}`
  에 한해 요구. `M=span_ℂ(S₁∪{χ,χ̄})` 면 `φ∈M` 잔차는 `span_ℂ S₁` 에 들어가므로 가설은 정확히 honest
  한 (5.5)+(5.2.e) `X,X̄⊥S₁^{τ₁}`. **이것이 (5.6.3) 격자 등거리 `Z[S₁∪{χ,χ̄}]→Z[Irr G]` 로,
  §7 data 가 실제 공급하는 형태.** 증명은 전역판과 동일 `inner_block_expand`, 단 잔차의 ∈M 을
  submodule 닫힘으로.
- **`retarget_isCoherent`** (大域 assembly, `noncomputable def`): `hS₁:IsCoherent τ S₁ A` (τ₁:=
  hS₁.extension) + orthonormal {χ,χ̄}/{X,X̄} + `X̄=X−(χ−χ̄)^τ` + (5.5)+(5.2.e) 전역 orthogonality
  + (5.6.2) image eq `(χ−a·χ₁)^τ=X−a·χ₁^{τ₁}` (a:ℕ) + (5.1)-generation `hgen` ⟹
  `IsCoherent τ (S₁∪{χ,χ̄}) A`. `τ₂:=retarget …` **구성** (posit 無). 등거리는 전역 keystone,
  `extends_on_supported` 는 세 차이생성원 `{χ−χ̄,χ−a·χ₁}∪Z[S₁,L^#]` 위 일치 + span-induction.
  ⚠️ **여전히 전역 keystone 가설 의존** ⟹ (5.6) 일반위치 비충족 (X,X̄∈span{τ₁χ,τ₁χ̄} 특수상황,
  예: (5.2.d) 2-원소 base, 에서만 적용가능). 정직한 정리지만 main (5.6) 일반형은 아님.
- **재사용 infra** (전부 sorry/axiom 無): `eq_on_zSpan_of_eq_on` (두 ℤ-character map 이 생성집합
  위 일치 ⟹ ℤ-span 위 일치, span_induction), `inner_eq_zero_of_mem_zSpan` (η⊥T ⟹ η⊥ℤ[T]),
  `retarget_eq_on_zSpan_of_orthogonal` (T⊥{χ,χ̄} 의 ℤ-span 위 retarget=τ₁),
  `inner_eq_zero_of_eq_intCast_sum` (X=∑c(α)•α + η⊥각 α ⟹ η⊥X; `X_eq` → hX_ortho 다리).

**정밀 잔존 (단 하나, 정의적 결정)**: main (5.6) 의 유일 gap 은 `IsCoherent.extension_isometry`
필드가 **전역** `IsIntegralIsometry` (∀φ,ψ over all CF(L)) 를 요구한다는 점. 격자 등거리
`retarget_inner_eq_on` 은 이미 구성됨. 두 경로:
  1. **`IsCoherent` 약화 (권장, 수학적으로 정확)**: `extension_isometry` 를 격자-相対
     (`Z[S]` 위 등거리) 로 재정의. 근거: (a) Peterfalvi (5.6.3) 자체가 격자 등거리만 주장,
     (b) **하류 소비자 `S08 IndChainDecomposition.ofIsCoherent` 는 `extension_inner_eq` 를 ζt∈S
     (격자원) 에만 적용** — 전역성 전혀 미사용 (S08_CoherenceTheorems.lean:251-253 확인),
     (c) 전역 등거리는 dim CF(L)≤dim CF(G) 필요 — FT 에서 일반적으로 보장 안 됨 ⟹ 현 정의는
     일반적으로 **충족불가능**일 수도. 이 약화 후 `retarget_inner_eq_on` + 본 bridge infra 가
     즉시 main (5.6) 완성. **단 shared `IsCoherent`/S08 영향 ⟹ main 합류시 정의 결정 필요
     (worktree 단독 변경 회피).**
  2. Witt/유니터리 부분공간-등거리 확장 (격자 등거리 → 전역): dim 조건 성립시에만 존재,
     bespoke `ClassFunction.inner` 용 mathlib 부재 ⟹ multi-day brick. 경로 1 이 우월.

### (2026-05-31, Round 23 PASS 1) (5.6.3) 射영동정 `Da.X=D₀.X` + (5.5)+(5.2.e) image-side orthogonality 構成

`retarget_isCoherent_of_decompositions` の 3 opaque 仮설 (`hX_eq`, `hX_ortho`, `hXbar_ortho`) 을 genuine
한 (5.5)/(5.6.2)/(5.2.e) data 로부터 *構成* (posit 無, sorry/axiom 無, AxiomsCheck 4 신규 全 allowlist;
`lake build OddOrder` 緑 3360; commits 32a8c37 / e340467). 상세는 `notes/peterfalvi/s08_coherence_theorems.md`
Round 23 PASS 1 항목.

- **`X_eq_tau1_chi_of_Y_eq`** : (5.6.2) collapse `Da.Y = a·χ₁^{τ₁}` 로부터 `Da.X = χ^{τ₁}` (tau1 의
  `χ−a·χ₁` 상 선형성, `a:ℕ` map_nsmul, `sub_left_inj` 상쇄). (5.6.3) "X 가 ψ 에 무관" 의 핵.
- **`X_eq_of_tau1_eq_on_chi`** : `Da.X=Da.tau1 χ` + τ₁-agreement `Da.tau1 χ=D₀.tau1 χ` (honest) +
  `D₀.tau1 χ=D₀.X` ((5.5)) ⟹ `Da.X=D₀.X`. posited `hX_eq` 를 더 원시적 `htau1_chi` 로 치환 후 내부 도출.
- **`inner_X_eq_zero_of_orthogonal_imageSet`** / **`inner_conjImage_eq_zero_of_orthogonal_imageSet`** :
  per-element `∀α∈R(χ), ⟨η,α⟩=0` ⟹ `⟨η,X⟩=0` / `⟨η,X̄⟩=0` (X, X̄=X−(χ−χ̄)^τ 둘 다 ℤ[R(χ)]).
  posited sum-level `hX_ortho`/`hXbar_ortho` 를 단일 per-element `hperElem` 로 치환 후 내부 도출.

**잔존**: `retarget_isCoherent_of_decompositions` 의 posited-conclusion 仮설은 `hY : Da.Y=a·Da.tau1 χ₁`
((5.6.2) collapse, (5.6.1) form 존재 필요) 뿐. + 각 step `D₀`/`Da` 생산 ((5.4) τ₁ 구성) 과 `hperElem`
의 family `{R(χᵢ)}` 결합. 이들이 hstep 완전 방전의 다음 패스.

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
