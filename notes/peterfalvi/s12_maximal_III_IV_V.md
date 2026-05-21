# Peterfalvi §12: Maximal Subgroups of Types III, IV and V — mini-roadmap

**スコープ**: Peterfalvi §12 (pp.58-63, mmd `04.12_pp_58_63_Maximal_Subgroups_of_Types_III_IV_and_V.mmd` 136 行).
**結果数**: (10.1)-(10.7) 計 7 個の番号付き結果 + (10.8)-(10.11) 関連 4 個の補助定理 = 計 11 個.
**形式化先** (予定): `OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean`
**ROADMAP 上の位置**: Phase 2b 第 6 波 (§11 完成必須).
**役割**: Type III/IV/V maximal subgroup の混合分析。特に (10.7) [S,S] が Frobenius となる条件を確立し、§13 (Type III/IV の精密化) と §14 (Type I) への分岐点を構成する.

---

## TL;DR

§12 は Peterfalvi の **最初の型分類応用章** で、§11 で確立した Type II/III/IV の詳細な指標構造を **Type III/IV/V の 3 型に拡張** し、Dade isometry + coherence 理論を本格的に適用する. 最重要結果は:

1. **(10.1) Hypothesis**: Type III/IV/V の統一仮説体系. M′, M″, W₁, W₂, V の記号整備.
2. **(10.2)-(10.3) 基本構造**: ζ ∈ ℐ×ℐ の指標個数制約, w₂ は素数, パラメータ d, δ, n の確定.
3. **(10.4)-(10.6) Coherence 応用**: τ (Dade isometry) の拡張, α_{ij} 仮想指標の support 計算.
4. **(10.7) [S,S] Frobenius の実現**: S が Type II maximal ⇒ [S,S] (derived) が Frobenius group となる. **§16 最終矛盾の重要な段階**.
5. **(10.8) Theorem**: ℐ が coherent でない (背理法で § 13-14 へ).
6. **(10.10) Type V 非存在**: M が Type V ⇒ ℐ が coherent (矛盾) ⇒ **G に Type V maximal なし**.

**計算の特徴**: §11 よりも **計算が簡潔** (§11 は case (a)/(b) 分岐で指標集合複雑化, §12 は 3 型統一で単純化). しかし **Dade isometry の実装最初の本格応用** であり、form の isometry 性質が顕著に効く.

---

## §12 全 11 結果表 (概要)

| # | 結果 | 行範囲 | 型 | 題名・主張 | 依存 | 難度 |
|---|------|--------|------|-----------|------|-----|
| 1 | **(10.1)** | 5-9 | **Hypothesis** | Type III/IV/V 統一. M′, M″, W₁, W₂, V 定義. 𝒮 指標集合. τ Dade isometry. | (8.4) | — |
| 2 | **(10.2)** | 11-14 | Theorem | ζ ∈ 𝒮∩Irr M, deg ζ = w₁ 存在. 証明: Frobenius (M′/M″)⋊W₁. | (10.1), (8.4.d) | ★ |
| 3 | **(10.3)** | 16-18 | Theorem | w₂ 素数. d, δ, n 独立. d > 1, n ∈ ℕ. 証明: (8.8) + (4.5.a) 指標定理. | (10.1), (8.8), (4.5.a) | ★★ |
| 4 | **(10.4)** | 19-21 | **Hypothesis** | 仮説拡張: ζ, d, δ, n を (10.2)-(10.3) から持ち込み. (b) ℐ coherent, τ₁ 拡張. | (10.2), (10.3) | — |
| 5 | **(10.5)** | 23-43 | Theorem | α_{ij} := μ_{ij} - δμ_{i0} - nζ の support ⊆ A₀(M). τ 下で α_{ij}^τ = δ(ω_{ij}^σ - ω_{i0}^σ) - nζ^{τ₁}. | (10.4), (4.3)-(4.4) | ★★★ |
| 6 | **(10.6)** | 45-68 | Theorem | (a) μ_j^{τ₁} = δΣ_i ω_{ij}^σ, (μ₀-ζ)^τ = Σ_i ω_{i0}^σ - ζ^{τ₁}. (b) g ∈ G-Ã(M), ord g prime to w₁ ⇒ \|ζ^{τ₁}(g)\| ≥ 1. | (10.5), (5.8), (3.9) | ★★★ |
| 7 | **(10.7)** | 69-75 | **Theorem** | **S Type II ⇒ [S,S] Frobenius with kernel S_F.** 中核結果. 証明: 背理法 + (9.10)-(9.9.b) + character orthogonality. | (10.4), (8.8), (8.13), (8.18.b), (9.10), (9.8.b), (9.9.b) | ★★★★ |
| 8 | **(10.8)** | 77-101 | **Theorem** | **ℐ is not coherent.** 中核結果. 証明: ℐ coherent 仮定 → character norm 計算 + (10.6.b) + size bound → |M′| < 2w₁w₂ → 矛盾. | (10.1), (10.4)-(10.6), (8.4.d), (7.5), (7.8.b), (8.6.a), (8.11) | ★★★★★ |
| 9 | **(10.9)** | 103-109 | Theorem | w₁ < w₂ ⇒ (μ₀-ζ)^τ - Σ_{i<w₁} ω_{i0}^σ は (Irr W)^σ に直交. | (10.1), (3.8) | ★★ |
| 10 | **(10.10)** | 111-134 | **Theorem** | **G has no Type V maximal.** (10.10.1) p = 2w₁-1, w₁ < w₂. (10.10.2) ℐ = ℐ₁∪{μ_j}, d=p, δ=-1, n=2. (10.10.3)-(10.10.4) ℐ coherent (矛盾). | (8.7), (6.4)-(6.5.c), (10.8) | ★★★★ |
| 11 | **(10.11)** | 136 | Remark | **Case (b) Theorem (8.8) ⇒ \|W₁\|, \|W₂\| 素数**. Type II coherence. | (8.6.a), (10.10), (9.3)-(9.6), (9.11) | ★ |

**合計**: 7 個の主結果 (10.1)-(10.7) + 4 個の補助・関連定理 (10.8)-(10.11) = **計 11 個の論理ブロック**.

---

## (10.1)-(10.3) 基本定理: Hypothesis から w₂ 素数へ

### (10.1) Hypothesis: Type III/IV/V の統一枠組み

**設定**:
- M: G の **Type III, IV または V の maximal subgroup**
- H = Fitting subgroup of M (denoted M′ in original, following notation from (8.4))
- U: H を complement する cyclic group
- W₁, W₂: §10 Definition (8.4) における cyclic divisor
- V: (M′/M″) ⋊ W₁ の Frobenius 群の核
- 𝒮 = {Ind_{M′}^M θ | θ ∈ Irr M′, θ ≠ 1_{M′}}: induced character 集合
- τ: Dade isometry relative to (A₀(M), M, G)
- w₁ = |W₁|, w₂ = |W₂|

**重要**: (8.15) で (4.6) および (5.2) の Hypothesis が L=M, H=K=M′ で満たされる.

### (10.2) ζ 指標の存在

**定理**: ∃ ζ ∈ 𝒮 ∩ Irr M s.t. ζ(1) = w₁.

**証明**:
- (8.4.d) ⇒ W₂ ⊂ M″
- M′ solvable, M′ ≠ 1 ⇒ (M′/M″) ⋊ W₁ は Frobenius (odd order)
- Frobenius の特性化 (kernel = M′/M″ abelian) ⇒ M′ の non-principal linear character を induced すると, Irr M での w₁ 次不可約が得られる

### (10.3) w₂ 素数と d, δ, n パラメータ

**定理**:
- w₂ は素数
- μ_{ij}(1) = d (0 ≤ i < w₁, 0 < j < w₂) は i, j 独立
- δ_j (by (4.3.b)-(3.9.b) automorphism) は j 独立
- d > 1
- n = (d - δ) / w₁ ∈ ℕ

**証明キー**:
- (8.8) ⇒ ∃ S Type II maximal with |S:[S,S]| = w₂
- (4.5.a) ⇒ μ_{ij}(1) 独立性
- (3.9.b) automorphism u ⇒ δ_j = δ_1, μ_{0j}(1) = μ_{01}(1)

---

## (10.4)-(10.6) Dade Isometry の実装

### (10.4) Hypothesis: Coherence と τ₁ 拡張

**定義**:
- (a) (10.2)-(10.3) の ζ, d, δ, n を固定
- (b) **𝒮 が coherent** (§7 定義) かつ **τ₁ は τ の Z[𝒮] への拡張**

このHypothesisは実質的に "ℐ が character norm を保存する isometry を持つ" という Dade 理論の直接的応用.

### (10.5) 仮想指標 α_{ij} の support と isometry 値

**定理**:

α_{ij} := μ_{ij} - δμ_{i0} - nζ とするとき,
- Supp(α_{ij}) ⊆ A₀(M)
- (10.4) Hypothesis 下で:
  $$\alpha_{ij}^τ = δ(ω_{ij}^σ - ω_{i0}^σ) - n\zeta^{τ_1}$$

**証明概要** (複雑な計算):
1. (4.3.c) + (4.4) ⇒ (μ_{ij} - δμ_{i0})(x) = 0 for x ∈ W₁^#
2. (4.4) ⇒ μ_{i0}(1) = 1 ⇒ α_{ij}(1) = 0 by n の定義
3. α_{ij} は W₁ で vanish ⇒ (2.1) より α_{ij} は V^M ⊂ A₀(M) でのみ support
4. Dade τ 下での isometry 計算: norm bound で a = 0 を導出 (norm bound argument)

**数学的意義**: 仮想指標 α_{ij} を Dade isometry で pull back すると, Irr(W) の直交部分 (ω_{ij}^σ - ω_{i0}^σ) に単純な形で表現される. 後続の coherence 議論の基礎.

### (10.6) 指標の解析的性質

**定理**:
- (a) 0 < j < w₂ ⇒ μ_j^{τ₁} = δ Σ_{i<w₁} ω_{ij}^σ
  - また (μ₀ - ζ)^τ = Σ_{i<w₁} ω_{i0}^σ - ζ^{τ₁}
- (b) g ∈ G - Ã(M), ord(g) prime to w₁ ⇒ |ζ^{τ₁}(g)| ≥ 1

**証明 (a)**:
- (10.5) から Σ_i α_{ij} = μ_j - δμ₀ - nw₁ζ を Dade τ で isometry
- Orthogonality と Theorem (5.8) の特殊化により μ_j^{τ₁} を確定

**証明 (b)** (鍵):
- (μ₀ - ζ)^τ は G - Ã(M) で vanish (τ の定義)
- ⇒ ζ^{τ₁}(g) = Σ_{i<w₁} ω_{i0}^σ(g)
- (3.9.c) ⇒ ω_{i0}^σ(g) ∈ ℤ
- Reality 引数 (ω̄_{i0}^σ = ω_{i0}^σ conjugate) ⇒ Σ_{0<i<w₁} ω_{i0}^σ(g) ∈ 2ℤ
- ⇒ ζ^{τ₁}(g) は奇数 ⇒ |ζ^{τ₁}(g)| ≥ 1

---

## (10.7) [S,S] Frobenius 定理 — §12 の中核結果

### ステートメント

**Theorem**: Hypothesis (10.4) 下. S を Type II maximal とすると, **[S,S] は Frobenius group with kernel S_F**.

### 証明概要 (背理法 + character orthogonality)

**仮定**: [S,S] が Frobenius でない と仮定 (背理法).

**Step 1**: 記号設定
- H = S_F, [S,S] = H ⋊ U
- 𝒯 = {Ind_{HU}^S χ | χ ∈ Irr(HU), H ⊄ Ker χ}: S 側の induced character 集合
- τ: Dade isometry on (A(S), S, G)

**Step 2**: Support separation (8.13.c4), (8.18.b)
- (8.13.c4): M not Frobenius with kernel M_F ⇒ no conjugate of S supports M
- (8.18.b): Ã(S) ∩ Ã₁(M) = ∅
- ⇒ α ∈ Z[𝒮, M^#], β ∈ Z[𝒯, S^#] ⇒ (α^τ, β^τ) = 0 (direct calculation)

**Step 3**: Coherence から λ ∈ 𝒯 ∩ Irr S 存在 (背理)
- (9.10), (9.8.b), (9.9.b) ⇒ HU not Frobenius ⇒ ∃ r ≠ 0 s.t. ν_r ∈ 𝒯, ∃ λ ∈ 𝒯 ∩ Irr S with λ(1) = ν_r(1)
- (5.7) ⇒ {λ, λ̄, ν_r, ν̄_r} coherent
- τ₂ extension of τ

**Step 4**: Orthogonality 矛盾
- α = μ_s - dζ (0 < s < w₂), β = ν_r - λ として
- (5.8) ⇒ μ_s^{τ₁} = ± Σ_i ω_{i's'}^σ, ν_r^{τ₂} = ± Σ_j ω_{r'j}^σ
- ⇒ (α^τ, β^τ) = (± Σ_i ω_{i's'}^σ - dζ^{τ₁}, ± Σ_j ω_{r'j}^σ - λ^{τ₂}) = 0 (orthogonality)
- しかし (4.1) + (5.3.b) より ω_{ij}, ζ^{τ₁}, λ^{τ₂} は pairwise orthogonal
- ⇒ 0 = ±1 **矛盾**

**結論**: [S,S] は Frobenius group with kernel S_F.

### 数学的意義

§16 の最終矛盾導出に極めて重要. Type II maximal の commutator structure を **Frobenius 化** することで, 後続 §13-§15 で Type III/IV/V の detailed structure に制約が生じる.

---

## (10.8) ℐ が coherent でない — 背理法の開始

### ステートメント

**Theorem**: Hypothesis (10.1) 下, **𝒮 is not coherent**.

### 証明戦略 (極度に技巧的な character norm bound)

**仮定**: 𝒮 が coherent と仮定.

**Step 1**: Character norm から size constraint
- (7.5) with I = {1}, L₁ = M, A₁ = A(M):
  $$\frac{1}{|G|}\left(\sum_{g\in G_0 \cup G_1} |\chi(g)|^2 - |G_0 \cup G_1|\right) + \|\chi^ρ\|^2 - \frac{|A(M)|}{|M|} \leq 0$$
  ここで χ = ζ^{τ₁}, G₀ = {g ∈ G : ord(g) prime to w₁, g ∉ Ã(M)}, G₁ = G - (Ã(M) ∪ G₀).

- (10.6.b) ⇒ |-|G₁|/|G| + ‖χ^ρ‖² - |A(M)|/|M| ≤ 0

**Step 2**: Fitting subgroup size 利用
- (8.4.d) ⇒ (M′/M″) ⋊ W₁ Frobenius (odd order)
- ⇒ |M′| ≥ 2w₁ + 1
- (7.8.b) ⇒ ‖χ^ρ‖² ≥ 1 - ŵ₁/|M′|

**Step 3**: G₁ の元の大きさ制約
- 任意 x ∈ G₁ ⇒ ∃ a of prime order dividing w₁ s.t. x ∈ C_G(a)
- (8.11) ⇒ H は Hall subgroup
- (8.6.a) ⇒ C_G(a) ⊂ S (a ∈ H^#)
- (10.7) ⇒ x ∈ [S,S] または x ∈ S - [S,S]
- (2.1) ⇒ x conjugate to V element

- ⇒ G₁ ⊂ (H^#)^G ∪ V^G
- TI-subset ⇒ |G₁| = |G|/|S|(|H|-1) + |G|/(w₁w₂)(w₁w₂ - w₁ - w₂ + 1)

**Step 4**: 最終矛盾
- 上の計算を組み合わせると:
  $$\frac{w_1}{|M'|} > \frac{1}{w_2} - \frac{1}{w_1 w_2} - \frac{1}{w_2|U|}$$

- |U| ≥ 2w₂ + 1 ≥ 7 ⇒
  $$\frac{w_{1}w_{2}}{|M^{\prime}|}>1-\frac{1}{3}-\frac{1}{7}>\frac{1}{2} \Rightarrow |M^{\prime}|<2w_{1}w_{2}$$

- しかし |M′/M″| ≥ 2w₁ + 1, |M″| ≥ w₂ ⇒ |M′| ≥ (2w₁ + 1)w₂ ≥ 2w₁w₂ + w₂ > 2w₁w₂ **矛盾**

**形式化上の課題**: 複数の size constraint の fold が必要. (7.5), (7.8.b), (8.4.d), (8.6.a), (8.11), (10.6.b), (10.7) の綿密な連鎖. 推定 150-200 行.

---

## (10.9)-(10.11) 補助定理と Type V 非存在

### (10.9) w₁ < w₂ 下での orthogonality

**定理**: w₁ < w₂ ⇒ (μ₀ - ζ)^τ - Σ_{i<w₁} ω_{i0}^σ は (Irr W)^σ に orthogonal.

**証明**: 
- (μ₀ - ζ)^τ の support が V に limited ⇒ (3.8) を適用
- Norm calculation: ‖(μ₀ - ζ)^τ‖² = ‖μ₀ - ζ‖² = w₁ + 1 < w₂ ⇒ (3.8) parameter 制約満たす

### (10.10) Type V 非存在の完全証明

**Theorem**: **G has no maximal subgroup of Type V.**

**証明** (三段階):

#### (10.10.1) Type V の基本パラメータ

Type V で Definition (8.7) case (a) 不成立 ⇒ case (c) ⇒
- |H| = p³ (non-abelian p-group)
- p = w₂ (素数)
- w₁ | (p+1)

**補題**: p = 2w₁ - 1, w₁ < w₂.

**証明**: w₁ | (p+1) ⇒ p = 2kw₁ - 1 for some k ≥ 1.
- |H:H′| = p² (non-abelian of order p³)
- (6.5.a) ⇒ p² ≤ 4w₁² + 1
- ⇒ 4k²w₁² - 4kw₁ + 1 ≤ 4w₁² + 1
- ⇒ k² ≤ 1 ⇒ k = 1 ⇒ **p = 2w₁ - 1**

#### (10.10.2) 指標集合の分解

𝒮 = 𝒮₁ ∪ {μ_j | 0 < j < p}, where
- 𝒮₁: (p²-1)/w₁ 個の irreducible of degree w₁
- d = p, δ = -1, n = 2

**証明**: H non-abelian of order p³ ⇒ H′ = Z(H) order p, W₂ = H′.
- (H/H′) ⋊ W₁ Frobenius ⇒ 𝒮₁ has (|H:H′|-1)/w₁ = (p²-1)/w₁ irreds of deg w₁
- θ ∈ Irr H ⇒ θ(1) | p³, θ(1)² ≤ p³ ⇒ θ(1) ∈ {1, p}
- Elements of 𝒮 - 𝒮₁ have degree pw₁ ⇒ {μ_j}

#### (10.10.3)-(10.10.4) Coherence 証明

τ₁: τ の Z[𝒮₁] 上の拡張 (by (5.7)).

α_{ij} の support と isometry を (10.5) 同様に計算して, ℐ が coherent となることを示す.

**最終矛盾**: (10.8) Theorem ℐ is not coherent と (10.10.4) ℐ coherent が矛盾 ⇒ **Type V 非存在**.

### (10.11) Case (b) Theorem (8.8) 下での注記

**Remark**: Theorem (8.8) case (b) (全異なり) ⇒
- |W₁|, |W₂| 素数
- Type II maximal ⇒ (9.3)-(9.6) + (9.11) で H は elementary abelian of order p^q

---

## Type III, IV, V の差と §11-§13 との関係

### Type III vs IV vs V

| 特性 | Type III | Type IV | Type V |
|------|----------|---------|--------|
| **定義 (8.6)** | U abelian | U non-abelian | Weaker |
| **§12 ステータス** | (10.1)-(10.7) 분석 | (10.1)-(10.7) 분석 | (10.10) 非存在証明 |
| **[S,S]** | Frobenius (10.7) | Frobenius (10.7) | — |
| **H 構造** | elementary abelian (§13で) | 미터 | p³ non-ab (10.10.2) |
| **w₂** | 素数 | 素数 | 素数 |

### §11 (Type II/III/IV 基礎) との関係

§11 は:
- (9.1) Wielandt 作用
- (9.2)-(9.3) Type II/III/IV の分離 (C_H(U) = 1 vs p = |W₂| prime)
- (9.4)-(9.9) chief factor + Clifford 分岐 (Case (a) vs (b))
- (9.10)-(9.11) Frobenius 実現と coherence 完全性

§12 は:
- **§11 を入力として**, Type III/IV/V を統一仮説 (10.1) で処理
- (10.3) で w₂ 素数を再導出 (§11 (9.3) と同じ)
- (10.7) [S,S] Frobenius を Type II に対して導出
- (10.8) ℐ non-coherence を背理法確立

**関係**: §11 (指標層の基礎) + §12 (型別分岐の開始) = **Phase 2b の最初の本格応用層**.

### §13 (Type III/IV の精密化) との橋渡し

§13 は:
- **(11.2) Hypothesis**: Type III/IV に特化 (§12 の Type III/IV 部分を取り出し)
- **(11.3)-(11.5)**: M′, M″, H₀ の commutator chain 完全確定
- **(11.6)-(11.7)**: H = elementary abelian p^q, H₀ = 1
- **(11.8)-(11.9)**: Character orthogonality + Case (b) of (9.7) 単独化 → **Type III 最終確定**

**role 分担**:
- §12: Type III/IV/V を一括し, 共通の Hypothesis (10.1) で character norm bound → ℐ non-coherent
- §13: III/IV に戻り, commutator structure を完全にリバースエンジニアリング → **III のみ残す, IV は削除**

### §14-§16 への橋渡し

```
§11 (Type II/III/IV 基礎)
  ↓
§12 (Type III/IV/V 混合分析)
  ├─→ (10.7) [S,S] Frobenius ← Type II の最終性質
  ├─→ (10.8) ℐ non-coherent ← 背理法の開始
  └─→ (10.10) Type V 非存在 ← 最初の削除
      ↓
§13 (Type III/IV 精密化) ← §12 (10.1)-(10.7) を継承
  ├─→ (11.5) M″ = HC ← commutator structure
  ├─→ (11.7) H elementary abelian p^q
  └─→ (11.9.c) Case (b) + Type III 確定 ← Type IV も削除
      ↓
§14 (Type I, 独立) ← §13 と無関係に並行形式化可
      ↓
§15 (S, T subgroups) ← §14 完了必須
      ↓
§16 (G 非存在) ← §3-§15 全体の最終矛盾
```

---

## mathlib カバレッジと実装課題

| 概念 | 既存 | §12 要件 | Gap | 推定工数 |
|------|------|----------|-----|---------|
| Frobenius group | 基本 | (10.2), (10.7) | kernel/complement 分解 | 1 日 |
| Dade isometry | §4 完備 | (10.4)-(10.6), (10.8) | isometry 計算 + extension τ₁ | 3-4 日 |
| Coherence | §7 完備 | (10.4), (10.8) | Hypothesis (6.3) application | 2 日 |
| Character orthogonality | 基本 | (10.5)-(10.6), (10.9) | support 限定 + norm bound | 2 日 |
| p-group | 基本 | (10.10.2) | non-abelian p³ 構造 | 1 日 |
| **合計** | | | | **9-11日** |

### 実装の段階化

#### Phase 1: 基礎 (Hypothesis + ζ 指標)
- (10.1) Hypothesis structure: definitions
- (10.2) ζ 指標存在: Frobenius の性質利用
- **工数**: 30-50 行 (§11 notation 参照)

#### Phase 2: Dade 応用 (10.4)-(10.6)
- (10.4) Hypothesis coherence
- (10.5) α_{ij} support + isometry
- (10.6) 指標値 + norm constraint
- **工数**: 200-250 行 (character norm argument 複雑)

#### Phase 3: 中核定理 (10.7)-(10.8)
- (10.7) [S,S] Frobenius: 複数の subcases + orthogonality
- (10.8) ℐ non-coherent: size bound calculation
- **工数**: 300-350 行 (論理複雑)

#### Phase 4: 補助定理 + Type V (10.9)-(10.11)
- (10.9) w₁ < w₂ orthogonality
- (10.10) Type V 非存在の 3 段階証明
- (10.11) Case (b) remark
- **工数**: 150-200 行

**全体**: **680-850 行** (§11 と同程度).

---

## Phase 2b 形式化着手順 (第 6 波 中盤)

**前提**: §11 (Type II/III/IV 基礎) 完成

### Week 1: (10.1)-(10.3) 基礎
- (10.1) Hypothesis 大構造
- (10.2) ζ 指標 (§11 (9.1)-(9.2) と比較して短い)
- (10.3) w₂ 素数 (§11 (9.3) と平行)

**チェックポイント**: (8.4)-(8.6) Notation との complete alignment

### Week 2: (10.4)-(10.6) Dade 適用
- (10.4) Hypothesis coherence + τ₁
- (10.5) α_{ij} support 計算: (4.3)-(4.4), (2.1) の triple citation
- (10.6) 指標値 + norm bound: (5.8) Theorem 適用

**課題**: (10.5) の norm bound で a = 0 導出 (§11 (9.11.7) 参照)

### Week 3: (10.7) [S,S] Frobenius
- **最重要**: Type II maximal の commutator が Frobenius
- 背理法 + character orthogonality (§11 (9.10) 拡張)
- (8.13.c4), (8.18.b), (9.10), (9.8.b) の綿密な chain

**難度**: 高 (multiple case analysis)

### Week 4: (10.8) ℐ non-coherence
- **最複雑**: size bound calculation の多段階
- (7.5) norm bound + (7.8.b) + (8.4.d) + (8.6.a) + (8.11)
- G₁ decomposition (H^#)^G ∪ V^G

**難度**: 極高 (numerical constraint chain)

### Week 5: (10.9)-(10.11) 補助 + Type V
- (10.9) simple case
- (10.10) Type V 非存在 (3 段階)
- (10.11) Case (b) remark

**チェックポイント**: Type V 非存在で §12 role 完成

---

## 未解決 / TODO

1. **§11 vs §12 の type notation 完全一致確認**: §11 では (9.7) で Case (a)/(b) 分岐, §12 では Type III/IV/V 統一. (8.4)-(8.6) Definition と同期必須. Phase 2b Week 1 冒頭.

2. **(10.5) norm bound の a = 0 確定**: 複数の inner product 計算が必要. §11 (9.11.7) の norm argument と比較. 推定 50-100 行の補助lemma.

3. **(10.8) size constraint の numerical chain**: 5 個以上の inequalities を fold. 誤差累積に注意. Lean での `omega` tactic 有効性確認.

4. **§13 (11.2) Hypothesis と §12 (10.1) の notation overlap**: M′, M″, W₁, W₂, H₀, V 等. §13 で (11.2) で新たに H₀, C, u を導入. §12 との整合を明確化 (separate Hypothesis structure).

5. **Frobenius group (10.7) の formalization**: H = S_F, [S,S] = H ⋊ U. H が Hall π-group であることの formal 证明. 推定 30-50 行.

6. **mathlib への Dade isometry 拡張検証**: (10.4)-(10.6) の τ₁ 拡張が mathlib `Isometry` class hierarchy でどう express されるか. §4 完成後に確認.

---

## 関連ファイル・参考

- **原典**: `/Users/ywr/odd-order/references/peterfalvi/04.12_pp_58_63_Maximal_Subgroups_of_Types_III_IV_and_V.mmd` (136 行)
- **前置**: `notes/peterfalvi/s11_maximal_II_III_IV.md` (11 結果 + 18 論理ブロック)
- **後置**: `notes/peterfalvi/s13_maximal_III_IV.md` (9 結果 + 14 論理ブロック, Type III 確定)
- **並行**: `notes/peterfalvi/s14_maximal_type_I.md` (13 結果, Type I 独立)
- **最終**: `notes/peterfalvi/s16_nonexistence_g.md` (11 結果, G 非存在)

---

**作成**: 2026-05-22
**出典**: Peterfalvi §12 (pp.58-63, mmd 136 行)
**関連**: Phase 2b 第 6 波 形式化計画, §11 完成必須, §13-§14 並行可, §15-§16 後置
**次**: §13 (Type III/IV 精密化, §12 (10.1)-(10.7) を継承, commutator structure)
