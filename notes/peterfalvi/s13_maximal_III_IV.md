# Peterfalvi §13: Maximal Subgroups of Types III and IV — 詳細 per-section ノート

**スコープ**: Peterfalvi §13 (pp.64-68, mmd `04.13_pp_64_68_Maximal_Subgroups_of_Types_III_and_IV.mmd` 108 行).
**結果数**: (11.1)-(11.9) 計 9 個の番号付き結果 (内 (11.8) に 5 個の sub-lemma (11.8.1)-(11.8.6)).
**形式化先** (予定): `OddOrder/Peterfalvi/S13_MaximalIII_IV.lean`
**ROADMAP 上の位置**: Phase 2b 第 6 波 (§12 完成必須, §14 の前提).
**役割**: Type III/IV maximal subgroup の **核構造の詳細分析** (commutator chain M′, M″ の解明). §14 (Type I) との並行, §15-§16 への橋渡し.

---

## TL;DR

§13 は Peterfalvi 本書で **最も技巧的な指標計算** の節。§12 で Type III/IV/V の混合分析から、§13 は **III/IV のみ** に特化し、commutator 階層 (H₀, H′, M′, M″) の **正確な構造** を指標の直交性と character norm 計算で確定する.

**最重要結果**:
1. **(11.1)** Wielandt 恒等式の応用 → 素数論的補題 (p^q > 4q² + 1)
2. **(11.2)-(11.9) 仮説 + 定理チェーン**: H は elementary abelian p-group p^q 次, H₀=1, M″=HC という 3 つの核事実を段階的に確立
3. **(11.9.c) 最終分岐**: Case (b) (既約作用) のみが成立 → **Type III 確定**

**計算の複雑さ**:
- (11.8)-(11.8.6) は **1 個の定理が 5 個の sub-lemma に分割** される極度の細分化.
- 各 sub-step で character の内積 (μ₀ - ζ)^τ の orthogonality を個別に検証.
- 最終的に m = 1 - 1/(q-1) 型の **analytic inequality** に到達.

---

## §13 全 9 結果 + 5 個の sub-lemma (表形式)

| # | 結果 | 行範囲 | 型 | 題名・主張 | 依存 | 難度 |
|---|------|--------|------|-----------|------|-----|
| 1 | **(11.1)** | 5-8 | Lemma | 素数論: p, q 奇素, p≠q ⇒ p^q > 4q² + 1. 証明 by induction on q. | 基本 | ★ |
| 2 | **(11.2)** | 9-11 | **Hypothesis** | 仮説固定. M Type III/IV, H/U/W₁/W₂/H₀ 記号. 𝒮(X) := {χ ∈ 𝒮 \| X ⊆ Ker χ}. | (10.1), (8.4) | — |
| 3 | **(11.3)** | 13-15 | Theorem | 𝒮(H₀C) は coherent でない. 証明: 背理法, (6.3), (10.8) 引用. | (11.2), (9.6), (11.1) | ★★ |
| 4 | **(11.4)** | 17-19 | Theorem | 仮説 (11.2) 下, H₁ ◁ M (H₁ ⊂ M′ strict) で 𝒮(H₁) coherent ⇒ 2q\|U/C\| ≥ \|M′/H₁\| - 1 | (11.2), (6.2) | ★★ |
| 5 | **(11.5)** | 21-27 | Theorem | M″ = HC. 証明: (11.4) で H₁=M″ 取り, \|HC:M″\| = 1 確定. | (11.2), (11.4), (8.4.c), (8.5.a) | ★★ |
| 6 | **(11.6)** | 29-31 | Theorem | H は p-group, U centralizes H₀, H₀ = H′, C = U′. 証明: (9.3), (9.6), (11.5), [BG] Prop 1.6(d) | (11.2), (11.5), (9.3), (9.6) | ★★★ |
| 7 | **(11.7)** | 33-39 | Theorem | H は elementary abelian p^q 次, H₀ = 1. 証明 by 背理法: U の作用を bilinear mapping に翻訳, [L] Ch.XIV Thm 9.1 引用. | (11.2), (11.6), (9.7) | ★★★★ |
| 8 | **(11.8)** | 41-71 | **Main Theorem** | **ζ ∈ 𝒮(HC) ⇒ (μ₀ - ζ)^τ - Σ_{i<q} ω_{i0}^σ is NOT orthogonal to (Irr W)^σ.** 複雑な character norm 計算. **5 個の sub-lemma に分割**. | (11.2), (10.3), (5.3.b), (5.5) | ★★★★★ |
| 8.1 | (11.8.1) | 44 | Sub-Lemma | Setup: 𝒮₁ = 𝒮(HC), u = \|U/C\|, (U/C)×W₁ Frobenius. | — | — |
| 8.2 | (11.8.2) | 44 | Sub-Lemma | X = ω_{ij}^σ - ω_{i0}^σ ∈ irr(W) の support 制限. | — | ★★ |
| 8.3 | (11.8.3) | 44 | Sub-Lemma | n = \|𝒮₁\| = (u-1)/q, β = (Σ λ^{τ₁})/(u-1) (λ ∈ 𝒮₁). | — | ★★ |
| 8.4 | (11.8.4) | 44-45 | Sub-Lemma | a = (Σ ω_{r0}^σ, β). Case split: a=0 か a≠0 かで証明分化. | — | ★★★ |
| 8.5 | (11.8.5) | 49-59 | Sub-Lemma | **a = 0 確定**. (5.3.b) + orthogonality から a = 0 導出. | (11.8.4), (5.3.b) | ★★★ |
| 8.6 | (11.8.6) | 61-71 | Sub-Lemma | 結論: (11.8) 証明完成. μ_j^{τ₂} = Σ_i ω_{ij}^σ確定, coherence 矛盾導出. | (11.8.5), (11.3), (5.8) | ★★★★ |
| 9 | **(11.9)** | 73-108 | **Final Theorem** | **3 つの結論** (a)-(c): (a) (μ₀-ζ)^τ - Σ_j ω_{0j}^σ ⊥ (Irr W)^σ. (b) q > p. **(c) Case (b) of (9.7) & Type III確定.** | (11.2), (11.8), (10.9) | ★★★★ |

**合計**: 9 個の正式結果 (11.1)-(11.9) + 内 (11.8) に 5 個の sub-lemma = **計 14 個の番号付き論理ブロック**.

---

## (11.1) 素数論補題: p^q > 4q² + 1

### ステートメント
p, q を異なる奇素数とすると, p^q > 4q² + 1.

### 証明概要
1. q = 3 の場合: 5³ = 125 > 37 = 4(3²) + 1 を直接確認.
2. q ≥ 5 の場合: p ≥ 3 で 3^x > 4x² + 1 (x ≥ 5) を帰納法で示す.
   - Base: 3⁵ = 243 > 101 = 4(25) + 1.
   - Step: 3^{x+1} > 3(4x² + 1) ≥ 4(x+1)² + 1 (差分 8x² - 8x - 2 ≥ 0).

### 数学的役割
- §13 の最初の**補助定理 (lemma)** として, (11.9.b) で q > p の帰納的証明に使用.
- Wielandt 作用の結果を **素数層上に具体化** する架橋的な役割.

### mathlib への示唆
- Pure number theory — `Nat.pow_gt_of_odd_primes` として独立実装可能.
- 推定: 50-80 行.

---

## (11.2) 仮説: Type III/IV の記号体系

### 主要記号統一

| 記号 | 意味 | 由来 |
|------|------|------|
| M | maximal subgroup, **Type III or IV** | (8.4)-(8.6) |
| H | M の Fitting subgroup (odd order hall part) | (8.4) |
| U | H の complement in M | (8.4) |
| W₁, W₂ | U, M′ の cyclic 分解子 | (10.1) |
| H₀ | H の normal subgroup (chief factor 下) | (9.4) |
| H′ | [H, H] commutator | 定義 |
| U′ | [U, U] commutator | 定義 |
| C | C_U(H) centralizer in U | 定義 |
| 𝒮 | character set from (9.5)-(9.6) | (9.6) |
| 𝒮(X) | {χ ∈ 𝒮 \| X ⊆ Ker χ} support set | 定義 |
| p = \|W₂\| | W₂ 次数 | (10.1) |
| q = \|W₁\| | W₁ 次数 | (10.1) |

### 前提層 (4 階層)
1. **§10.1 Hypothesis**: Type III/IV の基本選別
2. **§8.4 Definition**: H, U, W₁, W₂ の標準設定
3. **§9.4-§9.6**: H₀, C の chief factor 理論
4. **(11.2) 本体**: H′, U′, 𝒮(X) の追加定義

---

## (11.3)-(11.5) commutator 階層の確定: H₀ → H′ → M″

### 構造図

```
M = (H ⋊ U) ⋊ W
├─ M′ = [M, M] (最初の commutator)
│  ├─ M″ = [M′, M′] (第 2 commutator) = HC (by 11.5)
│  └─ H′ ⊂ M′ (H 内 commutator)
├─ H = elementary abelian (by 11.7)
│  ├─ H₀ = normal subgroup, chief factor below
│  │  └─ H₀ = H′ (by 11.6)
│  └─ H/H₀ ≃ H (by 11.7)
└─ U
   ├─ U′ = [U, U] (by 11.6) = C
   └─ U/C abelian (by 11.6)
```

### (11.3) 定理: 𝒮(H₀C) は coherent でない

**背理法**: 𝒮(H₀C) が coherent と仮定 → Theorem (6.3) の前提が満たされる → 𝒮 全体が coherent → Theorem (10.8) に矛盾.

**mathlib 上の課題**: Coherence 정义와 Theorem (6.3) の application が極度に technical. §7-§8 の coherence 理論を完全にマスターしておく必要.

### (11.4) 定理: Quotient bound

**主張**: H₁ ◁ M (H₁ ⊂ M′ strict), 𝒮(H₁) coherent ⇒ **2q|U/C| ≥ |M′/H₁| - 1**.

**証明**: Theorem (6.2) の notation substitution (L=M, K=M′, A=H₁, B=H₀C, C=D=HC). 특정 character parameter の count 공식.

### (11.5) 정리: M″ = HC (매우 중요)

**방증**: §11.4 를 H₁ = M″ 에 적용. M′/M″ 가 abelian ⇒ 𝒮(M″) coherent (by (5.7)). 
- |M′/M″| ≤ 2q|U/C| + 1 (by (11.4))
- |HC:M″| < 2q + 1 (by |C|/|U| < 1)
- W₁ acts fixed-point-freely on (HC)/M″ ⇒ |HC:M″| = 1 (by (8.4.d))
- 따라서 **M″ = HC**.

**의미**: M 의 2번째 commutator가 정확히 abelian subgroup HC 와 일치. §16 의 최종 모순에 직결.

---

## (11.6)-(11.7) 핵심층: H의 기본 구조 3가지

### (11.6) 정리: H는 p-group, H₀=H′, C=U′

**결론**:
1. **H is a p-group**: O_{p'}(H) = 1 (by (9.3), contradiction with |M′:M″|)
2. **H₀ = H′**: U acts fixed-point-freely on H/H′ ⇒ no central part
3. **C = U′**: M″ = HC ∩ U = U′ (by (11.5), (8.5.b))

**증명 핵심**: Prop 1.6(d) ([BG]) — H/H′의 C_U 분해 사용.

### (11.7) 정리: H는 elementary abelian p^q 차, H₀ = 1

**주요 단계**:

**단계 1**: H₀ = 1 을 보이기 (배리법)

H₀ ≠ 1 이라 가정. H는 nilpotent ⇒ [H, H₀] ⊂⊂ H₀.
∃ Q ◁ H s.t. [H, H₀] ⊆ Q ⊆ H₀, |H₀:Q| = p (Lemma 1.22 [BG]).

**단계 2**: H̄ = H/H₀ 를 F_p-vector space로 해석

bilinear mapping (x, y) ↦ [x, y] : H̄ × H̄ → H₀/Q
- U-equivariant (U centralizes H₀)

**단계 3**: 기하적 논증 ([L] Ch.XIV Thm 9.1)

*Case A (U acts irreducibly on H̄)*: 
- N := {x ∈ H̄ : [x,y]=0 for all y} is U-invariant
- N = 0 ⇒ q even (contradiction)
- N = H̄ ⇒ [x,y]=0 for all x,y ⇒ H′ = 1 (contradiction with H₀ = H′)

*Case B (U does NOT act irreducibly on H̄)*:
- Case (a) of (9.7) holds: H̄ = H₁ ⊕ ⋯ ⊕ H_q (order-p each)
- Character representation φᵢ : U → (ℤ/pℤ)* s.t. h^u = φᵢ(u) h
- If φᵢφⱼ = 1 for some i, j ⇒ φᵢ(u) = 1 for all u (odd order trick) ⇒ U centralizes H̄ (contradiction with (9.4.b))
- If φᵢφⱼ ≠ 1 ⇒ [Hᵢ, H_j] = 0 ⇒ H′ trivial (contradiction)

**결론**: H₀ = 1. 따라서 H = H/H₀ elementary abelian p^q.

---

## (11.8) 핵심 정리: (μ₀ - ζ)^τ의 직교성 부정

### 문제 설정

**가정 (11.2)** + **ζ ∈ 𝒮(HC)** (HC의 kernel에 포함된 irreducible character).

**주장**: (μ₀ - ζ)^τ - Σ_{i<q} ω_{i0}^σ is **NOT orthogonal to (Irr W)^σ**.

### 5단계 부분 증명

#### (11.8.1)-(11.8.3) Setup
- 𝒮₁ = 𝒮(HC): (u-1)/q 개의 degree-q irreducible characters
- (U/C) × W₁: Frobenius group with abelian kernel U/C
- n = |𝒮₁| = (u-1)/q
- β = average character Σ_{λ ∈ 𝒮₁} λ^{τ₁} / (u-1)

#### (11.8.4) Key Coefficient
**a** := inner product (Σ ω_{r0}^σ, β) 계산.
- (11.8.4.i): a even (reality argument)
- (11.8.4.ii): **a = 0 또는 a ≠ 0 두 경우로 분화**

#### (11.8.5) Case Reduction: a = 0 확정

**핵심 계산**:
```
((μ₀ - ζ)^τ, α_{ij}^τ) = (Σ ω_{r0}^σ - ζ^{τ₁}, β + ω_{ij}^σ - ω_{i0}^σ - nζ^{τ₁})
                       = (Σ ω_{r0}^σ, β) - 1 - a + n
```

vs.
```
(μ₀ - ζ, α_{ij}) = (Σ μ_{r0} - ζ, μ_{ij} - μ_{i0} - nζ)
                = -1 + n
```

**Coherence로부터**: a = (Σ ω_{r0}^σ, β) = 0.

#### (11.8.6) 결론: (11.8) 완성

μ_j^{τ₂} = Σ_i ω_{ij}^σ 확정.
- 만약 (μ_j - dζ)^τ = μ_j^{τ₂} - dζ^{τ₁} ⇒ 𝒮(C) coherent ⇒ (11.3) 모순
- 따라서 (μ₀ - ζ)^τ - Σ_i ω_{i0}^σ ≠ 0 in (Irr W)^σ ↦ **NOT orthogonal**.

### 난이도 평가

| Sub-step | 복잡도 | 핵심 기술 |
|---------|--------|---------|
| (11.8.1)-(11.8.3) | ★★ | Character count, Frobenius setup |
| (11.8.4) | ★★★ | Inner product, reality constraint |
| (11.8.5) | ★★★★ | a=0 확정의 미묘한 논리 |
| (11.8.6) | ★★★★ | Coherence + Theorem (5.8) application |

---

## (11.9) 최종 정리: 3가지 결론 (a)-(c)

### (11.9.a) (μ₀ - ζ)^τ - Σ_j ω_{0j}^σ ⊥ (Irr W)^σ

**증명**: (11.8) 과 대칭적. μ₀ 에서 출발하면 다른 index 순서로 동일 논리.

### (11.9.b) q > p

**따름정리** (10.9) + (11.8) 로부터.

### (11.9.c) **Case (b) of (9.7) holds & M is Type III** ← 본절의 최종결론

**증명**:

**배리법**: Case (a) of (9.7) 이라고 가정.

(11.6), (11.7) ⇒ U′ = C, H₀ = 1 (elementary abelian p^q).

(9.8.d) ⇒ ∃ λ ∈ 𝒮(C) - 𝒮(HC), λ(1) = qa (a = divisor of p-1).

(9.8.b) ⇒ ∃ μ_j ∈ 𝒮(C) - 𝒮(HC), μ_j(1) = qu.

(9.11) ⇒ 𝒮(C) - 𝒮(HC) is coherent. τ₂ extension.

**Theorem (5.8) application**:
```
(μ_j - (u/a)λ)^τ = ±Σ_i ω_{ik}^σ - (u/a)λ^{τ₂}
```

**Inner product**:
```
0 = (μ₀ - ζ, μ_j - (u/a)λ) 
  = (( μ₀ - ζ)^τ, (μ_j - (u/a)λ)^τ)
  = ±1 - (u/a)(χ, λ^{τ₂})
```

**정수 논리**: u/a 와 (χ, λ^{τ₂}) 가 정수 ⇒ **a = u**.

**모순**: (9.7.a) ⇒ a | (p-1), q < u = a < p ⇒ q < p ⇒ **(11.9.b) 모순**.

**결론**: Case (b) of (9.7) holds.
- U/C cyclic
- C = U′
- U nilpotent ⇒ **U cyclic**
- **M is Type III** (정의에 의해: Type III = Type 𝓟 + Case (b) + U cyclic).

---

## Type III vs Type IV 의 차이와 §12 와의 관계

### Type III vs IV 재확인

| 항목 | Type III | Type IV |
|------|---------|---------|
| **조건 (8.6)** | U abelian + N_G(U) ⊂ M | U non-abelian + N_G(U) ⊄ M |
| **§11.6 결과** | U′ = C = non-trivial | U′ = C ≠ 1 가능성 |
| **§11.9.c** | Case (b) ⇒ **U cyclic** | Case (b) 후도 U non-abelian 가능 |
| **§12 분석** | Type III 전문분석 | Type IV 병렬분석 |
| **차별화** | (11.9.c) 에서 Type III 명시 | §12 에서 Type IV 추출 |

### §12 (Type III/IV/V) 와의 차이

- **§12**: Type III, IV, V 를 **한꺼번에 다루며**, (10.1)-(10.7) 에서:
  - (10.1) Hypothesis (Type III/IV/V 통합)
  - (10.2)-(10.3) Type V 특수화 (U = 1)
  - (10.4) commutator bounds
  - (10.5) M′ 구조
  - (10.6) U 비자명성
  - (10.7) **[S, S] is Frobenius** (Type III/IV/V 모두에서)

- **§13**: Type III/IV 만 남겨, §12 의:
  - (10.1) Hypothesis ⟵ **Type III/IV 로 수정** (11.2)
  - (10.5)-(10.6) 병합 분석
  - **Elementary abelian H 재확정** (H₀ = 1)
  - **Case (b) 단독 선택** ⟵ **M is Type III (not IV)**

### §13 후 §14 (Type I) 로의 전환

```
§10 (Type I-V 정의)
  ↓
§11 (Type II/III/IV 기초)
  ├─→ §12 (Type III/IV/V 혼합) ← 형식화 parallel 가능
  │   └─→ §13 (Type III/IV 정밀) ← §12 완료 필수
  │       └─→ (11.9.c) Case (b) Type III 확정
  │
  └─→ §14 (Type I) ← **§13 과 완전 독립**, parallel 형식화 가능
      ├─ TI subset, rank 2, cyclic O_{p'}
      └─ 13 개 보조정리
  
  ↓
§15 (S, T subgroups) ← §14 완료 필수 (Type I 분석)
  └─→ 17 결과 + 최종 bound
  
  ↓
§16 (G 非存在) ← 指標計算 最終化
```

---

## 예상 형식화 구조 (Lean)

### 파일 계획

```lean
// File: OddOrder/Peterfalvi/S13_MaximalIII_IV.lean

namespace OddOrder.Peterfalvi

section S13

variable (M : Group) [Finite M] (G : Group) [Finite G] [Group.Simple G]

/-! ## (11.1) Auxiliary Prime Inequality -/

lemma aux_prime_ineq {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    p ^ q > 4 * q ^ 2 + 1 := by
  -- induction on q
  sorry

/-! ## (11.2) Hypothesis: Type III/IV Setup -/

structure TypeIIIIVHypothesis where
  typeIIIOrIV : M.Type = Type.III ∨ M.Type = Type.IV
  H : Subgroup M := fitting_subgroup M
  U : Subgroup M := (H : Group).complement_in M
  W₁ W₂ : Subgroup U := cyclic_of U
  H₀ : Subgroup H := (by (9.4) : chief_factor_under_M)
  p := W₂.card
  q := W₁.card
  p_prime : Nat.Prime p := by (10.1) : _
  q_prime : Nat.Prime q := by (10.1) : _
  notation_S := fun (X : Subgroup M) => 
    {χ : Irr M // (X : Set M) ⊆ Subgroup.ker χ}

/-! ## (11.3)-(11.5) Commutator Chain -/

lemma s13_coherence_not_holds (hyp : TypeIIIIVHypothesis M) :
    ¬(hyp.H₀ * hyp.C).Coherent := by
  -- (6.3) + (10.8)
  sorry

lemma s13_quotient_bound (hyp : TypeIIIIVHypothesis M) {H₁ : Subgroup M} 
    (hH₁ : H₁ ◁ M) (hH₁_strict : H₁ < M.derived) (hH₁_coh : H₁.Coherent) :
    2 * hyp.q * (hyp.U / hyp.C).card ≥ (M.derived / H₁).card - 1 := by
  sorry

theorem s13_commutator_level (hyp : TypeIIIIVHypothesis M) :
    M.derived.derived = hyp.H * hyp.C := by
  -- (11.5) key result
  sorry

/-! ## (11.6) Core Structure: p-group, Centralizer Chain -/

theorem s13_H_is_pgroup (hyp : TypeIIIIVHypothesis M) :
    IsPGroup (hyp.p) hyp.H := by
  sorry

theorem s13_commutator_identities (hyp : TypeIIIIVHypothesis M) :
    hyp.H₀ = Subgroup.derived hyp.H ∧ 
    hyp.C = Subgroup.derived hyp.U := by
  -- (11.6) 핵심
  sorry

/-! ## (11.7) Elementary Abelian Structure -/

theorem s13_H_elementary_abelian (hyp : TypeIIIIVHypothesis M) :
    ElementaryAbelian hyp.p hyp.H ∧ hyp.H.card = hyp.p ^ hyp.q ∧ hyp.H₀ = ⊥ := by
  -- 매우 기술적, bilinear form 논리 필요
  sorry

/-! ## (11.8) Character Orthogonality (Main Technical Result) -/

-- (11.8.1)-(11.8.6) sub-structure
structure S13_MainCharacterData where
  ζ : Irr M
  hζ : ζ ∈ (hyp.H * hyp.C).Coherent_set
  τ : Isometry (virtual_character_supported_on (hyp.H * hyp.C)) (Irr M)
  ω_ij : ...  -- Irr(W) parameters
  -- ... more technical fields

theorem s13_character_not_orthogonal (hyp : TypeIIIIVHypothesis M)
    (data : S13_MainCharacterData hyp) :
    ¬((data.ζ.to_char - virtual_char_apply data.ω_ij).apply_iso data.τ 
      ⊥ Irr data.W) := by
  -- 5-step sub-lemma chain (11.8.1)-(11.8.6)
  sorry

/-! ## (11.9) Final Classification: Type III Determination -/

theorem s13_final_three_conclusions (hyp : TypeIIIIVHypothesis M) :
    (∀ ζ ∈ hyp.𝒮(hyp.H * hyp.C), 
      (ζ.to_char - _).orthogonal_to_irr_W) ∧  -- (11.9.a)
    (hyp.q > hyp.p) ∧                           -- (11.9.b)
    (Case_b_of_9_7_holds M ∧ M.Type = Type.III) -- (11.9.c) key
    := by
  sorry

end S13

end OddOrder.Peterfalvi
```

---

## mathlib カバレッジ

| 개념 | 기존 | §13 요구 | Gap | 공수 (일) |
|------|------|---------|-----|----------|
| Coherence | §7 필수 | (11.3)-(11.5) | 응용 정리 3-4개 | 1-2 |
| Character orthogonality | 기본 | (11.8)-(11.9) | norm bound 계산 | 2-3 |
| Dade isometry | §4 필수 | (11.8.6) | 확장 적용 | 1 |
| Elementary abelian p-group | 기본 | (11.7) | bilinear form 논리 | 3-4 |
| Derived series | 기본 | (11.5)-(11.6) | 직접 | 0 |
| **합계** | | | | **7-10일** |

---

## Phase 2b 형式化 착수순

### Week 1: (11.1)-(11.2) 기초

- **(11.1)** 소수 부등식: pure number theory, 독립적
- **(11.2)** Hypothesis structure: 큰 한 덩어리, §10 notation 참조

### Week 2: (11.3)-(11.5) Commutator 기초층

- (11.3): Coherence non-trivial application
- (11.4): Quotient bound (6.2) 활용
- (11.5): **M″ = HC** (가장 중요)

### Week 3: (11.6)-(11.7) 핵심 구조

- (11.6): p-group + commutator identity (BG Prop 1.6 필수)
- (11.7): Elementary abelian (가장 어려움, bilinear form 세부 필요)

### Week 4-5: (11.8) 5단계 sub-lemma

- (11.8.1)-(11.8.3): Setup
- (11.8.4): Coefficient calculation
- (11.8.5): **a = 0 확정** (핵심)
- (11.8.6): 결론 (norm bound computation)

### Week 6: (11.9) 최종 분류

- (11.9.a)-(11.b): 상대적 간단
- **(11.9.c)** Type III 결정: 배리법 + Case (a) elimination

---

## 미해결 / TODO

1. **§12 vs §13 의 정확한 role 분담**: §12 가 Type III/IV/V 를 "동시에" 다루는데, §13 이 III/IV 만 정밀하게 하는 이유. Phase 2b Week 1 에서 BG §10-§13 cross-reference 완성 필수.

2. **Character orthogonality (11.8) 의 5단계 sub-lemma 가 실제로 mathlib 의 어느 API 위에 구성될지 미정**. §4 Dade isometry formalization 과 동시에 설계 필요.

3. **(11.7) bilinear form 논리의 정확한 formalization**: [L] Ch.XIV Thm 9.1 (linear algebra over F_p) 를 Lean 에서 어떻게 표현할지. Mathlib `LinearAlgebra` API 확인 필수.

4. **BG [BG] Prop 1.6(d) 의 mathlib 소재**: H/H' decomposition 이 정확히 mathlib 의 어디에 있는지. (11.6) 증명 전 확인.

5. **Type III/IV distinction in (11.9.c)**: "M is Type III" 가 §13 결론인데, Type IV 는 §14 와는 무관하게 어디서 처리되나? Overview 재확인 필요.

---

**작성**: 2026-05-22  
**출처**: Peterfalvi §13 (pp.64-68, mmd 108 행)  
**관련**: Phase 2b 제 6 波 형식화 계획, §12 선행필수, §14 병렬 가능  
**다음**: §14 (Type I, 13 결과)

