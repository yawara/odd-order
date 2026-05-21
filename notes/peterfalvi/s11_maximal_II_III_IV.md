# Peterfalvi §11: Maximal Subgroups of Types II, III and IV — mini-roadmap

**スコープ**: Peterfalvi §11 (pp.50-57, mmd 04.11_pp_50_57_On_the_Maximal_Subgroups_of_G_of_Types_II_III_and_IV.mmd 202 行).
**結果数**: (9.1)-(9.11) 計 11 個の番号付き結果.
**形式化先** (予定): `OddOrder/Peterfalvi/S11_MaximalTypesII_III_IV.lean`
**ROADMAP 上の位置**: Phase 2b 第 6 波 (§10 + BG §11-§13 完成必須, §9 並行可)
**役割**: Type II/III/IV maximal subgroup の指標論的詳細分析。BG 局所構造を Peterfalvi 流 Wielandt + cohomology 手法で再解釈し、§12-§16 の分岐点を確立.

---

## TL;DR

§11 は Peterfalvi 本書の **最初の大型応用章**。§3-§8 (Dade isometry + Coherence) の中核理論を初めて具体的な Type (Type II/III/IV) に適用し、その構造を徹底分析する. 最大のポイント:

1. **(9.1) Wielandt 作用**: solvable 群上の Frobenius 作用の fixed-point 定理 → 指標個数の等式
2. **(9.2)-(9.3) 型 II/III/IV の基本分離**: U centralizer と H order の関係式
3. **(9.4)-(9.6) 前提層**: H₀ の chief factor 構造、H̄ = H/H₀ の elementary abelian 形式化
4. **(9.7) Cliff 分岐**: 2 つの Case に分かれる
   - **Case (a)**: H̄ = ⊕_{i=1}^q H_i, 各 H_i order p → Type II 典型
   - **Case (b)**: U 既約作用, F = 𝔽_{p^q} field structure → Type III/IV 精密形式
5. **(9.8)-(9.9) 指標列**: Case (a), (b) 各々の reducible/irreducible 指標のカウント
6. **(9.10) Frobenius 実現**: (9.9.c) からの specialization → Type II ⟺ HU が Frobenius
7. **(9.11) Coherence 完全性**: S(H₀C′) ⊆ Irr(M) が coherent → §12-§13 応用基盤

---

## §11 全 11 結果表

| 内容 | 行範囲 | 題名・記述 | 文字数 | 型 | 役割 |
|------|--------|-----------|--------|------|------|
| **(9.1)** | 5-22 | Wielandt Fixed-Point + Frobenius | 850 | Theorem | Frobenius group: \|C_H(UE)\|^{\|E\|}\|H\|=\|C_H(E)\|^{\|E\|}\|C_H(U)\|. 指標等式 |
| **(9.2)** | 23 | Hypothesis | 120 | Definition | M maximal Type II/III/IV, 記号統一 |
| **(9.3)** | 24-28 | Type II/III/IV 分離定理 | 580 | Theorem | Type II: C_H(U)=1 / Type III,IV: p=\|W_2\| prime |
| **(9.4)** | 29-36 | Chief Factor 構成 | 650 | Proposition | ∃ H₀ ◁ M, H̄ は p-chief factor (elementary abelian) |
| **(9.5)** | 38-40 | Hypothesis (記号増) | 950 | Definition | C=C_U(H̄), u=\|Ū\|, χ∈Irr HU sets 定義 |
| **(9.6)** | 41-46 | Central Facts | 580 | Proposition | U≠C, H̄ chief factor, \|H̄\|=p^q |
| **(9.7)** | 47-70 | Clifford Dichotomy | 1200 | Theorem | Case (a): 分散 H̄ = ⊕H_i / Case (b): 既約 F=𝔽_{p^q} |
| **(9.8)** | 71-90 | Case (a) 指標集合 | 1050 | Theorem | (a) a\|\chi(1) / (b)-(d) reducible/irred count |
| **(9.9)** | 91-105 | Case (b) 指標集合 | 850 | Theorem | (a)-(c) Case (b) の指標, 特に C=1, u=(p^q-1)/(p-1) |
| **(9.10)** | 106-110 | Frobenius 実現化 | 340 | Theorem | HU Frobenius with kernel H (Type II) |
| **(9.11)** | 111-203 | Coherence 完全性 | 4650 | Theorem | S(H₀C′) coherent for τ (8 個 sub-lemma) |

**合計**: 本体 10 個 + (9.11) 内部 8-lemma = 18 個の論理ブロック.

---

## (9.1) Wielandt 固定点定理と Frobenius 作用

### ステートメント

U ⋊ E を kernel U を持つ Frobenius group とし、UE が有限 solvable 群 H に作用し、gcd(|H|, |UE|) = 1 と仮定する。
このとき:

$$|C_H(UE)|^{|E|} |H| = |C_H(E)|^{|E|} |C_H(U)|$$

**系**: (i) C_H(E) = 1 ⇒ U は H を centralize
      (ii) C_H(U) = 1 ⇒ |H| = |C_H(E)|^{|E|}

### 数学的意義

- **Wielandt の定理** ([HB] Ch.XI Thm 12.4): solvable group 上の任意群作用に対する fixed-point 公式
- **Frobenius 構造の利用**: Frobenius group の特性と conjugacy classes の algebra により character count 等式へ変換
- **§11 全体の基盤**: (9.2)-(9.9) のすべての character count は (9.1) をベースに議論

### mathlib 形式化

- **既存**: Frobenius.group の定義、group algebra 基本 API
- **新規**: Wielandt の定理の mathlib 引入 (未収載の可能性)
- **推定**: 200-300 行

---

## (9.2)-(9.3) Type II/III/IV の基本分離

### (9.2) 記号固定

M: maximal subgroup of G, **Type II, III or IV**. H, U, W₁, W₂ from Definition (8.4) [§10], q = |W₁|

### (9.3) 構造定理

**Type II**:
- C_H(U) = 1
- |H| = |W₂|^q

**Type III, IV**:
- p = |W₂| is prime
- C_H(UW₁) = 1
- |H| = p^q |C_H(U)|

---

## (9.4)-(9.6) Chief Factor 層の構成

### (9.4) Maschke 分解

∃ H₀ ◁ M s.t.
- (a) H₀ ⊂ H, H̄ = H/H₀ は non-trivial elementary abelian p-group
- (b) Type III/IV では p = |W₂|, H̄ は chief factor, U acts non-centrally

### (9.5) 大規模記号導入

- C = C_U(H̄)
- Ū = U/C, u = |Ū|
- W̄₂ = C_{H̄}(W₁)
- χ ∈ Irr HU sets X, S, 𝒳(Y), 𝒮(Y)

### (9.6) 中心的事実

- (i) U ≠ C
- (ii) H̄ is chief factor of M
- (iii) |W̄₂| = p, |H̄| = p^q

---

## (9.7) Clifford 定理による分岐

### Case (a): 分散的 (Distributed)

H̄ = H₁ ⊕ ⋯ ⊕ H_q (各 order-p)
- W₁ acts transitively on {H₁, …, H_q}
- U/C_U(H_i) cyclic of order a (divides p-1)
- Ū ≅ (Z/aZ)^{q-1}

### Case (b): 既約的 (Irreducible)

U acts irreducibly on H̄
- ∃ field F with |F| = p^q
- ∃ U^* ⊂ F^*, U^* cyclic
- u = |U^*| divides (p^q - 1)/(p - 1), coprime to p - 1

---

## (9.8) Case (a) 指標集合

### (9.8.a) 次数の制約

χ ∈ 𝒳(H₀) ⇒ a | χ(1)

### (9.8.b,c,d) Reducible/Irreducible カウント

- (b) 𝒮(H₀) には exactly p-1 個の reducible μⱼ, deg qu
- (c) 𝒮(H₀C) には irred char deg qu from linear
- (d) 𝒮(H₀U′) には ≥ (p-1)u/(a²)個の irreds deg qa

---

## (9.9) Case (b) 指標集合

### (9.9.a) 既約作用での次数

χ ∈ 𝒳(H₀) ⇒ u | χ(1)
χ ∈ 𝒳(H₀C′) ⇒ χ(1) = u

### (9.9.b) p-1 個の reducible

𝒮(H₀) and 𝒮(H₀C) each contain exactly p-1 reducible μⱼ, deg qu

### (9.9.c) Critical Specialization

𝒮(H₀C′) が irred なし ⇒ **C = 1, u = (p^q - 1)/(p - 1)**

---

## (9.10) Frobenius 実現化

**Theorem**: (9.9.c) の条件 ⇒
- Case (9.7.b) holds
- H̄⋊U is Frobenius with kernel H̄
- U cyclic of order (p^q - 1)/(p - 1)
- Type II の場合: HU is Frobenius with kernel H

---

## (9.11) Coherence 完全性証明

### Overall Theorem

**𝒮(H₀C′) is coherent for τ** (Dade isometry τ from §8)

### 内部構造: 8 個の sub-lemma

**(9.11.1) Extremal Bound**: 𝒮₃ ≠ ∅ ⇒ a = (p-1)/2, C = U′, |𝒮₁| = 2u/a

**(9.11.2) Intersection**: w ∈ W₁^# ⇒ U₁ ∩ U₁^w = C, u ≤ a²

**(9.11.3) Irreducible Count**: |𝒮₄| = (1/q) · [((p^q - 1) - (p-1)q) / u - (p-1)]

**(9.11.4) Support 計算**: γ = Ind_{HU₁}^M 1_{HU₁}, α = γ - ψ₁
- Supp(α) ⊆ A(M)
- ‖α‖² = a + 1 + (q-1)a²/u

**(9.11.5) S₄ Non-emptiness**: |𝒮₄| > ‖α‖²

**(9.11.6) Orthogonality**: α^τ is orthogonal to 𝒮₃^{τ₃}

**(9.11.7) Coefficient Analysis**: β = λ₁ - (u/a)ψ₁
- β^τ = Γ - (u/a)ψ₁^{τ₁} + b Σ_{ψ∈𝒮₁} ψ^{τ₁}
- b ∈ {0, 1}, ‖Γ‖² = 1

**(9.11.8) Final Contradiction**: 仮定 𝒮₂ ⊂ 𝒮(H₀C′) leads to contradiction
- Hence: **𝒮(H₀C′) is coherent**

---

## BG §1 引用箇所

### Prop 1.5(d): C_{H̄}(U) = 1

使用場面: (9.3), (9.4), (9.6)

### Prop 1.6(d): H/H' = C_{H/H'}(U) × [H/H', U]

使用場面: (9.4)

### Thm 1.8: Burnside operator

使用場面: (9.4)

### Lem 1.22, Prop 1.16

使用場面: (9.4), (9.7.b)

---

## §12-§16 への橋渡し

```
§11 (Type II/III/IV 詳細)
├─→ (9.7) Clifford 分岐 → Case (a) vs (b)
├─→ (9.8)-(9.9) 指標集合 (case別)
├─→ (9.10) Frobenius 実現
└─→ (9.11) Coherence 完全性
     ↓
§12 (Type III/IV/V)
├─→ (10.7) [S,S] is Frobenius ← (9.10)
└─→ commutator structure per type ← (9.7)-(9.9)
     ↓
§13 (Type III/IV kernel)
├─→ kernel structure ← (9.4)-(9.6)
└─→ character distinctions ← (9.7)-(9.9)
     ↓
§15 (S and T subgroups)
├─→ Type II specificity ← (9.3), (9.10)
├─→ character lifting ← (9.11)
└─→ normalizer/conjugacy ← (9.8)-(9.9)
     ↓
§16 (Non-existence of G)
├─→ (9.11) coherence completes character argument
└─→ (9.10) Frobenius property finalizes structure
```

---

## mathlib カバレッジ

| 概念 | 既存 | §11 要件 | Gap | 推定工数 |
|------|------|---------|-----|---------|
| Frobenius group | 基本 | (9.1), (9.10) | Fixed-point 定理, character algebra | 2-3 日 |
| Clifford theorem | 既存 | (9.7) | Direct | 0 日 |
| Schur lemma | 既存 | (9.7.b) | Direct | 0 日 |
| Dade isometry | §4 必須 | (9.11) | Isometry性質 | 3-4 日 |
| Coherence | §7 必須 | (9.11) | 定義+応用補題 | 2-3 日 |

**合計**: 10-15 日 (前提 §4, §7, BG 完了後)

---

## Phase 2b 形式化着手順 (第 6 波)

**前提**: Phase 2a (BG) 完成, §1-§10 完成, §3-§9 完成

### Week 1-2: (9.1)-(9.3) 基礎
- (9.1) Wielandt 定理, Frobenius group 定義
- (9.2) Hypothesis 記号統一
- (9.3) Type II/III/IV 分離

### Week 3: (9.4)-(9.6) 中間層
- (9.4) Maschke, chief factor
- (9.5) 記号導入
- (9.6) 中心的事実

### Week 4: (9.7) Clifford 分岐
- Case (a) 分散, U/C_U(H_i) cyclic
- Case (b) 既約, F = 𝔽_{p^q}

### Week 5: (9.8)-(9.9) 指標集合
- (9.8) Case (a) reducible/irred count
- (9.9) Case (b), 特に C=1 specialization

### Week 6: (9.10)-(9.11) 最終層
- (9.10) Frobenius 実現化
- (9.11) Coherence 完全性 (複数 sub-lemma, 400-500 行)

---

## 未解決 / TODO

1. **Wielandt 定理の mathlib 所在確認** → (9.1) 形式化前
2. **Field isomorphism φ: H̄ → (F, +) 構成** → (9.7.b) 세부
3. **(9.11) norm bounds の精密化** → (9.11.4)-(9.11.5)
4. **BG [BG] §11-§13 exact reference lookup** → Phase 2b Week 1
5. **§10-§11 notation 相互参照検証** → 統合テスト

---

**작성**: 2026-05-22  
**출처**: Peterfalvi §11 (pp.50-57, mmd 202 행)  
**관련**: Phase 2b 제 6 波 형식화 계획  
**다음**: §12 (Type III/IV/V), §13 (Type III/IV kernel)

