# Peterfalvi App.A: A Theorem of Suzuki — per-section 調査ノート

**スコープ**: Peterfalvi Appendix A (pp. 97–134, 38 ページ).
mmd ファイル群: `05.0_A_Theorem_of_Suzuki.mmd` ~ `05.6_Characterization_of_PSU3_q.mmd` (7 ファイル, 713 行).
**全 21 結果** (Proposition + Lemma + Theorem).
形式化先 (予定): `OddOrder/Peterfalvi/Appendices/Suzuki.lean` (Phase 2b 第 7 波, 本体完了後).
ROADMAP 上の位置: **FT 本筋外** (△). 記念的再録, Bender–Suzuki–Ree 理論と BN-pair の関連.

---

## TL;DR

**Suzuki 1962 二重推移群定理**: 仮説 (A1)-(A3)
- (A1) G 二重推移群, H はある点の安定化群, t は involution (t ∉ H), D = H ∩ H^t, Q ⊲ H で H = Q ⋊ D, |Q| 偶数, |D| 奇数.
- (A2) G は faithful に作用.
- (A3) G の 2-rank ≥ 2 (位数 4 の elementary abelian 部分群).

**結論**: ∃ 正規部分群 L (G/L 奇数) s.t. L ≅ **PSL(2,q), Sz(q), PSU(3,q)** のいずれか (q は 2 の冪, q > 2).

**mathlib 現状**:
- ✓ PSL(2,q): mathlib `Matrix.ProjectiveSpecialLinearGroup` で既存 (有限体上).
- ✗ Sz(q) (Suzuki group): **未実装**.
- ✗ PSU(3,q): **未実装**.
- Peterfalvi 自身が記念的に再録した付録 → FT 本筋では使用されず, 代わりに本体の強力な induction hypothesis に置き換え.

---

## 05.*.mmd ファイル構成と全 21 結果

### ファイル 1: 05.0_A_Theorem_of_Suzuki.mmd (Intro, Part II 導入)

**内容**: Suzuki 1962 定理 statement と証明概観.

**結果**: 0 個 (Intro のみ).

**重要な議論**:
- Hypotheses (A1)-(A3) の明確な文言化.
- Theorem A statement: L ≅ PSL(2,q), Sz(q), PSU(3,q).
- Zassenhaus group の既知分類に頼る (Huppert XI より).
- Suzuki の「生成元と関係式の方法」(generators & relations) の導入.
- "If V ≠ 1, either O^{2'}(G) ≠ G or G ≅ PSU(3,q)" という中心的還元.

**記号と前提**:
```
K = {x ∈ D | x^t = x^{-1}}
V = C_D(t)
W = C_V(K)
canonical form: x = atb (a,b ∈ Q, t ∈ I)
distinguished involution s ∈ Q ∩ I (unique pair (s,r) with tst = r^{-1}tr)
structure equation: tst = r^{-1}tr
```

---

### ファイル 2: 05.1_pp_97_98_Introduction.mmd (Introduction, 重複)

**内容**: Intro の重複再掲. App.A の Hypothesis (A1)-(A3) と Theorem A statement, 
Bender–Suzuki の歴史的背景, split BN-pair of rank 1 の分類との関係.

**結果**: 0 個 (Intro のみ).

---

### ファイル 3: 05.2_pp_99_99_Notation.mmd (Notation)

**内容**: App.A 全体で使用する記号.

**記号の定義** (Lean 型注:不等号 ⊂, 右作用, stalilizer G_a, π-group, O_π(G), O^π(G), π-component, F(G), Ω_1(P), Irr(G), Res, Ind など).

**結果**: 0 個 (Notation のみ).

---

### ファイル 4: 05.3_pp_100_107_General_Properties_of_G.mmd (Chapter I)

**内容**: Hypotheses (A1)-(A3) から G の基本的性質を导出.

**全 16 結果** (最大):

| # | 種別 | 内容 | pp. | Lean |
|---|---|---|---|---|
| 1.Prop.1 | (a)-(e) | 基本構造: H^g ∩ H conjugate to D; Q contains Sylow 2-subgroup; N_G(Q) = H; O_{2'}(G) ⊂ ∩_x H^x | 100-101 | 16 補題に分割可 |
| 1.Prop.2 | (a)-(d) | Involution の基本性質: I は conjugacy class; s ∈ Q ∩ I ⇒ u ↦ s^u permutes I - (H ∩ I) | 101 | 4 補題 |
| 1.Prop.3 | (main) | \|K\| = \|H ∩ I\|; s^K = H ∩ I | 101-102 | 1 結果 |
| 1.Prop.4 | (a)-(c) | Canonical form: G - H = HtQ; (s,r) 一意; N(G) = C_D(Q) ⊂ C_D(t) | 102 | 3 補題 |
| 1.Lemma | (a)-(b) | X = {x ∈ X \mid x^t = x^{-1}}: X = Y × Z (Y = C_X(t)) | 102-103 | 1 補題 (bijectivity) |
| 1.Prop.5 | (main) | V = C_D(s); W = C_D(H ∩ I) | 103 | 1 補題 |
| 1.Prop.6 | (a)-(c) | X ⊂ D, \|\Omega_X\| ≥ 3: C_G(X) doubly transitive on Ω_X; \|C_Q(X)\| 偶; X conjugate in D to subgroup of V | 103-104 | 3 補題 |
| 1.2.Prop.1 | (a)-(c) | Q の構造: K - {1} は Q に fixed-point-freely; Q は nilpotent; H ∩ I ⊂ Z(Q) | 104-105 | 3 補題 |
| 1.2.Prop.2 | (main) | K は D の cyclic normal subgroup | 105 | 1 補題 (Fitting の定理応用) |
| 1.2.Prop.2.Cor. | (main) | Sylow 2-subgroup S は abelian または Suzuki 2-group | 105-106 | 1 系 (Suzuki 2-群の定義) |
| 1.2.Prop.3 | (main) | ∃ Aut(F_q) の部分群 A と iso Q_0 ⋊ (D/W) ≅ L(F_q, A) (Q_0 ≅ F_q additive, K ≅ F_q^*) | 106 | 1 補題 (field realization) |
| 1.3.Lemma.1 | (main) | Induction hypothesis 仮定下: L = O^{2'}(G) = ⟨Q^x \| x ∈ G⟩ (Q は 2-group) | 106 | 1 補題 |
| 1.3.Prop.1 | (a)-(c) | X ⊂ V nontriv: L = C_G(X) は (A1) 満たす; \|C_Q(X)\| 偶, 3 cases 成立 | 106-107 | 3 補題 |
| 1.3.Prop.2 | (main) | G が non-simple ⇒ Theorem A の結論成立 (正規部分群の帰納法) | 107 | 1 補題 |
| 1.3.Lemma.2 | (main) | Conjugacy in V: X, Y ⊂ V conjugate in G ⇒ conjugate in V | 107 | 1 補題 |
| 1.3.Lemma.3 & 4 & 5 | (補助) | Strongly real element の characterization; PSL(2,q) の部分群生成; Suzuki 2-group type B 下の W cyclic | 107-109 | 3 補題 |

**Lean structural note**: 
- Proposition 1(a)-(e) は 各パートが独立な補題となり得る.
- Prop.1(c) (Sylow 2-subgroup) と Prop.1(b) (N_G(X) ⊂ H) は 双対性が強い → unified lemma で統合可.
- Props 2-6 と Section 2, 3 の結果は Q, K, V, W の "階層的定義" として組織化 (可能).

---

### ファイル 5: 05.4_pp_108_114_The_First_Case.mmd (Chapter II: First Case)

**内容**: Case (B1): V が素位数 p の部分群 P を含み, C_G(P) の 2-rank = 1.
このケースで Theorem A 成立を証明.

**全 1 主定理 + 17 補題/計算**:

| # | 種別 | 内容 | pp. | Lean |
|---|---|---|---|---|
| II.Thm.B | (main) | Case (B1) ⇒ Theorem A | 108 | 1 定理 |
| II.(1)-(17) | 補題群 | Wielandt fixed-point 定理の応用; near-field F の導入; 3 個の sub-case に分割; (10.1)-(10.2) の p-rank 計算; Hall–Wielandt 定理適用; 最終的に case (10.2): p=|Σ|=3, F ≅ F_{9,2} に帰着 | 108-114 | 17 補題 |

**主要な論証スケッチ**:
1. (1)-(4): V = W ⋊ P の構造と |Q_0| = 2^p 導出.
2. (5)-(6): Q_1 が trivial の場合分け 3 cases.
3. (7)-(9): N = P, Σ ≅ C_W(P), p = f (characteristic of near-field).
4. (10)-(12): p-part of |G| の計算 → case (10.1) or (10.2).
5. (13)-(17): case (10.2) 에서 Sylow 3-subgroup 계산 → 모순 유도 (transferと正規化関数).

**Lean comment**: 
- 17 個の sub-lemma は Wielandt, Hall–Wielandt, Fitting, transfer の古典定理群 (既に mathlib に多く).
- near-field F_{9,2} の実装が必要 (F_{3^2} 上の non-associative 構造).

---

### ファイル 6: 05.5_pp_115_121_The_Structure_of_H.mmd (Chapter III: Structure of H)

**内容**: Case (C1)-(C2): V ≠ 1, C_G(P) が全 prime order subgroup P に対し 2-rank ≥ 2.
このケースで Q が 2-group, S (Sylow 2-subgroup) の構造 決定.

**全 1 定理 + 多数の補題**:

| # | 種別 | 内容 | pp. | Lean |
|---|---|---|---|---|
| III.Thm.C | (main) | Case (C1) ⇒ Q は 2-group | 115 | 1 定理 (Feit–Sibley coherence 定理応用) |
| III.Prop (S 構造) | (main) | 3 cases: (a) S = Q_0, st order 3; (b) S Suzuki type A, st order 5, W=1; (c) S Suzuki type B, st order 3, W≠1 | 116-117 | 1 명제 + 3 경우 분석 |
| III.2.Prop | (main) | Case (b) (st order 5): (SK) ∪ (SKtS) は subgroup | 117-119 | 1 명제 |
| III.3.Prop | (main) | Case (c) (S Suzuki type B): S ⋊ KW ≅ S_1 ⋊ K_1 W_1 (explicit realization in E = F_{q^2}) | 119-125 | 명제 + 상세 계산 |

**Lean structural note**: 
- Theorem C の証明は Feit–Sibley coherence 정리 (App. IV의 정리) 응용 → coherence condition 확인 필요.
- III.Prop 의 3 경우는 "induction on C_G(P)" 방식으로 재귀적 구조.
- III.3 의 realization은 binary quadratic 대수 형식 (quadratic mapping χ(a,b) = a^{1+θ} + ...) 도입 → 매우 기술적.

---

### ファイル 7: 05.6_pp_122_134_Characterization_of_PSU3_q.mmd (Chapter IV: Characterization of PSU(3,q))

**内容**: Mappings f, g, h の explicit 計算と PSU(3,q) の特性化.

**全 2 主定理 + 多数の補題**:

| # | 種別 | 内容 | pp. | Lean |
|---|---|---|---|---|
| IV.Lemma (H1-H6) | 恒等式群 | Canonical form における f, g, h の関数方程式 6 個 | 122-123 | 6 補題 (形式的計算) |
| IV.Lemma (Canonical structure) | (main) | f により G は同型類で決定; split BN-pair of rank 1 → generators & relations method | 123-124 | 1 補題 |
| IV.SS.2 (Preliminary calc.) | (main) | f(ωs^a)の形; 帰納的数列 (u_i), (v_i), (d_i) 定義; β が W の生成元 (order m) | 124-131 | ~20 補題 (数値/技術的) |
| IV.Prop. (SS.2) | (main) | ∃ ω, ζ: f(ω) = (ω^{-1})^ζ and h(ω) ∈ W | 131-132 | 1 명제 |
| IV.Prop. (SS.3) | (main) | θ=1 and f(ρ) = (ρ/y, 1/y) for all ρ ∈ Q - Q_0 → **O^{2'}(G) ≅ PSU(3,q)** | 132-138 | 1 명제 |
| IV.Prop. (SS.4) | (main) | V ≠ W case: U/(P∩U) ≅ PSU(3,ℓ) with q=ℓ^p | 138-142 | 1 명제 |

**Lean structural note**: 
- SS.1 의 H1-H6은 formal identities → proof by direct calculation (split BN-pair property).
- SS.2 의 (u_i), (v_i), (d_i) 수열은 continued fraction / eigenvalue decomposition 형식 → Lean에서 convergence 증명 필요.
- SS.3 의 main proposition: θ=1의 증명은 **field characteristic의 구체적 계산** (eq. (*) 이후) → 매우 기술적, 여러 경우 분석.
- SS.4: induction on C_G(P) 및 quotient 분석 → 최종 귀결 정리.

---

## Suzuki 정리 (Theorem A): 명확한 statement

**Hypotheses (A1)-(A3)**:
```
(A1) G: finite group acting 2-transitively on set Ω
     H: stabilizer of a point in Ω
     t: involution in G - H
     D = H ∩ H^t
     ∃ Q ⊲ H: H = Q ⋊ D, |Q| even, |D| odd

(A2) G acts faithfully on Ω

(A3) G has 2-rank ≥ 2 (contains elementary abelian subgroup of order 4)
```

**Theorem A (Suzuki 1962)**:
```
∃ normal subgroup L of G such that:
- |G/L| is odd
- L ≅ PSL(2,q), Sz(q), or PSU(3,q)
  where q is a power of 2, q > 2
- the action of L on Ω agrees with the standard 2-transitive action
```

**Proof structure** (App. A, Chapters I-IV):
1. **Ch.I**: Hypotheses (A1)-(A3) ⇒基本構造と K, V, W の characterization.
2. **Ch.II (Case B1)**: V に素位数部分群 P, C_G(P) の 2-rank = 1 → **transfer + Hall-Wielandt → quotient homomorphism** 存在 → induction で帰結.
3. **Ch.III (Case C1-C2)**: V ≠ 1, C_G(P)の 2-rank ≥ 2 ⇒ **Feit-Sibley coherence** → Q は 2-group, S の構造 3 cases.
4. **Ch.IV (Determination of f)**: generators & relations method 利用; binary quadratic 形式 χ(a,b) の explicit 計算 → **θ=1 ⇒ f(ρ) = (ρ/y, 1/y)** → O^{2'}(G) ≅ PSU(3,q).

---

## PSL(2,q), Sz(q), PSU(3,q) の Lean 表現

### 既存: PSL(2,q)

**mathlib 所在**:
```lean
-- Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean
scoped[MatrixGroups] notation "PSL(" n ", " R ")" => 
  Matrix.ProjectiveSpecialLinearGroup (Fin n) R
```

**Spec**:
- PSL(n,R) = SL(n,R) / Z(SL(n,R)) (where R is a commutative ring).
- Fin n フォーマルで SL の商 quotient.
- 有限体 F_q (q power of 2) 上では action on 1-dim projective subspaces → doubly transitive.

**Utilization**: App.A での PSL(2,q) リファレンスは mathlib から直接引け (isomorphism).

### 未実装: Sz(q)

**Definition (Huppert & Black, Ch.XI, §3)**:
```
For q = 2^(2m+1) (odd exponent of 2):
Sz(q) = Suzuki group of order q^2(q^2+1)(q-1) (simple)

Generated by matrix-like relations:
  |Sz(q)| = q^2(q-1)(q^2+1)
  Automorphism group: PGL(2,q) acting on Sz(q)
```

**Known properties** (to be formalized):
- Sharply 2-transitive group on q^2 + 1 points.
- Uniquely determined (up to isomorphism) by (A1)-(A3) when V=1 or |V|=1.
- Sylow 2-subgroup is abelian (unlike PSU(3,q)).

**Lean proposal**: 
```lean
namespace FiniteGroups.SuzukiGroup

-- q = 2^(2m+1), q > 2
variable {F : Type*} [FiniteField F] (hq: ∃ m, card F = 2^(2*m + 1))

structure Suzuki where
  -- (Lie-theoretic or combinatorial realization)
  -- Option 1: Matrix generators & relations (most direct from Peterfalvi)
  -- Option 2: Permutation group on F^2 (action, stabilizer chains)
  -- Option 3: Abstract group axioms (generators, orders, relations)

lemma Suzuki.card : card (Suzuki F) = (card F)^2 * ((card F)^2 + 1) * ((card F) - 1) := ...
lemma Suzuki.is_simple : IsSimpleGroup (Suzuki F) := ...
lemma Suzuki.two_transitive : ... -- (Sz(q) acts 2-transitively on (q^2+1) points)
```

### 未実装: PSU(3,q)

**Definition**:
```
PSU(3,q) = Projective Special Unitary group over F_q
         = SU(3,q) / Z(SU(3,q))
         = {3×3 matrices A over F_q with A^H * A = λI, det(A)=1} / scalars

where F_q: finite field, char=2
      H: conjugate transpose (Hermitian involution σ: x → x^q)
      |PSU(3,q)| = q^3(q^2-1)(q^3+1) (simple)
```

**Known properties** (to be formalized):
- Sharply 2-transitive on q^3 + 1 points.
- Sylow 2-subgroup is Suzuki 2-group of type B.
- Distinguished involution st has order 3 (unlike Sz(q) where it has order 5).

**Lean proposal**:
```lean
namespace FiniteGroups.SpecialUnitaryGroup

variable {F : Type*} [FiniteField F] (hq: char F = 2)

-- SU(3, F_q) as group of unitary 3×3 matrices
structure SpecialUnitary3 where
  matrix : Matrix (Fin 3) (Fin 3) F
  det_eq : det matrix = 1
  hermitian_cond : matrix^H * matrix = 1  -- A^H A = 1 (unitary condition)

-- PSU(3,q) = SU(3,q) / Z(SU(3,q))
def PSU3 : Group := SpecialUnitary3 F / center (SpecialUnitary3 F)

lemma PSU3.card : card (PSU3 F) = (card F)^3 * ((card F)^2 - 1) * ((card F)^3 + 1) := ...
lemma PSU3.is_simple : IsSimpleGroup (PSU3 F) := ...
lemma PSU3.two_transitive : ... -- (PSU(3,q) acts 2-transitively on (q^3+1) points)
lemma PSU3.sylow_2_structure : ... -- Suzuki 2-group of type B
```

---

## Phase 1 Ch.8 (Permutation Groups) との依存

**Connection**:

Ch.8 (Isaacs) の結果群:
- **8.16**: 2-transitive ⇒ primitive (Block theory).
- **8.17**: Primitive + transposition ⇒ Sym (Jordan's theorem).
- **8.29**: PSL(n,q) is 2-transitive on projective space.
- **8.30**: Iwasawa criterion (Simplicity).

**App.A の依存** (Peterfalvi は Ch.8 を直接引用):
- Hypothesis (A1) "G acts doubly transitively" → Ch.8.6 (double transitivity via regular normal subgroup).
- Proposition 1.3.Lemma.1 の "Q は regular on Ω - {H}" → Ch.8.5 (regular subgroups).
- Primitive action の primitivity block 理論 → Ch.8.11-8.14.
- Sylow 2-subgroup の cyclicity 判定 → Ch.8 の rank / height の議論と相補.

**Lean dependency graph**:
```
Phase 1 / Ch.8 (Permutation Groups)
         ↓ (8.16, 8.29, 8.30)
Phase 2a / Peterfalvi 主体 (Ch.1-16)
         ↓ (BN-pair, structure theorems)
Phase 2b / App.A (Suzuki characterization)
         ↓ (generators & relations)
Phase 2c / Final classification (如有必要)
```

---

## FT 経路との関係 (△ 本筋外)

**Peterfalvi 本体と App.A の関係**:

1. **FT 本筋** (Peterfalvi Ch.1-16): 
   - Odd order group の structure theorem (O (odd-order normal subgroup) の存在).
   - BN-pair of rank 1 の完全分類.
   - Suzuki の結果は auxiliary only (single reference point, not recursive).

2. **App.A の位置付け**:
   - **記念的再録** (Suzuki 1962 の historic theorem をまとめて提示).
   - **Bender's theorem** の前提条件: 「偶数位数の proper 部分群 H で H ∩ H^x が常に奇数」.
   - **Split BN-pair classification** の重要な component (but not blocking).

3. **Peterfalvi の simplification**:
   - Suzuki (1962) の「generators & relations」method を preserve.
   - Chapter II (First Case) で Wielandt fixed-point の活用 (simplified from Suzuki's transfer argument).
   - Chapter III (Structure of H) で Feit-Sibley coherence theorem (新しい tool).
   - Chapter IV で binary quadratic forms の explicit 計算 (simplified but technical).

**Lean 実装 priority**:
- Phase 2a (Ch.1-16): **High priority** (FT 본체).
- Phase 2b (App.A): **Low priority** (記念的, 自己完結).
- Suzuki/PSU 그룹: 차후 **특화 라이브러리로 분리 가능** (mathlib 기여 모드로 별도).

---

## mathlib カバレッジ

### 既存・直接利用可能

| 항목 | mathlib 所在 | 相当 | Status |
|---|---|---|---|
| PSL(2,q) | `LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean` | App.A Lemma 4 | ✓ 直接引用可 |
| SL(n,q) perfect | `LinearAlgebra/Matrix/SpecialLinearGroup.lean` | App.A II引用 | ✓ 既存 |
| Sylow subgroup | `GroupTheory/Sylow.lean` | 全章 | ✓ 既存 |
| Nilpotent groups | `GroupTheory/Nilpotent.lean` | Ch.I Prop.1(b) | ✓ 既存 |
| Elementary abelian | `GroupTheory/Pgroup.lean` | Hypothesis (A3) | ✓ 既存 |
| Transfer theorem | `GroupTheory/Transfer.lean` | Ch.II (1)-(9) | ✓ 既存 |
| Hall-Wielandt | 標準論文 (mathlib に partial) | Ch.II (12) | ✓ partial |
| Commutative diagrams | `CategoryTheory/Diagram/...` | formal | ✓ 既存 |

### 新規実装必須

| 項目 | 必要性 | 難度 | Lean Effort |
|---|---|---|---|
| Suzuki group Sz(q) | High | Very High | 300-500 行 (combinatorial + properties) |
| PSU(3,q) | High | Very High | 400-600 行 (Hermitian, unitary condition) |
| Suzuki 2-group (type A, B, C, D) | High | High | 200-400 行 (Appendix III の分類) |
| Feit-Sibley coherence | Medium | High | 150-250 行 (character-theoretic) |
| Split BN-pair formalism | Medium | Medium | 100-200 行 (generic axioms) |
| Generators & relations | Low | Medium | 50-100 行 (meta-group) |
| Binary quadratic forms | Low | High | 100-200 行 (Chapter IV SS.2-3 計算) |

**Estimation**: App.A 전체 ≈ **1500-2500 행** Lean.

---

## Phase 2b 形式化着手順 (本体完了後)

**Recommended order**:

1. **Appendix III (Suzuki 2-groups)** ← **먼저** (Ch.III 証明の前提)
   - Definitions (type A-D).
   - Structure theorem (generator, Sylow 2-subgroup).
   - Higman classification (order formula).

2. **Appendix I (Fixed-point-free actions)** (Ch.I, II で多用)
   - Proposition 1-2 (Frobenius, fixed-point-free).
   - Application to p-groups.

3. **Appendix II (Near-fields)** (Ch.II で登場)
   - Definition & basic properties.
   - F_{9,2} (quaternion 구조 over F_3).

4. **Appendix IV (Feit-Sibley coherence)** (Ch.III で crucial)
   - Coherence condition.
   - Induction على cohesive families.

5. **Chapter I - IV** (順序: I → II → III → IV)
   - Ch.I: General properties.
   - Ch.II: Case B1 (Hall-Wielandt).
   - Ch.III: Case C1-C2 (Feit-Sibley).
   - Ch.IV: Generators & relations (f, g, h 計算).

6. **Suzuki group & PSU(3,q)** (Ch.IV 完成後)
   - Sz(q) の定義と characterization (Theorem A 파트 1).
   - PSU(3,q) の定義と characterization (Theorem A 파트 3).
   - Isomorphism statement & verification.

---

## 未解決 / TODO

### 技術的課題

1. **Suzuki 2-group の実装**:
   - Type A-D の通常な (vs. non-standard) 定義の統一.
   - Higman の분류 정리 statement (order formula vs. 구조).
   - Q/Q_0 의 module structure 계산 (biadditive form χ).

2. **Near-field F_{9,2}**:
   - Quaternion 대수로 realise (F_3 係数).
   - Multiplication table の explicit 표현.
   - Automorphism group의 structure.

3. **Binary quadratic forms (Chapter IV)**:
   - χ(a,b) = a^{1+θ} + εa^θ·θ^θ + b^{1+θ} 의 formal definition.
   - Quadratic extension E/F 위에서의 작용 (σ automorphism).
   - Convergence of (u_i), (v_i), (d_i) 수열 (continued fraction).

4. **Generators & relations method**:
   - Suzuki's method의 formal axiomatization (split BN-pair).
   - txt = g(x)h(x)tf(x) 관계식 ⇒ group 결정.
   - Inverse: given f, reconstruct G (uniqueness up to isomorphism).

5. **Feit-Sibley coherence theorem**:
   - Coherence 조건의 character-theoretic statement.
   - Induction 증명 (coherent families의 inductive structure).

### 라이브러리 dependencies

- `Mathlib.GroupTheory.Transfer` (확장 가능?)
- `Mathlib.LinearAlgebra.Matrix.Charpoly` (characteristic polynomial, minimal polynomial).
- `Mathlib.FieldTheory.Galois` (automorphisms of fields, Galois theory).
- `Mathlib.Data.Fintype.Powerset` (combinatorial enumeration for orbits).

### 문서화 / 검증

1. **Lean code comments**: Peterfalvi pp. reference.
2. **Theorem statements**: Hypothesis names (A1)-(A3), case names (B1)-(C2).
3. **Proof outlines**: mmd ← Lean theorem comments (교호 참조).
4. **Abbrev./notation**: K, V, W, Q_0, Q_1, S 등 일관된 정의.
5. **Cross-references**: Ch.1-16 via `OddOrder.Peterfalvi.Chapters.*`.

---

## 결론

**App.A: A Theorem of Suzuki** は:
- **스코프**: Suzuki 1962 두 배 추이 군 정리의 완전 재증명 (simplified, Peterfalvi version).
- **규모**: 4 장, ~20 보조정리, 3 주요 케이스 분석, 생성원과 관계식 방법.
- **mathlib 현황**: PSL(2,q)는 현존 (사용 가능), Sz(q) & PSU(3,q)는 완전 신규.
- **난도**: 높음 (Feit-Sibley, Hall-Wielandt, 이진 이차 형식, 연분수 수열).
- **우선순위**: Phase 2b (FT 본체 완료 후). 기념적 재록 (본 경로에 필수 아님).
- **Lean effort**: ~1500-2500 행 (appendices 포함). Suzuki group 실현이 가장 도전적.

**다음 단계**: Phase 2a (Ch.1-16) 형식화 완료 후, App.A 의존 관계를 역추적하여 Appendix I-IV 부터 점진적 구현.

