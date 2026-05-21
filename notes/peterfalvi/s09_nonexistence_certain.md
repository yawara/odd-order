# Peterfalvi §9: Non-existence of a Certain Type of Group of Odd Order — mini-roadmap

**スコープ**: Peterfalvi §9 (pp. 38-43), mmd `04.9_pp_38_43_Non-existence_of_a_Certain_Type_of_Group_of_Odd_Order.mmd` (162 行).  
形式化先 (予定): `OddOrder/Peterfalvi/S09_NonExistenceCertainGroup.lean`.  
ROADMAP 上の位置: **Phase 2b 第 4 波** (§3-§8 完成後, BG §3 完成必須).  
**BG App.C と内容重複** (BG L4759-5005, 246 行). Phase 2b §9 を一次, BG App.C を二次 (整合性確認用) として扱う方針.

---

## TL;DR — Theorem C: 有限体上の Frobenius 群の非存在定理

**Peterfalvi §9 の意義**: 指標理論を用いて、特定の構造を持つ奇数位数群の **完全な非存在** を証明する。BG App.C は同一内容を、有限体 $F_{p^q}$ と Frobenius 群 $H = PU$ (加法群 P と norm-1 単位元群 U) の観点から再述したもの。

**Theorem C (BG App.C の結論)**:  
primes $p, q$ が条件 (A) $(\frac{p^q-1}{p-1}, p-1) = 1$ を満たし、  
$F_{p^q}$ の加法群 $P$ と norm-1 部分群 $U$ で組んだ半直積 $H = PU$ が、  
仮説 (B) (G への埋め込み、加群的作用、元 y, Q) を満たすなら：  
**$p \leq q$**.  

この定理は Peterfalvi の主著では **§9 の最終的な系 (Theorem (7.11))** で「そのような構造を持つ群は存在しない」として結論される。

---

## §9 全 6 結果の詳細抽出

| # | 行範囲 | 種別 | 号番 | ステートメント要約 | 役割 |
|---|--------|------|------|-------------------|------|
| (7.1) | L3-7 | **Hypothesis** | (H1) | **Dade isometry ρ の定義**: $\chi \in {\rm CF}(G)$ に対し $\chi^\rho(a) = \frac{1}{\|H(a)\|} \sum_{x \in H(a)} \chi(ax)$ を定める。(2.2) 仮説下で Dade isometry τ が存在. | 基本設定：ρ の定義、$A^\tau$ 導入 |
| (7.2) | L9-19 | **Lemma** | (7.2.a)-(7.2.b) | (a) $\alpha \in {\rm CF}(L,A)$ ⟹ $\alpha^{\tau\rho} = \alpha$. (b) $\chi \in {\rm CF}(G)$ ⟹ $\|\chi^\rho\|^2 \leq \|\chi\|^2$, 等号 ⟺ $\chi$ は τ の像 | ρ-τ 複合の基本性質 |
| (7.3) | L20-35 | **Lemma** | (7.3) | $\frac{1}{\|G\|}\sum_{g \in A^\tau} \|\chi(g)\|^2 \geq \|\chi^\rho\|^2$. 等号 ⟺ χ は $aH(a)$ 上定数 | 積分不等式 |
| (7.4) | L36 | **Hypothesis** | (H2) | 部分群族 $(L_i)_{i \in I}$、各々に (7.1) の仮説が成立、$A_i^{\tau_i}$ pairwise disjoint, $G_0 = G - \bigcup A_i^{\tau_i}$ | 複数 Frobenius 族の設定 |
| (7.5) | L38-51 | **Theorem** | (7.5) | 仮説 (7.4) 下で、$\chi \in \operatorname{Irr}G$ に対し $\frac{1}{\|G\|}\left(\sum_{g \in G_0} \|\chi(g)\|^2 - \|G_0\|\right) + \sum_{i \in I}(\|\chi^{\rho_i}\|^2 - \frac{\|A_i\|}{\|L_i\|}) \leq 0$ | **主不等式**：characteristic formula の等号条件解析 |
| (7.6)-(7.8) | L52-106 | **Setup + Lemma** | (7.6)-(7.8.c) | (7.6) 仮説：$H \triangleleft L$, $A = H^\#$, $\|H\| = h$, $\|L:H\| = e$, $\mathcal{T} = \{\operatorname{Ind}_H^L \theta : \theta \in \operatorname{Irr} H\}$ coherent. (7.7) χ^ρ の explicit formula. (7.8) Coherence と isometry 拡張時の norm 評価 | **Coherence 応用**：正規部分群版の詳細計算 |
| (7.9) | L107-113 | **Key Lemma** | (7.9) | 仮説 (7.4) ($I=\{1,2\}$), G 奇数位数, coherent setup ⟹ $(\beta_1, \zeta_2^{\nu_2}) \neq 0$ または $(\beta_2, \zeta_1^{\nu_1}) \neq 0$ | **２つの Frobenius 族の絡み合い**：反orthogonality |
| (7.10) | L115-155 | **Theorem** | (7.10) | k ≥ 2 個の Frobenius 群 $L_i$ (kernel $H_i$ nilpotent, $H_i^#$ TI-subset, $\gcd(h_i, h_j)=1$) ⟹ ある i で $\frac{\|G_0\|-1}{\|G\|} \geq (e-1)(\frac{h-2e-1}{eh} + \frac{2}{h(h+2)})$ | **構造定理**：位数下界の具体化 |
| (7.11) | L157-162 | **THEOREM** | **Theorem (7.11)** | 仮説 (7.10) を満たす群 G で $G_0 = \{1\}$ は存在しない | **最終非存在**：FT 証明のクローザー |

---

## BG App.C と Peterfalvi §9 の精密対応マップ

### 目的の関係

- **Peterfalvi §9**: **純指標論的** アプローチ。Dade isometry (§4-§8 で確立) + Coherence + 複数 Frobenius 族の制約条件から、矛盾を導く。
- **BG App.C**: **有限体代数的** アプローチ。Frobenius 群 $H = PU$ (加法 + norm-1 群) の具体的性質（norm 計算、Hilbert Satz 90、Galois theory）を活用し、**$p > q$ と仮定した時の矛盾** を直接導く。

### 構造対応

| Peterfalvi §9 概念 | BG App.C 概念 | 対応関係 | 注 |
|------------------|-------------|--------|-----|
| 仮説 (7.1)-(7.4) | 仮説 (A)-(B) (L4765-4809) | **等価な仮説体系** | (7.1)-(7.3) は Dade/ρ 記号法, (A)-(B) は幾何的 |
| $\tau$ (Dade isometry) | σ: $H \to G$ (monomorphism) | 指標論 vs 幾何的埋め込み | τ は σ から導出される |
| $A_i^{\tau_i}$ (Dade orbit) | σ(P_0)G の共役類 | 等価 | Frobenius kernel の作用軌道 |
| **(7.11) Theorem** | **Theorem C** (L4765-4773) | **同一の非存在定理** | Peterfalvi が指標論で, BG が有限体代数で証明 |
| Coherence (§7-§8) | Norm 計算 + 条件 (A)-(B) の equivalence | 補題的支援 | BG Preliminary Remarks (I)-(XI) に対応 |

### 詳細対応 — 6 結果と 3 補題の関係

**Peterfalvi (7.1)-(7.5) ↔ BG 前置き (I)-(XI)**

- **(7.1)-(7.2)-(7.3)**: Dade isometry ρ と ||χ^ρ|| の性質  
  ↔ **BG (VI)-(VII)-(VIII)**: Galois 理論（Frob automorphism α: x ↦ x^p）, U = norm-1 の cyclic property

- **(7.4)-(7.5)**: 複数 TI-subset 族の制約条件  
  ↔ **BG (IX)-(X)-(XI)**: H は Frobenius 群, Q = C_Q(P_0) ⊕ [Q, P_0], y の置き方

**Peterfalvi (7.6)-(7.8)-(7.9)-(7.10)-(7.11) ↔ BG Lemma C.1/C.2/C.3**

- **(7.6) 仮説**: $A = H^\#$, normal 部分群 H の coherent 族  
  ↔ **BG (B) 仮説**: σ(P_0) normalizes Q, σ(P_0)^y normalizes U

- **(7.9) Key Lemma**: 2 つの coherent 族の non-orthogonality  
  ↔ **BG Lemma C.3 Step 1-4**: 関係式 (C.2)-(C.10) による y, P_0, U の絡み合い検証

- **（7.10) Theorem**: k ≥ 2 Frobenius 族 ⟹ $G_0$ 大 (数値不等式)  
  ↔ **BG Lemma C.1**: E=E^{-1} ∧ |E|≥2 ⟹ p ≤ q

- **(7.11) Theorem**: $G_0 = \{1\}$ 不可能  
  ↔ **BG Theorem C**: 仮説 (A)-(B) + $p > q$ 仮定 ⟹ 矛盾 (Lemma C.1/C.2/C.3)

### BG Preliminary Remarks (I)-(XI) の役割

これら 11 個の観察・補題（BG L4777-4809）は、Theorem C の **proof 前置き** を形成する：

| Remark | 内容 | Peterfalvi §9 への対応 |
|--------|------|----------------------|
| (I) | Condition (A) ≡ q ∤ (p-1) | (7.4)-(7.5) 仮説の等価変形 |
| (II) | Peterfalvi 例: p=2, G=SL(2,2^q) | 仮説 (B) の非自明性確認 |
| (III) | 最小反例 ⟹ p>q | (7.11) の矛盾の出所 |
| (IV)-(V) | 拡張: p≤3, 奇素数 | Phase 3 結合時の精密化 |
| (VI) | 加法群表記 (乗法化) | (7.1)-(7.3) の σ 記号化 |
| (VII) | Galois theory: $\operatorname{Gal}(F_{p^q}/F_p) = \langle \alpha \rangle$, Satz 90 | (2.5)-(2.6) Dade 計算の基礎 |
| (VIII) | $F_{p^q}^* = F_p^* \times U$ | (7.4) 仮説の TI-subset 条件 |
| (IX) | H は Frobenius 群 | (7.6) normal H 仮説の正当化 |
| (X)-(XI) | Q 分解, y ∈ [Q, P_0] | (7.7)-(7.8) explicit 計算の前置き |

---

## Theorem C のステートメント詳細と Frobenius 群構造

### Theorem C — 完全ステートメント (BG L4765-4773)

```lean
-- 仮説 (A): 素数 p, q の条件
theorem condition_A (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] :
  (Nat.gcd (p^q - 1 / (p - 1)) (p - 1) = 1) ↔ ¬(q ∣ (p - 1)) := by
  sorry

-- Frobenius 群 H = PU の定義
def FrobeniusGroup.H (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Group :=
  -- P = F_{p^q} の加法群
  -- U = {x / x^p : x ∈ (F_{p^q})^*} の norm-1 部分群
  -- H = P ⋊ U (semidirect)
  sorry

-- 仮説 (B): 埋め込みと加群的条件
structure Hypothesis_B (G : Type*) [Group G] (p q : ℕ) : Prop :=
  (monomorphism : ∃ (σ : H ↪* G), true)
  (Q_abelian : ∃ (Q : Subgroup G), IsCyclic Q.carrier ∧ false)
  (P0_normalizes : sorry) -- σ(P_0) normalizes Q
  (conjugate_normalizes : sorry) -- σ(P_0)^y normalizes U

-- Theorem C: メイン定理
theorem TheoremC (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] 
    (hA : condition_A p q) (G : Type*) [Group G] (hB : Hypothesis_B G p q) :
    p ≤ q := by
  -- Lemma C.1/C.2/C.3 の系列で証明
  sorry
```

### Frobenius 群 $H = PU$ の数学的構造

**加法群 $P$**: $F_{p^q}$ の加法群，order $p^q$.
- Abelian, exponent p (characteristic p).
- 部分群 $P_0 = $ image of $F_p^+$ (under embedding $F_p \hookrightarrow F_{p^q}$), order p.

**norm-1 群 $U$**: multiplicative subgroup of $(F_{p^q})^*$
$$U = \left\{ \frac{x}{x^\alpha} : x \in (F_{p^q})^* \right\}$$
where $\alpha$ = Frobenius automorphism, $x^\alpha = x^p$.
- Cyclic of order $\frac{p^q - 1}{p - 1}$ (by Satz 90).
- Action on $P$ by multiplication: $u \cdot p = up$ (in $F_{p^q}$).

**Semidirect $H = P \rtimes U$**:
- Frobenius group: kernel P, complement U.
- U acts irreducibly on P (char theory, Theorem 6.8 Isaacs).
- IsFrobeniusGroup H P U (Phase 1 定義経由).

**Norm function $N: F_{p^q} \to F_p$**:
$$N(x) = x \cdot x^p \cdot x^{p^2} \cdots x^{p^{q-1}} = \prod_{i=0}^{q-1} x^{p^i}.$$
- Multiplicative: $N(xy) = N(x)N(y)$.
- $N: (F_{p^q})^* \to F_p^*$ surjective (norm map).
- $U = \ker(N|_{(F_{p^q})^*})$ (kernel of norm).

**Set E (BG L4809)**:
$$E = \{ a \in F_{p^q} : N(a) = N(2-a) = 1 \}.$$
This set appears centrally in BG Lemma C.1/C.2/C.3.

---

## Lean 形式化の設計方針

### 1. Frobenius 群 $H = PU$ の表現

**方針**: Phase 1 Ch.6 (Frobenius groups) の `IsFrobeniusGroup` を活用。

```lean
-- FiniteField API を用いた定義
def TheoremC.H (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Type :=
  AddGroup (FiniteField p q) ⋊ (NormOneSubgroup p q : Subgroup _)

-- Norm 関数を Algebra.Norm または独自定義で
def norm_map (p q : ℕ) : F_{p^q}^* → F_p^* :=
  fun x => ∏ i in Finset.range q, x ^ (p ^ i)

-- norm-1 群
def NormOneSubgroup (p q : ℕ) : Subgroup (FiniteField.Multiplicative p q) :=
  (norm_map p q).ker
```

**mathlib カバレッジ**: 
- `FiniteField` (基本)
- `Algebra.Norm` (norm 関数) — **HIGH** 被覆度
- Frobenius automorphism: `FiniteField.frobenius` (p-power endomorphism)
- Semidirect product: `SemidirectProduct` type

### 2. Norm 関数 $N: F_{p^q} \to F_p$ の実装

**2 つの選択肢**:

**案 1 (mathlib 既存)**: `Algebra.Norm` を活用
```lean
import Mathlib.Algebra.CharP.Norm

def norm_Fpq (p q : ℕ) : F_{p^q} →* F_p :=
  Algebra.norm F_p  -- (F_pq : F_p)-algebra 構造経由
```
**メリット**: mathlib 既存、定理豊富.  
**デメリット**: Field extension algebra 設定が重い可能性.

**案 2 (自製)**: norm の定義を直接展開
```lean
def norm (x : F_{p^q}) : F_p :=
  ∏ i in Finset.range q, (x.map (Frobenius p q i))
```
**メリット**: Peterfalvi 流の積 $\prod_i x^{p^i}$ をそのまま表現.  
**デメリット**: Frobenius map の反復定義が必要.

**推奨**: **案 1** (mathlib `Algebra.Norm`)、mathlib 完全カバー.

### 3. 条件 (A) $(\frac{p^q-1}{p-1}, p-1) = 1$ の形式化

```lean
-- BG Preliminary Remark (I)
lemma condition_A_equiv (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] :
  Nat.gcd (cyclotomic_polynomial_size p q) (p - 1) = 1 ↔
  ¬(q ∣ (p - 1)) := by
  sorry

-- 値計算:
def cyclotomic_polynomial_size (p q : ℕ) : ℕ := (p^q - 1) / (p - 1)
-- ただし q ≥ 1, p ≥ 2 前提
```

**数論的計算**: Lean 数値計算ライブラリ or `decide` tactic で簡約可能.

### 4. Hypothesis (B) の形式化

```lean
structure Hypothesis_B (G : Type*) [Group G] (p q : ℕ) : Prop where
  (monomorphism : ∃ (σ : H p q ↪* G), true)
  (Q_abelian : ∃ (Q : Subgroup G), CommGroup Q)
  (Q_prime : ∃ (Q : Subgroup G), ∀ g ∈ Q, Nat.Prime (order g))
  (P0_normalizes_Q : ∃ (σ : H p q ↪* G) (Q : Subgroup G), 
    ∀ x ∈ σ '' (P_0 p q), ∀ q ∈ Q, Commute x q)
  (conjugate_normalizes_U : ∃ (σ : H p q ↪* G) (y : G),
    ∀ u ∈ σ '' (NormOneSubgroup p q),
    ∀ x ∈ σ '' (P_0 p q), Commute (x ^ y) u)
```

### 5. Theorem C の Lean statement

```lean
theorem TheoremC (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] 
    (hA : condition_A p q)
    (G : Type*) [Group G] (hB : Hypothesis_B G p q) :
    p ≤ q := by
  -- Lemma C.1: E = E^{-1} ∧ |E| ≥ 2 → p ≤ q
  have h1 : E_inv_closed p q := sorry  -- Lemma C.3
  have h2 : card (E p q) ≥ 2 := sorry  -- Lemma C.2
  exact LemmaC1 h1 h2
```

---

## BG App.C との統合方針

### 統合戦略

**推奨案: A (最小二重化)**

- **実装先**: `OddOrder/Peterfalvi/S09_NonExistenceCertainGroup.lean`
- **BG App.C**: section docstring で概要を述べ、参照ポインタを置く (実装は Peterfalvi 側で統一)
- **整合性確認**: Phase 3 時に `OddOrder.BG.AppC.TheoremC ≅ OddOrder.Peterfalvi.S09.TheoremC` と同値補題を追加
- **Norm 関数**: `OddOrder.FiniteField.Norm` namespace 下で統一定義

**案 B との比較**:
- 案 B (独立実装): 両方書くと補題群が 2 倍になり、保守負荷増加.
- 案 C (BG スキップ): BG が phase 2a の最終拠点なので非推奨.

### 具体的ファイル構成

```
OddOrder/Peterfalvi/S09_NonExistenceCertainGroup.lean
  ├── import ...Dade ...Coherence ...TISubset
  ├── section TheoremC
  │   ├── def FrobeniusGroup.H (p q : ℕ)
  │   ├── def norm_map (p q : ℕ)
  │   ├── def NormOneSubgroup (p q : ℕ)
  │   ├── lemma condition_A_equiv
  │   ├── structure Hypothesis_B
  │   ├── lemma C1 : E=E^{-1} ∧ |E|≥2 → p≤q
  │   ├── lemma C2 : |E|≥2
  │   ├── lemma C3 : E=E^{-1}
  │   └── theorem TheoremC : Hypothesis_B → p ≤ q
  │   └── theorem NonExistence : No G with Hypothesis (7.10) and G_0={1}
  └── /-- (section docstring で BG App.C との対応注記) --/

OddOrder/BG/AppC.lean (既存)
  └── /-- § AppC に対する参照を追加 (実装は Peterfalvi 側) --/

OddOrder/FiniteField/Norm.lean (新規, 共用)
  ├── def norm : F_{p^q} → F_p
  ├── lemma norm_multiplicative
  ├── lemma norm_surjective
  └── /-- norm-1 部分群, Satz 90 --/
```

---

## §3-§8 (Dade/Coherence) との依存構造

### (7.6)-(7.8) Coherence 応用

**(7.6) 仮説**: 
- Normal $H \triangleleft L$, $A = H^\#$ TI-subset
- $\mathcal{T} = \{\operatorname{Ind}_H^L \theta : \theta \in \operatorname{Irr} H\}$ が coherent

**(7.7)-(7.8)**: 
- Coherence 拡張 ν で isometry $\tau$ を全 $Z[\mathcal{S}]$ に延長
- norm の下界 $\|\zeta^{\nu\rho}\|^2 \geq 1 - e/h$ (e ≤ (h-1)/2 仮定)

**Phase 1-2b 依存**:
- §7 (Coherence) 完成 **必須** → (7.6)-(7.8) 形式化可能
- §4 (Dade Isometry) の (2.5)-(2.6) 主定理も同時に必須

### (7.11) Theorem と §16 (Non-existence of G) の接続

**Peterfalvi §9 (7.11)**: 
$$\text{No } G \text{ with Hypothesis (7.10) and } G_0 = \{1\}.$$

**Peterfalvi §16 (14.1)-(14.11)**: 
$$\text{Minimal counterexample } G \text{ to FT is impossible.}$$

**接続**:
- §9 は **特定の構造（k 個 Frobenius 族）** の不可能性を示す
- §16 は **最小単純群 G** が必ずこの構造を持つことを示す（§10-§15 経由）
- §9 + §16 の合成で **G は存在しない** = **FT 完成**

**Phase 3 統合時**:
```lean
theorem FeitThompson (G : Type*) [Group G] [Fintype G] (h : Odd (Nat.card G)) :
    IsSolvable G := by
  -- § 9 (= BG App.C): Frobenius 족 structure 불가능
  have h_frobenius := S09.NonExistence
  -- § 16: G は Frobenius 족 structure 필요
  have h_structure := S16.MinimalGroupStructure
  -- 矛盾
  exact absurd h_structure h_frobenius
```

---

## mathlib カバレッジ評価

| 結果 | 内容 | mathlib カバレッジ | 評価 |
|------|------|------------------|------|
| (7.1)-(7.2)-(7.3) | ρ 定義, ||χ^ρ|| 性質 | `Character.orthogonality`, `DadeIsometry` (Phase 2b 新規) | **low-mid** |
| (7.4)-(7.5) | 複数 TI-subset 不等式 | `Finset.sum`, orthogonality relations | **mid** |
| (7.6)-(7.8) | Coherence + 計算 | `Coherence` type (新規), norm 評価 | **low** |
| (7.9) | 2 族の非直交 | virtual character inner product | **mid** |
| (7.10) | k 族の構造定理 | 数値計算, inequality chain | **mid** |
| (7.11) | **最終定理** | BG App.C lemma 直接活用 | **low** |
| (A)-(B) 仮説 | Frobenius 群, norm | `FiniteField.Norm`, `IsFrobeniusGroup` | **high** |
| C.1/C.2/C.3 | Norm 計算, E の性質 | `Algebra.Norm`, 有限体計算 | **high** |

**総括**:
- **(A)-(B) 仮説, norm 関数**: mathlib **HIGH** カバレッジ (FiniteField, Algebra.Norm 既存)
- **Dade/Coherence/TI-subset**: Phase 2b 新規 (**LOW**)
- **数値計算・不等式**: 部分的 (**MID**)

---

## Phase 2b 形式化着手順

### 全体スケジュール (§9 に焦点)

| 波 | 節 | 期間 | 依存 | 工数 |
|----|----|----|-----|------|
| 1  | §3 (Preliminary) | Phase 2b Week 1-2 | Phase 1 終 | 3 日 |
| 2  | §4 (Dade) | Phase 2b Week 3-4 | §3 終 | 5 日 |
| 3  | §5-§6 | Phase 2b Week 5 | §4 終 | 4 日 |
| 4  | §7-§8 (Coherence) | Phase 2b Week 6 | §6 終 | 5 日 |
| **4b** | **§9 (THIS)** | **Phase 2b Week 7** | **§8, BG Ch.3 終** | **3-4 日** |
| 5  | §10-§15 | Phase 2b Week 8-12 | BG Ch.4 终 | 15+ 日 |
| 6  | §16 | Phase 2b Week 13 | §15 終 | 3 日 |

### §9 内 6 結果の実装順

**Day 1: 設定と基本補題**
1. `condition_A_equiv` (A) ↔ q ∤ (p-1) 証明
2. `FrobeniusGroup.H` 定義 (P, U, H = P ⋊ U)
3. `NormOneSubgroup`, `norm_map` 定義 (mathlib `Algebra.Norm` 活用)
4. `Hypothesis_B` structure

**Day 2: 前置き補題**
5. Lemma C.2: |E| ≥ 2 (BG 直接形式化 or 参照)
6. Lemma C.3: E = E^{-1} (BG Step 1-4 の翻訳)
7. Lemma C.1: E=E^{-1} ∧ |E|≥2 ⟹ p ≤ q (比較簡単)

**Day 3-4: Theorem (7.11) と Theorem C**
8. (7.1)-(7.3): ρ の性質 (§4 定義経由)
9. (7.4)-(7.5): 複数族の不等式 (§4-§8 応用)
10. (7.6)-(7.8)-(7.9)-(7.10): Coherence setup + 構造定理 (§7-§8 経由)
11. **(7.11) Theorem**: $G_0 = \{1\}$ 불가능 (최종)
12. **Theorem C**: 仮説 (A)-(B) ⟹ p ≤ q (Lemma C.1/C.2/C.3 系列)

---

## BG との文献的対応表

| Peterfalvi | BG | 形式化時の処理 |
|-----------|-----|-------------|
| §9 全体 | App.C L4759-5005 | Peterfalvi 一次、BG 二次 (検証用) |
| (7.1)-(7.3) ρ の性質 | (I)-(XI) Preliminary Remarks | Dade isometry (§4) 前提 |
| (7.6)-(7.8) Coherence | (VI)-(VII) Galois theory | Satz 90 = Hilbert の定理 |
| (7.9)-(7.10) 構造 | Lemma C.1/C.2/C.3 | 有限体計算による具体化 |
| (7.11) **Theorem** | **Theorem C** | **FT クリティカル** |

---

## 未解決 / 形式化時の TODO

### 優先度 **HIGH**

1. **norm_map の mathlib 接続を確認**: `Algebra.Norm` が F_pq → F_p に直結するか, Field extension algebra 設定の重さ.
   - 代替案: direct sum 計算 $\prod_i x^{p^i}$ で自製するか?

2. **Frobenius automorphism の Lean API**: `FiniteField.frobenius` の使用方法, 反復適用 (x ↦ x^{p^i})
   - `Polynomial.Frobenius` との対応確認.

3. **§4-§8 (Dade, Coherence) の仕上がりを確認してから**: (7.6)-(7.8) explicit formula は Coherence 拡張 ν に依存。Phase 2b Week 7 時点で §8 が 100% 完成していることが必須.

### 優先度 **MID**

4. **BG App.C Lemma C.3 の完全な Lean 翻訳**: Step 1-4 の長い関係式は自動化困難. どこまで `sorry` で逃げるか設計.
   - 案: Lemma C.3 のみ reference として BG を指し、詳細証明は Phase 3 で deferred.

5. **condition_A の数値計算**: $(\frac{p^q-1}{p-1}, p-1) = 1$ を gcd で表現, `Nat.gcd` tactic で処理可能か.

6. **Hypothesis_B の完全形式化**: (B) の p' abelian 条件 (odd order 下 p' = odd) の厳密な日本語化.

### 優先度 **LOW** (Phase 3)

7. **§9 と §16 の最終統合**: §16 が G の structure をどう約束するか, (7.11) の hypothesis をいかに instantiate するか (Phase 3).

8. **FT main theorem の最終 statement**: 
   ```lean
   theorem FeitThompson (G : Type*) [Group G] [Fintype G] (hOdd : Odd (Nat.card G)) :
       IsSolvable G
   ```
   に §9 + BG の結果がどう流れ込むか (Phase 4).

---

## 参考: BG App.C の詳細構成 (L4759-5005)

```
L4759-4761: 序論 (Peterfalvi 1984 論文の再編)
L4762-4764: Appendix D 標題
L4765-4809: **THEOREM C + Preliminary Remarks (I)-(XI)**
  L4765-4773: Theorem C ステートメント
  L4777-4809: Remark (I)-(XI)
L4811-4815: Proof 開始 ("3. Proof of the Main Theorem")
L4815-4826: **Lemma C.1** (E=E^{-1} ∧ |E|≥2 ⟹ p≤q)
L4827-4872: **Lemma C.2** (|E|≥2 証明, q≥5 と q=3 分岐)
L4875-5002: **Lemma C.3** (E=E^{-1} 証明, Step 1-4)
L5004-5005: Problem 1 (p=3 可能性)
```

**計 3 Lemma + 1 Main Theorem** — Peterfalvi §9 の 6 結果と complementary.

---

*作成: 2026-05-22. 出典: Peterfalvi `04.9_pp_38_43_*.mmd` (162 行) + BG `local-analysis.mmd` (L4759-5005, 246 行). Phase 2b 第 4 波 (§8 完了, BG Ch.3 完了後着手).*

