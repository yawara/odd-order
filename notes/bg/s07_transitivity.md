# BG §7: The Transitivity Theorem — mini-roadmap

**スコープ**: BG §7 (mmd L2131-2314, PDF pp. 55-60), **6 結果**.
形式化先 (予定): `OddOrder/BG/Ch2_Uniqueness/S07_Transitivity.lean`.
ROADMAP 上の位置: **Phase 2a 第 3 波** (§6 + Phase 1 Ch.7 完成必須).
**FT 経路**: ☆☆☆ **クリティカル**. 最小反例 G を本書で fix する節 (L2133). Hypothesis 7.1 が §8, §9, §10-§16 全体の暗黙前提.

---

## TL;DR

§7 は **最小反例 G の最大 q-subgroup への作用の推移性** を証明する節. 中核は **Hypothesis 7.1** (L2141-2145): G が最小反例と fixed したときの記法 ℳ, 𝒰, SCN_3(p), ℋ_H(A;π) の定義 + maximal q-subgroup の K-作用が transitive になる条件を 6 つの結果 (Lemma 7.1, Theorem 7.2-7.6) で精密化. 本節で G が nonabelian simple と確定し、§8-§16 では G の maximal subgroup の構造を調べる stage が opened.

---

## §7 全 6 結果一覧

| # | 種別 | mmd 行 | statement (1-2 行) | Lean 難度 | 被引用 |
|---|------|--------|-------|---------|--------|
| **7.1** | Lem | 2147-2175 | **Inductive Lemma**: Hypothesis 7.1, Q₁, Q₂ ∈ H_G^*(A;q) with ∃H proper, A ⊆ H, H∩Q_i ≠ 1 ⇒ Q₂=Q₁^k for k ∈ K. **[Core structural lemma, induction on order]** | **大** | **Thm 7.2, 7.3, 7.4 全て、§8-§10 多用** |
| **7.2** | Thm | 2177-2185 | **m(Z(A))≥3 ⇒ transitivity**: Hypothesis 7.1, m(Z(A))≥3 ⇒ K acts transitively on H_G^*(A;q). | 中 | Thm 7.6 証明, §8 L2378 |
| **7.3** | Thm | 2187-2195 | **m(Z(A))≥2 + q ∈ π(C_G(A)) ⇒ transitivity**: 弱い rank 条件だが q が C_G(A) の素因子あれば OK. | 中 | Thm 7.4 帰納用 |
| **7.4** | Thm | 2197-2250 | **Key Propagation Theorem**: Hypothesis 7.1, P proper π-subgroup with A ⊴ P, K transitive on H_G^*(A;q) ⇒ 4 conclusions: (a) C_K(P)=O_{π'}(C_G(P)), (b) O_{π'}(C_G(P)) transitive on H_G^*(P;q), (c) H_G^*(P;q) ⊆ H_G^*(A;q), (d) normalizer structure. | **大** | **§8 L2382, §9 多用, App.C** |
| **7.5** | Prop | 2252-2307 | **Sufficient Condition for Hyp 7.1**: A abelian p-subgroup satisfies (1) A={x ∈ C_G(A): x^p=1} + p-length 1, or (2) A ∈ SCN_2(P) ⇒ A satisfies Hypothesis 7.1. | 中-大 | **§8 L2850, §10-§13 via SCN_2/SCN_3 chain** |
| **7.6** | Thm | 2311-2313 | **Thompson Transitivity Theorem (special case)**: p ∈ π(G), A ∈ SCN_3(p), q ∈ p' ⇒ O_{p'}(C_G(A)) acts transitively on H_G^*(A;q). Proof: Prop 7.5 + Thm 7.2. | 短 | **§8 L2466, §9 L2511, §10-§13 all sections, App.C** |

---

## Hypothesis 7.1 — G 最小反例の固定

### Statement (mmd L2141-2145)

```
(1) A: nonidentity proper subgroup of G, π=π(A), K=O_{π'}(C_G(A))
(2) ∀ proper subgroup X ⊇ A: ⟨H_X(A;π')⟩ = O_{π'}(X)
```

### 解釈

1. **記法の確立**:
   - **A**: G の proper subgroup
   - **π = π(A)**: A の prime divisors (A の位数に現れる素数集合)
   - **π' = π(G) \ π**: complementary primes
   - **K = O_{π'}(C_G(A))**: C_G(A) の p'-core (最大の π'-subgroup)

2. **核心条件 (2)**:
   - **ℋ_X(A;π')**: A により normalize される X の π'-subgroup 全体の集合
   - **⟨ℋ_X(A;π')⟩ = O_{π'}(X)**: H_X(A;π') の生成は O_{π'}(X) に等しい (X が A を含むあらゆる subgroup で)

3. **意味**: 
   - C_G(A) の π'-部分は K に contained
   - A を含む subgroup X での π'-core は A-normalize される subgroup 全体で生成される

### Lean 表現の設計方針

```lean
-- Hypothesis 7.1 setup
structure Hypothesis71 (G : Type*) [Group G] (A : Subgroup G) : Prop where
  A_proper : A < ⊤
  A_nontrivial : A ≠ ⊥
  A_primes_def : let π := (Fintype.filter (fun p : ℕ => Nat.Prime p ∧ p ∣ A.card) _)
  C_G_A_complement : ∀ (x : G), x ∈ Subgroup.center (A.sylow_complement) → x ∈ K
  hyp2_condition : ∀ (X : Subgroup G), A ≤ X → X < ⊤ →
    let H_X_pi' := {y : Subgroup X | A.normalize y ∧ Coprime y.card (π.prod id)}
    Subgroup.closure (H_X_pi'.image Subgroup.subgroupOf) = SubgroupOcore π' X
```

### 下流での使用パターン

- **§8**: maximal subgroup M の Fitting F(M) の rank ≥ 3 ⇒ C_F(A₀) ∈ 𝒰 (§8 Thm 8.1)
- **§9**: 一意性定理で central structure を固定
- **§10-§13**: maximal subgroup の族を分類するとき, E や M_α の定義で implicit 前提

---

## Lemma 7.1 — 推移性の基底定理

### Statement (mmd L2147-2151)

```
Hypothesis 7.1, q ∈ π', Q₁, Q₂ ∈ H_G^*(A;q),
∃ proper H: A ⊆ H, H∩Q₁ ≠ 1, H∩Q₂ ≠ 1
─────────────────────────────────────────
Q₂ = Q₁^k for some k ∈ K
```

### 核心論理

**Induction on |G|_q / |Q₁ ∩ Q₂|** (L2153):

1. **Base**: Q₁ ∩ Q₂ = 1
   - H での Sylow q-subgroup に lift して Q₁^h, Q₃ を作成 (h ∈ K)
   - |Q₁^h ∩ Q₃| > 1 だから inductive hypothesis を再適用
   - 結論: (Q₁^h)^f = Q₃^g = Q₂ for f,g ∈ K

2. **Inductive step**: Q₁ ∩ Q₂ ≠ 1
   - Q = Q₁ ∩ Q₂, H = N_G(Q) へ reduce (§6 Lem 6.6 apply)
   - |Q| ≥ |N_{Q_i}(Q)| なら Q_i = Q で終了
   - 否ば sub-case に分岐

### Lean 形式化の鍵点

- **Order divisibility**: Fintype.card の inductive argument
- **Sylow theory**: `Sylow.exists_subgroup_dvd_of_dvd` (A-invariant Hall)
- **Coprime action stabilizer**: `Subgroup.stabilizer_of_coprime`
- **Normalizer structure**: Lem 6.5 との chain

---

## Theorem 7.2-7.3 — Transitivity Conditions (rank 系)

### Thm 7.2: m(Z(A)) ≥ 3

**直感**: A の center に rank ≥ 3 の elementary abelian があれば, 任意の Q₁, Q₂ ∈ H_G^*(A;q) は K-conjugate.

**証明線**:
- Z(A) ⊇ B (order p³ elementary abelian, p ≠ q) を取る
- Proposition 1.16 (Coprime action form): Q₁ = ⟨C_{Q₁}(C) : C ⊆ B, B/C cyclic⟩
- 特に C_{Q₁}(C) ≠ 1 for some C (order p²) exist
- Lem 7.1 with H = C_G(z) (z ∈ C#) で結論

**Lean難度**: 中. Coprime action の characterization (Proposition 1.16) が blackbox化していれば短い.

### Thm 7.3: m(Z(A)) ≥ 2 + q ∈ π(C_G(A))

**直感**: rank 条件が弱い (≥ 2) が, q が C_G(A) の divisor であれば still transitive.

**証明線**:
- B ∈ E_p^2(Z(A)) を取る (rank 2 elementary)
- R ∈ H_G^*(A;q) containing Sylow q-subgroup of C_G(A) exists
- Lem 7.1 chaining: Q₁ → R → Q₂ via Prop 1.16 + C_G(x) centralizer

**役割**: Thm 7.4 の帰納証明で B から A への lifting で使用 (L2212).

---

## Theorem 7.4 — 推移性の伝播定理

### Statement (mmd L2197-2203)

```
Hypothesis 7.1, q ∈ π', P proper π-subgroup with A ⊴ P,
K acts transitively on H_G^*(A;q)
───────────────────────────────────────
(a) C_K(P) = O_{π'}(C_G(P))
(b) O_{π'}(C_G(P)) acts transitively on H_G^*(P;q)
(c) H_G^*(P;q) ⊆ H_G^*(A;q)
(d) Normalizer formula: N_G(P) = C_K(P)·(N_G(P) ∩ N_G(Q)) ∀Q ∈ H_G^*(P;q)
```

### 意味

**最重要**: Hypothesis 7.1 を A に対して verify → P を含む larger π-subgroup でも同じ性質が propagate される.

### 証明構成 (L2207-2250)

**Induction on |P:A|**:

1. **Composition series reduction** (L2206-2212):
   - P の composition series で k ≤ n-2 なら P_{n-1} へ reduce, inductive hypothesis apply

2. **Base case** (k = n-1 or n):
   - A ⊴ P, |P/A| は π-prime (式 7.2)
   - P acts on Ω = H_G^*(A;q) (order divides |K|)
   - P/A は Ω 上 fixed point を持つ (Cauchy)

3. **Case 1**: 1 ∈ H_G^*(P;q) ⇒ trivial

4. **Case 2**: 1 ∉ H_G^*(P;q)
   - (c) 証明: Q ∈ H_G^*(P;q) ⇒ Q ⊇ N_{Q₁}(Q) for Q₁ ∈ H_G^*(A;q) (L2224-2232)
     → |Q| = |O_{π'}(N_G(Q))|_q ⇒ Q = Q₁ ∈ H_G^*(A;q)
   - (b) 証明: Hall π-subgroup conjugacy in N_{KP}(Q₂) (L2234-2244)
   - (d) 証明: Lem 6.5 apply

### FT 役割

**§8, §9 で最頻出の lemma**: Thm 7.4 を apply して, F(M) (Fitting of maximal M) の structure を F(M) の p-Sylow での transitivity に還元.

---

## Proposition 7.5 — Hypothesis 7.1 の十分条件

### Statement (mmd L2252-2257)

```
A: abelian p-subgroup
─── case (1) ───
A = {x ∈ C_G(A) : x^p = 1} ∧ every proper subgroup has p-length 1
─── or case (2) ───
A ∈ SCN_2(P) for some P ∈ Syl_p(G)
───────────────────────────────
A satisfies Hypothesis 7.1
```

### 解釈

**Case (1)** (L2261):
- A は C_G(A) での p-elementary radical (Ω₁(C_G(A)))
- p-length 1 (§6 Lem 6.6 に密接)
- Thm 6.7 から直接出る

**Case (2)** (abelian SCN_2):
- A が Sylow p-subgroup P の SCN_2(P) に属する (= strongly closed normal abelian)
- Deeper: (7.4) で B ∈ E_p^2(A) と Z(P) の relative position より
- Lem 6.6 (p-length 1 characterization) + Thm 6.1 (Hall-Higman) で証明

### 形式化の鍵

- **SCN_2(P) definition** (App.A に登場予定): A ⊴ P かつ A strongly closed
- **p-length 1 群の性質**: BG §6 Lem 6.6 all 4 parts
- **Z(P) modular form**: L2265-2271, Ω₁(Z(P)) の role

### 下流: 暗黙の SC N_3 chain

§7 では SCN_2 → SCN_3 chain が L2137, L2311, L2378, L2850 で登場:
```
A ∈ SCN_2(P) ⇒ Prop 7.5 apply ⇒ Hyp 7.1 verify
     ↓
  Thm 7.2 / Thm 7.4 apply (m(Z(A))≥3 or A ⊴ P cases)
     ↓
  Thm 7.6 (Thompson Transitivity) が A ∈ SCN_3(p) でも work
```

---

## Theorem 7.6 — Thompson Transitivity Theorem

### Statement (mmd L2311-2312)

```
p ∈ π(G), A ∈ SCN_3(p), q ∈ p'
─────────────────────────
O_{p'}(C_G(A)) acts transitively on H_G^*(A;q)
```

### 意味 (per overview)

**§7 の最終結論**: G が nonabelian simple で, A が SCN_3(p) (maximal strongly closed normal abelian p-group chain の rank ≥ 3 element) なら, p' の任意の素 q に対して, C_G(A) の p'-core K は H_G^*(A;q) (A-normalize される maximal q-subgroup 全体) 上推移的に作用.

### 証明 (L2313)

```
Proof.: This follows from Proposition 7.5 and Theorem 7.2.
```

- **Step 1**: Prop 7.5 case (2) by SCN_3 の定義 (App.A ?)
  → A ∈ SCN_2(P) sufficient (SCN_3 ⊆ SCN_2 + rank ≥ 3)
  → A satisfies Hyp 7.1
  
- **Step 2**: Thm 7.2 (m(Z(A)) ≥ 3 + Hyp 7.1)
  → K acts transitively on H_G^*(A;q) ∀q ∈ p'

### FT での役割

**決定的**: §8, §9, §10-§13 全体で最頻出. 特に:
- **§8 L2466**: "By (8.11) and the Thompson Transitivity Theorem (Theorem 7.6), H_G^*(A;q) contains a unique element"
- **§9-§13**: maximal subgroup の core structure を determine する際, A ∈ SCN_3(p) → transitivity → singleton 結論

---

## 記法 ℳ, 𝒰, SCN_3(p), ℋ_H(A;π) の Lean 実装方針

### ℳ (maximal subgroup の族)

```lean
def maximal_subgroups (G : Type*) [Group G] := {M : Subgroup G | IsMaximal M}
notation:50 "ℳ" => maximal_subgroups
```

### 𝒰 (unique-maximal-override subgroup)

```lean
def U_set (G : Type*) [Group G] : Set (Subgroup G) :=
  {H : Subgroup G | H < ⊤ ∧ ∃! M ∈ maximal_subgroups G, H ≤ M}
notation:50 "𝒰" => U_set
```

### SCN_3(p) (strongly closed normal abelian p-group with rank ≥ 3)

```lean
def SCN_3 (p : ℕ) (G : Type*) [Group G] [Fact (Nat.Prime p)] : Set (Subgroup G) :=
  {A : Subgroup G | 
    (∀ P : Sylow p G, A ∈ SCN_2 p P) ∧ -- A is in some SCN_2(P)
    (∃ P : Sylow p G, A ≤ P ∧ mingens A.card p ≥ 3)}
```

### ℋ_H(A;π) (A-normalize される π-subgroup 全体)

```lean
def H_pi (H : Subgroup G) (A : Subgroup G) (π : Finset ℕ) : Set (Subgroup H) :=
  {K : Subgroup H | A.normalize K ∧ ∀ p ∈ π, p ∣ K.card → False}

def H_pi_star (H : Subgroup G) (A : Subgroup G) (π : Finset ℕ) : Set (Subgroup H) :=
  {K ∈ H_pi H A π | ∀ K' ∈ H_pi H A π, K ≤ K' → K' = K}
```

### ℋ_H^*(A;q) (single prime specialization)

```lean
def H_q_star (H : Subgroup G) (A : Subgroup G) (q : ℕ) [Fact (Nat.Prime q)] : Set (Subgroup H) :=
  H_pi_star H A ({q}ᶜ : Finset ℕ)
```

---

## §8-§16 全章での Hypothesis 7.1 暗黙前提

### §8 (Fitting Subgroup of a Maximal Subgroup)

| 行範囲 | 引用 | 文脈 |
|--------|------|------|
| **L2348-2376** | Hyp 7.1 verify for A = C_F(A₀) | Thm 8.1 証明: maximal M に対して, A ∈ E_p^*(F(M)), m(A)≥3 ⇒ Hyp 7.1 証明する |
| **L2378** | Thm 7.2 apply (m(Z(A))≥3) | O_{π'}(C_G(A)) transitive on H_G^*(A;q) |
| **L2382** | Thm 7.4 apply | P ⊇ A ⇒ O_{π'}(C_G(P)) transitive, normalizer structure |

### §9-§13 (Uniqueness, Maximal Subgroup Analysis)

| 章 | 行範囲 | 引用 |
|-----|--------|------|
| **§9** | L2511, L2515 | Thm 7.6 (Thompson), Hyp 7.1 + Thm 7.4 via Thm 7.6 |
| **§10** | L2795-2801 | Thm 7.4 + Lem 6.6 chain (p-length 1 characterization) |
| **§11-§13** | L2937, L2944 | "the fundamental Thompson Transitivity Theorem (Theorem 7.6)" explicit mention |

### App.A (p-Stability)

- **Thm A.4(b)**: "P ∈ Syl_p(G) ⇒ every normal abelian ⊆ O_{p',p}(G)" **= odd-order version of Hyp 7.1 + Thm 6.2**
- Thm 7.2, 7.3, 7.4, 7.6 を odd-order context で specialize

---

## mathlib カバレッジ評価

| 概念 | mathlib | 新規実装 | Lean難度 |
|------|---------|----------|---------|
| **maximal subgroup (ℳ, IsMaximal)** | high | thin wrapper | 短 |
| **nonabelian simple group** | low | 定義既存, instances 要 | 短 |
| **elementary abelian p-subgroup (E_p^*(G))** | mid | Fintype.rank + coprime action | 中 |
| **Hall π-subgroup, π' complement** | high | `exists_subgroup_dvd`, SchurZassenhaus | 短 |
| **Thompson J-subgroup (J(P))** | **low (new)** | Phase 1 Ch.7 で実装予定 | **大** |
| **SCN_2(P), SCN_3(p)** | **low (new)** | Subgroup.NormalClosure + characteristic chain | **大** |
| **ℋ_H(A;π) (A-normalize subgroup)** | **low (new)** | Subgroup.stabilizer_of_coprime の拡張 | 中 |
| **Sylow theory + A-invariant Hall** | mid | mathlib Sylow, coprime action lemmas | 中 |
| **Frobenius action (Proposition 1.16)** | **low (new)** | Phase 1 Ch.3 で新規 | 中 |
| **Fitting subgroup F(G)** | low | Phase 1 Ch.2 で新規 | 大 |

**総合**: Phase 1 Ch.7 (J(P)) 完成 + Phase 1 Ch.6 (Frobenius) + §6 (p-length 1, Lem 6.5, 6.6) が prerequisites. 本身は **2-3 週** (import + wrapper).

---

## Phase 2a 形式化着手順

### 推奨順序 (§7 内)

1. **記法の形式化** (1-2 日):
   - ℳ, 𝒰 定義 (maximal, unique-override)
   - ℋ_H(A;π), ℋ_H^*(A;π) 定義 + basic API
   - Hypothesis 7.1 structure definition

2. **Lemma 7.1** (3-4 日):
   - **induction on order divisibility**
   - coprime action stabilizer (§6 Lem 6.5 application)
   - Sylow conjugacy + normalizer structure
   - *Most critical lemma; requires Lem 6.5/6.6 all parts*

3. **Theorem 7.2, 7.3** (2-3 日):
   - Prop 1.16 (elementary abelian characterization) import
   - C_G(z) centralizer application
   - Lem 7.1 chaining

4. **Theorem 7.4** (3-4 日):
   - Composition series reduction
   - Hall π-subgroup conjugacy (N_{KP} + solvable Hall theory)
   - Lem 6.5, 6.6 + Sylow induction chain

5. **Proposition 7.5** (2-3 日):
   - Case (1): Thm 6.7 application (p-length 1 → Hyp 7.1)
   - Case (2): SCN_2 definition + (7.4), (7.5), (7.6), (7.7) case split
   - *Requires App.A SCN definitions if available*

6. **Theorem 7.6** (1 日):
   - Prop 7.5 + Thm 7.2 chaining
   - Thompson Transitivity final statement

### 並列可能性

- **Group A**: Lem 7.1 (foundations)
- **Group B**: Thm 7.2, 7.3 (Lem 7.1 後)
- **Group C**: Thm 7.4 (Lem 7.1 + Lem 6.5/6.6 並行)
- **Group D**: Prop 7.5 (Thm 7.2 + App.A SCN 待ち)
- **Group E**: Thm 7.6 (final, trivial)

**推奨**: Group A (3-4 日) → Group B∥C (5-7 日) → Group D (2-3 日) → Group E (1 日)
= **計 11-15 日, 或いは 他セクション並列化で短縮可**.

---

## 下流被引用の詳細

### Thm 7.4 被引用 (FT critical)

| セクション | 行 | 引用パターン |
|-----------|-----|-----------|
| **§8** | L2382 | "By Theorem 7.4, [propagation of transitivity]" |
| **§9** | L2511-2515 | Thm 7.6 → Thm 7.4 chain (uniqueness theorem proof core) |
| **§10** | L2795-2801 | Thm 7.4 output (normalizer structure) in M_α/M_σ definition |

### Thompson Transitivity (Thm 7.6) 被引用

| 行 | 書籍位置 | 引用 |
|----|---------|------|
| **L2466** | §8 | "the Thompson Transitivity Theorem (Theorem 7.6), H_G^*(A;q) contains a unique element, say, Q. Thus N_G(A) normalizes Q" |
| **L2850** | §8 Thm 8.1(b) | "By Proposition 7.5, A satisfies Hypothesis 7.1" → Thm 7.6 apply |
| **L2937** | §10 | "the fundamental Thompson Transitivity Theorem (Theorem 7.6)" explicit mention in theorem context |
| **L2944** | §10 Prop 10.2 | "By Proposition 7.5, the subgroup A satisfies Hypothesis 7.1" → "Lemma 7.1 shows Q₂=Q₁^k" |

---

## Phase 1 依存関係確定

### Phase 1 Ch.7 (Thompson J-subgroup) 完成の必須性

**Lemma 7.1, Thm 7.2-7.6 は logically J(P) の定義に依存しない**が, 下流 §8-§16 で J(P) normality (Thm 6.2 = Isaacs Thm 7.6) が全体に浸透. したがって:

**順序**:
1. Phase 1 Ch.7 (J(P), J(P) ⊴ C_G(Z(J(P))), p-stability) → 完成
2. Phase 1 Ch.6 (Frobenius, Proposition 1.16) → 完成
3. BG §6 (Lem 6.5, 6.6, Thm 6.7) → 完成
4. **↑ ここまで**
5. **BG §7 着手可能** (§6 prerequisites all met)

### SCN_2, SCN_3 定義の前提

- **SCN_2(P)** (strongly closed normal abelian in P): Subgroup.NormalClosure + characteristic property
  - BG mmd 内での定義は Lemma 5.1 (L1789-1968, §5 Narrow p-Groups) に implicit
  - **Phase 2a §5 完成時に定義必須** or Prop 7.5 proof で局所定義

- **SCN_3(p)** (SCN_2 に rank ≥ 3 条件): L2137, L2311 で登場
  - Prop 7.5, Thm 7.6 の前提
  - Phase 2a 着手時点で App.A (p-stability) から import 予定 or 局所定義

---

## 未解決 / TODO

| 項目 | 状態 | 確認先 |
|------|------|--------|
| **SCN_2(P), SCN_3(p) 完全定義** | TBD | mmd L1789-2000 (§5) + App.A check; Definition 5.1 vs Prop 7.5 notation align |
| **Proposition 1.16 (elementary abelian characterization)** | TBD | Phase 1 Ch.3 (Frobenius) 完成待ち → Lem 7.1, Thm 7.2 proof で多用 |
| **App.A p-stability Thm A.4(b)** | TBD | "P ∈ Syl_p(G) ⇒ every normal abelian ⊆ O_{p',p}(G)" statement 完全形式化 (Hyp 7.1 variant) |
| **§7 内 proof 詳細** | TBD | Lem 7.1 induction base case, Prop 7.5 case (2) の (7.4)-(7.7) calc (mmd L2265-L2307 長い) |
| **Notation alignment** | TBD | ℋ_H(A;π) の `H_H` prefix convention (BG vs Isaacs) |

---

## 付録: SCN_2 / SCN_3 chain の理解

### Background (App.A 参照予定)

**SCN_p(G)** = "Subgroups of Centralizer Normal in G": A ⊆ Z(P) normal in G, contained in one Sylow p-subgroup など複数の strong closure 条件.

**BG での specialization**:
- **SCN_2(P)**: A ⊴ P, A abelian, A strongly closed (∀ g ∈ G, A^g ∩ P = A)
- **SCN_3(P)**: SCN_2 + min-gen(A,p) ≥ 3 (elementary abelian rank ≥ 3)

### §7 での use

1. **Prop 7.5**: A ∈ SCN_2(P) ⇒ Hyp 7.1 sufficient condition
2. **Thm 7.6**: A ∈ SCN_3(p) ⇒ Thompson transitivity direct (Prop 7.5 + Thm 7.2)
3. **§8 Thm 8.1**: SCN_3(P) elements が F(M) に contained (maximal M)

---

## Summary: Phase 2a §7 の位置付け

**§7 = Phase 2a 第 3 波の開端**. §1-§6 (Elementary + Additional) 完成後, §7 で **最小反例 G を确定し, その maximal subgroup structure を §8-§16 で分析する stage を open**. Hypothesis 7.1 + Lemma 7.1 + Thompson Transitivity (Thm 7.6) が全後続章の **隠れた前提枠組み** (implicit logical scaffolding).

形式化難度は **中** (per-result induction + coprime action) だが, 関連定義 (SCN, ℋ notation, maximal subgroup family) が §1-§6 の延長で複合化. 特に Lem 7.1 の inductive argument が FT 全体で最重要の推移性原理 (transitivity lemma).

---

*作成: 2026-05-22*
*出典: `references/bg/local-analysis.mmd` lines 2131-2314 (§7 全文)*
*クロス参照: `notes/bg/_overview.md` (overview), `notes/bg/s06_additional.md` (§6 dependent), `notes/isaacs/ch07_thompson.md` (Phase 1 J(P))*

