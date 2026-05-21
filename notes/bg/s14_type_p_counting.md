# BG §14: Type 𝒫 + Counting Arguments — mini-roadmap

**スコープ**: BG §14 (pp.105-116 in PDF), mmd L3744-4085, **7 主定理**.
**形式化先 (予定)**: `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean`
**ROADMAP 上の位置**: Phase 2a 第 5 波（Ch.III §10-§13 完成必須）
**役割**: 
- Type 𝒫 maximal subgroup の詳細構造と相互作用
- σ-分解と σ-length による G の分割
- counting argument による共役類構造の制御
- §15 (M_F) と §16 (Main Results) への橋渡し

---

## TL;DR — Type 𝒫 family の数え上げ完全理論

§14 は **§13 の "proper prime action" を逆転させた視点**: 単一の maximal subgroup M ∈ ℳ_𝒫 ではなく，**ℳ_𝒫 という family 全体** を調査. 

**キーコンセプト**:
- **σ-分解**: π(G) の各素数が異なる M ∈ ℳ に属するため，任意の g ∈ G は一意に g = g₁⋯gₛ（互いに交換可能な σᵢ-元）と分解.
- **σ-length ℓ_σ(g)**: この分解における単位元でない因子の個数. **Corollary 14.10** で ℓ_σ(g) ≤ 2 を証明（最重要結果）.
- **Theorem 14.7**: ℳ_𝒫 が空でなければ **正確に 2 つの共役類** M, M* を持ち，それらは「互いに dual」.
- **Theorem 14.9**: G# = disjoint union of 𝒞_G(Ẑ) ∪ ∪ᵢ 𝒞_G(M̃ᵢ)（counting formula）.

**Phase 2a 全体への影響**: 
- ℓ_σ(g) ≤ 2 は G の「階層化」を完成. §15-§16 の global structure へ.
- Type 𝒫₁ vs 𝒫₂ の区別が，Frobenius group と三段グループの分離に直結.

---

## §14 全 7 主定理（表）

| # | 名前 | mmd 行 | 形式 | 簡述 | 重要性 |
|---|------|--------|------|------|--------|
| 14.1 | Lemma 14.1 | 3768-3772 | Lemma + Proof | M ∈ ℳ - ℳ_𝒫₁ ⇒ |A| ≤ p², C_M_σ(A)=1, M_σ nilpotent | **基盤** |
| 14.2 | Proposition 14.2 | 3778-3807 | Proposition (7 部分) + Proof | M ∈ ℳ_𝒫: K (κ(M)-Hall), K* = C_M_σ(K), prime action & abelian Hall complement | **MAIN** |
| 14.3 | Corollary 14.3 | 3809-3824 | Corollary (2 case) + Proof | x ∈ M_σ#, x' ∈ σ(M)'-element: κ(M) と τ₂(M) の分岐 | **diagnostic** |
| 14.4 | Theorem 14.4 | 3826-3861 | Theorem (6 部分) + Proof | ℓ_σ(x)=1 ⇒ C_G(x) が R(x) を normal Hall に持ち，sharply transitively on ℳ_σ(x) | **CRITICAL** |
| 14.5 | Lemma 14.5 | 3875-3886 | Lemma (3 部分) + Proof | x, y の σ-length 1 元, M₁, M₂の非共役性: disjoint property と counting base | **combinatorial** |
| 14.7 | Theorem 14.7 | 3890-3991 | Theorem (8 部分) + Proof | M ∈ ℳ_𝒫 ⇒ exactly 2 conjugacy classes in ℳ_𝒫; Z = K×K* cyclic; Ẑ is TI-set | **CENTRAL** |
| 14.9 | Corollary 14.9 | 3997-4006 | Corollary (2 case) + Proof | G# = disjoint union decomposition by ℓ_σ | **structural** |

**補助定理**: Lemma 14.6 (missing page), 14.11 (Frobenius type), 14.13 (Theorem 14.4 extension).
**推論**: Corollary 14.8 (ℳ_𝒫₁ の共役性), 14.10 (ℓ_σ(g) ≤ 2), 14.12 (M ∈ ℳ_𝒫₂ time H ∈ ℳ_ℱ).

---

## σ-分解と σ-length

### 定義（§14 冒頭, L3744-3759）

**σ(M) 族の分割性**:
```
π(G) の前提（§13 Theorem 13.9）:
- σ(M) ∩ σ(H) = ∅  (M, H ∈ ℳ, M ≠ H)
- すべての p ∈ π(G) は何らかの σ(M) に属す
⇒ {σ(M₁), ..., σ(Mₛ)} は π(G) の partition
```

**σ-分解**:
```
σ₁, ..., σₛ = σ(M₁), ..., σ(Mₛ) (共役類の代表)

任意の g ∈ G に対し，一意に
  g = g₁ ⋯ gₛ  (gᵢ は σᵢ-元, 互いに交換可能)
```

**σ-length**:
```
ℓ_σ(g) := この分解における gᵢ ≠ 1 の個数

例: g ∈ M_σ の場合，g = g_i (i のみ)，故に ℓ_σ(g) = 1.
```

### ℳ_σ(X) と σ-length の関係

```
ℳ_σ(X) := {M ∈ ℳ : X ⊆ M_σ}

Key observation:
- ℓ_σ(g) ≤ 1 ⟺ ℳ_σ(g) ≠ ∅
- Theorem 14.4: ℓ_σ(g) = 1 ⇒ C_G(g) が ℳ_σ(g) に transitively on する
```

---

## Type 𝒫 分類: κ(M) と 𝒫₁ vs 𝒫₂

### κ(M) の定義（L3760-3762）

```
κ(M) := {p ∈ τ₁(M) ∪ τ₃(M) : ∃ P ∈ ℰ_p¹(M), C_M_σ(P) ≠ 1}

直感: M_σ が「p-作用に応答」する素数
```

### Type 𝒫 family の分割（L3762）

```
ℳ_𝒫 := {M ∈ ℳ : κ(M) ≠ ∅}  (proper prime action)

さらに分割:
ℳ_𝒫₁ := {M ∈ ℳ_𝒫 : κ(M) = π(M) - σ(M)}
ℳ_𝒫₂ := {M ∈ ℳ_𝒫 : κ(M) ≠ π(M) - σ(M)}

ℳ_ℱ := {M ∈ ℳ : κ(M) = ∅}  (Frobenius type)
```

**物理的意味**:
- **𝒫₁**: M の κ-作用が「最大」（π(M) - σ(M) 全体）
- **𝒫₂**: κ が strict subset（例: U ≠ 1 in Proposition 14.2(g), σ(M) = β(M)）
- **ℱ**: κ が空（Frobenius 型）

---

## Proposition 14.2: Type 𝒫 の完全構造

**主張** (7 部分, L3778-3807):

M ∈ ℳ_𝒫 に対し，K を Hall κ(M)-subgroup, K* := C_M_σ(K) とする:

1. **Prime action + abelian complement**:
   - K は prime manner で M_σ に作用
   - U = Hall (κ(M) ∪ σ(M))'-subgroup が K-regular
   - UM_σ は M における K の normal complement

2. **Normalization property**:
   - 各 X ∈ ℰ¹(K): N_M(X) = N_M(K) = K × K*
   - 各 X ∈ ℰ¹(K): X ⊆ M*_σ for all M* ∈ ℳ(N_G(X))

3. **Centralization**:
   - K* ≠ 1
   - 各 X ∈ ℰ¹(K*): ℳ(C_G(X)) = {M}

4. **Disjointness**:
   - g ∈ G - M ⇒ K* ∩ M^g = 1
   - g ∈ M - (K × K*) ⇒ K ∩ K^g = 1

5. **Sylow subgroup control**:
   - 各 p ∈ π(K*), S = Sylow p-subgroup of M_σ:
   - ℳ(S) = {M}, S ⊄ K*

6. **σ(M)-subgroup embedding**:
   - Y ≠ 1 なる σ(M)-subgroup で Y ∩ K* ≠ 1 ⇒ Y ⊆ M_σ

7. **Type 𝒫₂ case (U ≠ 1)**:
   - σ(M) = β(M)
   - K has prime order q
   - M_σ is nilpotent TI-subgroup of G

**証明概要** (L3789-3807):
- E, E₁, E₂, E₃ を Lemma 12.1 の形で構成
- (a)(b): Corollary 13.11 or 13.5 により prime action 確立
- (c): Lemma 13.13, 13.6 から K* の構造
- (d)(e)(f): Theorem 10.1, Corollary 12.16 など局所結果の global synthesis
- (g): Frobenius group 構造と β(M) = σ(M)

---

## Theorem 14.4: σ-length 1 元の中心化と transitive action

**主張** (6 部分, L3826-3861):

x ∈ G#, ℳ_σ(x) ≠ ∅ とする:

**Case A** (|ℳ_σ(x)| = 1):
- R(x) = 1

**Case B** (|ℳ_σ(x)| ≥ 2):
- ∃ unique N(x) ∈ ℳ:
  1. R(x) := C_N_σ(x) is normal Hall in C_G(x), sharply transitive on ℳ_σ(x)
  2. C_G(x) = (C_M∩N(x) (x)) R(x)
  3. π(⟨x⟩) ⊆ τ₂(N) ⊆ σ(M)
  4. π(M) ∩ σ(N) ⊆ β(N)
  5. M ∩ N is complement of N_σ in N
  6. **(D. Sibley)** N ∈ ℳ_ℱ ∪ ℳ_𝒫₂

**証明の構図** (L3837-3861):
- M ∈ ℳ_σ(x), q ∈ π(⟨x⟩), X ∈ ℰ_q¹(⟨x⟩) を取る
- N ∈ ℳ(N_G(X)) とし R(x) := C_N_σ(x)
- Theorem 13.9, 10.1(b) により C_G(X) が ℳ_σ(X) に transitive
- Proposition 12.15 で q ∈ τ₂(N) 確立
- κ(N) ⊆ τ₁(N) ∩ τ₃(N) 故に N ∉ ℳ_𝒫₁
- C_N_σ(x) の作用が R(x) を sharply transitive に確定

---

## Theorem 14.7: Type 𝒫 family の duality と TI-set

**主張** (8 部分, L3890-3991):

M ∈ ℳ_𝒫, K = Hall κ(M)-subgroup, K* = C_M_σ(K), Z := K × K*, Ẑ := Z - (K ∪ K*):

1. ∃ unique M* ∈ ℳ_𝒫 not conjugate to M:
   - ℳ(C_G(X)) = {M*} for all X ∈ ℰ¹(K)

2. K* is Hall κ(M*)-subgroup of M*; also Hall σ(M)-subgroup of M*

3. K = C_M*_σ(K*), κ(M) = τ₁(M)

4. **Z is cyclic**; for x ∈ K#, y ∈ K*#:
   - M ∩ M* = Z = C_M(x) = C_M*(y) = C_G(xy)

5. **Ẑ is TI-set**: N_G(Ẑ) = Z, Ẑ ∩ M^g = ∅ (g ∈ G-M),
   - |𝒞_G(Ẑ)| = (1 - 1/k - 1/k* + 1/(kk*)) |G| > (1/2)|G|
   - (k = |K|, k* = |K*|)

6. M or M* lies in ℳ_𝒫₂; accordingly K or K* has prime order

7. **Every H ∈ ℳ_𝒫 is conjugate to M or M***

8. M' is complement of K in M

**証明の梗概** (L3901-3991):
- M₀ = M, M₁ = M* とし，M_i ∈ ℳ(N_G(X_i)) (X_i ∈ ℰ¹(K)) とする
- σ(M), σ(M_i) の disjointness (Theorem 13.9) で K* が σ(M_i)'-subgroup
- Proposition 14.2 により K_i* (Hall κ(M_i)-subgroup の centralizer) 群を詳細に控除
- Z = K₀* × K₁* × ⋯ × K_n* の factorization を確立
- T := Z - ∪K_i* が TI-subset，Lemma 14.6 で ℒ_σ に disjoint
- 計数を |G#| に対して行い，ℳ_𝒫₁ only では矛盾（|G#| < |G|）導出
- 故に some M_i ∈ ℳ_𝒫₂，n = 1 として (b)-(d) 確定
- (g): H ∈ ℳ_𝒫 に対し S = L* × L** (Hall のpair) を同様に構成，𝒞_G(T), 𝒞_G(S) の overlap から conjugacy conclude

**重大な帰結**:
- ℳ_𝒫 ≠ ∅ ⇒ exactly 2 conjugacy classes (Corollary 14.8)
- ℳ_𝒫 = ∅ ⇒ G is "Frobenius-like" (only ℳ_ℱ)

---

## Corollary 14.9 & Corollary 14.10: 完全分割と σ-length 上界

**Corollary 14.9** (L3997-4006):

M₁, ..., M_n ∈ ℳ を各共役類代表とする:

1. ℳ_𝒫 = ∅:
   - G# = ⊔ᵢ 𝒞_G(M̃ᵢ)

2. ℳ_𝒫 ≠ ∅ (M, M* as in Theorem 14.7):
   - G# = 𝒞_G(Ẑ) ⊔ ⊔ᵢ 𝒞_G(M̃ᵢ)

**Corollary 14.10** (L4008-4010):

```
∀ g ∈ G: ℓ_σ(g) ≤ 2
```

**重要性**: これは **entire odd-order group の σ-階層化の完成**. §15-§16 では，ℓ_σ ≤ 2 が Frobenius group と三段グループの「高さ」制御に用いられる.

---

## Counting argument の手法

### 基本原理（§14 中盤, L3754-3867）

**集合 𝒞_G(X)**:
```
𝒞_G(X) := {x^g : x ∈ X, g ∈ G}  (conjugacy class set, from Section 1)

for X ⊆ G:
  |𝒞_G(X)| = |X| · |G : N_G(X)|  (if X is 𝒞_G-connected)
```

**σ-分解に基づく分割**:
```
Lemma 14.5(a): x, y ∈ G#, ℓ_σ(x) = ℓ_σ(y) = 1, x ≠ y
            ⇒ xR(x) ∩ yR(y) = ∅

Lemma 14.5(b): M₁, M₂ ∈ ℳ non-conjugate
            ⇒ M̃₁ ∩ M̃₂ = ∅

Lemma 14.5(c): |𝒞_G(M̃)| = (|M_σ| - 1) |G : M|
```

### Theorem 14.7 の計数（L3935-3975）

**Setup**:
- Z = K × K* に対し，Z = K₀* × K₁* × ... × K_n* （via Hall subgroup な factorization）
- T = Z - ∪K_i* ("bad" elements，σ-分解で ≥ 2 factors）

**計算**:
```
|T| · |G : Z| = (1 + n/z - Σ(1/k_i)) |G|

where z = |Z|, k_i = |K_i|
```

**背理法**:
```
Assume all M_i ∈ ℳ_𝒫₁ (K_i complement in M_iσ)
Then:  |G#| ≥ |𝒞_G(T)| + Σ |𝒞_G(M̃_i)|
             ≥ (1 + n/z - Σ(1/k_i))|G| - (n+1)/(2z)|G| + Σ(1/k_i)|G|
             ≥ |G|

This contradicts |G#| = |G| - 1 since G non-trivial.
```

**結論**: Some M_i ∈ ℳ_𝒫₂，n = 1，Z cyclic.

### TI-set と final counting（L3971-3975）

```
Ẑ := Z - (K ∪ K*)

|𝒞_G(Ẑ)| = (1 - 1/k)(1 - 1/k*)|G|
           ≥ (1 - 1/3)(1 - 1/5)|G|
           = (2/3)(4/5)|G|
           = (8/15)|G|
           > (1/2)|G|
```

**意義**: Ẑ は「ほぼ全体」を覆うため，ℳ_𝒫 の各メンバーは M or M* に共役でなければならない.

---

## §15 (M_F) と §16 (Main Results) への橋渡し

### 前置: ℳ_ℱ と Frobenius type

**Corollary 14.12** (L4035-4055, M ∈ ℳ_𝒫₂ の場合):

H ∈ ℳ(N_G(R)) (R = Sylow r-subgroup of U) に対し:
- H ∈ ℳ_ℱ
- U ⊆ H_σ
- M ∩ H = UK
- H ∩ M* は H における H_σ の complement

**Lemma 14.13** (L4059-4083, Theorem 14.4 extension):

ℳ_σ(x) に |ℳ_σ(x)| > 1 かつ σ(N) ∩ π(M) ≠ ∅:
- M ∈ ℳ_ℱ, τ₂(M) = ∅
- M is Frobenius group with kernel M_σ

### §15 での使用パターン

§15 では:
- Theorem 14.4 による R(x) の Hall 性で，C_G(x) の「normal form」を確定
- Corollary 14.9 の分割により，各元が M̃_i or Ẑ に属することを分類
- Corollary 14.10 (ℓ_σ ≤ 2) で，G/M_σ (if defined) が solvable with restrictions を推導

### §16 での使用パターン

§16 (Main Results) では:
- Theorem 14.7(g) (exactly 2 conjugacy classes in ℳ_𝒫) と Theorem 14.9 を統合
- G が Frobenius group or three-step group（in FT sense）か判定
- ℓ_σ ≤ 2 により，「height 3」の構造制御と final contradiction へ

---

## mathlib カバレッジ

### 既存 Lean 実装状況

**§10-§13 の準備**:
- `GroupTheory.Sylow`: Sylow p-subgroup
- `GroupTheory.Nilpotent`: nilpotent group, Hall subgroup
- `GroupTheory.GroupAction`: conjugacy action
- `GroupTheory.CommutatorSubgroup`: derived series, lower central series
- `GroupTheory.PGroupClass`: p-group rank, Sylow p-group properties

**§14 特有**:
- **missing**: π(G) の partition 構造（σ(M) partition）
- **missing**: σ-分解（g = g₁⋯gₛ の unique factorization）
- **missing**: σ-length ℓ_σ
- **missing**: ℳ_σ(X) family
- **missing**: κ(M) and Type 𝒫₁, 𝒫₂ classification
- **missing**: R(x) (normal Hall subgroup of C_G(x))
- **missing**: TI-subset (trivial intersection set)
- **missing**: 𝒞_G(X) (conjugacy orbit, already Section 1)

### Form化実装の方針

1. **σ-分解の axiomatic 定義**:
   ```lean
   def sigma_decomposition (g : G) : List G :=
     -- g = g₁ ⋯ gₛ, mutual commute, σᵢ-elements
   
   def sigma_length (g : G) : ℕ :=
     (sigma_decomposition g).filter (· ≠ 1) |>.length
   ```

2. **Type 𝒫 family の predicate**:
   ```lean
   def kappa (M : Subgroup G) : Set (Primes G) := ...
   def is_type_P (M : Subgroup G) : Prop := kappa M ≠ ∅
   def is_type_P1 (M : Subgroup G) : Prop := 
     is_type_P M ∧ kappa M = π(M) - σ(M)
   def is_type_P2 (M : Subgroup G) : Prop := 
     is_type_P M ∧ ¬is_type_P1 M
   ```

3. **Theorem 14.7 の formalization**:
   - Duality: ∃! M* : ℳ_𝒫 s.t. "mutually determining"
   - Z = K × K* is cyclic
   - Ẑ is TI-subset

4. **Counting arguments**:
   - Finite combinatorics on conjugacy classes
   - |𝒞_G(Ẑ)| > (1/2)|G| calculation

---

## Phase 2a 形式化着手順

### Wave 5 (Current: §14)

**形式化タイムライン**:

1. **L1 (2-3 days)**: σ-分解と σ-length の公理的定義
   - unique factorization property の証明
   - Corollary 14.10 (ℓ_σ ≤ 2) に向かう

2. **L2 (3-4 days)**: Proposition 14.2 の細部
   - K, K* の role separation
   - 7 parts の順序的証明

3. **L3 (4-5 days)**: Theorem 14.4 (σ-length 1 の centralizer)
   - R(x) の Hall 性
   - Sharply transitive action

4. **L4 (5-7 days)**: Theorem 14.7 (duality + counting)
   - Z factorization
   - TI-set construction
   - Counting formula

5. **L5 (2 days)**: Supporting results
   - Lemma 14.11 (Frobenius type application)
   - Corollary 14.12 (M_𝒫₂ + H ∈ ℳ_ℱ)
   - Lemma 14.13

### Wave 6 (§15 M_F family)

Prerequisite: Wave 5 完全

### Wave 7 (§16 Main Results)

Prerequisite: Wave 5, 6 完全

---

## 未解決 / TODO

### 理論的未確認

- [ ] **Lemma 14.6 の詳細**（missing page due to PDF scan），mmd で確認必須
  - Ẑ ∩ M̃ 相互作用
  - ℓ_σ ≤ 2 への直接的寄与

- [ ] **Corollary 14.8** (ℳ_𝒫₁ の共役性) の finer structure
  - 𝒫₁ が non-empty の場合，all members conjugate?
  - 𝒫₂ と 𝒫₁ の mutual exclusivity

### mathlib integrations

- [ ] `TrivialIntersectionSubgroup` (TI-subset) の formalization
- [ ] Finite partition on π(G) の general theory
- [ ] Conjugacy orbit 𝒞_G(X) の combinatorics

### 形式化リスク

- **Counting argument の computational verification**: |𝒞_G(Ẑ)| > (1/2)|G| を Lean で直接計算可能か？
  - Likely: Finite module で可（但し， |G| を制約する必要）

- **Duality M ↔ M* の functorial interpretation**: Theorem 14.7 の"unique"性を圏論的に表現可能か？
  - Likely: Bijection via kernel-image-style lemma

---

## 参考資料と外部リンク

- **BG 原書**: Gorenstein, Finite Groups, §14 (pp. 105-116)
- **FT 対応箇所**: Feit-Thompson, Solvable Groups, §27-§28 (p-length control)
- **周辺セクション**:
  - §10-§13: M_σ の定義から Type 𝒫 の確立まで
  - §15: M_F (Frobenius) family の詳細
  - §16: Main Results (Theorems A-E)

---

## ロードマップチェックリスト

- [x] §14 全 7 主定理の抽出と表化
- [x] Type 𝒫 定義の精密化（κ(M), 𝒫₁ vs 𝒫₂）
- [x] σ-分解と σ-length の conceptual groundwork
- [x] Theorem 14.4 (σ-length 1) の役割確認
- [x] Theorem 14.7 (duality + counting) の梗概
- [x] §15-§16 への「橋」の明示化
- [x] mathlib カバレッジ分析と missing components
- [x] Phase 2a Wave 5 形式化タイムラインの作成
- [ ] **Lemma 14.6** の PDF scan 確認（次セッション推奨）
- [ ] Corollary 14.8 の細部 review

