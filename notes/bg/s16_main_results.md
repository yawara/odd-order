# BG §16: The Main Results — per-section 調査ノート (Phase 2a 終結)

> ## ❄ FROZEN (2026-07-02)
> **Prop 16.1 + Thm D/E/I/II landed** (sorry-free; wrapper/skeleton queue は完了 or moot)。
> 残 3 sorry = `theoremA_maximal_structure` / `theoremB_U_and_A_tame` / `aSets_support_slice` の
> overstatement 宣言 (do-not-prove-as-is、faithful variant あり = memory [[ft-settled-findings]])。
> 以下は履歴。
>
> **2026-07-15 更新**: bare `theoremA_maximal_structure` overstatement は consumer 0 を再確認後に
> 宣言ごと retire。canonical Theorem A は
> `theoremA_maximal_structure_faithful`。残る `theoremB_U_and_A_tame` /
> `aSets_support_slice` は引き続き frozen legacy surface であり、faithful APIs を使用する。

**スコープ**: BG §16 "The Main Results" (pp.123-134, mmd L4256-4449).
**結果数**: Theorem A-E の 5 個の主要定理 + Theorem I, II + Proposition 16.1 (基礎補題, 型分類を統合).
**形式化先** (予定): `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean`.
**ROADMAP 上の位置**: **Phase 2a 第 5 波（終結）**. §15 M_F 完成必須. 完成後 Phase 2b Peterfalvi §10 入力.
**役割**: BG 局所解析の最終結論。最小反例 G の最大部分群構造の完全刻画. App.C (最終矛盾) へ橋渡し.

---

## TL;DR — Theorem A-E が最小反例 G の局所構造の最終形

§16 は Theorems A--E で最大部分群の局所構造を再包装し、Proposition 16.1 と Theorems I--II で Type I--V / character-theory interface へ渡す最終統合章。

**FT 構造**:
- **Theorem A** (8 条件): M_σ（σ-部分群）と κ-部分群 K の基本構造
- **Theorem B** (5 条件): U の Sylow と A(M)-M_σ の TI 性質
- **Theorem C** (11 条件, K ≠ 1 時): K* (centralizer) と paired maximal M*
- **Theorem D** (4 条件 + recovered tail): M_σ の共役性 + R(x) normal complement/action + escaping centralizer の Type I/II landing
- **Theorem E** (3 条件): `\widetilde M = ⋃ xR(x)` の counting、`σ(M_i)` の `π(G)` 分割、`G#` の covering

**Proposition 16.1**: M の Type (I, II, III, IV, V) 分類と A-E の対応を統合的に述べる重要補題. M_F = M_σ ⟺ Type I, II, V を確立.

**Theorem I, II** (pp.129-136): FT Chapter IV Theorems 14.1, 14.2 の直接翻訳.
- Theorem I: G の nilpotent Hall subgroup の共役性 (Burnside theorem 精密版)
- Theorem II: A(M), A_0(M) の "tamely imbedded subset" 性質 (TI-subset 一般化)

---

## §16 全体構成（pp.123-134, mmd L4256-4449）

### Part 1: 導入 + 記号定義（pp.123-124, L4256-4288）

**L4256-4259**: 冒頭解説
- BG 局所解析 vs FT CN-定理との平行性の説明
- Theorem A-E が FT Thm 14.1, 14.2 の一般化であることの摘示
- 本章の位置付け: character theory に向けた基盤形成

**L4260-4262**: M_F の定義と M_σ との関係
```
M = arbitrary maximal subgroup of G
M_F = largest nilpotent normal Hall subgroup of M
    (= M の中の Fitting subgroup の Hall part)
M_σ = normal Hall subgroup on σ(M)-primes
特に CN-case では M_F = M_σ (ほぼ常に一致)
```

**L4264-4267**: Prime set σ(M), κ(M) の定義
```
σ(M) = {p ∈ π(M) | ∃ (∀) Sylow p-subgroup P of M with N_G(P) ⊆ M}
       (M の Sylow normalizer が M に含まれる素数)
κ(M) = {p ∈ π(M) - σ(M) | Sylow p-subgroup P cyclic ∧ ∃x ∈ P# s.t. C_{M_σ}(x) ≠ 1}
       (σ(M) の complementary primes で cyclic Sylow かつ M_σ-centralizer 非自明)
```

**L4268-4270**: A(M), A_0(M) 記号 + ℳ(X) 記号
```
ℳ(X) = {maximal subgroups of G containing X}
𝒞_Y(X) = {x^y | x ∈ X, y ∈ Y}  (conjugates by Y)
```

### Part 2: Theorem A-E (pp.124-129, L4274-4388)

#### **Theorem A** (L4274-4283) — 8 条件、最大部分群の基礎構造

```
1. M has unique normal Hall σ(M)-subgroup M_σ
   ∧ M_σ is σ(M)-Hall subgroup of G (not just M)
2. M has cyclic Hall κ(M)-subgroup K
3. ∃ K-invariant complement U in M s.t. UM_σ ◁ M = KUM_σ
   ∧ U ◁ UK
4. C_U(k) = 1 for all k ∈ K#  (U is fixed-point-free for K action)
5. K* = C_{M_σ}(K) ≠ 1 ∧ (K ≠ 1 ⟹ C_M(k) = K × K* for k ∈ K#)
6. 1 ⊂ M_F ⊆ M_σ ⊆ M' ⊂ M ∧ M'/M_F is nilpotent
7. M'' ⊆ F(M) = C_M(M_F)·M_F ∧ (K ≠ 1 ⟹ F(M) ⊆ M')
8. M_F ≠ M_σ ⟹ U = 1, F(M) is TI-subset, K has prime order
```

**要点**:
- (1)-(2): σ, κ-Hall subgroup の一意性と cyclic 性
- (3)-(4): K ⋊ U の semidirect product; U は K-fixed-point-free
- (5): K* (centralizer in M_σ) の存在と centralizer の product structure
- (6)-(7): derived series と Fitting subgroup の layering
- (8): M_F ≠ M_σ のときの極端化 (U = 1, K prime order)

**型分類への橋渡し**:
- **Case 𝓕**: K = 1, U ≠ 1 (Frobenius-like)
- **Case 𝓟₁**: K ≠ 1, U = 1 (prime-cyclic complement)
- **Case 𝓟₂**: K ≠ 1, U ≠ 1 (prime ⊗ general complement)

#### **Theorem B** (L4295-4314) — 5 条件、U と A(M) の TI 性質

```
1. Every Sylow subgroup of U is abelian of rank ≤ 2
2. ⟨U ∩ Ĥ_{M_σ}⟩ is abelian
   (where Ĥ_{M_σ} = {a ∈ M | C_{M_σ}(a) ≠ 1})
3. ∃ U_0 ⊆ U (exp(U_0) = exp(U)) s.t. U_0 ∩ Ĥ_{M_σ} = 1
4. ℳ(C_G(X)) = {M} for every non-trivial X ⊆ U with C_{M_σ}(X) ≠ 1
   (centralizer localization: U と M_σ の coupling により M unique)
5. A(M) - M_σ is TI-subset of G
   (with normalizer M)
```

**要点**:
- (1)-(2): U の Sylow structure の制約と abelian subgroup の一致
- (3): U の exponent-preserving subgroup で M_σ-centralizer が trivial
- (4)-(5): **Character theory 準備**: U の centralizer localization + A(M) の global embedding

#### **Theorem C** (L4303-4315) — 11 条件、K ≠ 1 時の paired structure

```
Assume K ≠ 1. Then:
1. U is abelian ∧ N_G(U) ⊄ M
2. K* is cyclic, 1 ⊂ K* ⊆ M_F, M_F not cyclic
3. M' = UM_σ ∧ K* ⊆ M''
4. ∃! M* ∈ ℳ_𝓟 s.t. K = C_{M*}(K*) ∧ K* is Hall κ(M*)-subgroup
5. ℳ(C_G(X)) = {M}, ℳ(C_G(Y)) = {M*}
   for all subgroups X ⊆ K*, Y ⊆ K of prime order
6. M ∩ M* = Z = K × K*, which is cyclic
7. M or M* is of type 𝓟₂ ∧ every H ∈ ℳ_𝓟 conjugate to M or M*
8. Ẑ = Z - (K ∪ K*) is TI-subset with N_G(Ẑ) = Z
9. 𝒞_M(Ẑ) = A_0(M) - A(M) is TI-subset of G
10. U ≠ 1 ⟹ K prime order ∧ F(M) is TI-subset containing M_σ
11. U = 1 ⟹ K* prime order
```

**要点**:
- (1)-(3): K ≠ 1 時の M, M' の structure、K* (= paired centralizer) の存在
- (4)-(6): **Paired maximal M* (dual structure)**: K と K* の role reversal
- (7)-(9): **TI-subset covering**: Z, Ẑ の global embedding
- (10)-(11): U 存在・非存在時の type 分化

#### **Theorem D** (L4317-4368) — 4 条件、M_σ の共役性と R(x) normalizer

```
1. Whenever two elements of M_σ are conjugate in G, they are conjugate in M
2. For g ∈ G - M: M_σ ∩ M^g = M_σ ∩ M_σ^g is cyclic
3. For x ∈ M_σ#: C_M(x) is Hall subgroup of C_G(x) ∧
   ∃ R(x) ◁ C_G(x) acting sharply transitively on {M^g | x ∈ M^g}
4. If x ∈ M_σ# ∧ C_G(x) ⊄ M, then C_G(x) lies in unique maximal N = N(x) of G:
   R(x) = C_{N_σ}(x), N_σ = N_F
   x ∈ A(N) - N_σ, N ∈ ℳ_𝓕 ∪ ℳ_{𝓟₂}
   M ∩ N complements N_σ in N
   if N ∈ ℳ_{𝓟₂}, then M ∈ ℳ_𝓟, M is Frobenius with cyclic complement, and M_F is not TI
```

**要点**:
- (1)-(2): M_σ の (G, M) conjugacy + cyclic intersection property
- (3): **Thompson R(x) subgroup**: normalizer action on maximal cosets
- (4): **Centralizer localization** — C_G(x) ⊆ unique maximal (Type I or II)

#### **Theorem E** (L4370-4388) — `\widetilde M` counting and `σ` partition

```
For each x ∈ M_σ#, take R(x) from Theorem D and define
  \widetilde M = ⋃_{x∈M_σ#} xR(x).

1. |𝒞_G(\widetilde M)| = (|M_σ| - 1)|G:M|.
2. If M_i represent maximal-subgroup conjugacy classes, then π(G) is the
   disjoint union of the σ(M_i).
3. The union of the 𝒞_G(\widetilde M_i) is disjoint; it covers G# when
   ℳ_𝓟 is empty, and otherwise G# is the disjoint union of that union and
   𝒞_G(Ẑ) for M ∈ ℳ_𝓟.
```

Lean status: `theoremE_sigma_partition_and_counting` now records these three clauses.
The older `aSets_support_slice` remains as a separate Peterfalvi-facing A(M)/A_0(M) support surface, not as a replacement for Theorem E.

---

### Part 3: Type 定義 (pp.125-128, L4327-4349)

#### **π* 定義** (L4330)

```
π* = {p ∈ π(G) | Sylow p-subgroup P of G is
  cyclic or contains A of order p with C_P(A) = A × B, B cyclic}
```

**意義**: Frobenius-compatible prime set (Lemma 10.13 参照)

#### **Proposition 16.1** (L4352-4398) — 型分類の統合

```
(a) M Type I ⟺ M ∈ ℳ_𝓕
(b) M Type II ⟺ M ∈ ℳ_{𝓟₂}
(c) M Type III or IV ⟺ M ∈ ℳ_{𝓟₁} ∧ M_F ≠ M_σ
(d) M Type V ⟺ M ∈ ℳ_{𝓟₁} ∧ M_F = M_σ
(e) M' = UM_σ ⟺ M not Type I
(f) M_F = M_σ ⟺ M Type I, II, or V
```

**証明構造** (L4356-4398):
1. L4360: ℳ_𝓕 (K=1, U≠1) ⟹ Type I (Thm B(1)-(3) + Thm 15.7(c))
2. L4362-4362: Type I but not ℳ_𝓕 ⟹ K*=C_H(K)≠1 ⟹ contradiction (condition Iiii)
3. L4364-4374: ℳ_𝓟 (K≠1) ⟹ M'=UM_σ, W_1=K, W_2=K*, Type II-V conditions (Ti)-(T6) ✓
4. L4384-4392: Type II/III/IV/V の case 分け (M_σ=H vs not, U=1 vs ≠1, N_G(V) condition)

**FT での使用**: Prop 16.1 の (a)-(f) が §17-§24 の型別分析の出発点.

#### **Type I** (Frobenius-like, L4331-4337)

```
Definition:
1. 1 ⊂ H ⊂ M  (H = M_F non-trivial)
2. Each complement E to H in M contains abelian A s.t. C_E(x) ⊆ A for all x ∈ H#
3. Each complement E has E_0 (exp E_0 = exp E) s.t. HE_0 Frobenius with kernel H
4. Every Sylow of M/H abelian rank ≤ 2
5. (At least one of):
   (5a) H TI-subset in G
   (5b) H abelian rank 2
   (5c) ∀p ∈ π(H): p ∈ π* ∧ exp(M/H) | (p-1); ∃p s.t. O_{p'}(M) cyclic
```

#### **Type II, III, IV** (L4340-4348)

```
Common (T1)-(T6):
(T1) M' is Hall subgroup containing H
(T2) ∃ nilpotent V ◁ M' (complement to H) with N_M(V) cyclic W_1 of order |M/M'|
(T3) H not cyclic ∧ M'' ⊆ F(M) ⊆ M'
(T4) ∃ cyclic W_2 ⊆ H with C_{M'}(x) = W_2 for x ∈ W_1#
(T5) ∀ non-empty W_0 ⊆ W - (W_1 ∪ W_2): N_G(W_0) = W (W = W_1 × W_2)
(T6) ∀ prime order A_0, A_1 conjugate in G but not M: C_H(A_0)=1 or C_H(A_1)=1

Type II (T7-II):
(i) W_1 prime order
(ii) F(M) = C_M(H)·H is TI-subset of G
(iii) V abelian rank ≤ 2
(iv) V ≠ 1 ∧ N_G(V) ⊄ M
(v) ∀ non-empty A ⊆ M' with C_H(A)≠1: N_G(A) ⊆ M

Type III (T7-III):
(iii) V abelian ∧ N_G(V) ⊆ M

Type IV (T7-IV):
(iii) V not abelian ∧ N_G(V) ⊆ M
```

#### **Type V** (L4347)

```
Type 𝓟 + V = 1:
(T1)-(T6) ∧ (∀ M/M' cyclic W_1) ∧ M' = H
(At least one of):
(Va) H TI-subset
(Vb) ∃p ∈ π(H) ∩ π*: O_{p'}(H) cyclic, |W_1| | (p-1)
(Vc) ∃p ∈ π(H) ∩ π*: O_{p'}(H) cyclic, |O_p(H)| = p³, |W_1| | (p+1)
```

---

### Part 4: 主定理 (pp.129-136, L4400-4436)

#### **Theorem I** (L4402-4410) — Nilpotent Hall 共役性 + Type dichotomy

```
Theorem I:
(i) Two elements of a nilpotent Hall subgroup H of G are conjugate in G
    ⟺ they are conjugate in N_G(H)

Either every maximal subgroup of G is Type I, or all of:
1. ∃ cyclic W = W_1 × W_2 s.t. N_G(W_0) = W for non-empty W_0 ⊂ W - W_1 - W_2
   ∧ W_i ≠ 1
2. ∃ maximal S, T (not Type I) with:
   S = W_1 S', T = W_2 T', S' ∩ W_1 = 1, T' ∩ W_2 = 1, S ∩ T = W
3. Every maximal is conjugate to S, T, or Type I
4. S or T is Type II
5. Both S, T Type II, III, IV, or V
```

**意義**: 
- (i) Burnside theorem の solvable 推定 (Corollaries 15.3, 15.4)
- (ii) Case (a): Type I-only → §14 で矛盾
- (ii) Case (b): S, T paired structure → §11-§15 で矛盾

#### **Theorem II** (L4416-4435) — A(M), A_0(M) の "tamely imbedded subset"

```
Theorem II (FT 14.2):
For M maximal, X ∈ {A(M), A_0(M)}, D = {x ∈ X# | C_G(x) ⊄ M}:

(Ti) Conjugate elements in X are conjugate in M

(Tii) If D ≠ ∅:
  ∃ maximal subgroups M_1,...,M_n of Type I or II with H_i = M_{iF}:
  (a) (|H_i|, |H_j|) = 1 for i ≠ j  (coprime Fitting)
  (b) M_i = H_i(M ∩ M_i) ∧ M ∩ H_i = 1
  (c) (|H_i|, |C_M(x)|) = 1 for x ∈ X#  (coprime centralizer)
  (d) A_0(M_i) - H_i is non-empty TI-subset with N_G(·) = M_i
  (e) ∀x ∈ D, ∃ conjugate y ∈ D, ∃i: C_G(y) = C_{H_i}(y) C_M(y) ⊆ M_i

(Tiii) If some M_i Type II, then M Frobenius (Type I) with cyclic complement
       ∧ M_F not TI-subset of G
```

**意義**:
- (Ti): M_σ の共役性 (Thm D(1))
- (Tii): **Supporting subgroup system** (M_1,...,M_n) の存在・性質
- (Tiii): **Frobenius obstruction** (M_i Type II ⟹ M Type I)

---

## §1-§15 からの結論統合経路

### Dependency chain

```
§1 (Solvable Hall)
 ├─→ §2 (Representations)
 ├─→ §3 (Frobenius Actions) ─┐
 ├─→ §4 (Rank ≤ 2 p-groups)   │
 └─→ §5 (Narrow p-groups) ────┼──→ §6 (Additional) [normal-J]
                              │        ↓
                         App.A (p-Stability)
                              │
                    ┌─────────┴─────────┐
                    ↓                   ↓
                §7 (Transitivity)  [Thm 6.2 引用]
                    ↓
                §8 (Fitting) ───→ §9 (Uniqueness)
                    ↓                 ↓
              §10-§11 (M_α, M_σ, Exceptional)
                    ↓
              §12-§13 (E, Prime Action)
                    ↓
              §14 (Type 𝒫 counting)
                    ↓
              §15 (M_F) ────────────┐
                                   ↓
                          ★ §16 (Main Results)
                              ↓
                          App.C + Peterfalvi §9
                              ↓
                          [最終矛盾]
```

### 各 Theorem が依拠する章

| Theorem | 前提結果 | 章 | 概要 |
|---------|--------|------|------|
| **A** | Thm 15.2 (M_F characterization) | §15 | M_F ⊆ M_σ ⊆ M' の layering |
| **A** | Thm 6.2 (normal-J) | §6 | Sylow normalizer 性質 (FT critical) |
| **A** | §3, §4, §5 | Ch.I | Frobenius + rank small p-group structure |
| **B** | Thm A | §16 | A-E の sequence |
| **B** | §13 (Prime Action) | §13 | U の Sylow structure control |
| **C** | Thm A, B | §16 | K ≠ 1 時の M, M* paired characterization |
| **C** | Prop 16.1, Thm 15.7(c) | §15, §14 | Type 𝓕, 𝓟 分類の基礎 |
| **D** | Thm A, B, C | §16 | M_σ の global conjugacy property |
| **D** | Thm 6.2 (normal-J via R(x)) | §6 | Normalizer stabilizer R(x) |
| **E** | Lemma 14.5(c), Theorem 13.9, Corollary 14.9 | §14/§13 | `\widetilde M` counting, `σ` partition, `G#` covering |
| **I** | Cor 15.3, 15.4 | §15 | Nilpotent Hall subgroup の normality |
| **II** | Thm B(5), C(9), D(4) | §16 | TI-subset supporting subgroup system |

### FT critical path

**§6 Thm 6.2** が §8, §9, App.A で 7+ 回引用される **最重要ボトルネック**:
- L2456, L2478, L2482: §8 Fitting subgroup
- L2511, L2515: §9 Uniqueness
- App.A Thm A.4, App.B, App.C: 後続理論

**Phase 2a 完了条件**:
1. §15 M_F 完成 ✓
2. App.A p-Stability (normal-J 証明根拠) ✓
3. Thm 6.2 import from Isaacs Ch.7 ✓

---

## Peterfalvi §10 (Type I-V) との対応（詳細）

### (8.11) Sylow normalizer theorem と Theorem A

**BG Theorem A(1)**: M_σ is σ(M)-Hall subgroup of G
↓ restate in Peterfalvi notation ↓
**Peterfalvi (8.11)**: Non-trivial Sylow P of M_s ⇒ N_G(P) ⊆ M (M_s = M_F for Type I,II,V)

**Formalization strategy**:
- BG: σ(M) = {p | ∃ Sylow p of M with N_G(P) ⊆ M}
- Peterfalvi: M_s as the Fitting key → Sylow structure via Type
- **Bridge**: Prop 16.1(f) で M_F = M_σ (Type I, II, V) を確立 → (8.11) は特例

### (8.12) Type I, II Sylow property と Theorem B

**BG Theorem B(1)-(5)**:
- Every Sylow of U abelian rank ≤ 2
- A(M) - M_σ is TI-subset
↓ ↓
**Peterfalvi (8.12)(a)-(c)**:
- Sylow of U abelian rank ≤ 2
- A(M) - A_1(M) is TI-subset
- Unique maximal containing C_G(X) for X ⊆ U with C_H(X) ≠ 1

### (8.13) Theorem [主定理 II] と Theorem D

**BG Theorem D**:
- M_σ conjugacy in M
- M_σ ∩ M^g cyclic
- R(x) = C_{N_σ}(x) normalizer action
- N(x) Type I or II
↓ ↓
**Peterfalvi (8.13)(c1)-(c4)**:
- C_G(x) = C_{L_F}(x) × C_M(x) (direct product decomposition)
- x ∈ A(L) - A_1(L)
- L Type I or II

**Key equation**: BG Theorem D(4) statement ≡ Peterfalvi (8.13.c)

### (8.8) Theorem (Case dichotomy) と Theorem C

**BG Theorem C** (K ≠ 1):
- M' = UM_σ
- K* ⊆ M_F cyclic
- ∃! M* paired with M
- Type II ∨ Type III,IV,V mixture
↓ ↓
**Peterfalvi (8.8) Case (b)**:
- ∃ cyclic W = W_1 × W_2, S, T maximal
- S ∩ T = W
- S Type II ∨ S,T Type II,III,IV,V

---

## App.C ("The Final Contradiction") との橋渡し

### 構造的位置付け

**BG App.C (L4759-5005)**: Peterfalvi 1984 paper の改訂版 (Carlip-Wheeler)

**歴史ライン**:
1. FT 1963 Ch.VI: generator-relation argument (17 ページ、非常に複雑)
2. Peterfalvi 1984 paper: 大幅簡略化 (Steward action / Frobenius family)
3. BG App.C: Peterfalvi 論文の再編解説版
4. Peterfalvi 本体 §9: **同一証明をさらに進化させた版** (coherence 活用)

**論理的内容**:

| 部分 | BG App.C | Peterfalvi §9 | 役割 |
|------|---------|-------------|------|
| **Main Theorem C** | "p ≤ q for Frobenius F_{p^q} family" | (9.1)-(9.8) Non-existence | G が存在しない最終矛盾 |
| **Lemma C.1** | Steward action 性質 | (9.9)-(9.14) 補題群 | Character support 制限 |
| **Lemma C.2** | p, q の order 関係 | (9.15)-(9.20) | Sylow normalizer control |
| **Peterfalvi 独自** | — | (9.21)-(9.33) Coherence + §15 統合 | さらに詳細な character 分析 |

### Phase 3 での統合方針

**Option 1** (BG 中心):
- OddOrder/BG/AppC_FinalContradiction.lean を実装
- Peterfalvi §9 notation を BG 경로 위에 embed
- 장점: BG 일관성 유지
- 단점: Peterfalvi 고유 기술 (coherence) 손실

**Option 2** (Peterfalvi 중심):
- OddOrder/Peterfalvi/S09_NonExistence.lean을 메인
- BG App.C는 추가 참고 문헌 (cross-reference docstring)
- 장점: Peterfalvi 체계 완전성
- 단점: 이중 형식화 비용

**推奨**: **Option 2 (Peterfalvi 중심)** — Phase 2b で Peterfalvi §9 완료時점에 App.C 동시 형식화. BG App.C는 docstring으로만 언급.

---

## Phase 3 (최종結合) 에서 BG §16 + Peterfalvi 의 역할

### Phase 3a: Global classification unification

**BG §16 Theorem A-E** の output:
- G の maximal subgroup の 5 type 分類 ✓
- Type I-V の detailed structure ✓
- M_σ の global embedding + supporting subgroup system (Theorem II) ✓

**Peterfalvi §10-§16** の input:
- BG Theorem A-E を再구성 (8.11)-(8.13) ✓
- **§11-§15 への독립적 분석 진행**:
  - §11: Type II, III, IV 의 character 방정
  - §12: Type V, [S,S] Frobenius family
  - §13: Type III, IV 의 kernel structure
  - §14: Type I 최상세 분석
  - §15: S, T paired 구조의 character property

**결합점**: Peterfalvi §15 (S, T subgroups) 에서 BG Theorem C, I, II 를 **character theory 관점에서 재논증**. S ∩ T = W 의 cyclic 성질 + character support 의 mutual exclusion.

### Phase 3b: Contradiction completion

**최종 矛盾 체인**:
```
BG §16 Theorem I, II (maximal dichotomy + supporting subgroup)
    ↓ (Peterfalvi §14 입력)
Peterfalvi §10-§15 (Type I-V character analysis)
    ↓ (Case (a): Type I-only OR Case (b): S,T mixed)
Case (a): Type I maximal characterization → character degree 제약 → 矛盾
Case (b): S, T support mutual exclusion → S ∩ T = W cyclic compatibility 불가 → 矛盾
    ↓
Peterfalvi §9 + BG App.C (Frobenius family non-existence)
    ↓
[최종 FT 矛盾 도출]
```

---

## mathlib カバレッジ (§16 레벨)

### 新規実装 (Lean 4 없음 부분)

| 개념 | mathlib status | 필요 구현 | 추정 비용 |
|------|---------------|----------|----------|
| **Theorem A-E statement** | 없음 | BG §16 notation (~M_σ, σ(M), κ(M), A(M)) + 5 theorem restate | 5-7 일 |
| **Proposition 16.1** | 부분 (Prop 확장만) | Type I-V 분류의 inductive 정의 + 동치 증명 | 3-4 일 |
| **Theorem I (conjugacy)** | 부분 (Burnside base) | Corollary 15.3, 15.4 import + solvable 정밀화 | 2 일 |
| **Theorem II (TI subset)** | 없음 | "Supporting subgroup system" predicate + tamely imbedded characterization | 4-5 일 |
| **Type I-V classification** | 없음 (Peterfalvi와 중복) | Peterfalvi S10 과 통합된 inductive type 정의 | 4 일 |

**합계**: §16 단독 형식화 **18-25 일**, 단 **Peterfalvi §10 과 동시진행 시 10-12 일** (공유구현 활용).

### 사전 요구사항 (Phase 2a 필수)

1. **§15 M_F 완성** (OddOrder.BG.Ch4.S15)
   - M_F characterization (Theorem 15.2)
   - M_F ⊆ M_σ, M_F is Hall π(H) subgroup

2. **§6 Theorem 6.2 구현** (OddOrder.Isaacs.Ch7 import)
   - Z(J(S))·O_{p'}(G) ⊴ G
   - Thompson J-subgroup + normal subgroup forming

3. **App.A (p-Stability)** (prerequisite to §6)
   - Theorem A.4(b): every normal abelian subgroup of P ⊆ O_{p',p}(G)
   - p-stability predicate

---

## Phase 2a 형식化 着手順 (§16 전용)

### Week 1: Theorem A 정의 + 조건들 형식화

```lean
-- OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean

namespace BG.Ch4.S16

-- σ(M), κ(M) 정의
def sigma_primes (M : Subgroup G) : Set ℕ :=
  {p ∈ primeFactors (Nat.card M) |
   ∀ P : SylowSubgroup p M, (P.normalizer : Set G) ⊆ M}

def kappa_primes (M : Subgroup G) : Set ℕ :=
  {p ∈ primeFactors (Nat.card M) - sigma_primes M |
   (∀ P : SylowSubgroup p M, Nat.card P = p ∨ Cyclic P) ∧
   ∃ x ∈ P.nonbot, (Subgroup.centralizer x M_σ).nontrivial}

-- Theorem A 조건
structure TheoremA_Structure (M : Subgroup G) where
  -- 조건 1-8: M_σ unique, K cyclic κ-Hall, U complement, ...
```

### Week 2: Theorem B, C 형식化 + supporting subgroup notation

### Week 3: Proposition 16.1 (type classification) 증명

### Week 4: Theorem D (M_σ conjugacy) + Theorem I, II 

### Week 5: Integration + Peterfalvi S10 alignment testing

---

## 미해결 사항 및 TODO

### 1. recovered §16 page gap

**Status**: resolved in `references/bg/local-analysis.mmd` at L4366--4388. The recovered text contains the Theorem D(4) tail and the full Theorem E statement.

**Lean status**: `S16_MainResults.lean` exposes the recovered D(4) tail and a named `theoremE_sigma_partition_and_counting` endpoint. Remaining work is proof filling from Lemma 14.5(c), Theorem 13.9, and Corollary 14.9, not source recovery.

### 2. App.A (p-Stability) 의존성

**현상**: Thm 6.2 증명이 App.A 를 참고함

**해결책**: 
- Phase 2a 중 App.A 부터 형식화
- 그 후 §6 Thm 6.2 구현
- 또는 Isaacs Ch.7 Theorem 7.6 직접 import (권장)

### 3. Type 𝓕 의 Frobenius API 통합

**문제**: Type 𝓕 정의가 BG App.A + Peterfalvi §10 에서 중복 등장

**해결책**: Peterfalvi S10 형식화 시점에 공동 설계

### 4. Theorem II ("tamely imbedded subset") 의 증명

**상태**: BG 문장만 제시, 상세 증명은 pp.136 onwards

**조치**: Phase 3 에서 Peterfalvi §14-15 통합 시 complete (§16 단계에선 statement restate 만)

### 5. Peterfalvi 통합 시점

**현재 계획**: Peterfalvi S10 과 BG S16 을 **병렬 형식화** (ROADMAP 상 같은 주차)

**교정 필요**: 
- Peterfalvi mmd 재검토 (notation 정확성)
- BG notation → Peterfalvi notation 변환표 작성

---

## 관련 섹션 및 파일 참고

### BG 본체 내 링크

| 節 | 파일 | 주요 내용 |
|----|------|---------|
| §15 M_F | notes/bg/s15_subgroup_mf.md | M_F 특성화 (§16 직입) |
| §14 Type 𝒫 | notes/bg/s14_maximal_type_p.md | Type 분류 기초 |
| §13 Prime Action | notes/bg/s13_prime_action.md | E subgroup control |
| §6 Additional | notes/bg/s06_additional.md | Thm 6.2 (normal-J critical) |

### Peterfalvi 연계

| 節 | 파일 | 상관관계 |
|----|------|---------|
| §10 | notes/peterfalvi/s10_structure_minimal_simple.md (削除済, git履歴) | **직접 input** (8.11)-(8.13) ≡ Thm A-E |
| §11-§15 | notes/peterfalvi/s11-s15_type_analysis.md (예정) | §16 Theorem I,II 입력 |
| §9 | notes/peterfalvi/s09_non_existence.md | App.C 통합 |

### Isaacs 역참조

| Chapter | 개념 | §16 사용 |
|---------|------|---------|
| Ch.2 | Fitting subgroup | M_F 정의 |
| Ch.7 | Thompson J(S) | Thm 6.2 (normal-J) |

---

## 결론: Phase 2a 종료점으로서 §16 의 위상

**§16 은 BG 국소해석 전체의 최종정리 및 Peterfalvi 로의 교량** 역할:

1. **국소해석 완성** (§1-§15): maximal subgroup structure 의 완전 분류
2. **지표론 준비** (§16 output): Type I-V classification = Peterfalvi §10-§15 입력
3. **모순유도 시작** (Phase 3): Theorem I,II + supporting subgroup system → Peterfalvi §14-15 에서 character 분석 → 최종 모순

**mathlib 관점**: 
- Type 분류 + supporting subgroup 시스템은 **새로운 추상** (완전 새 구현)
- Theorem A-E 는 **BG 특화 지역분석 결과** (현지화, generalize 곤란)
- Phase 3 에서 Peterfalvi 와 합친 후에야 **일반적 유한군론 API 후보** 로 평가 가능

**推奨 형식化 순서**:
1. App.A (p-Stability) — Isaacs Ch.7 기초
2. §6 (Additional) — Thm 6.2 import or restate
3. § 7-§15 — 통상의 의존 체인
4. **§16 + Peterfalvi §10 병렬** — notation 공동설계
5. Peterfalvi §11-§15 + BG App.C — Phase 3 준비

---

*작성: 2026-05-22*  
*출전: `references/bg/local-analysis.mmd` L4256-4449 (pp.123-134)*  
*연계: BG _overview.md (L43), Peterfalvi s10_structure.md, ROADMAP Phase 2a*  
*다음 단계: Phase 2a 제 5 파 개시 시 App.A → §6 → §7-§15 → §16 순차 형식화*

---

## 2026-06-18 (lane G): Prop 16.1 type-`P` data construction layer — engine + bridges DONE

**landed (commit `1a4ccfd9`, `S16_MainResults`, all sorry-free + axiom-clean, AxiomsCheck 5 decls):**
the shared `TypePData` construction layer feeding the three type-`P` forward bridges
(`hP2II`/`hP1neIIIIV`/`hP1eqV`) of `proposition_type_classification`.  Analogous to
`typeFData_of_kappa_eq_bot` for type I (the F→I core).

1. `normalizer_eq_sup_of_isTISubset_of_isCyclic` — the genuine `normalizer_V` reduction
   (Peterfalvi (8.4)): for cyclic `W = W₁⊔W₂` and `V = W∖(W₁∪W₂)` `TI` relative to `W`, every
   nonempty `X ⊆ V` has `N_G(X) = W`.  `≤ W` from `IsTISubset` (`mem_set_normalizer_iff''` lands a
   conjugate of `a∈X⊆V` back in `V`); `≥ W` from abelianness of the cyclic `W` (`IsCyclic.commGroup`
   + `congrArg Subtype.val (mul_comm …)`).  **Pure group theory, unconditional** — reusable.
2. `typePData_of_inputs` (`def`) — assembles the 20-field `TypePData M` from the BG-local
   structural facts as **18 named §14/§15 hypotheses** (gated-endpoint pattern).  Derives inside:
   `W_eq` (defn `W := W₁⊔W₂`), `W1_cyclic`/`W2_cyclic` (`Subgroup.isCyclic_of_le` on cyclic `W`),
   `normalizer_V` (the reduction above).
3. `isTypeIII_or_IV_of_typePData` / `isTypeII_of_typePData` / `isTypeV_of_typePData` — type-specific
   last-mile packers.  III/IV is the clean part of `hP1neIIIIV` (decidable `IsMulCommutative ↥U`
   split, no deep gate); II holds `derived_typeF : IsTypeF (M')` + `derived_fitting_eq` as named
   residuals; V holds the Peterfalvi-(8.8) `alternative` trichotomy as a named residual.

### the next deep unit = the `typePData` WRAPPER (BG-σ ↔ Peterfalvi-H-U structural bridge)

To **discharge** the forward bridges (not just isolate them), a wrapper `typePData (hG hM hP …) :
TypePData M` must supply `typePData_of_inputs`' 18 hypotheses by citing the (sorried) §14/§15
results, with `H = M_F`, `W₁ = K`, `W₂ = K*`, `U = ?`.  **Field-provenance map** (verified
citable unless flagged):

| field | source | note |
|---|---|---|
| `H_eq` | `H := MF M`, `rfl` | `MF M = maxNilpotentNormalHall M` defn |
| `H_le` (M_F ≤ M') | `maxNilpotentNormalHall_le_derived` | chain M_F ≤ M_σ ≤ M' |
| `W1_le` (K ≤ M) | `hKM` | |
| `W2_le` (K* ≤ M_F ⊓ M'') | `typeP_kstar_in_mf` (K*≤M_F, K*≤M'') | |
| `W_cyclic` (K⊔K* cyclic) | `typeP_duality` | |
| `W1_nontrivial` (K≠⊥) | from `IsTypeP` (κ≠∅) | check exact lemma |
| `W2_nontrivial` (K*≠⊥) | `typeP_structure` (14.2c) / `typeP_kstar_in_mf` | |
| `M_complement` | `typeP_duality` part (h) | |
| `U_nilpotent` | `typeP_auxiliary_structure` conj5: U abelian ⟹ nilpotent | (K≠⊥) |
| `hTI` (zTilde TI) | `typeP_duality` (`IsTISubset (zTilde K K*) (K⊔K*)`) | matches `V` defn-eq |
| `centralizer_W1` (M'∩C(K#)=K*) | ⚠ **needs verification** — C_{M'}(K#)=K* identity | |
| `secondDerived_le_fitting` / `fitting_eq` / `fitting_lt_derived` | `mf_ne_msigma_typeP1_structure` (P1) | M_σ=M', F(M)=Q⊔(C(Q)⊓M), M_F<M' |
| `H_noncyclic` (¬cyclic M_F) | `typeP_kstar_in_mf` (last conj) | |
| **`U_le` / `U_normal` / `derived_complement`** | ⚠⚠ **the deep bridge** | see below |

**⚠⚠ key open subtlety (the genuine (8.x) content):** Peterfalvi's `derived_complement` is
`M' = H · U = M_F · U_pf` (internal complement of `M_F` in `M'`), but BG's σ-decomposition gives
`M' = U_bg ⊔ M_σ` (`typeP_auxiliary_structure` conj5, `U_bg` = the Hall `(κ∪σ)'`-complement).
Since **M_F ⊊ M_σ for type P₁** (`MF M ≠ Msigma M`), the two complements differ: `U_pf ≠ U_bg`.
Peterfalvi's `U` is a complement of `M_F` (not `M_σ`) in `M'`, so the wrapper must either
(a) construct `U_pf` (a Schur–Zassenhaus complement of the Hall-normal `M_F` in `M'`) and re-derive
`U_normal`/`U_le`, or (b) find a BG result giving the `M' = M_F U` form directly.  This is the deep
structural assembly Prop 16.1 is built on — NOT a quick citation.  **Recommend** resolving (a)/(b)
before attempting the wrapper; the engine + bridges above are already in place to receive it.
(Corrected mis-reading: the ordering is `M_F ≤ M_σ ≤ M' ≤ M`, NOT `M_σ ⊆ M_F`;
`maxNilpotentNormalHall_le_Msigma` S15:161.)

residual modest skeleton queue (lower value, §14-independent): `theoremA/C/E/aSets _of_inputs`
(bare sorry → named residual; F already did D / II-conj1 / A-ungated / B(1) / sigma-disjoint).


## 2026-06-18 (lane G, session #3) — POLE-1 connect + option-1 forward half

- ✅ **`section16MaximalPair_of_isMinimalSimpleOdd` sorry-free** (`FeitThompson.lean`, commit
  `651a2bae`): Pf 8.8 dichotomy case(b) via `Exists.choose` + case(a) all-Type-I 排除 (Pf 12.17
  `theorem88_caseB_holds` + 新補題 `not_isTypeI_of_isTypeNonI` = Prop 16.1 の系). lane-g §16 が初の
  FT spine 実 consumer に. 実 sorry 141→140. (issue 8014 closed.)
- ⚠ **`kappa_join_kstar_le_pair_inf` (forward inclusion) は除去済** (commit `48f4eb04` で一旦着地→
  本セッションで削除): lane-f が **full 等式 `typeP_pair_inf_eq : M ⊓ M* = K ⊔ K*`**
  (`S16_PairIntersection.lean:73`, BG Thm 14.7(4)/C(6)/I(2)) を landing し (main `1a09c4b7`)、forward を
  **インライン再導出** (`hfwd`, S16_PairIntersection:93-94) したため、私の forward 補題は consumer-0 の
  dead code に. CLAUDE.md 「維持負担のみの重複は書かない」方針で削除 (AxiomsCheck 登録も撤去).
  **⟹ option-1 の clause 復活は `typeP_pair_inf_eq` (full 等式) を直接 cite する.**
- **option-1 残作業 (lane-f landing 済 → unblock)**: `typeP_pair_inf_eq` を使い
  `theoremI`/Pf 8.8 に `W = S ⊓ T` clause 復活 + `Section16MaximalPair` に `W`/`W_eq_inter` field 追加
  (struct 変更ゆえ **要 hub/user 承認**) → typeP producer (`section16TypePStructure`, lane-f) dischargeable に.

### 2026-06-18 (lane-f 再開) — option-1 clause 復活 LANDED + tp producer gate 確定

- ✅ **`theoremI` の `S ⊓ T = W` clause 復活 LANDED** (`536974a9`): `typeP_pair_inf_eq` (gap B) を
  `theoremI_nilpotentHall_conjugacy_and_type_dichotomy` の type-P-pair 枝に配線 (partner bundle を
  typeP_duality から抽出 + `(κ∪σ)'`-Hall U を Hall 定理で構成)。sorry-free、full build 3860 green。
  consumer `maximalSubgroup_type_dichotomy` (S10:113) は `_hWinter` 1 個追加で透過 (W-data drop は不変)。
  `S16_MainResults` が `S16_PairIntersection` を import (cycle 無し)。**gap B が terminal でなくなった。**
- ❌ **`Section16MaximalPair` enrich + tp producer discharge は absent theory に bottom-out**
  (フィージビリティ監査, issue 7005)。上の「typeP producer dischargeable に」は**不成立**: tp は
  `W=W₁×W₂` で W₁/W₂ **両素数位数** (q<p) を要求し「W cyclic」より真に強い。enrich しても mp producer
  構成段で同じ gate に落ちる (relocate-not-resolve)。真の gate:
  - (a) **対の素数位数 P₁ 側** — `isTypeP2_kappaHall_prime` (S14:1555) は P₂ のみ;
  - (b) **`q_lt_p`** — ABSENT (Pf (13.2)(a)←(10.10)/(11.9) char-theoretic = lane-b 上流);
  - (c) **`W₁_normalizes_U`** + U/V (13.1)(b) semidirect — ABSENT (Pf「remark following Def (8.4)」=§8)。
  ∴ lane-f を tp 固定は非生産的。(a)(b)(c) は独立 issue で scope 推奨 (hub 判断、issue 7005「推奨」参照)。
