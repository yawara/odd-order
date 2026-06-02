# BG §8: The Fitting Subgroup of a Maximal Subgroup — mini-roadmap

**スコープ**: BG §8 (pp.61-63), mmd L2315-2485, **1 結果** (Theorem 8.1) + 内部補題群.
形式化先 (予定): `OddOrder/BG/Ch2_Uniqueness/S08_FittingOfMaximal.lean`
ROADMAP 上の位置: **Phase 2a 第 3 波** (§7 完成必須)
役割: maximal subgroup M の Fitting subgroup F(M) 構造定理. **Thm 6.2 (normal-J) の最重要応用先**; Uniqueness Theorem (§9 Thm 9.1) の主要補題.

---

## TL;DR

§8 は **1 つの main theorem** 「maximal subgroup M が large (= rank(F(M)) ≥ 3) ⇒ F(M) の大規模部分群は U に属する」を証明する. **Thm 6.2 (Z(J(P))·O_{p'}(G) ⊴ G)** を **3 箇所** (L2456, L2478, L2482) で引用し、counterexample 引数による背理法で結論を導く. 内部番号付き式 (8.1)-(8.13) で補題群を展開. FT cliffhanger: Thm 8.1 終了直後のマーク（§8 vs. §9 の dichotomy remarks）は「π₃ (Frobenius normalizing p'-subgroup) vs. π₄ (その他 odd-rank primes) の分岐は FT 本文の prime partition と平行」を述べている.

---

## §8 全 1 結果 + 番号付き式一覧

| # | 種別 | mmd 行 | statement 要約 | 形式化難度 | FT 経路 | 被引用 |
|---|------|--------|---------------|-----------|--------|--------|
| **8.1** | **Thm** | **2319-2482** | M ∈ ℳ, m(A₀) ≥ 3 (A₀ ∈ E*_p(F(M))) ⇒ (a) F(M) not p-group ⇒ C_F(M)(A₀) ∈ U; (b) F(M) = p-group ⇒ P Syl_p(G), SCN₃(P) ⊆ F(M) ∧ U | **高** (case split, Thompson Thm 7.6 多用, Thm 6.2 × 3) | ☆ | **§9 L2533** (Thm 9.1 proof: "By Theorem 8.1, r(F(H))≤2") |

**計**: 1 main theorem, 13 内部補題式 (8.1)-(8.13).

### 内部補題式一覧

| 式 | mmd 行 | 内容 | 役割 |
|----|--------|------|------|
| **(8.1)** | 2330 | `Z(F) ⊆ C_F(A₀) = A ⊆ F` | proof (a) setup: π(A) = π(F) |
| **(8.2)** | 2334 | `C_G(A) ⊆ ... ⊆ N_G(Z(F)_q) = M` | key closure: A centralizer contained in M |
| **(8.3)** | 2346 | `C_G(A) is π-group` | proof (a): π'-elements eliminated by (8.2) + Prop 1.10, 1.3 |
| **(8.4)** | 2356 | `Y = [Y, A_q]` (Y π'-group A-invariant) | proof (a): Hyp. 7.1 setup for Y |
| **(8.5)** | 2366 | `A_r ⊆ O_{q'}(C_X(Z(F)_q)) ⊆ O_{q'}(X)` | proof (a): inductive O_π'(X) containment |
| **(8.6)** | 2388 | `H*_G(A;q) = {1}, q ∈ π'` | proof (a): q-subgroup exhaustion via Thm 7.4 |
| **(8.7)** | 2400 | `[D_q, O_{q'}(A)] = 1` | proof (a): Sylow compatibility in H ∈ M(A) |
| **(8.8)** | L2434 (implicit) | `O_{p'}(H) = O_{p'}(M)` | proof (a): final M-coincidence |
| **(8.9)** | L2455 (implicit) | Z(J(P)) ⊴ M (Thm 6.2 直接結果) | proof (b): Sylow structure normalization |
| **(8.10)** | 2458 | `A* ⊆ M, A* = O_{p'}(C_G(A))` | proof (b): π'-complement localization |
| **(8.11)** | 2464 | `O_{p'}(C_G(A)) = 1` | proof (b): F = p-group ⇒ π'-part annihilated |
| **(8.12)** | 2472 | `H_G(A;p') = {1}` | proof (b): uniqueness of p'-part for Thm 7.6 application |
| **(8.13)** | 2480 | `O_{p'}(H) = 1, Z(J(R)) ⊴ H` | proof (b): R = Syl_p(H), contradiction setup via Thm 6.2 |

---

## Theorem 8.1 詳細

### Statement (mmd L2319-2322)

```
仮定:
  M ∈ ℳ (maximal subgroup of minimal counterexample G)
  p ∈ π(F(M))
  A₀ ∈ E*_p(F(M)) (maximal elementary abelian p-subgroup of F(M))
  m(A₀) ≥ 3 (rank ≥ 3)
  P = Syl_p(M)

結論:
  (a) If F(M) is not a p-group, then C_F(M)(A₀) ∈ U
  (b) If F(M) is a p-group, then:
      - P is a Sylow p-subgroup of G
      - Every element of SCN₃(P) ⊆ F(M) ∧ ∈ U
```

### 証明構造

#### Part (a): F(M) not p-group

**Goal**: Show C_F(M)(A₀) ∈ U (= every maximal containing C_f(M)(A₀) equals M).

**Strategy**: Hypothesis 7.1 (Thompson Transitivity setup) を A = C_F(A₀) に対して verify → **Thm 7.2** (Thompson transitivity) で H*_G(A;q)単元化 → Frattini argument で M 一意性.

**Key steps**:
1. **(8.1)-(8.2)**: π(A) = π(F) 確認 + C_G(A) ⊆ M (Z(F)_q normalization).
2. **(8.3)-(8.5)**: C_G(A) は π-group; Hypothesis 7.1 verify via (8.4), (8.5) induction.
3. **(8.6)**: **Thm 7.2** + **(8.3)** ⇒ H*_G(A;q) = {Q} for each q ∈ π'. **Thm 7.4** (Fitting 遺伝性) で H*_G(F;q) = {Q}.
4. **Frattini**: Q ⊴ M, Q ⊆ F, Q ∈ O_q(M) but q ∈ π' ⇒ Q = 1. ∴ H*_G(A;q) = ∅, q ∈ π'.
5. **(8.7)-(8.8)**: ∀H ∈ M(A), F(H) ⊆ M (Sylow p-analysis via Prop 1.4, 1.15). π(F(H)) = π(F(M)) from (8.6).
6. **最終**: O_{p'}(H) = O_{p'}(M) ⇒ H = N_G(O_{p'}(M)) = M. ∴ A ∈ U.

**論理的依存**:
- Thm 7.2 (Thompson Transitivity)
- Thm 7.4 (Fitting 部分群遺伝)
- Prop 1.3, 1.4, 1.6, 1.15 (nilpotent group basic)

#### Part (b): F(M) = p-group

**Goal**: Show (i) P Syl_p(G), (ii) ∀A ∈ SCN₃(P), A ∈ U.

**Strategy**: Counterexample 背理法. H ∈ M(A), H ≠ M と仮定 → Sylow order maximality argument で R Syl_p(H) 固定 → **Thm 6.2** twice (L2478, L2482) で Z(J(R)) ⊴ H → **Thm 6.2** を normalizer に適用し M = N_G(Z(J(R))) = H 矛盾.

**Key steps**:
1. **(8.9)**: F = O_p(M) ⇒ **Thm 6.1** で A ⊆ F. **Thm 6.2** より Z(J(P)) ⊴ M. ∴ N_G(P) ⊆ M ⇒ P Syl_p(G).
2. **(8.10)-(8.11)**: A* = O_{p'}(C_G(A)) ⊆ M (by (8.9)), but A* ⊆ F (p-group, Prop 1.10, 1.3) ⇒ A* = 1.
3. **(8.12)**: q ∈ p', **Thm 7.6** (Thompson Transitivity) + **(8.11)** ⇒ H_G(A;q) = {1}. ∀Y ∈ H_G(A;p'), Y = 1 (nilpotent = solvable).
4. **Assume** H ∈ M(A), H ≠ M. R Syl_p(H∩M) ⊇ A. Maximize |H∩M|_p by H selection.
5. **(8.13)**: **Thm 6.2** on R ⇒ Z(J(R)) ⊴ H, O_{p'}(H) = 1.
6. **Final**: N_G(R) ⊆ N_G(Z(J(R))) = H (from (8.13)). But (8.9) ⇒ N_G(R) ⊆ M. ∴ M = H 矛盾.

**論理的依存**:
- Thm 6.1 (Hall-Higman: A ⊆ O_{p',p}(G))
- **Thm 6.2** (Z(J(P))·O_{p'}(G) ⊴ G) — **3 回引用** (L2456, L2478, L2482)
- Thm 7.6 (Thompson Transitivity)
- Prop 1.3, 1.4, 1.10, 1.15

---

## Thm 6.2 引用箇所の精密文脈

§8 は **Thm 6.2 の最高密度引用セクション** (3 箇所、各々 critical step).

### 引用 1: L2456 (Part (b) first application)

```
By (8.9) and Theorem 6.2, we know that Z(J(P)) ⊴ M. 
Consequently N_G(P) ⊆ N_G(Z(J(P))) = M. 
Hence P is a Sylow p-subgroup of G and A ∈ SCN₃(p).
```

**文脈**: Part (b) setup. F = O_p(M) (p-group) 下で、Thm 6.1 で A ⊆ F を得た直後.

**役割**: **Thm 6.2** で `Z(J(P))·O_{p'}(G) ⊴ M` ⇒ Z(J(P)) ⊴ M (since O_{p'}(G) ⊆ C_G(Z(J(P))), O_{p'}(G)自体も normal). これにより N_G(P) localizes to M, **P が全体 G の Sylow p-部分群**という重大帰結を得る.

**非自明性**: Part (b) では F(M) = p-group = O_p(M) という仮定が強い。このとき O_{p'}(M) = 1 (proof of part (b), L2446). Thm 6.2 の出力 Z(J(P))·O_{p'}(G) ⊴ G で、O_{p'}(G)は可能性として nontrival だが、M に restrict すると O_{p'}(M) = 1 なので Z(J(P)) ⊴ M だけで充分.

### 引用 2: L2478 (Part (b) maximality argument)

```
By (8.12) and Theorem 6.2,
  O_{p'}(H) = 1 and Z(J(R)) ⊴ H.  ...(8.13)
```

**文脈**: Assume H ∈ M(A), H ≠ M, R = Syl_p(H∩M) ⊇ A. **Thm 6.2 を H に適用**.

**役割**: **Thm 6.2** to H (solvable, odd order) gives `Z(J(R))·O_{p'}(H) ⊴ H` (R Sylow p-subgroup of H). Combined with **(8.12)** (H_G(A;p') = {1} ⇒ O_{p'}(H) = 1 by solvability + Fitting nil), we deduce **Z(J(R)) ⊴ H alone**.

**非自明性**: R が H の Sylow p かどうかの check が L2474-L2477 で行われる (case split: |R| < |P| vs. |R| = |P|). いずれでも R Syl_p(H) となる. その上で H に Thm 6.2 を apply.

### 引用 3: L2482 (Part (b) final contradiction)

```
By (8.9), (8.13), and Theorem 6.2, M = N_G(Z(J(R))) = H. 
This contradicts our choice of H and completes the proof of Theorem 8.1.
```

**文脈**: Part (b) finish. (8.13) で Z(J(R)) ⊴ H を得た. N_G(Z(J(R))) を compute.

**役割**: **Thm 6.2 を G level で**再度 invoke. P = Syl_p(G) (from (8.9)) に対し Z(J(P)) ⊴ G. N_G(Z(J(P))) ⊇ M (from (8.9)). 一方、R = Syl_p(H) ⊆ Syl_p(G) = P なので (by maximality of |R| in H, and R ⊆ P given (8.9)), R と P の conjugacy から Z(J(R))と Z(J(P))の関係が定まり、実は **N_G(Z(J(R))) = M** が導ける (Sylow conjugacy + normalization closure). よって **H ⊆ N_G(Z(J(R))) = M**, but H ∈ M(A) ⇒ H maximal ⇒ **H = M**, contradiction.

**非自明性**: (8.9), (8.13), Thm 6.2 の三角形関係. (8.9) は P Sylow (global), (8.13) は R Sylow (of H), これらの conjugacy + Thm 6.2 (Z(J(Sylow)) normalizer structure) で得る.

---

## Lemma 6.5 引用の検証 + 訂正

### 既存 overview の記載

`notes/bg/_overview.md` L13, L35: 「§8 L2246 で Lem 6.5 引用」

### 実態

mmd L2246 は **§7 内** (Proposition 7.4 proof, part (d)). §8 (L2315-2485) では **Lem 6.5 の明示引用なし**.

**訂正**: `notes/bg/s08_fitting_max.md` では §8 は Lem 6.5 を引用しないと明記. ただし §8 proof (a) で使われる「M = K·U (K normal, U complement) 下での normalizer 分解」は Lem 6.5 の精神に相通じるが、§8 では K = O_{p'}(M), U に相当する部分は implicit (Frattini argument で Z(F)_q normalization 活用).

---

## §9 Uniqueness Theorem への橋渡し

### Thm 8.1 → Thm 9.1 の引用

**mmd L2533** (Thm 9.1 proof):
```
Hence F(H) ∉ U and no subgroup of F(H) lies in U. 
By Theorem 8.1, r(F(H)) ≤ 2. 
Therefore, by Theorem 4.20, H' ⊆ F(H).
```

**役割**: Thm 9.1 証明で、H ∈ M(B), B noncyclic p-group, B ∉ U と assume した時、F(H)の rank が ≤ 2 であることを **Thm 8.1** (contrapositive: r(F(H)) ≥ 3 かつ H maximal ⇒ nontrivial ∈ U, so if nothing ⊆ F(H) is in U, then r(F(H)) ≤ 2) で得る. これにより H' ⊆ F(H) (Thm 4.20: solvable + F nilpotent ⇒ derived ⊆ F) → Frattini argument で H ⊆ M 矛盾.

### Phase 2a 形式化順序への含意

1. **§7 Transitivity Theorem** 完成 (Thm 7.2, 7.4, 7.6)
2. **§8 Fitting of Max** 完成 (Thm 8.1 case (a), (b))
3. **§9 Uniqueness Theorem** 着手可能 (Thm 9.1, 9.6)

---

## 証明方針の分析

### Case (a) vs. Case (b) の分岐

**Remark at L2483**:
```
The theorem above has slightly different conclusions, but very different arguments 
according to whether (a) F(M) is not a p-group or (b) F(M) is a p-group. 
Similarly, there are slightly different arguments for these two cases in the proof of Theorem 9.1. 

This dichotomy reflects a division of π(G) in FT. 
In FT, Feit and Thompson defined 
  π₃ = {p : r_p(G) ≥ 3 and ∃ Syl_p(G) normalizing nonidentity p'-subgroup}
  π₄ = {p : r_p(G) ≥ 3, p ∉ π₃}
```

**FT 理論的背景**: Feit-Thompson原論文では、odd-order minimal counterexample G に対し、各 p ∈ π(G) を **π₃ (Frobenius-like: Sylow p が p'-subgroup を normalize)** と **π₄ (その他)** に分割. BG Remark は「§8 case (a) が π₃ に相当し、case (b) が π₄ に相当する」と述べている. **case (a)**: F(M) が mixed (多素因子) ⇒ 多くの π-primes active ⇒ Frobenius-style argument (case (a) Thompson Transitivity heavily uses). **case (b)**: F(M) = p-group (one prime) ⇒ single p-Sylow dominates ⇒ Sylow conjugacy + J-subgroup normalization (case (b)).

### 背理法: Counterexample within Counterexample

**Case (b) の logicality**: G 自体が **最小反例** (minimal counterexample to FT). Part (b) では「M maximal, F(M) = p-group, A ∈ SCN₃(P) ⇒ A ∈ U (M the unique maximal containing A)」を show したい. **Assume not**: H ∈ M(A), H ≠ M. このとき H は G より小さい solvable subgroup (≤ subgroup of non-solvable G). **Thm 6.2 を H に apply** → Z(J(R)) ⊴ H → N_G(Z(J(R))) ⊇ H ⇒ H = M 矛盾. この論証は「G が minimal counterexample という外部仮定を使わずに、H ⊂ G のみで Thm 6.2 を invoke できる」という意味で elegant.

---

## mathlib カバレッジ評価

| 概念 | mathlib | 新規実装 | 備考 |
|------|---------|----------|------|
| **Fitting subgroup F(G)** | **low** (Phase 1 Ch.2 で実装予定) | F(M) restrict に直結 | M ⊆ G に対する F(M) は F(G)の M-restriction |
| **Thompson J(P)** | **low** (Phase 1 Ch.7 で実装予定) | Z(J(P)), SCN₃(P) 定義に必須 | Isaacs Thm 7.2 based |
| **Elementary abelian E*_p(F(M))** | **mid** (elementary abelian subgroup: existing, maximal search: mid-new) | rank m(A₀) ≥ 3 check API | basic 部分群 theory は高い |
| **Sylow p-subgroup, Sylow conjugacy** | **high** (mathlib `Sylow` class + conjugacy existing) | — | 既存 API sufficient |
| **A-invariant subgroups, Hall cohort** | **mid** (basic Hall: existing, A-invariant: mid-new) | — | §7, §1 で実装済み想定 |
| **p-length, p-core O_p(G), O_{p'}(G)** | **high** (existing `Subgroup.pCore`, `IsSolvable.pLength`) | — | 既存 API sufficient |
| **Centralizer, Normalizer, Frattini argument** | **high** (existing) | — | 既存 API sufficient |
| **solvable characterization** | **high** (existing `IsSolvable`) | — | 既存 API sufficient |

**Phase 1 前提条件**:
- Isaacs Ch.7 (Thompson J(P), Thm 7.2, 7.4, 7.6)
- Isaacs Ch.4 (Sylow theory, Hall)
- BG §1, §3, §4, §5, §6 (preliminaries)

**難度**: Thm 8.1 は **高** (case split, nested induction, Thm 6.2 × 3 依存, Thompson Transitivity 活用). **3-4 週の集中実装想定**.

---

## Phase 2a 形式化着手順

### 前提チェックリスト

- [ ] **Phase 1 Ch.7** (Thompson J(P), Thm 7.2, 7.4, 7.6) ✓ = Gate 条件
- [ ] **BG §1** (Elementary Properties of Solvable) ✓
- [ ] **BG §3** (Frobenius Actions) ✓
- [ ] **BG §4** (p-Groups Small Rank) ✓
- [ ] **BG §5** (Narrow p-Groups) ✓
- [ ] **BG §6** (Additional Results, Thm 6.1, 6.2 in scope) ✓
- [ ] **BG §7** (Transitivity Theorem, Thm 7.2, 7.4, 7.6) ✓

### 実装ステップ

1. **§8 setup** (1-2 日)
   - `maximal_subgroup M` と `fitting_subgroup F(M)` の formalization
   - `elementary_abelian_large A₀ : E*_p(F(M))`
   - `rank_ge_three : m(A₀) ≥ 3`

2. **Part (a) proof** (7-10 日)
   - Hypothesis 7.1 verification for A = C_F(A₀)
   - (8.1)-(8.6) step-by-step: π(A) = π(F) → C_G(A) ⊆ M → H*_G(A;q) = {1} → Frattini
   - Thompson Transitivity (Thm 7.2) invocation
   - Fitting hereditary (Thm 7.4) + normalizer computation

3. **Part (b) proof** (10-14 日)
   - F(M) = p-group case detection + O_p(M) = F
   - Thm 6.1 application (A ⊆ O_{p',p}(F(M)))
   - **Thm 6.2 L2456**: Z(J(P)) ⊴ M ⇒ P Syl_p(G)
   - (8.10)-(8.12): π'-part elimination
   - Counterexample H ∈ M(A) → Sylow maximize |H∩M|_p → (8.13) **Thm 6.2 L2478** → **Thm 6.2 L2482** final contradiction

4. **Theorem statement formalization** (1-2 日)
   - Part (a), (b) as separate lemmas / branches
   - Final `theorem_8_1`: aggregate statement

5. **Remark + docstring** (1 日)
   - π₃/π₄ dichotomy explanation
   - Thm 8.1 → Thm 9.1 dependency marker
   - FT historical context

### Lean skeleton

```lean
namespace OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal

-- (8.1)-(8.5) helper lemmas
lemma aux_8_1 (M : Subgroup G) (A : Subgroup (fitting_subgroup M)) : 
  center (fitting_subgroup M) ⊆ centralizer A := sorry

lemma aux_8_2 (M : Subgroup G) (A : Subgroup (fitting_subgroup M)) :
  centralizer A ⊆ M := sorry

-- ... (8.3)-(8.6) lemmas

lemma part_a (M : Subgroup G) (A₀ : Subgroup (fitting_subgroup M)) 
    (h_not_p_group : ¬IsPGroup p (fitting_subgroup M))
    (h_rank : m(A₀) ≥ 3) :
  centralizer A₀ ∈ 𝒰 := by
  -- Hypothesis 7.1 + Thompson Transitivity
  sorry

lemma part_b (M : Subgroup G) (A : Subgroup (Sylow p M))
    (h_p_group : IsPGroup p (fitting_subgroup M))
    (h_scn3 : A ∈ SCN₃ p)
    (h_rank : m A ≥ 3) :
  (p ∈ Sylow_primes G) ∧ (A ∈ 𝒰) := by
  -- Thm 6.2 × 3 + counterexample
  sorry

/-- Theorem 8.1 (main) --/
theorem theorem_8_1 (M : Subgroup G) (p : ℕ) (A₀ : Subgroup (fitting_subgroup M))
    (h_mem : M ∈ 𝓜) (h_prime : p ∈ π(fitting_subgroup M))
    (h_elem_ab : A₀ ∈ E*_p(fitting_subgroup M)) (h_rank : m(A₀) ≥ 3) :
    ((¬IsPGroup p (fitting_subgroup M) → centralizer A₀ ∈ 𝒰) ∧
     (IsPGroup p (fitting_subgroup M) → (p ∈ Sylow_primes G) ∧ 
                                         (∀ A ∈ SCN₃ p, A ⊆ fitting_subgroup M ∧ A ∈ 𝒰))) := by
  sorry
```

---

## 未解決 / TODO

| 項目 | 状態 | 詳細 |
|------|------|------|
| **Thm 6.2 formal statement in §6** | TBD | Phase 1 Ch.7 Thm 7.6 との import strategy 確定要 (選択肢 1 vs. 2, note s06_additional.md 参照) |
| **Thm 7.2, 7.4, 7.6 formalization timeline** | TBD | Phase 1 第 5 波スケジュール確認 |
| **Hypothesis 7.1 formal setup** | TBD | §7 ノートで detail 化予定; part (a) で direct verification 必要 |
| **SCN₃(P) as concrete subgroup class** | TBD | Phase 1 Ch.4 定義への参照 確認 + Sylow specialization API check |
| **H_G(A;q) (H-invariant q-subgroup) definition** | TBD | Isaacs notation; Phase 1 Ch.7 で `H_invariant_subgroup` class expected |
| **Thm 4.20 formalization (solvable ⇒ H' ⊆ F(H))** | TBD | Phase 1 Ch.4 / BG §4 scope; Phase 2a 前に確認 |

---

## リンク & クロス参照

- **Related notes**: 
  - `notes/bg/_overview.md` (BG overview, 修正: L35 Lem 6.5 引用訂正要)
  - `notes/bg/s06_additional.md` (BG §6, Thm 6.2 詳細)
  - `notes/bg/s07_transitivity.md` (BG §7, Thm 7.2, 7.4, 7.6)
  - `notes/bg/s09_uniqueness.md` (BG §9, Thm 9.1 — §8.1 引用)
  
- **Phase 1 references**:
  - `notes/isaacs/ch07_thompson.md` (Isaacs Thm 7.6)
  - `notes/isaacs/ch04_solvable.md` (Thm 4.20, p-length)

- **ROADMAP**: [ROADMAP.md#phase-2a--bender-glauberman](../../ROADMAP.md)

---

**作成**: 2026-05-22

**出典**: 
- `references/bg/local-analysis.mmd` lines 2315-2485 (§8 全体), PDF pp.61-63 (本文)
- `notes/bg/_overview.md` (BG overview, cross-validation)
- `notes/bg/s06_additional.md` (Thm 6.2 detailed)

**次ステップ**: 
- Phase 1 Ch.7 (Thompson J(P)) formalization progress monitor
- BG §7 ノート確定 (Thm 7.2, 7.4, 7.6, Hypothesis 7.1)
- §8 formal proof sketch (Lean 3 / Lean 4 syntax check)
- Phase 2a 第 3 波スケジュール (§7 完成後)

---

## Lean API status (2026-06-02 lane B6)

Current Lean spine lives in `OddOrder/BG/Ch2_Uniqueness/S08_FittingOfMaximal.lean`.

- `fittingInG M` is the canonical `G`-ambient realization of `F(M)`, with `fittingInG_le` recording `F(M) ≤ M`.
- `isMaxElemAbelianIn p A0 H` is the concrete `E_p^*(H)` predicate. Accessors landed: `isMaxElemAbelianIn_isElementaryAbelian`, `isMaxElemAbelianIn_le`, and `isMaxElemAbelianIn_eq_of_isElementaryAbelian_of_le`.
- Remaining §8 `sorry`s are exactly Theorem 8.1(a) and Theorem 8.1(b). They remain hard because the proofs consume §7 transitivity plus BG §6 normal-J/p-length inputs; the statement still keeps Lemma 5.1 nonemptiness out of the theorem hypothesis.
