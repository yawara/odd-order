# Peterfalvi §16: Non-existence of G — mini-roadmap (FT 完了)

**スコープ**: Peterfalvi §16 (pp.87-92, 184 行), mmd `04.16_pp_87_92_Non-existence_of_G.mmd` (11 結果).
形式化先 (予定): `OddOrder/Peterfalvi/S16_NonExistenceG.lean`
ROADMAP 上の位置: **Phase 2b 第 7 波** (§3-§15 全部 + BG §16 完成必須)
役割: **Peterfalvi 本体の最終章. FT 完了 = G の非存在**, Phase 3 (BG + Peterfalvi 統合) の直前

---

## TL;DR — FT 完了

Peterfalvi §16 は **指標論の最後の砦**. §15 までに完成した S, T の指標論を使い、8 つの段階的制約条件から出発して、最終的に「極小反例群 G は存在しない」という矛盾を導く. その矛盾は BG Appendix C (Theorem C = "statements (14.2)(a), (b) ⇒ p ≤ q" に反する) から生じる.

**メカニズム**:
1. **(14.1)-(14.4)**: 仮説設定と初期ステップ. 最大部分群 L の構造を確定
2. **(14.5)-(14.7)**: L の構造から U (の特性化) を分析
3. **(14.8)-(14.9)**: 重要不等式 (norm 比較) と T の Type を確定
4. **(14.10)-(14.11)**: 別の最大部分群 M を導入. 両者の対比で矛盾を導く
5. **(14.11.1)-(14.11.4)**: M を詳細に分析. 指標論計算が中心

**最終矛盾**: (14.11.4) で `1/p ≤ pq/k` と `v > pq` の同時成立不可.

---

## §16 全 11 結果 (表)

| # | 結果 | 型 | 頁 | 主張 | 依存 | 指標論計算 |
|---|------|------|-----|------|------|----------|
| 1 | (14.1) | Hyp | 87 | q < p (新仮説) | (13.1) | — |
| 2 | (14.2) | Thm | 87 | G 非存在の最終形. (a) PU≃F⋊U*, (b) Q elementary, W₂^y normalizes U | (14.1) | BG Thm.C と統合 |
| 3 | (14.3) | Hyp | 87 | L maximal ⊃ N_G(U). H=L_F. τ (Dade), φ (char), β_L (virtual char diff) | (14.1) | setup |
| 4 | (14.4) | Prop | 87 | Case (9.7.b) for M=T, v=(q^p-1)/(q-1) | (9.7.b), (13.13), (13.15) | case calc |
| 5 | (14.5) | Prop | 87 | ∃ y ∈ Q : L = H ⋊ (W₁W₂^y) | (13.17.c), (13.17.b) | structure |
| 6 | (14.6) | Prop | 88 | Case (9.7.b) for M=S (not (9.7.a)) | (13.13) [BG Prop 1.16] | rank 2 cyclic product |
| 7 | (14.7) | Prop | 88 | U characteristic in H ⇒ Thm(14.2) holds | (13.2.b), (14.5), (13.15) | norm action |
| 8 | (14.8) | Prop | 88 | (a) q^{p+1} > p^{q+1}, (b) (v-1)/p > (u-1)/q | analysis | **key inequality** |
| 9 | (14.9) | Prop | 88-89 | T is Type II (not Type III) | (5.7), (5.3.b), (5.5), (13.18.c), (13.19) | inner product on Dade |
| 10a | (14.10) | Hyp | 89 | M maximal ⊃ N_G(V), K=M_F, τ (Dade), ψ (char), β_M | (14.9) | setup |
| 10b | (14.11) | Thm | 89 | K=V, \|M:K\|=pq (主結果) | (14.9)-(14.10) + **nested** | **character arithmetic** |
| 10b-i | (14.11.1) | Prop | 89 | k > 2pv, (k-1)/e ≥ (v-1)/p > (u-1)/q | (13.17), (14.8) | modular arithmetic |
| 10b-ii | (14.11.2) | Prop | 89 | e=pq, β_M^τ = Σ(±η_{ij}) - χ | (7.8), (13.19) | **inner product norm** |
| 10b-iii | (14.11.3) | Prop | 90 | g ∈ G_0 (generic) ⇒ \|ψ^{τ₁}(g)\| ≥ 1 | (5.9), (8.6.a), (2.1), (3.9.c), (3.9.a) | algebraic character eval |
| 10b-iv | (14.11.4) | Prop | 90-91 | **最終矛盾**: 1/p ≤ pq/k かつ v > pq は矛盾 | (7.5), (14.11.1)-(14.11.3) | **norm inequality cascade** |
| 11 | (14.12) | Prop | 91 | L ≅^conj M ⇒ Thm(14.2) holds | (14.11), (14.4), (13.12) | structure |
| 12 | (14.13) | Hyp | 91 | L not ≅^conj M. h=\|H\| | (14.12) | — |
| 13 | (14.14) | Prop | 91 | (a) (β_M^τ, φ^{τ₁}) ≠ 0 ∧ (h-1)/pq ≤ pq-1, or (b) (β_L^τ, ψ^{τ₁}) ≠ 0 ∧ q=3 ∧ p=5 | (8.17.c), (7.9) | **orthogonality switch** |
| 14 | (14.15) | Prop | 91 | u = (p^q-1)/(p-1) | (14.6), (13.15), (14.5) | norm division |
| 15 | (14.16) | Prop | 91 | H = U (最終完成) | (14.5), (14.15), (14.14) | **direct contradiction** |
| (Concl) | (14.17)? | Concl | 91-92 | Thm(14.2), (14.12), (14.16), (14.7) ⇒ Thm(14.2) ∴ G ∄ | (14.2)-(14.16) | **synthesis** |

**注**: (14.11) は 4 つのネストした sub-propositions から構成 (14.11.1)-(14.11.4). 実質 15 個のステップ. 最終矛盾は (14.11.4) と (14.16) の 2 か所から同時発生.

---

## (14.1)-(14.11) 論理依存図

```
(13.1) [Hyp§15 全部]
    ↓
(14.1) Hypothesis: q < p
    ├─ (14.2) Theorem: G 非存在 [ネストした帰結]
    │
    ├─→ (14.3) Hypothesis: L maximal, τ Dade, ...
    │    ├─→ (14.4) Case (9.7.b) for T
    │    │    ├─→ (14.5) ∃ y ∈ Q : L = H ⋊ (W₁W₂^y)
    │    │    │    ├─→ (14.6) Case (9.7.b) for S (exhausts (9.7.a))
    │    │    │    │    └─→ (14.7) U char in H ⇒ (14.2)
    │    │    │    │
    │    │    │    └─→ (14.8) Key inequality: (a) q^{p+1} > p^{q+1}
    │    │    │                                 (b) (v-1)/p > (u-1)/q
    │    │    │        └─→ (14.9) T is Type II [not III]
    │    │    │                [uses Dade inner product]
    │    │    │
    │    │    └─→ (14.10) Hypothesis: M maximal ⊃ N_G(V), K=M_F, ...
    │    │         └─→ (14.11) K=V, |M:K|=pq [MAIN RESULT]
    │    │              ├─→ (14.11.1) k > 2pv, (k-1)/e ≥ (v-1)/p
    │    │              │    ├─→ (14.11.2) e=pq, β_M^τ expansion
    │    │              │    │    ├─→ (14.11.3) generic g: |ψ^{τ₁}(g)| ≥ 1
    │    │              │    │    │    └─→ (14.11.4) 最終矛盾!
    │    │              │    │    │        "1/p ≤ pq/k ∧ v > pq"
    │    │              │    │    │         矛盾
    │    │              │    │
    │    │              └─→ (14.12) L ≅^conj M ⇒ (14.2)
    │    │                   └─→ (14.13) Hypothesis: L ≄^conj M
    │    │                        ├─→ (14.14) (a) or (b) case split
    │    │                        │    ├─→ (14.15) u = (p^q-1)/(p-1)
    │    │                        │    │    └─→ (14.16) H = U
    │    │                        │    │         └─→ (14.2) holds
    │    │                        │    │
    │    │                        │    └─→ (14.15), (14.16)
    │    │
    └─→ [Conclusion] (14.2) より G ∄. BG Thm.C と統合 ⇒ FT 完成
```

**フロー**:
- **(14.1)** 新仮説導入
- **(14.3)** 第一の最大部分群 L setup
- **(14.4)-(14.7)** L の直接分析. (14.7) 肯定的終結 (U characteristic)
- **(14.8)** 中断. 新しい制約条件 (norm inequality)
- **(14.9)** Type II 確定
- **(14.10)** 第二の最大部分群 M setup. L vs M の 対比戦略
- **(14.11)** メインゲーム. 2 つの矛盾パス
  - Path A: (14.11.4) で直接矛盾
  - Path B: (14.12)-(14.16) で M ≄ L の仮定の下で矛盾
- **結論**: 両パスとも (14.2) を導く

---

## (14.11) 主結果 = no minimal counterexample G exists

### (14.11) のステートメント

```lean
theorem feitThompson_fourteen_eleven 
    (q p : ℕ) (hpq : q < p) (hprime_q : Nat.Prime q) (hprime_p : Nat.Prime p)
    (G : Type*) [Group G] [Finite G] (hG_odd : Odd (Nat.card G))
    (hG_simple : Group.IsSimple G)
    -- (13.1) の全仮説（最小反例 G）
    [hG_min : IsMinimalCounterexample G]
    -- (14.3), (14.10) の L, M setup
    (L M : Subgroup G) (hL : IsMaximalSubgroup L ∧ N_G U ≤ L)
                       (hM : IsMaximalSubgroup M ∧ N_G V ≤ M)
    -- 指標論 setup: Dade, character
    (τ_L τ_M : Dade.Isometry) (φ ψ : Character G)
    -- Main claim
    : K = V ∧ (M : Set G).card / |M : K| = p * q
```

### (14.11.4) の矛盾の詳細

`(14.11.4) Conclusion.` (pp.90-91, line 105-123):

**入力**:
- (14.11.1): k > 2pv, (k-1)/e ≥ (v-1)/p > (u-1)/q
- (14.11.2): e = pq, β_M^τ = Σ(±η_{ij}) - χ (character norm)
- (14.11.3): generic g, |ψ^{τ₁}(g)| ≥ 1 (algebraic bound)
- (7.5): ρ mapping (Hypothesis 7.1)
- (7.8.b): norm inequality on Dade image

**計算**:
1. (7.5) より, Frobenius 形 inner product の Dade norm:
   ```
   (1/|G|) Σ_{g∈G_0} |ψ^{τ₁}(g)|² - |G_0| - (W periphery) - (P#)^G - (Q#)^G
   + ||ψ^{τ₁}ρ||² - |K#|/|M|  ≤ 0
   ```

2. (14.11.3) で |ψ^{τ₁}(g)| ≥ 1 を使い，上記の ≤0 不等式を整理:
   ```
   1 - pq/k ≤ ||ψ^{τ₁}ρ||² ≤ 1 - 1/p - 1/q + 1/(pq) + (smaller terms)
   ```

3. 再配置:
   ```
   1/p + 1/q ≤ pq/k + 2/(pq) + 1/(uq) + 1/(vp)
   ```

4. u > 2q, v > 2p > 2q より:
   ```
   2/(pq) + 1/(uq) + 1/(vp) < 2/q² + 1/(2q²) + 1/(2q²) = 3/q² ≤ 1/q
   ```

5. よって:
   ```
   1/p ≤ pq/k
   ```

6. (14.11.1) で k > 2pv 使い変形:
   ```
   v < k/p ≤ pq
   ```

7. しかし (14.4) で v = (q^p - 1)/(q - 1) ≡ 1 (mod q) かつ VW₂ Frobenius より v ≡ 1 (mod p).
   したがって:
   ```
   v > pq [矛盾!]
   ```

**機械化**: Lean で `linarith`, `norm_num`, `decide` の組み合わせで証明可能. 中核は arithmetic inequality cascade.

---

## BG §16 (Theorem B) + App.C (Theorem C) との合体方針 (Phase 3)

### BG との関係図

| 位置 | 内容 | 役割 |
|------|------|------|
| **BG §16 Main Results** | Type I-V の統合から P, Q の位数・正規化群の最終形 | §15 出力 = §16 入力 |
| **BG App.C Theorem C** | "statements (14.2)(a), (b) ⇒ p ≤ q" の矛盾 | (14.2) ⇒ 矛盾 |
| **Peterfalvi §16** | (14.1)-(14.11) で G 非存在 | FT の character-theoretic 締め括り |

### Phase 3 統合スキーム

```
Phase 2a 完成:
  BG Main Results (§16) ⇒ Type I-V 統合
         ↓
  BG App.C Theorem C: "statements (a), (b) ⇒ p ≤ q"
         ↓
Phase 2b 完成:
  Peterfalvi §3-§15 ⇒ 指標論の基礎 + S, T の詳細
         ↓
  Peterfalvi §16 (14.1)-(14.11)
         ↓
Phase 3 (統合):
  (14.2)(a), (b) ∧ (14.1) q < p ⇒ 矛盾 [BG App.C Thm.C 使用]
         ↓
Phase 4 (メイン定理):
  ∀ G odd order, simple ⇒ False
  ∴ FT: ∀ G odd order ⇒ solvable
```

### Phase 3 タスク (形式化の観点)

1. **BG App.C Theorem C の Lean statement**:
   ```lean
   theorem bg_appendix_c (p q : ℕ) [hp : Nat.Prime p] [hq : Nat.Prime q]
       (ha : FField.equation (F_q := 𝔽 q) (u_star := ...) ...)
       (hb : Elementary Q ∧ W2_acts_free_on Q ∧ ...)
       : p ≤ q
   ```

2. **Peterfalvi (14.2)(a), (b) の Lean statement**:
   ```lean
   theorem peterfalvi_fourteen_two (q < p) :
       eq_at_fq (PU) ∧ element_y_condition
   ```

3. **統合補題**:
   ```lean
   theorem feit_thompson_final (G : Group) [Odd card] [Simple G] :
       False := by
         have h_14_2 := peterfalvi_fourteen_two
         have h_14_1 : q < p := ...
         have h_bg_thm_c := bg_appendix_c
         -- h_14_2.a, h_14_2.b ⇒ BG Thm.C p ≤ q と矛盾
   ```

---

## Phase 4 FeitThompson メイン定理の statement

### 最終形 (Lean 4)

```lean
/-- The Feit-Thompson Theorem: every finite group of odd order is solvable. -/
theorem feitThompson (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card G) → IsSolvable G := by
  intro hodd
  -- 背理法: G simple かつ nonsolvable と仮定
  by_contra hnonsol
  push_neg at hnonsol
  -- G has simple quotient S
  obtain ⟨S, hS : IsSimple S, hodd_S : Odd (Nat.card S)⟩ := ...
  -- S minimal counterexample
  have hS_min : IsMinimalCounterexample S := ...
  -- 前 Phase 2 論理: Type I-V + §15 で S の構造確定
  have htype : SpecificStructure S := Phase2a_output
  -- Phase 2b §3-§15: 指標論で S の構造再分析
  have hchar : CharacterTheory.SpecificStructure S := Phase2b_output
  -- Phase 3: (14.2) ∧ (14.1) ∧ BG App.C ⇒ False
  exfalso
  exact Phase3_synthesis htype hchar
```

### 最終メイン定理の段階的アンロック

| Phase | 出力 | 形式化ファイル | 準備完了 |
|-------|------|---------------|--------|
| Phase 1 | Isaacs Ch.1-10 形式化 | `Isaacs/*.lean` | 2026-10-31 (予) |
| Phase 2a | BG Ch.1-4 形式化 | `BG/*.lean` | 2026-12-31 (予) |
| Phase 2b | Peterfalvi §1-§16 形式化 | `Peterfalvi/*.lean` | 2027-03-31 (予) |
| Phase 3 | BG + Peterfalvi 統合 | `Theorems/Phase3_*.lean` | 2027-04-30 (予) |
| **Phase 4** | **FeitThompson メイン定理** | **Theorems/FeitThompson.lean** | **2027-05-31 (予)** |

---

## 指標論計算の Lean tactic 戦略

### (14.8) Key Inequality: `q^{p+1} > p^{q+1}`

```lean
lemma fourteen_eight_a (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) 
    (hpq : q < p) (hp5 : p ≥ 5 ∨ (q = 3 ∧ p ≥ 5)) :
    q ^ (p + 1) > p ^ (q + 1) := by
  have : Real.log q / (q + 1) > Real.log p / (p + 1) := by
    -- f(x) = (log x) / (x + 1) decreasing for x ≥ 5
    have mono_f : ∀ x y : ℝ, x ≥ 5 → y ≥ 5 → x < y → 
        Real.log x / (x + 1) > Real.log y / (y + 1) := by
      intros x y _ _ hxy
      -- derivatives, calculus library
      sorry
    -- apply to p, q
    cases' (by omega : q = 3 ∨ q ≥ 5) with hq3 hq5
    · -- q = 3 case
      norm_num [hq3]
      sorry
    · -- q ≥ 5 case
      have : mono_f p q ‹p ≥ 5› ‹q ≥ 5› hpq
      sorry
  -- conclude q^{p+1} > p^{q+1} from inequality on logs
  sorry
```

**Tactic 選択**:
- `norm_num`: 小さい素数 (p=5, q=3) の直接計算
- `linarith`: 線形不等式の accumulated sum
- `polyrith` (必要に応じ): polynomial inequality
- 微積分: `deriv` + `Monotone` lemma from mathlib

### (14.11.4) Final Norm Inequality

```lean
lemma fourteen_eleven_four (M K : Subgroup G) (hM : IsMaximalSubgroup M)
    (hK : K = V) (hcard : (M : Set G).card / |M : K| = p * q)
    (hodd_pq : p * q ≤ 2 * (M : Set G).card / (K : Set G).card) :
    ∃ (ψ : Character G), (1 : ℚ) / p + 1 / q ≤ 
        (p * q / (K : ℕ) : ℚ) + 2 / (p * q) + 
        1 / (u * q) + 1 / (v * p) := by
  -- (7.5) Dade isometry inner product
  have dade_norm := Dade.inner_product_formula ...
  -- (14.11.3): generic element character eval ≥ 1
  have char_gen : ∀ g ∈ G_0, 1 ≤ |ψ.map g| := fourteen_eleven_three ...
  -- arithmetic cascade: norm ≤ bounds
  calc (1 : ℚ) / p + 1 / q 
      ≤ (p * q / (K : ℕ) : ℚ) + 2 / (p * q) + 
        1 / (u * q) + 1 / (v * p) := by
    -- combine dade_norm + char_gen + (14.11.1) size bound
    have sum_bound := by linarith [dade_norm, char_gen]
    norm_num at sum_bound ⊢
    exact sum_bound
```

**Tactic 選択**:
- `linarith`: norm の線形結合 (多くは OK)
- `nlinarith`: 非線形項 (v, u の quadratic)
- `field_simp` + `ring`: 分数式の通分・化簡
- `norm_num`: 3/q² ≤ 1/q の確認

### (14.14) Orthogonality Switch (case analysis)

```lean
lemma fourteen_fourteen (τ_L τ_M : Dade.Isometry) 
    (φ : Character G) (ψ : Character G)
    (h_disj : Dade.Image τ_L ∩ Dade.Image τ_M = ∅) :
    (inner τ_L β_M φ ≠ 0) ∨ (inner τ_M β_L ψ ≠ 0) := by
  by_contra h_neg
  push_neg at h_neg
  -- (8.17.c): supports disjoint
  obtain ⟨h_disj_L, h_disj_M⟩ := h_disj
  -- (7.9): orthogonality consequence
  have ortho := Dade.orthogonal_image τ_L τ_M h_disj_L h_disj_M
  -- contradiction with inner products
  exact absurd (h_neg.1) (ortho φ)
```

**Pattern**: 直交性補題の Dade isometry API への編入が中核. Lean では `⟨χ, hχ⟩` 形の support 制限を predicate として組み込む方が自然.

### 指標の代数的評価 (14.11.3)

```lean
lemma fourteen_eleven_three (ψ : Character G) (g : G) 
    (hg : g ∈ G_0) : 1 ≤ |ψ.map g| := by
  -- g ∉ Ã(M), ∉ W^# conjugacy class, ∉ P^# conjugacy class, ∉ Q^# conjugacy class
  have h_generic := hg -- g is generic
  -- then g has order prime to p*q
  have h_ord : Nat.gcd (orderOf g) (p * q) = 1 := by
    -- from (14.11.3) argument: elements of order divisible by p or q
    -- come from centralizers of P^# or Q^#, which intersect (W periphery)
    sorry
  -- (3.9.c): η_{ij}(g) ∈ ℤ for generic g
  have η_int : ∀ i j, (η i j).map g ∈ (ℤ : Set ℂ) := 
    character_integer_at_generic_order h_ord
  -- (3.9.a): η_{ij} complex conjugate = η_{rs} (involution on pairs)
  have conj_pairs : ∀ i j, ∃ r s, conj (η i j) = η r s := 
    character_conjugate_pair i j
  -- ψ^{τ₁}(g) = Σ(±η_{ij}(g)) → sum of ±1 integers → odd
  have ψ_sum : ψ.map g = ∑ i j, (sign i j : ℤ) * (η i j).map g := by
    -- from (14.11.2) decomposition
    sorry
  have ψ_odd : 2 ∣ (ψ.map g).re + 1 := by
    -- Σ ±1 sum = odd ⇒ |·| ≥ 1
    rw [show (ψ.map g).re = ∑ i j, (sign i j : ℝ) by norm_num [ψ_sum]]
    norm_num -- Σ (±1) ∈ 2ℤ + 1
  linarith [Complex.abs_nonneg (ψ.map g), ψ_odd]
```

---

## mathlib カバレッジ

### 既存利用可能な API

| 概念 | mathlib | 使用箇所 |
|------|---------|---------|
| `Character G` | `Mathlib/RepresentationTheory/Character.lean` | (14.2)-(14.11) φ, ψ の定義 |
| `IsSolvable G` | `Mathlib/GroupTheory/Solvable.lean` | Phase 4 メイン定理 |
| `IsSimple G` | `Mathlib/GroupTheory/Simple.lean` | 背理法前置 |
| Inner product on virtual characters | `Mathlib/RepresentationTheory/Character.lean` | (14.11.4) norm calculation |
| `Nat.Prime p` | `Mathlib/Data/Nat/Prime.lean` | (14.1), (14.4) 素数性 |

### 新規要実装 (§16 特有)

| 概念 | 型/定義 | 箇所 | 予想量 |
|------|--------|------|--------|
| Dade Isometry | `structure Dade.Isometry` | (14.3), (14.10) setup | §4 (既出) で実装済予定 |
| Minimal counterexample | `class IsMinimalCounterexample` | (14.1)-(14.11) 仮説 | 100 行程度 (Phase 2 共通) |
| Generic element condition | `def IsGeneric (g : G) : Prop` | (14.11.3) | 30 行 |
| Character norm inequality | `lemma character_norm_bound` | (14.11.4) | 50 行 |

### §16 独自の高度な計算

1. **Norm cascade**: (7.5) ⇒ (14.11.1)-(14.11.4) の Dade norm 展開. `LinearMap.norm` + `InnerProductSpace` API の活用
2. **Modular arithmetic**: (14.11.1) の `k ≡ x ≡ 1 (mod p)` 推論. `Nat.ModEq` 使用
3. **Character evaluation**: (14.11.3) の `η_{ij}(g) ∈ ℤ` 確認. `Character.integerValuedOn` + `ConjugateClasses` API

### 完全新規で実装必須

- **Norm inequality cascade (14.11.4)**: 
  ```lean
  lemma norm_ineq_cascade : 1/p + 1/q ≤ pq/k + 2/(pq) + ... → False
  ```
  (200 行の tactic proof)

- **Generic element character bound (14.11.3)**:
  ```lean
  lemma generic_char_integer : OrderOf g ∣ ... → ...map g ∈ ℤ
  ```
  (100 行)

- **Orthogonality orthogonal image lemma (14.14)**:
  ```lean
  lemma dade_orthogonal_images : Dade.Image τ_L ⊥ Dade.Image τ_M → ...
  ```
  (80 行)

---

## Phase 2b 形式化着手順

### §16 着手のチェックリスト

**必須前提**:
- [ ] §3-§15 全て Lean で完成
- [ ] BG 全部 (Ch.1-§16) Lean で完成
- [ ] Dade Isometry (§4) の型定義完成
- [ ] Coherence 定義 (§7) 完成
- [ ] S, T の型・引理完成 (§15)

**§16 形式化の分割計画**:

**Wave 1 (week 1)**: (14.1)-(14.7) 基盤部
- `OddOrder/Peterfalvi/S16_NonExistenceG.lean` 創設
- Hypothesis (14.1), (14.3), (14.10) 定義
- Lemmas (14.4)-(14.7) の Lean 化 (40 行 × 4 = 160 行)
- 依存: §15 出力、Dade (§4) setup

**Wave 2 (week 2)**: (14.8)-(14.9) Key Inequality + Type II
- Lemma (14.8.a): `q^{p+1} > p^{q+1}` (calculus, `norm_num`)
- Lemma (14.8.b): `(v-1)/p > (u-1)/q` (inequality from (a))
- Lemma (14.9): T Type II (`Dade.inner_product_formula`)
- (120 行)
- 依存: (14.4)-(14.7), Dade coherence

**Wave 3 (week 3)**: (14.10)-(14.11.2) M の構造
- Hypothesis (14.10) setup (20 行)
- Lemma (14.11): Main claim (20 行 statement)
- Lemma (14.11.1): Size bound `k > 2pv` (40 行)
- Lemma (14.11.2): `e=pq, β_M^τ expansion` (60 行, norm computation)
- (140 行)
- 依存: (14.9), Dade isometry orthogonality

**Wave 4 (week 4)**: (14.11.3)-(14.11.4) 最終矛盾
- Lemma (14.11.3): Generic character bound (100 行, modular arithmetic + character eval)
- Lemma (14.11.4): Final norm inequality cascade (200 行, `linarith` + `norm_num`)
- Proof of (14.11): これら sub-lemmas から synthesis (30 行)
- (330 行)
- 依存: Character theory (§3), Dade (§4), S, T analysis (§15)

**Wave 5 (week 5)**: (14.12)-(14.16) + 統合
- Lemma (14.12): L ≅^conj M ⇒ (14.2) (50 行)
- Hypothesis (14.13) (10 行)
- Lemma (14.14): Case split (a) or (b) (80 行, orthogonality switch)
- Lemma (14.15): `u = (p^q-1)/(p-1)` (60 行, modular reasoning)
- Lemma (14.16): `H = U` (60 行, final structure)
- Theorem (14.2): Conclusion from (14.7) ∨ (14.12) ∨ (14.16) (30 行)
- (290 行)

**§16 合計**: 1000-1200 行 Lean 4 コード

### 実装の段階的検証

| Wave | ターゲット補題 | 形式化行 | 確認項目 |
|------|----------------|--------|---------|
| 1 | (14.1)-(14.7) | 160 | Hypothesis 定義、基本補題の structure |
| 2 | (14.8)-(14.9) | 120 | 不等式証明、norm inequalityの精密性 |
| 3 | (14.10)-(14.11.2) | 140 | Dade isometry の拡張、modular arithmetic |
| 4 | (14.11.3)-(14.11.4) | 330 | **最難 wave**. 指標論計算の cascade. tactic strategy の決定 |
| 5 | (14.12)-(14.16) + (14.2) | 290 | 最終統合、背理法の完結 |

---

## 未解決 / TODO

### 形式化設計上

1. **Generic element G_0 の定義の精密さ**:
   ```lean
   def G_0 := G - [Ã(M) ∪ (W^#)^G ∪ (P^#)^G ∪ (Q^#)^G]
   ```
   この補集合の形式化が複雑. `Set.compl` + `Set.finite` 論でどこまで簡潔に書けるか?

2. **(14.11.4) の norm inequality cascade の tactic 戦略**:
   - (7.5) の Frobenius 形 inner product formula を精密に Lean に組むには?
   - `Finset.sum` 表記と `Dade` 構造のメタ計算が発生. 計算補題のライブラリ化が必須
   - `linarith` で解ける範囲 vs `nlinarith`, `polyrith` の使い分け

3. **Character evaluation on generic elements (14.11.3)**:
   - `η_{ij}(g) ∈ ℤ` の証明は、`Integer.coe` + `Character.integerValuedOn` + conjugate class 構造の組み合わせ
   - `Complex.abs |·| ≥ 1` の推理は `norm_num` で OK か、別途補題か?

### 指標論の API 設計

4. **Dade Isometry の `τ₁` 拡張 (11 ヶ所出現)**:
   - `τ : CF(L, A^#) ≃ₗ[ℂ] ...` からの拡張 `τ₁ : Z[ℒ] → Z[Irr G]`
   - Peterfalvi §4-§8 で既出だが、§16 での繰り返し利用パターンを統一する型デザイン

5. **Coherence predicate との関係**:
   - (14.11.2) の `β_M^τ = Σ(±η_{ij}) - χ` が coherent か否かの判定は?
   - §8 の coherence theorem が §16 で直接引かれるか、間接的 (case by case) か?

### BG 統合関連

6. **BG App.C Theorem C の Lean statement**:
   - "statements (a), (b) ⇒ p ≤ q" を (14.2) と対応させる型が必要
   - Phase 3 で BG と Peterfalvi の統合ポイント明示

7. **Phase 3 統合スクリプト**:
   - (14.2) ∧ (14.1) q < p ∧ BG Thm.C ⇒ False の Lean 形
   - 矛盾の source (norm inequality か divisibility か) の確認

### 検証とドキュメント

8. **§16 proof narrative の補強**:
   - §15 出力 (S, T の詳細構造) が §16 setup (L, M の最大部分群性) にどう繋がるか、docstring で明示
   - 「L と M の対比」という戦略が global に見えるドキュメント作成

9. **tactic script の best practice 整備**:
   - `norm_num`, `linarith`, `nlinarith`, `field_simp` の使い分けを example 付きで記録
   - character evaluation のモジュール化

---

## 参考: 他節との形式化進行状況 (予想)

| § | 形式化状況 | 推定 Wave | 依存 chain |
|---|----------|----------|-----------|
| 1-2 | 記号・序 (done trivial) | — | none |
| 3 | 指標論基礎 | Wave 0 | Isaacs, mathlib |
| 4 | Dade isometry | Wave 1 | §3 + mathlib |
| 5-6 | Dade 응용 | Wave 2 | §4 |
| 7-8 | Coherence | Wave 3 | §4-§6 |
| 9 | Non-existent Certain Type | Wave 4 | §7-§8 + BG App.C |
| 10-14 | Type I-V 分析 | Wave 5-6 | §9 + BG Ch.3-§16 |
| **15** | **S, T 詳細** | **Wave 7** | **§14 + BG §15** |
| **16** | **Non-existence G** | **Wave 8** | **§15 + BG §16 + §9** |

---

## 参考文献・リンク

- **Peterfalvi, T.** (2000). _Character Theory for the Odd Order Theorem_. LMS Lecture Note Series 272.
  mmd 参考: `/Users/ywr/odd-order/references/peterfalvi/04.16_pp_87_92_*.mmd`

- **Brauer, R. & Fowler, K.A.** (1955). _On groups of even order_. Ann. Math.
  References: BG (Phase 2a) + BG App.C (Theorem C)

- **BG overview**: `notes/bg/_overview.md` (Phase 2a のロードマップ)

- **Phase 2b overview**: `notes/peterfalvi/_overview.md` (全 §1-§16 + 付録)

- **FT クリティカルパス**: Phase 1 Isaacs → Phase 2a BG → Phase 2b Peterfalvi §3-§16 → Phase 3 (統合) → Phase 4 (メイン定理)

---

*作成: 2026-05-22*
*スコープ*: Peterfalvi §16 pp.87-92 (184 行, 11 結果 (14.1)-(14.11))
*形式化先 (予定)**: OddOrder/Peterfalvi/S16_NonExistenceG.lean (1000-1200 行)
*次ステップ*: Phase 2a (BG 全部) + §15 (S, T) 完成後、Wave 1 から着手

