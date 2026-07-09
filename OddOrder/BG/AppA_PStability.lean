/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppA_PStabilityBasic

/-!
# TAIL

Prefix-split from `OddOrder.BG.AppA_PStability` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.BG.AppA
open Representation Module Function LinearMap Submodule

universe uF uG uV

variable {p : ℕ} [Fact p.Prime]
variable {F : Type uF} [Field F] [CharP F p]
variable {V : Type uV} [AddCommGroup V] [Module F V] [Module.Finite F V]
variable {G : Type uG} [Group G]

section PStability

/-! ### 共役元 helpers (A.3 用)

`y := g * x * g⁻¹` (= conjugate of `x` by `g`) は `x` と同じ性質を持つ:
- `(ρ y - 1) ^ 2 = 0` (quadratic minpoly 保存)
- `ρ y ≠ 1` (≠ 1 保存; ρ faithful の前提下)
- `IsPGroup p (zpowers y)` (p-element 保存)

A.3 Step 3 で `H := closure {x, gxg⁻¹}` を Baer-Suzuki で構築するとき, `y = gxg⁻¹`
が `x` と同じ性質 (= K = conjugacy class) を持つ事実が必要. -/

omit [Module.Finite F V] in
/-- `ρ (g * x * g⁻¹) - 1 = ρg * (ρx - 1) * ρg⁻¹` (conjugation factorization). -/
lemma representation_conj_sub_one
    (ρ : Representation F G V) (x g : G) :
    (ρ (g * x * g⁻¹) : Module.End F V) - 1
      = ρ g * ((ρ x : Module.End F V) - 1) * ρ g⁻¹ := by
  have hgg : (ρ g : Module.End F V) * ρ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, hgg]

omit [Module.Finite F V] in
/-- 共役元は同じ quadratic minimal polynomial を持つ: `(ρ x - 1)² = 0 ⇒ (ρ(gxg⁻¹) - 1)² = 0`.
A.3 で `y = gxg⁻¹` ∈ K (conjugacy class of x) も quadratic を持つことに使用. -/
lemma representation_conj_quadratic
    (ρ : Representation F G V) (x g : G)
    (hxsq : ((ρ x : Module.End F V) - 1) ^ 2 = 0) :
    ((ρ (g * x * g⁻¹) : Module.End F V) - 1) ^ 2 = 0 := by
  have hgg' : (ρ g⁻¹ : Module.End F V) * ρ g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [representation_conj_sub_one ρ x g]
  -- (ρg * A * ρg⁻¹)^2 = ρg * A * (ρg⁻¹ * ρg) * A * ρg⁻¹ = ρg * A² * ρg⁻¹ = 0
  calc (ρ g * ((ρ x : Module.End F V) - 1) * ρ g⁻¹) ^ 2
      = ρ g * ((ρ x : Module.End F V) - 1) * ρ g⁻¹
          * (ρ g * ((ρ x : Module.End F V) - 1) * ρ g⁻¹) := by rw [sq]
    _ = ρ g * ((ρ x : Module.End F V) - 1) * (ρ g⁻¹ * ρ g)
          * ((ρ x : Module.End F V) - 1) * ρ g⁻¹ := by
            simp only [mul_assoc]
    _ = ρ g * ((ρ x : Module.End F V) - 1) * 1
          * ((ρ x : Module.End F V) - 1) * ρ g⁻¹ := by rw [hgg']
    _ = ρ g * (((ρ x : Module.End F V) - 1)
          * ((ρ x : Module.End F V) - 1)) * ρ g⁻¹ := by
            simp only [mul_one, mul_assoc]
    _ = ρ g * ((ρ x : Module.End F V) - 1) ^ 2 * ρ g⁻¹ := by rw [← sq]
    _ = ρ g * 0 * ρ g⁻¹ := by rw [hxsq]
    _ = 0 := by rw [mul_zero, zero_mul]

omit [Module.Finite F V] in
/-- 共役元は `ρ` 上 `≠ 1` を保つ: `ρ x ≠ 1 ⇒ ρ(gxg⁻¹) ≠ 1`. -/
lemma representation_conj_ne_one
    (ρ : Representation F G V) (x g : G) (hxne : ρ x ≠ 1) :
    ρ (g * x * g⁻¹) ≠ 1 := by
  intro h
  apply hxne
  -- ρ(gxg⁻¹) = ρg ρx ρg⁻¹ = 1 ⇒ ρx = ρg⁻¹ * 1 * ρg = 1
  have hgg : (ρ g : Module.End F V) * ρ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hg'g : (ρ g⁻¹ : Module.End F V) * ρ g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h1 : (ρ g : Module.End F V) * ρ x * ρ g⁻¹ = 1 := by
    rw [← map_mul, ← map_mul]; exact h
  -- ρx = ρg⁻¹ * (ρg * ρx * ρg⁻¹) * ρg = ρg⁻¹ * 1 * ρg = 1
  have : (ρ x : Module.End F V)
       = ρ g⁻¹ * (ρ g * ρ x * ρ g⁻¹) * ρ g := by
    calc (ρ x : Module.End F V)
        = 1 * ρ x * 1 := by rw [one_mul, mul_one]
      _ = (ρ g⁻¹ * ρ g) * ρ x * (ρ g⁻¹ * ρ g) := by rw [hg'g]
      _ = ρ g⁻¹ * (ρ g * ρ x * ρ g⁻¹) * ρ g := by
            simp only [mul_assoc]
  rw [this, h1, mul_one, hg'g]

/-- 共役元は p-element を保つ: `IsPGroup p (zpowers x) ⇒ IsPGroup p (zpowers (gxg⁻¹))`.
証明: `SemiconjBy g x (gxg⁻¹)` ⇒ `orderOf x = orderOf (gxg⁻¹)`, IsPGroup は orderOf
で特徴付け. -/
lemma isPGroup_zpowers_conj [Finite G]
    (x g : G) (hxp : IsPGroup p (Subgroup.zpowers x)) :
    IsPGroup p (Subgroup.zpowers (g * x * g⁻¹)) := by
  have hp_prime : p.Prime := Fact.out
  -- SemiconjBy g x (gxg⁻¹): g * x = (g * x * g⁻¹) * g
  have hsemi : SemiconjBy g x (g * x * g⁻¹) := by
    unfold SemiconjBy
    group
  have horder : orderOf x = orderOf (g * x * g⁻¹) := hsemi.orderOf_eq g
  -- IsPGroup p (zpowers a) ↔ ∃ n, |zpowers a| = p^n; |zpowers a| = orderOf a (mathlib)
  rw [IsPGroup.iff_card] at hxp ⊢
  rw [Nat.card_zpowers, ← horder, ← Nat.card_zpowers]
  exact hxp

/-- **p-stability** (Gorenstein 1968 p.105 definition, BG App.A 用途).

`G` が `p`-stable とは: `F` の alg-closed char `p` 上の有限次元 nontrivial vector space
`V` への **忠実な representation** `ρ : G →* End F V` で、任意の `p`-element `x : G` が
**quadratic minimal polynomial** `(X - 1)²` を持つ(= `(ρ x - 1)² = 0` ∧ `ρ x ≠ 1`)
ことは無い、というもの.

Gorenstein は `GF(p^n)` 上の faithful rep で定義するが、`GF(p^n) → F` 拡張 (= base change)
で alg closure に持ち上がり同値. Lean では alg closure 版で statement.

**注意**: Gorenstein の p-stability は通常「`G` has no nontrivial normal `p`-subgroups」
かつ `p` odd の context で定義する. 本 def はそれらを前提に組み込まず、`IsPStable` を
使う側の定理 (A.3, A.4) で hypothesis として渡す方針 (def シンプル + 整合性).

下流: A.3, A.4(a) で使用. -/
def IsPStable (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ ⦃F : Type*⦄ [Field F] [CharP F p] [IsAlgClosed F]
    ⦃V : Type*⦄ [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    (ρ : Representation F G V), Function.Injective ρ →
    ∀ x : G, IsPGroup p (Subgroup.zpowers x) →
      ((ρ x : Module.End F V) - 1) ^ 2 = 0 → ρ x = 1

/-- **BG Theorem A.3** (mmd L4476, = Gorenstein Ch.3 §8 Thm 8.3 weakening,
mmd L2288): `p` odd, `G` に非自明な正規 `p`-部分群が無く (= `O_p(G) = 1`),
`G` が `p`-stable でないなら `|G|` は偶.

**証明 (= Gorenstein 8.3 翻訳, A.2 を 8.1 の代わりに使う, mmd L2290-L2310)**:
1. `¬ IsPStable p G` ⇒ ∃ ρ faithful, ∃ x p-element with quadratic minpoly.
2. `K := x` の conjugacy class. 全 K の元は同じ性質.
3. **Baer-Suzuki (Gorenstein 8.2)** で `O_p(G) = 1` + K で全 pair p-群を生成」が
   不可能 ⇒ ∃ y ∈ K, `H := ⟨x, y⟩` は p-群でない.
4. H-invariant chain `V ⊃ V_2 ⊃ ... ⊃ 0` で H が各 quotient 上既約.
5. `N_i := ker(H → End(V_i/V_{i+1}))`. ∃ i, `N_i ⊊ H` (反例: 全 N_i = H ⇒ H の
   p'-部分群は全 quotient 上自明 → V 上自明 (coprime action) → faithful より = 1 ⇒
   H p-群、矛盾).
6. `H/N_i` faithful irreducible action on `V_i/V_{i+1}`, x̄, ȳ quadratic minpoly.
7. **A.2 (`quadratic_two_generated_irreducible_finrank_eq_two` + closure_eq via x̄, ȳ
   generators)** で `|H/N_i|` 偶.
8. `2 ∣ |H/N_i| ∣ |H| ∣ |G|` ⇒ `|G|` 偶. ∎

依存:
- ✅ `OddOrder.Isaacs.Ch01.opCore` (= `O_p(G)`)
- ✅ `OddOrder.Isaacs.Ch02.baerSuzuki_pCore` (Baer-Suzuki 単一元 form)
- ✅ `quadratic_two_generated_irreducible_finrank_eq_two` (= A.2)
- ❌ H-invariant chain + quotient representation (新規)
- ❌ p'-element trivial on quotients ⇒ trivial on V (coprime action 結果)

詳細・着手順は issue [#0043](../../issues/0043-bg-appa-a3-pstability.md). -/
theorem thmA3 [Finite G] (_hp_odd : p ≠ 2)
    (h_Op_trivial : OddOrder.Isaacs.Ch01.opCore p G = ⊥)
    (h_not_pstable : ¬ IsPStable p G) :
    ¬ Odd (Nat.card G) := by
  intro hodd
  -- ## Step 1: ¬ IsPStable を unfold + push Not で証人を取り出す
  unfold IsPStable at h_not_pstable
  push Not at h_not_pstable
  obtain ⟨F, _, _, _, V, _, _, _, _, ρ, hfaithful, x, hxp, hxsq, hxne⟩ :=
    h_not_pstable
  -- ## Step 2: Baer-Suzuki で ⟨x, gxg⁻¹⟩ が非 p-群となる g を取得
  -- x ≠ 1 (ρ x ≠ 1 + faithful)
  have hx_ne_one : x ≠ 1 := by
    intro h; apply hxne; rw [h, map_one]
  -- x ∉ O_p(G) (= ⊥ なので x ≠ 1 から)
  have hx_not_in_Op : x ∉ OddOrder.Isaacs.Ch01.opCore p G := by
    rw [h_Op_trivial]
    intro h
    exact hx_ne_one (Subgroup.mem_bot.mp h)
  -- baerSuzuki_pCore.mpr の対偶で ∃ g, ⟨x, gxg⁻¹⟩ 非 p-群
  have h_exists_g : ∃ g : G,
      ¬ IsPGroup p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
    by_contra h_all
    push Not at h_all
    exact hx_not_in_Op
      ((OddOrder.Isaacs.Ch02.baerSuzuki_pCore x).mpr h_all)
  obtain ⟨g, h_pair_not_pgroup⟩ := h_exists_g
  -- ## Step 3: `y := g x g⁻¹` ∈ K (= conjugacy class of x) も同じ性質を持つ
  set y : G := g * x * g⁻¹ with hy_def
  -- y は p-element, ρ y は quadratic で ≠ 1
  have hysq : ((ρ y : Module.End F V) - 1) ^ 2 = 0 :=
    representation_conj_quadratic ρ x g hxsq
  have hyne : ρ y ≠ 1 := representation_conj_ne_one ρ x g hxne
  have hyp : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_conj x g hxp
  -- H := ⟨x, y⟩ ≤ G は非 p-群
  set H : Subgroup G := Subgroup.closure ({x, y} : Set G) with hH_def
  have hH_not_pgroup : ¬ IsPGroup p H := h_pair_not_pgroup
  -- x ∈ H, y ∈ H
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  -- ## Steps 4-8 (Gorenstein 8.3 mmd L2293-L2298): 合成列 + coprime action + A.2
  -- 残りの目標 = `2 ∣ |G|`. これを出せば `hodd : Odd |G|` と矛盾.
  --
  -- 4. H-invariant 合成列 `V = V_1 ⊋ V_2 ⊋ ... ⊋ V_{m+1} = 0` を構成
  --    (V finite-dim + 再帰的に H-irreducible quotient を取得).
  --    mathlib: `RingTheory.SimpleModule` / `Order.JordanHolder.CompositionSeries`.
  --
  -- 5. N_i := ker(H → End_F (V_i/V_{i+1})). 全 i で N_i = H と仮定すると
  --    H に nontrivial p'-subgroup Q が存在 (H not p-group, Cauchy + IsPGroup
  --    否定). Q は全 V_i/V_{i+1} 上自明 ⇒ **coprime action (Gorenstein Thm 3.4
  --    翻訳)** で Q は V 上自明 ⇒ ρ|_Q = 1
  --    ⇒ ρ faithful + Q ≠ 1 と矛盾. ∴ ∃ i, N_i ⊊ H.
  --
  -- 6. その i で H̄ := H/N_i, ρ̄ : H̄ → End_F (V_i/V_{i+1}) faithful + irreducible.
  --    H̄ = ⟨x̄, ȳ⟩ (closure 商).
  --
  -- 7. x̄, ȳ ≠ 1: もし x̄ = 1 なら H̄ = ⟨ȳ⟩ は p-group (ȳ p-element, `hyp` 使用).
  --    H̄ p-group + alg-closed char p faithful irreducible は不可能
  --    (= Gorenstein Thm 1.2 = repo `PGroupFixedVector.invariants_ne_bot` 系)
  --    ⇒ H̄ = 1 ⇒ N_i = H, 矛盾. 同様に ȳ ≠ 1.
  --
  -- 8. A.2 (`thmA2`) を H̄ ↷ V_i/V_{i+1} に適用 (closure_eq via x̄, ȳ 生成元)
  --    ⇒ ¬ Odd |H̄| ⇒ 2 ∣ |H̄|. 2 ∣ |H̄| ∣ |H| ∣ |G| (Lagrange) で 2 ∣ |G|. ∎
  --
  -- TODO 主要新規補題 (issue #0043 + notes/bg/appA_pstability.md):
  --   * H-invariant `CompositionSeries` of `V` as `F[H]`-module
  --   * `coprime_action_trivial_of_trivial_on_quotients` (= Gorenstein Thm 3.4)
  --   * `IsPGroup.faithful_irreducible_in_charP_trivial` (= Gorenstein Thm 1.2)
  --   * Quotient representation `H → H/N_i → End_F (V_i/V_{i+1})`
  have h_two_dvd : 2 ∣ Nat.card G := by
    -- ## Step 5: Set up ρ_H : Representation F ↥H V via subgroup restriction
    let ρ_H : Representation F ↥H V := ρ.comp H.subtype
    have hρH_faithful : Function.Injective ρ_H :=
      fun a b hab => Subtype.ext (hfaithful hab)
    -- Well-foundedness for `Subrepresentation ρ_H` via toSubmodule embedding.
    -- `Submodule F V` has WF (both directions) for finite-dim V.
    haveI hwf_LT : WellFoundedLT (Subrepresentation ρ_H) := by
      apply StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule)
      intros a b hab
      exact lt_of_le_of_ne hab.le
        (fun h => hab.ne (Subrepresentation.toSubmodule_injective h))
    haveI hwf_GT : WellFoundedGT (Subrepresentation ρ_H) := by
      apply StrictMono.wellFoundedGT (f := Subrepresentation.toSubmodule)
      intros a b hab
      exact lt_of_le_of_ne hab.le
        (fun h => hab.ne (Subrepresentation.toSubmodule_injective h))
    haveI : Nonempty (Subrepresentation ρ_H) := ⟨⊥⟩
    -- Get covBy chain in `Subrepresentation ρ_H`
    obtain ⟨a, h_min, n, h_max, h_cov⟩ :=
      exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Subrepresentation ρ_H)
    -- Translate to Submodule chain
    have h_a0_bot : (a 0).toSubmodule = ⊥ := by
      have h_eq : a 0 = ⊥ := h_min.eq_bot
      rw [h_eq]; rfl
    have h_an_top : (a n).toSubmodule = ⊤ := by
      have h_eq : a n = ⊤ := h_max.eq_top
      rw [h_eq]; rfl
    -- ## Step 6: 分岐 — H が全 quotient で自明か否か
    by_cases h_all_triv : ∀ i : ℕ, i < n → ∀ (h : ↥H) (v : V),
        v ∈ (a (i + 1)).toSubmodule → ρ_H h v - v ∈ (a i).toSubmodule
    · -- Case A: 全 quotient 自明 ⇒ coprime action chain で矛盾
      exfalso
      -- A.1: ∃ prime r ≠ p with r ∣ |↥H| (H not p-group + 素因数分解)
      have hH_card_pos : 0 < Nat.card ↥H := Nat.card_pos
      have hH_card_ne_zero : Nat.card ↥H ≠ 0 := hH_card_pos.ne'
      have h_not_pow : ¬ ∃ k : ℕ, Nat.card ↥H = p ^ k := by
        intro hc; exact hH_not_pgroup (IsPGroup.iff_card.mpr hc)
      obtain ⟨r, hr_prime, hr_dvd, hr_ne_p⟩ :
          ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card ↥H ∧ r ≠ p := by
        by_contra h_no
        push Not at h_no
        apply h_not_pow
        have hall : ∀ q ∈ (Nat.card ↥H).primeFactorsList, q = p := by
          intro q hq
          rw [Nat.mem_primeFactorsList hH_card_ne_zero] at hq
          exact h_no q hq.1 hq.2
        refine ⟨(Nat.card ↥H).primeFactorsList.length, ?_⟩
        rw [← List.prod_replicate, ← List.eq_replicate_of_mem hall,
          Nat.prod_primeFactorsList hH_card_ne_zero]
      -- A.2: Cauchy で q ∈ ↥H, orderOf q = r
      haveI : Fact r.Prime := ⟨hr_prime⟩
      obtain ⟨q, hq_order⟩ : ∃ q : ↥H, orderOf q = r :=
        exists_prime_orderOf_dvd_card' r hr_dvd
      -- q ≠ 1
      have hq_ne_one : q ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hq_order
        -- hq_order : 1 = r, and hr_prime.one_lt : 1 < r ⇒ 1 ≠ r
        exact hr_prime.one_lt.ne hq_order
      have hqG_ne_one : (q : G) ≠ 1 := by
        intro h
        exact hq_ne_one (Subtype.ext h)
      -- A.3: Q := zpowers q (as Subgroup ↥H) — work entirely in ↥H
      let Q : Subgroup ↥H := Subgroup.zpowers q
      let ρ_Q : Representation F ↥Q V := ρ_H.comp Q.subtype
      -- Cardinality of Q is r
      have hQ_card : Nat.card ↥Q = r := by
        rw [Nat.card_zpowers]; exact hq_order
      -- (Nat.card ↥Q : F) ≠ 0 since r ≠ p = char F
      haveI hQ_nezero : NeZero ((Nat.card ↥Q : F)) := by
        constructor
        intro h_zero
        rw [hQ_card] at h_zero
        have hp_dvd_r : p ∣ r := by
          rwa [CharP.cast_eq_zero_iff F p r] at h_zero
        have hp_prime : p.Prime := Fact.out
        rcases hr_prime.eq_one_or_self_of_dvd p hp_dvd_r with h1 | h2
        · exact hp_prime.one_lt.ne' h1
        · exact hr_ne_p h2.symm
      haveI : Finite ↥Q := inferInstance
      -- A.4: Apply coprime_action_trivial_chain to ρ_Q
      have h_Q_triv : ∀ (g : ↥Q) (v : V), ρ_Q g v = v := by
        apply OddOrder.GroupTheory.RepresentationTheory.coprime_action_trivial_chain
          ρ_Q (s := fun i : Fin (n + 1) => (a (i : ℕ)).toSubmodule)
        · -- s 0 = ⊥ (= h_a0_bot via beta + Fin cast)
          simpa using h_a0_bot
        · -- s (Fin.last n) = ⊤
          have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := by simp
          show (a ((Fin.last n : Fin (n + 1)) : ℕ)).toSubmodule = ⊤
          rw [hlast]; exact h_an_top
        · -- h_triv_quot
          intro g_q i v hv
          have h_eq : ρ_Q g_q v = ρ_H (g_q : ↥H) v := rfl
          show ρ_Q g_q v - v ∈ (a ((i.castSucc : Fin (n + 1)) : ℕ)).toSubmodule
          rw [h_eq]
          have hcastSucc : ((i.castSucc : Fin (n + 1)) : ℕ) = i.val := by simp
          have hsucc : ((i.succ : Fin (n + 1)) : ℕ) = i.val + 1 := by simp
          rw [hcastSucc]
          have hv' : v ∈ (a (i.val + 1)).toSubmodule := by
            have hv_in : v ∈ (a ((i.succ : Fin (n + 1)) : ℕ)).toSubmodule := hv
            rwa [hsucc] at hv_in
          exact h_all_triv i.val i.isLt (g_q : ↥H) v hv'
      -- A.5: ρ q = 1 (via ρ_Q at ⟨q, mem_zpowers_self⟩)
      have h_ρq_one : ρ (q : G) = 1 := by
        ext v
        rw [Module.End.one_apply]
        have hself : q ∈ Subgroup.zpowers q := Subgroup.mem_zpowers q
        have h_app := h_Q_triv ⟨q, hself⟩ v
        -- ρ_Q ⟨q, hself⟩ v = ρ_H q v = ρ (q : G) v
        change ρ (q : G) v = v at h_app
        exact h_app
      -- A.6: 矛盾 — q = 1 (by faithful) と q ≠ 1
      have hq_eq_one : (q : G) = 1 := by
        apply hfaithful
        rw [h_ρq_one, map_one]
      exact hqG_ne_one hq_eq_one
    · -- Case B: ∃ i, action non-trivial. Apply A.2.
      push Not at h_all_triv
      obtain ⟨i, hi_lt_n, q_witness, v_witness, hv_witness, h_not_triv_witness⟩ :=
        h_all_triv
      -- Step 7a: N_i := {h ∈ ↥H | h acts trivially on a(i+1)/a i}
      let N_i : Subgroup ↥H :=
        { carrier := { h | ∀ v ∈ (a (i + 1)).toSubmodule,
                            ρ_H h v - v ∈ (a i).toSubmodule }
          one_mem' := by
            intro v _
            show ρ_H 1 v - v ∈ (a i).toSubmodule
            simp [map_one, Module.End.one_apply]
          mul_mem' := by
            intro h₁ h₂ hh₁ hh₂ v hv
            show ρ_H (h₁ * h₂) v - v ∈ (a i).toSubmodule
            have h_decomp : ρ_H (h₁ * h₂) v - v
                = ρ_H h₁ (ρ_H h₂ v - v) + (ρ_H h₁ v - v) := by
              rw [map_mul, Module.End.mul_apply, map_sub]
              abel
            rw [h_decomp]
            exact (a i).toSubmodule.add_mem
              ((a i).apply_mem_toSubmodule h₁ (hh₂ v hv)) (hh₁ v hv)
          inv_mem' := by
            intro h hh v hv
            show ρ_H h⁻¹ v - v ∈ (a i).toSubmodule
            -- key: ρ_H h⁻¹ v - v = ρ_H h⁻¹ (-(ρ_H h v - v))
            have h_apply : ρ_H h⁻¹ (-(ρ_H h v - v)) = ρ_H h⁻¹ v - v := by
              rw [map_neg, map_sub]
              have hh_inv : ρ_H h⁻¹ (ρ_H h v) = v := by
                rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                  Module.End.one_apply]
              rw [hh_inv]; abel
            rw [← h_apply]
            exact (a i).apply_mem_toSubmodule h⁻¹
              ((a i).toSubmodule.neg_mem (hh v hv)) }
      -- Step 7b: witness ∉ N_i
      have h_q_notin_Ni : q_witness ∉ N_i := by
        intro h_in
        exact h_not_triv_witness (h_in v_witness hv_witness)
      -- Step 7c: N_i.Normal
      have hN_i_normal : N_i.Normal := by
        constructor
        intro n hn g v hv
        show ρ_H (g * n * g⁻¹) v - v ∈ (a i).toSubmodule
        -- ρ_H (g n g⁻¹) v = ρ_H g (ρ_H n (ρ_H g⁻¹ v))
        -- v = ρ_H g (ρ_H g⁻¹ v)
        -- so diff = ρ_H g (ρ_H n (ρ_H g⁻¹ v) - ρ_H g⁻¹ v)
        have h_inv_v : ρ_H g (ρ_H g⁻¹ v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply]
        have h_compute : ρ_H (g * n * g⁻¹) v - v
            = ρ_H g (ρ_H n (ρ_H g⁻¹ v) - ρ_H g⁻¹ v) := by
          rw [map_sub]
          congr 1
          · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
          · exact h_inv_v.symm
        rw [h_compute]
        have hgv_in : ρ_H g⁻¹ v ∈ (a (i + 1)).toSubmodule :=
          (a (i + 1)).apply_mem_toSubmodule g⁻¹ hv
        have h_n_act : ρ_H n (ρ_H g⁻¹ v) - ρ_H g⁻¹ v ∈ (a i).toSubmodule :=
          hn (ρ_H g⁻¹ v) hgv_in
        exact (a i).apply_mem_toSubmodule g h_n_act
      -- Step 7d: V_quot setup
      let aip1_top : Submodule F V := (a (i + 1)).toSubmodule
      let ai_in_aip1 : Submodule F ↥aip1_top :=
        (a i).toSubmodule.comap aip1_top.subtype
      -- a i ⋖ a (i+1) ⇒ a i < a (i+1) as Submodule
      have h_ai_lt_aip1 : (a i).toSubmodule < aip1_top := by
        have h_lt : a i < a (i + 1) := (h_cov i hi_lt_n).lt
        show (a i).toSubmodule < (a (i + 1)).toSubmodule
        exact lt_of_le_of_ne h_lt.le
          (fun h_eq => h_lt.ne (Subrepresentation.toSubmodule_injective h_eq))
      have h_ai_in_aip1_ne_top : ai_in_aip1 ≠ ⊤ := by
        intro h_eq
        apply h_ai_lt_aip1.ne
        apply le_antisymm h_ai_lt_aip1.le
        intro w hw
        have hw_subt : (⟨w, hw⟩ : ↥aip1_top) ∈ ai_in_aip1 := by rw [h_eq]; trivial
        exact hw_subt
      haveI hV_quot_nontriv : Nontrivial (↥aip1_top ⧸ ai_in_aip1) := by
        rw [Submodule.Quotient.nontrivial_iff]
        exact h_ai_in_aip1_ne_top
      haveI hV_quot_finite : Module.Finite F (↥aip1_top ⧸ ai_in_aip1) :=
        Module.Finite.of_surjective ai_in_aip1.mkQ ai_in_aip1.mkQ_surjective
      -- Step 7e: ρ_quot : Representation F ↥H (↥aip1_top ⧸ ai_in_aip1)
      have h_inv_aip1 : ∀ g : ↥H,
          ai_in_aip1 ≤ ai_in_aip1.comap ((a (i + 1)).toRepresentation g) := by
        intro g w hw
        change ((a (i + 1)).toRepresentation g w).val ∈ (a i).toSubmodule
        change ρ_H g w.val ∈ (a i).toSubmodule
        exact (a i).apply_mem_toSubmodule g hw
      let ρ_quot : Representation F ↥H (↥aip1_top ⧸ ai_in_aip1) :=
        Representation.quotient (a (i + 1)).toRepresentation ai_in_aip1 h_inv_aip1
      -- Step 7f: N_i acts trivially on V_quot (= IsTrivial ρ_quot.comp N_i.subtype)
      haveI hN_i_triv :
          Representation.IsTrivial (ρ_quot.comp N_i.subtype) := by
        constructor
        intro n
        apply LinearMap.ext
        intro v_q
        refine Quotient.inductionOn' v_q (fun w => ?_)
        -- Goal: ρ_quot ↑n (Quotient.mk' w) = 1 (Quotient.mk' w)
        change Submodule.Quotient.mk ((a (i + 1)).toRepresentation
                (N_i.subtype n) w) = Submodule.Quotient.mk w
        rw [Submodule.Quotient.eq]
        change ρ_H (N_i.subtype n) w.val - w.val ∈ (a i).toSubmodule
        exact n.property w.val w.property
      -- Step 7g: ρ_bar : Representation F (↥H ⧸ N_i) (V_quot)
      haveI := hN_i_normal
      let ρ_bar : Representation F (↥H ⧸ N_i) (↥aip1_top ⧸ ai_in_aip1) :=
        Representation.ofQuotient ρ_quot N_i
      -- Step 7h: ρ_bar faithful
      have hρ_bar_faithful : Function.Injective ρ_bar := by
        rw [injective_iff_map_eq_one]
        intro hbar
        refine Quotient.inductionOn' hbar (fun h => ?_)
        intro hh_eq
        rw [QuotientGroup.eq_one_iff]
        intro v hv
        have h_quot_h_eq : ρ_quot h = 1 := by
          apply LinearMap.ext
          intro v_q
          refine Quotient.inductionOn' v_q (fun w => ?_)
          -- Goal: ρ_quot h (Quotient.mk'' w) = 1 (Quotient.mk'' w)
          -- Rewrite ρ_quot via ρ_bar:
          have h_app : ρ_quot h (Submodule.Quotient.mk w) =
              ρ_bar (QuotientGroup.mk h) (Submodule.Quotient.mk w) :=
            (Representation.ofQuotient_coe_apply ρ_quot N_i h _).symm
          -- mk equals: Submodule.Quotient.mk w = Quotient.mk'' w
          have h_mk_eq : (Submodule.Quotient.mk w : ↥aip1_top ⧸ ai_in_aip1) =
              Quotient.mk'' w := rfl
          rw [← h_mk_eq, h_app]
          -- ρ_bar (QuotientGroup.mk h) = ρ_bar (Quotient.mk'' h) = 1
          have h_eq_qbar : (QuotientGroup.mk h : ↥H ⧸ N_i) = Quotient.mk'' h := rfl
          rw [h_eq_qbar, hh_eq]
        have h_app_v : ρ_quot h (Submodule.Quotient.mk ⟨v, hv⟩)
            = Submodule.Quotient.mk ⟨v, hv⟩ := by
          rw [h_quot_h_eq, Module.End.one_apply]
        change Submodule.Quotient.mk ((a (i + 1)).toRepresentation h ⟨v, hv⟩)
            = Submodule.Quotient.mk ⟨v, hv⟩ at h_app_v
        rw [Submodule.Quotient.eq] at h_app_v
        change ρ_H h v - v ∈ (a i).toSubmodule
        exact h_app_v
      -- Step 7i: ρ_bar irreducible
      have hρ_bar_irr : ∀ U : Submodule F (↥aip1_top ⧸ ai_in_aip1),
          (∀ g : ↥H ⧸ N_i, ∀ v ∈ U, ρ_bar g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
        intro U hU_inv
        -- W := comap mkQ U : Submodule of aip1_top, contains ai_in_aip1
        let W : Submodule F ↥aip1_top := Submodule.comap ai_in_aip1.mkQ U
        have hW_ge : ai_in_aip1 ≤ W := Submodule.le_comap_mkQ ai_in_aip1 U
        -- W invariant under (a(i+1)).toRepresentation
        have hW_inv : ∀ h : ↥H, ∀ w ∈ W, (a (i + 1)).toRepresentation h w ∈ W := by
          intro h w hw_W
          show ai_in_aip1.mkQ ((a (i + 1)).toRepresentation h w) ∈ U
          have h_step : ai_in_aip1.mkQ ((a (i + 1)).toRepresentation h w) =
              ρ_quot h (ai_in_aip1.mkQ w) := rfl
          rw [h_step]
          have hw_U : ai_in_aip1.mkQ w ∈ U := hw_W
          -- ρ_bar (QuotientGroup.mk h) (ai_in_aip1.mkQ w) = ρ_quot h (...)
          have h_eq : ρ_quot h (ai_in_aip1.mkQ w) =
              ρ_bar (QuotientGroup.mk h) (ai_in_aip1.mkQ w) :=
            (Representation.ofQuotient_coe_apply ρ_quot N_i h _).symm
          rw [h_eq]
          exact hU_inv (QuotientGroup.mk h) (ai_in_aip1.mkQ w) hw_U
        -- Build σ : Subrepresentation ρ_H with σ.toSubmodule = Submodule.map subtype W
        let σ : Subrepresentation ρ_H :=
          { toSubmodule := Submodule.map aip1_top.subtype W
            apply_mem_toSubmodule := by
              intro g v hv
              obtain ⟨⟨w, hw_aip1⟩, hw_W, hval_eq⟩ := hv
              refine ⟨(a (i + 1)).toRepresentation g ⟨w, hw_aip1⟩,
                hW_inv g ⟨w, hw_aip1⟩ hw_W, ?_⟩
              rw [← hval_eq]; rfl }
        -- a i ≤ σ
        have hai_le_σ : a i ≤ σ := by
          intro v hv
          have h_in_aip1 : v ∈ aip1_top := (h_cov i hi_lt_n).le hv
          refine ⟨⟨v, h_in_aip1⟩, ?_, rfl⟩
          show (⟨v, h_in_aip1⟩ : ↥aip1_top) ∈ W
          exact hW_ge hv
        -- σ ≤ a (i+1)
        have hσ_le_aip1 : σ ≤ a (i + 1) := by
          intro v hv
          obtain ⟨⟨w, hw_aip1⟩, _, hval_eq⟩ := hv
          rw [← hval_eq]; exact hw_aip1
        -- By covering: σ = a i or σ = a (i+1)
        have h_covby : a i ⋖ a (i + 1) := h_cov i hi_lt_n
        rcases h_covby.eq_or_eq hai_le_σ hσ_le_aip1 with hσ_eq_ai | hσ_eq_aip1
        · -- σ = a i ⇒ U = ⊥
          left
          rw [eq_bot_iff]
          intro u hu_U
          obtain ⟨w, rfl⟩ := ai_in_aip1.mkQ_surjective u
          have hw_W : w ∈ W := hu_U
          have hwval_σ : w.val ∈ σ.toSubmodule := ⟨w, hw_W, rfl⟩
          have hσ_eq : σ.toSubmodule = (a i).toSubmodule :=
            congr_arg Subrepresentation.toSubmodule hσ_eq_ai
          rw [hσ_eq] at hwval_σ
          have hw_ai : w ∈ ai_in_aip1 := hwval_σ
          show (ai_in_aip1.mkQ w : ↥aip1_top ⧸ ai_in_aip1) ∈
            (⊥ : Submodule F (↥aip1_top ⧸ ai_in_aip1))
          rw [Submodule.mem_bot, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero]
          exact hw_ai
        · -- σ = a (i+1) ⇒ U = ⊤
          right
          rw [eq_top_iff]
          intro u _
          obtain ⟨w, rfl⟩ := ai_in_aip1.mkQ_surjective u
          show w ∈ W
          have hwval_aip1 : w.val ∈ aip1_top := w.property
          have hσ_eq : σ.toSubmodule = (a (i + 1)).toSubmodule :=
            congr_arg Subrepresentation.toSubmodule hσ_eq_aip1
          have hwval_σ : w.val ∈ σ.toSubmodule := by
            rw [hσ_eq]; exact hwval_aip1
          obtain ⟨⟨w', hw'_aip1⟩, hw'_W, hval_eq⟩ := hwval_σ
          have h_eq_w : w = ⟨w', hw'_aip1⟩ := Subtype.ext hval_eq.symm
          rw [h_eq_w]; exact hw'_W
      -- Step 7j: closure {x_bar, y_bar} = ⊤ in ↥H ⧸ N_i
      let x_subt : ↥H := ⟨x, hxH⟩
      let y_subt : ↥H := ⟨y, hyH⟩
      let x_bar : ↥H ⧸ N_i := QuotientGroup.mk x_subt
      let y_bar : ↥H ⧸ N_i := QuotientGroup.mk y_subt
      -- closure {x_subt, y_subt} = ⊤ in ↥H
      have h_gen_subt : Subgroup.closure ({x_subt, y_subt} : Set ↥H) = ⊤ := by
        apply Subgroup.map_injective H.subtype_injective
        rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, H.range_subtype]
        congr 1
        ext g
        constructor
        · rintro ⟨a, ha_mem, rfl⟩
          rcases ha_mem with rfl | rfl
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ rfl
        · rintro (rfl | rfl)
          · exact ⟨x_subt, Set.mem_insert _ _, rfl⟩
          · exact ⟨y_subt, Set.mem_insert_of_mem _ rfl, rfl⟩
      -- closure {x_bar, y_bar} = ⊤ in ↥H ⧸ N_i
      have h_gen_bar : Subgroup.closure ({x_bar, y_bar} : Set (↥H ⧸ N_i)) = ⊤ := by
        have h_eq : ({x_bar, y_bar} : Set (↥H ⧸ N_i)) =
            (QuotientGroup.mk' N_i) '' ({x_subt, y_subt} : Set ↥H) := by
          ext z
          constructor
          · rintro (rfl | rfl)
            · exact ⟨x_subt, Set.mem_insert _ _, rfl⟩
            · exact ⟨y_subt, Set.mem_insert_of_mem _ rfl, rfl⟩
          · rintro ⟨a, ha_mem, rfl⟩
            rcases ha_mem with rfl | rfl
            · exact Set.mem_insert _ _
            · exact Set.mem_insert_of_mem _ rfl
        rw [h_eq, ← MonoidHom.map_closure, h_gen_subt,
          ← MonoidHom.range_eq_map]
        exact MonoidHom.range_eq_top_of_surjective _
          (QuotientGroup.mk'_surjective N_i)
      -- Step 7k: (ρ_bar x_bar - 1)² = 0 and similarly for y_bar
      have h_lift_sq : ∀ (z_subt : ↥H)
          (hzsq : ((ρ_H z_subt : Module.End F V) - 1) ^ 2 = 0),
          ((ρ_bar (QuotientGroup.mk z_subt) :
              Module.End F (↥aip1_top ⧸ ai_in_aip1)) - 1) ^ 2 = 0 := by
        intro z_subt hzsq
        apply LinearMap.ext
        intro v_q
        refine Quotient.inductionOn' v_q (fun w => ?_)
        -- Goal: ((ρ_bar (mk z_subt) - 1) ^ 2) (mk w) = 0 (mk w)
        -- Key fact: applying ρ_bar via ofQuotient_coe_apply: lifts to (a(i+1)).toRep z_subt
        -- (ρ_bar (mk z_subt) - 1) (mk u) = mk ((a(i+1)).toRep z_subt u - u) for any u
        have h_step : ∀ (u : ↥aip1_top),
            ((ρ_bar (QuotientGroup.mk z_subt) - 1)
              (Submodule.Quotient.mk u : ↥aip1_top ⧸ ai_in_aip1)) =
            Submodule.Quotient.mk ((a (i + 1)).toRepresentation z_subt u - u) := by
          intro u
          rw [LinearMap.sub_apply, Module.End.one_apply]
          have h_app : ρ_bar (QuotientGroup.mk z_subt) (Submodule.Quotient.mk u) =
              Submodule.Quotient.mk ((a (i + 1)).toRepresentation z_subt u) :=
            Representation.ofQuotient_coe_apply ρ_quot N_i z_subt _
          rw [h_app]; rfl
        set M : Module.End F (↥aip1_top ⧸ ai_in_aip1) :=
          (ρ_bar (QuotientGroup.mk z_subt) - 1) ^ 2 with hM_def
        have h_sq_app : M (Quotient.mk'' w) =
            Submodule.Quotient.mk ((a (i + 1)).toRepresentation z_subt
              ((a (i + 1)).toRepresentation z_subt w - w) -
              ((a (i + 1)).toRepresentation z_subt w - w)) := by
          show M (Submodule.Quotient.mk w) = _
          rw [hM_def, pow_two, Module.End.mul_apply, h_step, h_step]
        rw [h_sq_app]
        -- The inner argument equals 0 in ↥aip1_top.
        have h_inner_zero : (a (i + 1)).toRepresentation z_subt
            ((a (i + 1)).toRepresentation z_subt w - w) -
            ((a (i + 1)).toRepresentation z_subt w - w) = (0 : ↥aip1_top) := by
          apply Subtype.ext
          -- Compute .val
          have h_act : ∀ (u' : ↥aip1_top),
              ((a (i + 1)).toRepresentation z_subt u' : ↥aip1_top).val =
              ρ_H z_subt u'.val := fun _ => rfl
          show ((((a (i + 1)).toRepresentation z_subt
              ((a (i + 1)).toRepresentation z_subt w - w) -
              ((a (i + 1)).toRepresentation z_subt w - w)) : ↥aip1_top).val) =
              (0 : ↥aip1_top).val
          -- Step-by-step value computation
          rw [show ((((a (i + 1)).toRepresentation z_subt
                  ((a (i + 1)).toRepresentation z_subt w - w) -
                  ((a (i + 1)).toRepresentation z_subt w - w)) : ↥aip1_top).val) =
              (((a (i + 1)).toRepresentation z_subt
                  ((a (i + 1)).toRepresentation z_subt w - w)) : ↥aip1_top).val -
              (((a (i + 1)).toRepresentation z_subt w - w) : ↥aip1_top).val from rfl]
          rw [show ((((a (i + 1)).toRepresentation z_subt w - w) : ↥aip1_top).val) =
              ((a (i + 1)).toRepresentation z_subt w : ↥aip1_top).val - w.val from rfl]
          rw [h_act ((a (i + 1)).toRepresentation z_subt w - w), h_act w]
          show ρ_H z_subt (ρ_H z_subt w.val - w.val) - (ρ_H z_subt w.val - w.val)
              = (0 : V)
          -- (ρ_H z_subt - 1)² w.val = ρ_H z_subt (ρ_H z_subt w.val - w.val) - (ρ_H z_subt w.val - w.val)
          have h_at_val :
              ρ_H z_subt (ρ_H z_subt w.val - w.val) - (ρ_H z_subt w.val - w.val) = 0 := by
            have h := congr_arg (· w.val) hzsq
            simp only [LinearMap.zero_apply] at h
            rw [pow_two, Module.End.mul_apply,
              LinearMap.sub_apply, LinearMap.sub_apply,
              Module.End.one_apply, Module.End.one_apply] at h
            -- h : ρ_H z_subt (ρ_H z_subt w.val - w.val) - (ρ_H z_subt w.val - w.val) = 0
            exact h
          exact h_at_val
        rw [h_inner_zero, Submodule.Quotient.mk_zero]
        rfl
      have hx_bar_sq : ((ρ_bar x_bar : Module.End F _) - 1) ^ 2 = 0 := by
        have h_eq : ρ_H x_subt = ρ x := rfl
        exact h_lift_sq x_subt (by rw [h_eq]; exact hxsq)
      have hy_bar_sq : ((ρ_bar y_bar : Module.End F _) - 1) ^ 2 = 0 := by
        have h_eq : ρ_H y_subt = ρ y := rfl
        exact h_lift_sq y_subt (by rw [h_eq]; exact hysq)
      -- Step 7l: x_bar ≠ 1 and y_bar ≠ 1 (PGroupFixedVector argument)
      -- Helper: if z_subt ∈ N_i, then ↥H/N_i = ⟨other_bar⟩ p-group ⇒ contradiction
      -- We'll show: x_subt ∉ N_i and y_subt ∉ N_i.
      -- Argument structure (for x_subt):
      --   Suppose x_subt ∈ N_i. Then ↥H/N_i = closure {1, y_bar} = ⟨y_bar⟩.
      --   y_bar = image of y_subt (p-element) ⇒ y_bar is p-element ⇒ ⟨y_bar⟩ p-group.
      --   ⇒ ↥H/N_i p-group. ρ_bar faithful irreducible on V_quot in char p.
      --   PGroupFixedVector ⇒ ρ_bar.invariants ≠ ⊥, irreducibility ⇒ = ⊤
      --   ⇒ ρ_bar acts trivially ⇒ ↥H/N_i = 1 ⇒ q_witness ∈ N_i, 矛盾.
      have h_HN_not_pgroup_via : ∀ (z : G) (z_subt : ↥H) (hz_eq : (z_subt : G) = z)
          (hzp : IsPGroup p (Subgroup.zpowers z)),
          (Subgroup.zpowers (QuotientGroup.mk z_subt : ↥H ⧸ N_i)
            = (⊤ : Subgroup (↥H ⧸ N_i))) → False := by
        intro z z_subt hz_eq hzp h_top_zpow
        -- z_bar is p-element (via order divides z's order)
        have h_HN_pgroup : IsPGroup p (↥H ⧸ N_i) := by
          rw [IsPGroup.iff_card] at hzp
          obtain ⟨n, hn⟩ := hzp
          rw [Nat.card_zpowers] at hn
          have h_ord_z_subt : orderOf z_subt = orderOf z := by
            have h := orderOf_injective H.subtype Subtype.coe_injective z_subt
            simp only [Subgroup.coe_subtype] at h
            rw [hz_eq] at h
            exact h.symm
          have h_pow_mk : (QuotientGroup.mk z_subt : ↥H ⧸ N_i) ^ (p ^ n) = 1 := by
            have h_pow : z_subt ^ (p ^ n) = 1 := by
              rw [← h_ord_z_subt] at hn
              rw [← hn, pow_orderOf_eq_one]
            have h_eq : (QuotientGroup.mk z_subt : ↥H ⧸ N_i) ^ (p ^ n)
                = (QuotientGroup.mk (z_subt ^ (p ^ n)) : ↥H ⧸ N_i) := by
              show ((QuotientGroup.mk' N_i) z_subt) ^ (p ^ n) =
                (QuotientGroup.mk' N_i) (z_subt ^ (p ^ n))
              rw [map_pow]
            rw [h_eq, h_pow]; rfl
          have h_ord_mk_dvd : orderOf (QuotientGroup.mk z_subt : ↥H ⧸ N_i) ∣ p ^ n :=
            orderOf_dvd_of_pow_eq_one h_pow_mk
          obtain ⟨m, _, h_ord_mk⟩ := (Nat.dvd_prime_pow Fact.out).mp h_ord_mk_dvd
          -- Now ↥H ⧸ N_i = zpowers (mk z_subt) (by h_top_zpow), so card = orderOf mk z_subt
          intro g
          have h_g_in : g ∈ Subgroup.zpowers (QuotientGroup.mk z_subt : ↥H ⧸ N_i) := by
            rw [h_top_zpow]; trivial
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h_g_in
          -- g = (mk z_subt)^k. Order of g divides order of mk z_subt = p^m.
          refine ⟨m, ?_⟩
          have h_pow_g : g ^ (p ^ m) = 1 := by
            rw [← hk]
            rw [show ((QuotientGroup.mk z_subt : ↥H ⧸ N_i)^k)^(p^m)
                = ((QuotientGroup.mk z_subt : ↥H ⧸ N_i)^(p^m))^k by group]
            have : (QuotientGroup.mk z_subt : ↥H ⧸ N_i) ^ (p ^ m) = 1 := by
              rw [← h_ord_mk, pow_orderOf_eq_one]
            rw [this, one_zpow]
          exact h_pow_g
        -- ρ_bar.invariants ≠ ⊥
        haveI hHN_finite : Finite (↥H ⧸ N_i) := inferInstance
        have h_VQ_top_ne_bot : (⊤ : Submodule F (↥aip1_top ⧸ ai_in_aip1)) ≠ ⊥ := by
          intro h_bot
          obtain ⟨v, hv⟩ := exists_ne (0 : ↥aip1_top ⧸ ai_in_aip1)
          apply hv
          have : v ∈ (⊥ : Submodule F (↥aip1_top ⧸ ai_in_aip1)) := h_bot ▸ Submodule.mem_top
          exact (Submodule.mem_bot _).mp this
        have h_inv_ne_bot : ρ_bar.invariants ≠ ⊥ :=
          h_HN_pgroup.invariants_ne_bot ρ_bar h_VQ_top_ne_bot
        -- Irreducibility: invariants is ↥H/N_i-invariant
        have h_inv_subm_inv : ∀ g : ↥H ⧸ N_i, ∀ v ∈ ρ_bar.invariants,
            ρ_bar g v ∈ ρ_bar.invariants := by
          intro g v hv
          rw [Representation.mem_invariants] at hv ⊢
          intro h
          calc ρ_bar h (ρ_bar g v) = (ρ_bar h * ρ_bar g) v := by
                rw [Module.End.mul_apply]
            _ = ρ_bar (h * g) v := by rw [← map_mul]
            _ = ρ_bar g (ρ_bar (g⁻¹ * h * g) v) := by
                rw [show h * g = g * (g⁻¹ * h * g) by group, map_mul, Module.End.mul_apply]
            _ = ρ_bar g v := by rw [hv (g⁻¹ * h * g)]
        rcases hρ_bar_irr ρ_bar.invariants h_inv_subm_inv with h_bot | h_top
        · exact h_inv_ne_bot h_bot
        · -- ρ_bar.invariants = ⊤ ⇒ ρ_bar acts trivially
          have h_triv : ∀ g : ↥H ⧸ N_i, ρ_bar g = 1 := by
            intro g
            apply LinearMap.ext
            intro v
            have hv_inv : v ∈ ρ_bar.invariants := by rw [h_top]; exact Submodule.mem_top
            have := (Representation.mem_invariants ρ_bar v).mp hv_inv g
            rw [Module.End.one_apply]
            exact this
          -- ρ_bar = 1 ⇒ ↥H/N_i = 1 (faithful)
          have h_HN_trivial : ∀ g : ↥H ⧸ N_i, g = 1 := by
            intro g
            apply hρ_bar_faithful
            rw [h_triv g, map_one]
          -- But q_witness has nontrivial image in ↥H/N_i (since q_witness ∉ N_i)
          have h_q_bar_ne_one : (QuotientGroup.mk q_witness : ↥H ⧸ N_i) ≠ 1 := by
            intro h_eq; apply h_q_notin_Ni
            exact (QuotientGroup.eq_one_iff _).mp h_eq
          exact h_q_bar_ne_one (h_HN_trivial _)
      have hx_bar_ne : ρ_bar x_bar ≠ 1 := by
        intro h_eq
        have hx_bar_one : x_bar = 1 := hρ_bar_faithful (h_eq.trans (map_one ρ_bar).symm)
        -- closure {x_bar, y_bar} = ⊤; x_bar = 1 ⇒ ⟨y_bar⟩ = ⊤
        have h_zpow_y : Subgroup.zpowers y_bar = (⊤ : Subgroup (↥H ⧸ N_i)) := by
          apply le_antisymm le_top
          rw [← h_gen_bar]
          rw [Subgroup.closure_le]
          intro z hz
          rcases hz with hz | hz
          · subst hz; rw [hx_bar_one]; exact one_mem _
          · subst hz; exact Subgroup.mem_zpowers _
        exact h_HN_not_pgroup_via y y_subt rfl hyp h_zpow_y
      have hy_bar_ne : ρ_bar y_bar ≠ 1 := by
        intro h_eq
        have hy_bar_one : y_bar = 1 := hρ_bar_faithful (h_eq.trans (map_one ρ_bar).symm)
        have h_zpow_x : Subgroup.zpowers x_bar = (⊤ : Subgroup (↥H ⧸ N_i)) := by
          apply le_antisymm le_top
          rw [← h_gen_bar]
          rw [Subgroup.closure_le]
          intro z hz
          rcases hz with hz | hz
          · subst hz; exact Subgroup.mem_zpowers _
          · subst hz; rw [hy_bar_one]; exact one_mem _
        exact h_HN_not_pgroup_via x x_subt rfl hxp h_zpow_x
      -- Step 8: Apply thmA2 + Lagrange
      haveI : Finite (↥H ⧸ N_i) := inferInstance
      have h_HN_even : ¬ Odd (Nat.card (↥H ⧸ N_i)) :=
        thmA2 _hp_odd ρ_bar hρ_bar_faithful hρ_bar_irr x_bar y_bar h_gen_bar
          hx_bar_sq hx_bar_ne hy_bar_sq hy_bar_ne
      have h_2_dvd_HN : 2 ∣ Nat.card (↥H ⧸ N_i) := by
        rcases Nat.even_or_odd (Nat.card (↥H ⧸ N_i)) with h_even | h_odd
        · exact h_even.two_dvd
        · exact absurd h_odd h_HN_even
      -- Lagrange: |↥H ⧸ N_i| ∣ |↥H| ∣ |G|
      have h_HN_dvd_H : Nat.card (↥H ⧸ N_i) ∣ Nat.card ↥H := by
        rw [← Subgroup.index_eq_card]
        exact ⟨Nat.card N_i, N_i.index_mul_card.symm⟩
      have h_H_dvd_G : Nat.card ↥H ∣ Nat.card G := H.card_subgroup_dvd_card
      exact h_2_dvd_HN.trans (h_HN_dvd_H.trans h_H_dvd_G)
  exact hodd.not_two_dvd_nat h_two_dvd

/-- **BG Theorem A.4(a)** (mmd L4480, = Gorenstein Ch.6 §5 の特殊形): `p` odd, `G` 有限・
奇数位数で `O_p(G) = 1` (非自明な正規 `p`-部分群が無い) なら `G` は `p`-stable.

A.3 (`thmA3`) の対偶。`thmA3` が `¬IsPStable ∧ O_p(G)=1 ⇒ ¬Odd|G|` を与えるので,
`Odd|G|` のもとで `O_p(G)=1` なら `IsPStable`。BG の標準仮定「`G` solvable」は (a) には不要. -/
theorem thmA4a [Finite G] (hp_odd : p ≠ 2) (hodd : Odd (Nat.card G))
    (h_Op_trivial : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    IsPStable p G := by
  by_contra h_not
  exact thmA3 hp_odd h_Op_trivial h_not hodd

open scoped commutatorElement in
open OddOrder.GroupTheory OddOrder.Isaacs.Ch03 OddOrder.BG.Ch1.S01 in
/-- **Chain-stabilizer ⊆ centralizer (coprime)**: `M` 有限, `K ◁ M` を `p`-群, `D ≤ M` が
`K` と coprime (`(|D|,|K|)=1`) で `K` の chief series を stabilize
(`⁅Pᵢ, D⁆ ≤ Pᵢ₊₁`) するなら, `D ≤ C_M(K)`.

`MulAut.conjNormal : M →* MulAut ↥K` で `D` の作用を作り,
`coprime_stabilizes_chain_trivial` (BG Lem 1.9 多段一般形, S01 へ昇格済) を
`K` の chief series (`subgroupOf K` 化) に適用. -/
private theorem coprime_chainStabilizer_le_centralizer
    {M : Type*} [Group M] [Finite M]
    {K : Subgroup M} [K.Normal] (hK : IsPGroup p K)
    {D : Subgroup M} (hcop : (Nat.card ↥D).Coprime (Nat.card ↥K))
    (hsolv : IsSolvable ↥D ∨ IsSolvable ↥K)
    (hstab : ∀ i, ⁅chiefSeriesInside K i, D⁆ ≤ chiefSeriesInside K (i + 1)) :
    D ≤ Subgroup.centralizer (K : Set M) := by
  classical
  obtain ⟨N, hN⟩ := chiefSeriesInside_exists_eq_bot K
  set ψ : ↥D →* MulAut ↥K := (MulAut.conjNormal (H := K)).comp D.subtype with hψ
  set s : ℕ → Subgroup ↥K := fun i => (chiefSeriesInside K i).subgroupOf K with hs
  -- helper: `↑(ψ a g) = ↑a * ↑g * (↑a)⁻¹`
  have hψcoe : ∀ (a : ↥D) (g : ↥K), ((ψ a) g : M) = (a : M) * (g : M) * (a : M)⁻¹ := by
    intro a g; rw [hψ]; simp [MulAut.conjNormal_apply]
  have htrivψ : ∀ a : ↥D, ψ a = 1 := by
    refine coprime_stabilizes_chain_trivial ψ hcop hsolv s ?_ ?_ (n := N) ?_ ?_ ?_ ?_
    · -- Antitone s
      intro i j hij
      exact Subgroup.comap_mono (chiefSeriesInside_antitone K hij)
    · -- s 0 = ⊤
      simp [hs, chiefSeriesInside_zero, Subgroup.subgroupOf_self]
    · -- s N = ⊥
      simp [hs, hN, Subgroup.bot_subgroupOf]
    · -- normal
      intro i
      exact (inferInstance : (chiefSeriesInside K i).Normal).subgroupOf K
    · -- IsAInvariant
      intro i
      rw [isAInvariant_iff_smul_mem]
      intro a g hg
      rw [hs, Subgroup.mem_subgroupOf] at hg ⊢
      rw [hψcoe]
      exact (chiefSeriesInside_instNormal K i).conj_mem _ hg _
    · -- stabilize each factor
      intro i a x hx
      rw [hs, Subgroup.mem_subgroupOf] at hx
      refine ⟨x⁻¹ * ψ a x, ?_, by group⟩
      rw [hs, Subgroup.mem_subgroupOf]
      have hcoe : ((x⁻¹ * ψ a x : ↥K) : M) = ⁅(x : M)⁻¹, (a : M)⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hψcoe, commutatorElement_def]; group
      rw [hcoe]
      exact hstab i (Subgroup.commutator_mem_commutator
        (Subgroup.inv_mem _ hx) (SetLike.coe_mem a))
  -- conclude `D ≤ C_M(K)`
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := DFunLike.congr_fun (htrivψ ⟨x, hx⟩) ⟨k, hk⟩
  have h2 : (x : M) * k * x⁻¹ = k := by
    have := congrArg (Subtype.val) h1
    rwa [hψcoe] at this
  have h3 : x * k = k * x := by
    have := congrArg (· * x) h2
    simpa [mul_assoc] using this
  exact h3.symm

/-- `C_G(P)` を `N_G(P)` に制限したものは, `P` を `↥N_G(P)` の部分群 `P.subgroupOf N` と
見たときの `↥N_G(P)` 内 centralizer に一致する. `thmA4c` を `stabilityLiftAux`
(商 `M / C_M(K)` 形) に instantiate するときの橋渡し. -/
private theorem centralizer_subgroupOf_normalizer_eq {G : Type*} [Group G] (P : Subgroup G) :
    (Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.normalizer (P : Set G)) =
      Subgroup.centralizer
        ((P.subgroupOf (Subgroup.normalizer (P : Set G)) :
          Subgroup ↥(Subgroup.normalizer (P : Set G))) : Set _) := by
  have hP_le_N : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  ext n
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h m hm
    have hmP : (m : G) ∈ P := by
      have := hm; rwa [SetLike.mem_coe, Subgroup.mem_subgroupOf] at this
    exact Subtype.ext (h (m : G) hmP)
  · intro h x hx
    have hxN : x ∈ Subgroup.normalizer (P : Set G) := hP_le_N hx
    have hmem : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (P : Set G))) ∈
        (P.subgroupOf (Subgroup.normalizer (P : Set G)) : Set _) := by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hx
    exact congrArg Subtype.val (h ⟨x, hxN⟩ hmem)

open scoped IsMulCommutative in
/-- 自己同型 `φ : MulAut W` を `Additive W` 上の `ZMod p`-線形自己準同型と見るための
`MulAut W →* Module.End (ZMod p) (Additive W)`. `stability_perFactor` の共役表現コア. -/
private noncomputable def mulAutToEnd
    (W : Type*) [Group W] [IsMulCommutative W] (p : ℕ)
    [Module (ZMod p) (Additive W)] :
    MulAut W →* Module.End (ZMod p) (Additive W) where
  toFun φ := ((MulEquiv.toAdditive φ).toLinearEquiv
      (fun c x => ZMod.map_smul (MulEquiv.toAdditive φ).toAddMonoidHom c x)).toLinearMap
  map_one' := by ext x; rfl
  map_mul' φ ψ := by ext x; rfl

open OddOrder.GroupTheory OddOrder.BG.Ch1.S02 OddOrder.RepresentationTheory in
open scoped commutatorElement IsMulCommutative in
/-- **PSTAB — per-chief-factor p-stability** (= Gorenstein 6.5.3 steps 1-3, A.4(c)):
`M` 有限可解奇数位数, `p` odd, `K ◁ M` を `p`-群, `A ≤ M` を `p`-部分群で `[K,A,A]=1`.
このとき `K` の各 `M`-chief factor 上で `A` は trivial, すなわち `⁅Pᵢ, A⁆ ≤ Pᵢ₊₁`
(`Pᵢ := chiefSeriesInside K i`).

**証明 (issue #0047 PSTAB, sorry-free)**: `U := chiefSeriesInside K i`,
`V := chiefSeriesInside K (i+1)`. `U = ⊥` なら `⁅⊥,A⁆ = ⊥ ≤ V`. 以下 `U/V` が `M`-chief
factor (`isChiefFactor_chiefSeriesInside`) の場合:
1. `U/V` は elementary abelian `p`-群 (`IsChiefFactor.commutator_le_of_isSolvable` で abelian,
   `K` が `p`-群なので exponent `p`) ⇒ `AddCommGroup.zmodModule` で `ZMod p`-ベクトル空間.
2. `M` の conjugation 作用は `ZMod p`-線形 ⇒ `H_i := chiefFactorCentralizer U V` を kernel と
   する `Representation (ZMod p) (M ⧸ H_i) (U/V)`. **faithful** (kernel = `H_i`) + **irreducible**
   (`U/V` chief = `M/V` の minimal normal, `IsChiefFactor.isMinimalNormal_map_quotient`).
3. faithful + irreducible char-`p` ⇒ `O_p(M/H_i) = 1` (`PGroupFixedVector` =
   `IsPGroup.invariants_ne_bot`: 正規 `p`-部分群の固定空間は `M`-不変・非零 ⇒ irreducible で全空間
   ⇒ 自明作用 ⇒ faithful で `= 1`).
4. `M/H_i` は奇数位数可解 section で `O_p = 1` ⇒ **`thmA4a` で `IsPStable p (M/H_i)`**.
5. `[K,A,A]=1` ∧ `U ≤ K` ⇒ `[U,A,A] ≤ V` ⇒ 各 `ā ∈ Ā` (= `A` の `M/H_i` 像) は `U/V` 上
   quadratic (`(ρ ā - 1)² = 0`); `ā` は `p`-element (`A` `p`-群).
6. `IsPStable` は alg-closed 上定義 ⇒ `baseChangeRepresentation` (S02_Representations, 要 expose)
   で `ρ` を `AlgebraicClosure (ZMod p)` に持ち上げ (faithful + quadratic 保存) ⇒ `IsPStable` で
   `ρ' ā = 1` ⇒ faithful で `ā = 1` ⇒ `Ā = 1` ⇒ `A ⊆ H_i` ⇒ `⁅U, A⁆ ≤ V`. ∎

主要 API: `isChiefFactor_chiefSeriesInside`, `IsChiefFactor.isMinimalNormal_map_quotient`,
`solvable_minimal_normal_isElementaryAbelian`, `AddCommGroup.zmodModule`, `mulAutToEnd`,
`IsPGroup.invariants_ne_bot` (step 3 の O_p=1), `thmA4a`, `baseChangeRepresentation`
(+ `_faithful`). -/
private theorem stability_perFactor
    {M : Type*} [Group M] [Finite M] [IsSolvable M]
    (hp_odd : p ≠ 2) (hodd : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal] (hK : IsPGroup p K)
    {A : Subgroup M} (hA_p : IsPGroup p A)
    (hKAA : ⁅⁅K, A⁆, A⁆ = (⊥ : Subgroup M)) (i : ℕ) :
    ⁅chiefSeriesInside K i, A⁆ ≤ chiefSeriesInside K (i + 1) := by
  classical
  rcases eq_or_ne (chiefSeriesInside K i) ⊥ with hU0 | hU0
  · rw [hU0, Subgroup.commutator_bot_left]; exact bot_le
  -- chief factor case
  have hchief : IsChiefFactor (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) :=
    isChiefFactor_chiefSeriesInside hU0
  set U : Subgroup M := chiefSeriesInside K i with hUdef
  set V : Subgroup M := chiefSeriesInside K (i + 1) with hVdef
  haveI hVn : V.Normal := hchief.normal_bot
  haveI hUn : U.Normal := hchief.normal_top
  -- reduce to A ≤ C_M(U/V)
  suffices hAC : A ≤ chiefFactorCentralizer U V from
    chiefFactorCentralizer.commutator_le_of_le hAC
  -- W := U/V as a (normal, minimal-normal) subgroup of M/V
  set W : Subgroup (M ⧸ V) := U.map (QuotientGroup.mk' V) with hWdef
  haveI hWn : W.Normal := hUn.map _ (QuotientGroup.mk'_surjective V)
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal W := hchief.isMinimalNormal_map_quotient
  have hW_ne_bot : W ≠ ⊥ := hMin.2.1
  obtain ⟨q, hq_prime, hElem⟩ :=
    OddOrder.Isaacs.Ch03.solvable_minimal_normal_isElementaryAbelian hMin
  -- the elementary-abelian prime is p (W is a section of the p-group K)
  have hq_eq_p : q = p := by
    have hUp : IsPGroup p ↥U := by
      rw [hUdef]; exact hK.to_le (chiefSeriesInside_le K i)
    have hWp : IsPGroup p ↥W := by
      rw [hWdef]; exact hUp.map (QuotientGroup.mk' V)
    have hElemG : OddOrder.GroupTheory.IsElementaryAbelian q ↥W := hElem
    haveI : Fact q.Prime := ⟨hq_prime⟩
    have hp_prime : p.Prime := Fact.out
    haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW_ne_bot
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥W)
    obtain ⟨ka, hka⟩ := IsPGroup.iff_orderOf.mp hElemG.isPGroup x
    obtain ⟨kb, hkb⟩ := IsPGroup.iff_orderOf.mp hWp x
    have hox : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
    have hka0 : ka ≠ 0 := fun h => hox (by rw [hka, h, pow_zero])
    have hqd : q ∣ orderOf x := hka ▸ dvd_pow_self q hka0
    rw [hkb] at hqd
    exact (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp (hq_prime.dvd_of_dvd_pow hqd)
  rw [hq_eq_p] at hElem
  have hElemT : OddOrder.GroupTheory.IsElementaryAbelian p ↥W := hElem
  -- module structure on Additive ↥W
  haveI hWcomm : IsMulCommutative ↥W :=
    ⟨⟨fun a b => hElemT.comm a b⟩⟩
  have hpsmul : ∀ x : Additive ↥W, (p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hElemT.pow_eq_one x.toMul
  haveI hWmod : Module (ZMod p) (Additive ↥W) := AddCommGroup.zmodModule hpsmul
  haveI hWnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW_ne_bot
  haveI : Finite ↥W := inferInstance
  -- the conjugation representation ρ : M → End (Additive ↥W)
  set ρ : Representation (ZMod p) M (Additive ↥W) :=
    (mulAutToEnd ↥W p).comp ((MulAut.conjNormal (H := W)).comp (QuotientGroup.mk' V)) with hρdef
  have hρ_apply : ∀ (g : M) (x : Additive ↥W),
      ρ g x = Additive.ofMul (MulAut.conjNormal (H := W) (QuotientGroup.mk' V g)
        (Additive.toMul x)) := by
    intro g x; rfl
  -- faithfulness: ker ρ = C_M(U/V)
  have hker : ∀ g : M, ρ g = 1 ↔ g ∈ chiefFactorCentralizer U V := by
    intro g
    rw [chiefFactorCentralizer.mem_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg w hw
      have hx := DFunLike.congr_fun hg (Additive.ofMul (⟨w, hw⟩ : ↥W))
      rw [hρ_apply, Module.End.one_apply] at hx
      have hcoe := congrArg (Subtype.val) (Additive.ofMul.injective hx)
      rw [MulAut.conjNormal_apply] at hcoe
      exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
    · intro hg
      ext x
      have h : MulAut.conjNormal (H := W) (QuotientGroup.mk' V g) (Additive.toMul x)
          = Additive.toMul x := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        have hcomm := hg ((Additive.toMul x : ↥W) : M ⧸ V) (Additive.toMul x).2
        exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
      simp only [hρ_apply, Module.End.one_apply, h, ofMul_toMul]
  -- quotient M̄ := M / C and the lifted (faithful) representation
  set C : Subgroup M := chiefFactorCentralizer U V with hCdef
  haveI hCn : C.Normal := chiefFactorCentralizer.normal
  have hC_le_ker : C ≤ (ρ : M →* _).ker := fun g hg => (hker g).mpr hg
  set ρbar : Representation (ZMod p) (M ⧸ C) (Additive ↥W) :=
    QuotientGroup.lift C ρ hC_le_ker with hρbardef
  have hρbar_mk : ∀ g : M, ρbar (QuotientGroup.mk' C g) = ρ g := fun g => rfl
  have hρbar_faithful : Function.Injective ρbar := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    rw [hρbar_mk] at hx
    exact (QuotientGroup.eq_one_iff g).mpr ((hker g).mp hx)
  -- O_p(M̄) = ⊥: faithful + irreducible (chief factor) ⇒ no nontrivial normal p-subgroup.
  have hOp : OddOrder.Isaacs.Ch01.opCore p (M ⧸ C) = ⊥ := by
    set Q : Subgroup (M ⧸ C) := OddOrder.Isaacs.Ch01.opCore p (M ⧸ C) with hQdef
    have hQp : IsPGroup p ↥Q := OddOrder.Isaacs.Ch01.opCore_isPGroup p (M ⧸ C)
    haveI hQn : Q.Normal := OddOrder.Isaacs.Ch01.opCore.normal p (M ⧸ C)
    -- the restriction of `ρbar` to `Q`, and its (nonzero) invariant submodule
    set σ : Representation (ZMod p) ↥Q (Additive ↥W) := ρbar.comp Q.subtype with hσdef
    have hσ_apply : ∀ (q : ↥Q) (z : Additive ↥W), σ q z = ρbar (Q.subtype q) z :=
      fun _ _ => rfl
    have hWtop_ne : (⊤ : Submodule (ZMod p) (Additive ↥W)) ≠ ⊥ := by
      obtain ⟨w, hw⟩ := exists_ne (1 : ↥W)
      rw [Submodule.ne_bot_iff]
      refine ⟨Additive.ofMul w, Submodule.mem_top, fun h => hw ?_⟩
      rwa [← ofMul_one, Equiv.apply_eq_iff_eq] at h
    have hinv_ne : σ.invariants ≠ ⊥ := hQp.invariants_ne_bot σ hWtop_ne
    -- the subgroup of `W` fixed (pointwise) by `Q`
    let Wfix : Subgroup ↥W :=
      { carrier := {w : ↥W | ∀ q : ↥Q, σ q (Additive.ofMul w) = Additive.ofMul w}
        one_mem' := fun q => by rw [ofMul_one, map_zero]
        mul_mem' := fun {w w'} hw hw' q => by rw [ofMul_mul, map_add, hw q, hw' q]
        inv_mem' := fun {w} hw q => by rw [ofMul_inv, map_neg, hw q] }
    have hmem_Wfix : ∀ w : ↥W,
        w ∈ Wfix ↔ ∀ q : ↥Q, σ q (Additive.ofMul w) = Additive.ofMul w := fun _ => Iff.rfl
    set N : Subgroup (M ⧸ V) := Wfix.map W.subtype with hNdef
    -- (A) `N ≤ W`
    have hNle : N ≤ W := by rw [hNdef]; rintro _ ⟨w, _, rfl⟩; exact w.2
    -- (B) `N ≠ ⊥`: a nonzero invariant vector gives a nontrivial fixed element
    have hN_ne : N ≠ ⊥ := by
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinv_ne
      have hfix : Additive.toMul v ∈ Wfix :=
        (hmem_Wfix _).mpr fun q => by
          rw [ofMul_toMul]; exact (Representation.mem_invariants σ v).mp hv_mem q
      have hmemN : ((Additive.toMul v : ↥W) : M ⧸ V) ∈ N := by
        rw [hNdef]; exact ⟨Additive.toMul v, hfix, rfl⟩
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hmemN
      have hone : Additive.toMul v = 1 := by
        have hcoe : ((Additive.toMul v : ↥W) : M ⧸ V) = ((1 : ↥W) : M ⧸ V) := by
          rw [Subgroup.coe_one]; exact hmemN
        exact Subtype.coe_inj.mp hcoe
      exact hv_ne (by rw [← ofMul_toMul v, hone, ofMul_one])
    -- (C) `N` is normal in `M ⧸ V`: `Q ◁ M̄` makes the fixed set `M̄`-stable
    have hNnorm : N.Normal := by
      rw [hNdef]
      refine ⟨?_⟩
      rintro _ ⟨w, hw, rfl⟩ gbar
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V gbar
      have hconjW :
          (QuotientGroup.mk' V g) * (W.subtype w) * (QuotientGroup.mk' V g)⁻¹ ∈ W :=
        hWn.conj_mem _ w.2 _
      refine ⟨⟨_, hconjW⟩, (hmem_Wfix _).mpr fun q => ?_, rfl⟩
      have heq : (⟨_, hconjW⟩ : ↥W) = MulAut.conjNormal (QuotientGroup.mk' V g) w := by
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply, Subgroup.coe_subtype]
      rw [heq]
      have hρg : ρ g (Additive.ofMul w)
          = Additive.ofMul (MulAut.conjNormal (QuotientGroup.mk' V g) w) := by
        rw [hρ_apply, toMul_ofMul]
      rw [hσ_apply, ← hρg, ← hρbar_mk g, ← Module.End.mul_apply, ← map_mul]
      have hq' : (QuotientGroup.mk' C g)⁻¹ * Q.subtype q * QuotientGroup.mk' C g ∈ Q := by
        simpa using hQn.conj_mem (Q.subtype q) q.2 ((QuotientGroup.mk' C g)⁻¹)
      have hfixq' :
          ρbar ((QuotientGroup.mk' C g)⁻¹ * Q.subtype q * QuotientGroup.mk' C g)
              (Additive.ofMul w) = Additive.ofMul w := by
        have h2 := (hmem_Wfix w).mp hw ⟨_, hq'⟩
        rwa [hσ_apply] at h2
      have hconj_eq : Q.subtype q * QuotientGroup.mk' C g
          = QuotientGroup.mk' C g * ((QuotientGroup.mk' C g)⁻¹ * Q.subtype q
              * QuotientGroup.mk' C g) := by group
      rw [hconj_eq, map_mul, Module.End.mul_apply, hfixq']
    -- (D) minimality ⇒ `N = W` ⇒ `Q` acts trivially ⇒ `Q = ⊥`
    have hNW : N = W := (hMin.2.2 N hNnorm hNle).resolve_left hN_ne
    have hWfix_top : ∀ w : ↥W, w ∈ Wfix := by
      intro w
      have hwN : ((w : ↥W) : M ⧸ V) ∈ N := by rw [hNW]; exact w.2
      rw [hNdef] at hwN
      obtain ⟨w', hw', hw'eq⟩ := hwN
      rwa [← Subtype.coe_inj.mp hw'eq]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hρx : ρbar x = 1 := by
      have hone : ρbar (Q.subtype ⟨x, hx⟩) = 1 := by
        refine LinearMap.ext fun z => ?_
        rw [Module.End.one_apply, ← hσ_apply, ← ofMul_toMul z]
        exact (hmem_Wfix _).mp (hWfix_top (Additive.toMul z)) ⟨x, hx⟩
      exact hone
    exact hρbar_faithful (by rw [hρx, map_one])
  -- M̄ odd order ⇒ p-stable
  have hodd_bar : Odd (Nat.card (M ⧸ C)) :=
    hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card C)
  have hpstable : IsPStable p (M ⧸ C) := thmA4a hp_odd hodd_bar hOp
  -- now A ≤ C
  intro a ha
  set abar : M ⧸ C := QuotientGroup.mk' C a with habardef
  have habar_p : IsPGroup p (Subgroup.zpowers abar) := by
    have hmem : abar ∈ A.map (QuotientGroup.mk' C) := by
      rw [habardef]; exact Subgroup.mem_map_of_mem _ ha
    exact (hA_p.map (QuotientGroup.mk' C)).to_le (Subgroup.zpowers_le.mpr hmem)
  -- quadratic over the algebraic closure
  have hquadZ : ((ρbar abar : Module.End (ZMod p) (Additive ↥W)) - 1) ^ 2 = 0 := by
    have hρbar_eq : ρbar abar = ρ a := by rw [habardef]; exact hρbar_mk a
    -- `(ρ a - 1) y = ofMul (⁅ā, toMul y⁆)`  with `ā = mk' V a`
    have hsub : ∀ y : Additive ↥W,
        (ρ a - (1 : Module.End (ZMod p) (Additive ↥W))) y
          = Additive.ofMul (MulAut.conjNormal (QuotientGroup.mk' V a) (Additive.toMul y)
              * (Additive.toMul y)⁻¹) := by
      intro y
      rw [LinearMap.sub_apply, Module.End.one_apply, hρ_apply, ofMul_mul, ofMul_inv,
        ofMul_toMul, sub_eq_add_neg]
    -- coercion of `⁅ā, s⁆`-as-element-of-`↥W` into `M ⧸ V`
    have hcomm_coe : ∀ s : ↥W,
        ((MulAut.conjNormal (QuotientGroup.mk' V a) s * s⁻¹ : ↥W) : M ⧸ V)
          = ⁅(QuotientGroup.mk' V a), (s : M ⧸ V)⁆ := by
      intro s
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
        commutatorElement_def]
    rw [hρbar_eq]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, pow_two, Module.End.mul_apply, hsub x, hsub, toMul_ofMul,
      ← ofMul_one]
    refine congrArg Additive.ofMul ?_
    -- `↑w ∈ W = U.map (mk' V)`: pick `u ∈ U ≤ K` with `mk' V u = ↑w`
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp
      (show ((Additive.toMul x : ↥W) : M ⧸ V) ∈ U.map (QuotientGroup.mk' V) by
        rw [← hWdef]; exact (Additive.toMul x).2)
    apply Subtype.ext
    rw [Subgroup.coe_one,
      hcomm_coe (MulAut.conjNormal (QuotientGroup.mk' V a) (Additive.toMul x)
        * (Additive.toMul x)⁻¹),
      hcomm_coe (Additive.toMul x), ← hux, ← map_commutatorElement (QuotientGroup.mk' V),
      ← map_commutatorElement (QuotientGroup.mk' V)]
    -- `⁅a, ⁅a, u⁆⁆ ∈ ⁅⁅K, A⁆, A⁆ = ⊥`
    have huK : u ∈ K := chiefSeriesInside_le K i (hUdef ▸ hu)
    have hc1 : ⁅a, u⁆ ∈ ⁅K, A⁆ := by
      rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mem_commutator ha huK
    have hc2 : ⁅a, ⁅a, u⁆⁆ ∈ ⁅⁅K, A⁆, A⁆ := by
      rw [Subgroup.commutator_comm ⁅K, A⁆ A]
      exact Subgroup.commutator_mem_commutator ha hc1
    rw [hKAA] at hc2
    rw [Subgroup.mem_bot.mp hc2, map_one]
  set Kalg := AlgebraicClosure (ZMod p)
  haveI : CharP Kalg p := inferInstance
  have hρ'_faithful : Function.Injective (baseChangeRepresentation Kalg ρbar) :=
    baseChangeRepresentation_faithful Kalg ρbar hρbar_faithful
  have hquad' :
      ((baseChangeRepresentation Kalg ρbar abar :
          Module.End Kalg (TensorProduct (ZMod p) Kalg (Additive ↥W))) - 1) ^ 2 = 0 := by
    have happ : (baseChangeRepresentation Kalg ρbar abar :
        Module.End Kalg (TensorProduct (ZMod p) Kalg (Additive ↥W)))
        = Module.End.baseChangeHom (ZMod p) Kalg (Additive ↥W) (ρbar abar) := rfl
    rw [happ, show (1 : Module.End Kalg (TensorProduct (ZMod p) Kalg (Additive ↥W)))
          = Module.End.baseChangeHom (ZMod p) Kalg (Additive ↥W) 1 from (map_one _).symm,
        ← map_sub (Module.End.baseChangeHom (ZMod p) Kalg (Additive ↥W)), ← map_pow, hquadZ,
        map_zero]
  -- IsPStable kills ā
  have h1 : baseChangeRepresentation Kalg ρbar abar = 1 :=
    hpstable (baseChangeRepresentation Kalg ρbar) hρ'_faithful abar habar_p hquad'
  have habar1 : abar = 1 := hρ'_faithful (by rw [h1, map_one])
  exact (QuotientGroup.eq_one_iff a).mp habar1

open OddOrder.GroupTheory in
/-- **Stability lift, abstract form** (= Gorenstein 6.5.3 本体, normalizer 化を剥がした版):
`M` 有限可解奇数位数, `p` odd, `K ◁ M` を正規 `p`-部分群, `A ≤ M` を `p`-部分群で
`[K, A, A] = 1`. このとき `A` の `M / C_M(K)` での像は `O_p(M / C_M(K))` に含まれる.

`thmA4c` は本補題を `M := ↥N_G(P)`, `K := P.subgroupOf N` に instantiate して得る
(`C_M(K) = C_G(P).subgroupOf N`).

**証明骨格 (Gorenstein 6.5.3, mmd L4796)**: `Pᵢ := chiefSeriesInside K`,
`H := ⨅ᵢ C_M(Pᵢ/Pᵢ₊₁)`. (1) `C_M(K) ≤ H` (K を centralize ⇒ 各 factor も).
(2) `A ≤ H` — 各 chief factor で p-stability (`thmA4a`) + quadratic (`[K,A,A]=1`) ⇒
`A` は factor を centralize [= `stability_le_chiefFactorCentralizer`]. (3) `H/C_M(K)` は
`p`-群 — `H/C` は `Aut K` の chain-stabilizer, coprime stability で p'-元は自明
[= `chiefSeries_stabilizer_isPGroup`]. (4) `H ◁ M` かつ `H/C` p-群 ⇒
`H/C ⊆ O_p(M/C)` (`normal_pgroup_le_opCore`), `A ≤ H` で結論. -/
private theorem stabilityLiftAux
    {M : Type*} [Group M] [Finite M] [IsSolvable M]
    (hp_odd : p ≠ 2) (hodd : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal] (hK : IsPGroup p K)
    {A : Subgroup M} (hA_p : IsPGroup p A)
    (hKAA : ⁅⁅K, A⁆, A⁆ = (⊥ : Subgroup M))
    {C₀ : Subgroup M} [C₀.Normal] (hC₀ : C₀ = Subgroup.centralizer (K : Set M)) :
    A.map (QuotientGroup.mk' C₀) ≤ OddOrder.Isaacs.Ch01.opCore p (M ⧸ C₀) := by
  subst hC₀
  classical
  haveI hCnorm : (Subgroup.centralizer (K : Set M)).Normal := inferInstance
  -- `H := ⨅ᵢ C_M(Pᵢ/Pᵢ₊₁)`, intersection of chief-factor centralizers of the N-chief series of K.
  set H : Subgroup M :=
    ⨅ i : ℕ, chiefFactorCentralizer (chiefSeriesInside K i) (chiefSeriesInside K (i + 1))
    with hH
  -- (1) `C_M(K) ≤ H`: the centralizer of all of `K` centralizes every chief factor.
  have hC_le_H : Subgroup.centralizer (K : Set M) ≤ H := by
    rw [hH]
    refine le_iInf (fun i => ?_)
    rw [chiefFactorCentralizer.le_iff_commutator_le]
    refine le_trans ?_ (bot_le : (⊥ : Subgroup M) ≤ _)
    rw [Subgroup.commutator_le]
    intro u hu c hc
    have huK : u ∈ K := chiefSeriesInside_le K i hu
    have hcomm : u * c = c * u := Subgroup.mem_centralizer_iff.mp hc u huK
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  -- (2) `A ≤ H`: the per-chief-factor p-stability argument (Gorenstein 6.5.3 steps 1-3).
  have hA_le_H : A ≤ H := by
    rw [hH, le_iInf_iff]
    intro i
    rw [chiefFactorCentralizer.le_iff_commutator_le]
    exact stability_perFactor hp_odd hodd hK hA_p hKAA i
  -- (3) `H ◁ M`.
  haveI hHnorm : H.Normal := by
    rw [hH]; exact Subgroup.normal_iInf_normal (fun _ => inferInstance)
  -- (4) `H / C_M(K)` is a p-group (Gorenstein 6.5.3 steps 4-5, coprime stability).
  have hHmap_pgroup :
      IsPGroup p (H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))) := by
    -- `H` stabilizes every chief factor of `K`.
    have hH_stab : ∀ i, ⁅chiefSeriesInside K i, H⁆ ≤ chiefSeriesInside K (i + 1) := by
      intro i
      rw [← chiefFactorCentralizer.le_iff_commutator_le, hH]
      exact iInf_le _ i
    -- A Hall `{p}'`-subgroup `D` of `↥H` (exists: `↥H` finite solvable).
    obtain ⟨D, hD⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥H) {q : ℕ | q ≠ p}
    have hpD : ¬ p ∣ Nat.card ↥D := by
      intro hpdvd
      exact absurd rfl (hD.primeFactors_card_subset p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvd, Nat.card_pos.ne'⟩))
    -- `|D.map subtype| = |D|` is coprime to `|K| = p^j`.
    have hcardD' : Nat.card ↥(D.map H.subtype) = Nat.card ↥D :=
      (Nat.card_congr (D.equivMapOfInjective H.subtype (Subgroup.subtype_injective H)).toEquiv).symm
    have hcop : (Nat.card ↥(D.map H.subtype)).Coprime (Nat.card ↥K) := by
      obtain ⟨j, hjK⟩ := hK.exists_card_eq
      rw [hcardD', hjK]
      exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpD).symm.pow_right j
    -- `D.map subtype ≤ H` stabilizes the chief series, hence `≤ C_M(K)` (the helper).
    have hstabD' : ∀ i,
        ⁅chiefSeriesInside K i, D.map H.subtype⁆ ≤ chiefSeriesInside K (i + 1) :=
      fun i => le_trans (Subgroup.commutator_mono le_rfl (Subgroup.map_subtype_le D)) (hH_stab i)
    have hsolvD' : IsSolvable ↥(D.map H.subtype) ∨ IsSolvable ↥K := by
      haveI := hK.isNilpotent; exact Or.inr inferInstance
    have hD'C : D.map H.subtype ≤ Subgroup.centralizer (K : Set M) :=
      coprime_chainStabilizer_le_centralizer hK hcop hsolvD' hstabD'
    have hDC : D ≤ (Subgroup.centralizer (K : Set M)).subgroupOf H :=
      Subgroup.map_le_iff_le_comap.mp hD'C
    -- `D.index` is a power of `p` (Hall `{p}'` ⇒ index a `{p}`-number).
    obtain ⟨k, hk⟩ : ∃ k, D.index = p ^ k := by
      refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite
        (fun {d} hd hdvd => ?_)⟩
      simpa using hD.index_no_pi d
        (Nat.mem_primeFactors.mpr ⟨hd, hdvd, Subgroup.index_ne_zero_of_finite⟩)
    -- `|H.map(mk' C)| = (C ∩ H).index ∣ D.index = p^k`, so it is a power of `p`.
    set ψH : ↥H →* M ⧸ Subgroup.centralizer (K : Set M) :=
      (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))).comp H.subtype with hψH
    have hrange : ψH.range = H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))) := by
      rw [hψH, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : ψH.ker = (Subgroup.centralizer (K : Set M)).subgroupOf H := by
      rw [hψH, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hcard_eq :
        Nat.card ↥(H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))))
          = ((Subgroup.centralizer (K : Set M)).subgroupOf H).index := by
      rw [← hrange, ← hker]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψH).toEquiv).symm
    rw [IsPGroup.iff_card]
    have hdvd :
        Nat.card ↥(H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))) ∣ p ^ k := by
      rw [hcard_eq, ← hk]; exact Subgroup.index_dvd_of_le hDC
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    exact ⟨j, hj⟩
  haveI hHmap_norm :
      (H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))).Normal :=
    hHnorm.map _ (QuotientGroup.mk'_surjective _)
  calc A.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))
      ≤ H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))) :=
        Subgroup.map_mono hA_le_H
    _ ≤ OddOrder.Isaacs.Ch01.opCore p (M ⧸ Subgroup.centralizer (K : Set M)) :=
        OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hHmap_pgroup

/-- **BG Theorem A.4(c)** (mmd L4480(c), = Gorenstein "condition (B)" / Thm 6.5.3 翻訳):
`p` odd, `G` solvable odd order, `P` を `p`-部分群とする。`O_{p'}(G)·P ◁ G` かつ `A` が
`N_G(P)` の `p`-部分群で `[P,A,A]=1` なら, `A` の `N_G(P)/C_G(P)` での像は
`O_p(N_G(P)/C_G(P))` に含まれる (= **stability lift**, A.5/B.4 → Thm 6.2 の本線)。

**証明ルート (未完, issue #0047)**: condition (B) は「`G` が non-p-stable な section を
involve しない」とき成立 (Gorenstein 6.5.3 proof 末尾)。奇数位数可解 `G` では全 section が
`O_p=1` で p-stable (= `thmA4a` = `thmA3` 対偶) ⇒ condition (B)。詳細・step 分解は
issue [#0047](../../issues/0047-bg-appa-a4.md) 「A.4(c) 作業計画」。 -/
theorem thmA4c [Finite G] (hp_odd : p ≠ 2) (hsolv : IsSolvable G)
    (hodd : Odd (Nat.card G))
    {P : Subgroup G} (hP : IsPGroup p P)
    (_hPnorm : (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G ⊔ P).Normal)
    {A : Subgroup G} (hA_le : A ≤ Subgroup.normalizer (P : Set G)) (hA_p : IsPGroup p A)
    (hPAA : ⁅⁅P, A⁆, A⁆ = (⊥ : Subgroup G)) :
    (A.subgroupOf (Subgroup.normalizer (P : Set G))).map
        (QuotientGroup.mk' ((Subgroup.centralizer (P : Set G)).subgroupOf
          (Subgroup.normalizer (P : Set G))))
      ≤ OddOrder.Isaacs.Ch01.opCore p
          (↥(Subgroup.normalizer (P : Set G)) ⧸
            (Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.normalizer (P : Set G))) := by
  haveI : IsSolvable G := hsolv
  have hP_le_N : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  -- `P.subgroupOf N`, `A.subgroupOf N` inherit the `p`-group property (`≃* P`, `≃* A`).
  have hKp : IsPGroup p ↥(P.subgroupOf (Subgroup.normalizer (P : Set G))) :=
    hP.of_injective (Subgroup.subgroupOfEquivOfLe hP_le_N).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hP_le_N).injective
  have hAp' : IsPGroup p ↥(A.subgroupOf (Subgroup.normalizer (P : Set G))) :=
    hA_p.of_injective (Subgroup.subgroupOfEquivOfLe hA_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hA_le).injective
  -- Odd order descends along `N ≤ G` (a divisor of an odd number is odd).
  have hcardN_dvd : Nat.card ↥(Subgroup.normalizer (P : Set G)) ∣ Nat.card G :=
    (Subgroup.normalizer (P : Set G)).card_subgroup_dvd_card
  have hoddN : Odd (Nat.card ↥(Subgroup.normalizer (P : Set G))) := by
    rcases Nat.even_or_odd (Nat.card ↥(Subgroup.normalizer (P : Set G))) with hev | hod
    · exact absurd (hev.two_dvd.trans hcardN_dvd) hodd.not_two_dvd_nat
    · exact hod
  -- `[K, A', A'] = 1` inside `↥N` (pull back along the injective `subtype`).
  have hKAA' : ⁅⁅P.subgroupOf (Subgroup.normalizer (P : Set G)),
        A.subgroupOf (Subgroup.normalizer (P : Set G))⁆,
        A.subgroupOf (Subgroup.normalizer (P : Set G))⁆ = (⊥ : Subgroup _) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (Subgroup.normalizer (P : Set G)))
    simp only [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.map_bot,
      inf_eq_left.mpr hP_le_N, inf_eq_left.mpr hA_le]
    exact hPAA
  exact stabilityLiftAux (K := P.subgroupOf (Subgroup.normalizer (P : Set G)))
    hp_odd hoddN hKp hAp' hKAA' (centralizer_subgroupOf_normalizer_eq P)

/-- **BG Theorem A.4(b)** (mmd L4480(b), = Gorenstein 6.5.2 翻訳 = BG Thm 6.1, Hall-Higman 特殊形):
`p` odd, `G` solvable odd order, `P ∈ Syl_p(G)`, `A` を `P` の正規 abelian 部分群とする
(`A ≤ P` かつ `P ≤ N_G(A)`)。このとき `A ≤ O_{p',p}(G)`。

**証明 (Gorenstein 5.2 直接ルート)**: `N := O_{p'}(G)`, `Ḡ := G/N`, `R̄ := O_p(Ḡ)`,
`Ā := A の像`。`Ḡ` では `O_{p'}=⊥`。`Ā` は abelian `p`-群で `R̄ ≤ P̄ ≤ N_Ḡ(Ā)` ⇒
`⁅R̄,Ā,Ā⁆ ≤ ⁅Ā,Ā⁆ = ⊥`。`stabilityLiftAux` を `K := R̄` に適用し
`Ā·C_Ḡ(R̄)/C_Ḡ(R̄) ⊆ O_p(Ḡ/C_Ḡ(R̄))`。Hall-Higman (`O_{p'}(Ḡ)=⊥ ⇒ C_Ḡ(R̄) ⊆ R̄`,
`centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot`) で `C_Ḡ(R̄)` は `p`-群 ⇒ 商を
引き戻して `Ā ⊆ R̄ = O_p(Ḡ)` ⇒ `A ⊆ O_{p',p}(G)`。Gorenstein の Remark (A.4(c) の系) が
隠す "`A ⊆ P`" 推論を回避するため, A.4(c) でなく 5.2 自身 (= `stabilityLiftAux@K=O_p(Ḡ)`) を翻訳。 -/
theorem thmA4b [Finite G] (hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    (P : Sylow p G) {A : Subgroup G} (hA_le : A ≤ (P : Subgroup G))
    (hA_norm : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G)) [IsMulCommutative A] :
    A ≤ OddOrder.Isaacs.Ch03.oPiPrimePiCore ({p} : Set ℕ) G := by
  haveI : IsSolvable G := hsolv
  set N : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G with hN
  set mk := QuotientGroup.mk' N with hmk
  set Abar : Subgroup (G ⧸ N) := A.map mk with hAbar
  set Rbar : Subgroup (G ⧸ N) := OddOrder.Isaacs.Ch01.opCore p (G ⧸ N) with hRbar
  -- Step 0: instances / odd order on `Ḡ`; the `{q ∉ {p}} = {q ≠ p}` set identity
  have hset : {p_1 | p_1 ∉ ({p} : Set ℕ)} = {q | q ≠ p} := by ext q; simp
  have hoddBar : Odd (Nat.card (G ⧸ N)) :=
    hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card N)
  -- Step 1: `O_{p'}(Ḡ) = ⊥`
  have hOp'Bar : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (G ⧸ N) = ⊥ :=
    OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot {q | q ≠ p}
  -- Step 2: `Ā` is an abelian `p`-group, `R̄ ≤ P̄ ≤ N_Ḡ(Ā)`
  have hA_pg : IsPGroup p A := P.2.to_le hA_le
  have hAbar_pg : IsPGroup p Abar := hA_pg.map mk
  set Pbar : Sylow p (G ⧸ N) := P.mapSurjective (QuotientGroup.mk'_surjective N) with hPbar
  have hPbar_coe : (Pbar : Subgroup (G ⧸ N)) = (P : Subgroup G).map mk :=
    P.coe_mapSurjective (QuotientGroup.mk'_surjective N)
  have hR_le_NAbar : Rbar ≤ Subgroup.normalizer (Abar : Set (G ⧸ N)) := by
    refine le_trans (OddOrder.Isaacs.Ch01.opCore_le Pbar) ?_
    rw [hPbar_coe, hAbar]
    exact le_trans (Subgroup.map_mono hA_norm) (Subgroup.le_normalizer_map mk)
  -- Step 3: `⁅R̄, Ā, Ā⁆ = ⊥`
  have hAA : ⁅A, A⁆ = (⊥ : Subgroup G) := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (‹IsMulCommutative A›.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hAbarAbar : ⁅Abar, Abar⁆ = (⊥ : Subgroup (G ⧸ N)) := by
    rw [hAbar, ← Subgroup.map_commutator, hAA, Subgroup.map_bot]
  have hRAbar_le : ⁅Rbar, Abar⁆ ≤ Abar := by
    rw [Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hR_le_NAbar
  have hKAA : ⁅⁅Rbar, Abar⁆, Abar⁆ = (⊥ : Subgroup (G ⧸ N)) :=
    le_bot_iff.mp (le_trans (Subgroup.commutator_mono hRAbar_le le_rfl) hAbarAbar.le)
  -- Step 4: stabilityLiftAux with `K := R̄`
  have hStab := stabilityLiftAux (M := G ⧸ N) (K := Rbar) (A := Abar)
    hp_odd hoddBar (OddOrder.Isaacs.Ch01.opCore_isPGroup p (G ⧸ N)) hAbar_pg hKAA
    (C₀ := Subgroup.centralizer (Rbar : Set (G ⧸ N))) rfl
  -- Step 5: `C₀ := C_Ḡ(R̄) ≤ R̄` (Hall-Higman) ⇒ `C₀` is a `p`-group
  have hC₀_le_R : Subgroup.centralizer (Rbar : Set (G ⧸ N)) ≤ Rbar := by
    have hHH := OddOrder.BG.Ch1.S01.hall_higman_solvable_specialization (p := p) (G := G ⧸ N)
      (by rw [hset]; exact hOp'Bar)
    rwa [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore, ← hRbar] at hHH
  have hC₀_pg : IsPGroup p (Subgroup.centralizer (Rbar : Set (G ⧸ N))) :=
    (OddOrder.Isaacs.Ch01.opCore_isPGroup p (G ⧸ N)).to_le hC₀_le_R
  -- Step 6: pull back `Ā.map(mk' C₀) ≤ O_p(Ḡ/C₀)` to `Ā ≤ R̄`
  set C₀ := Subgroup.centralizer (Rbar : Set (G ⧸ N)) with hC₀
  have hcomap_pg : IsPGroup p
      ((OddOrder.Isaacs.Ch01.opCore p ((G ⧸ N) ⧸ C₀)).comap (QuotientGroup.mk' C₀)) := by
    refine (OddOrder.Isaacs.Ch01.opCore_isPGroup p _).comap_of_ker_isPGroup
      (QuotientGroup.mk' C₀) ?_
    rw [QuotientGroup.ker_mk']
    exact hC₀_pg
  have hcomap_le_R : (OddOrder.Isaacs.Ch01.opCore p ((G ⧸ N) ⧸ C₀)).comap
      (QuotientGroup.mk' C₀) ≤ Rbar :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hcomap_pg
  have hAbar_le_R : Abar ≤ Rbar :=
    le_trans (Subgroup.map_le_iff_le_comap.mp hStab) hcomap_le_R
  -- Step 7: `A ≤ O_{p',p}(G)`, which is defeq `comap (mk' N) (O_p(Ḡ))`
  -- (`{p_1 | p_1 ∉ {p}}` is defeq `{q | q ≠ p}` since `x ∈ {p} ≡ x = p`).
  show A ≤ Subgroup.comap mk (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N))
  rw [← Subgroup.map_le_iff_le_comap, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
  exact hAbar_le_R

open scoped commutatorElement in
/-- **BG Theorem A.5(1)** (mmd L4488): `p` odd, `G` solvable odd order, `P ◁ G` を `p`-部分群,
`X` を「`P` で正規化される abelian `p`-群」で生成される部分群とする。このとき
`X·C_G(P)/C_G(P) ⊆ O_p(G/C_G(P))`。

各生成子 `A` (abelian `p`-群, `P`-正規化) は `⁅P,A⁆ ≤ A` ∧ `⁅A,A⁆ = ⊥` ⇒ `⁅⁅P,A⁆,A⁆ = ⊥`
なので `stabilityLiftAux` (`K := P`, `P ◁ G`) で `A·C/C ⊆ O_p(G/C)`。`X ≤ ⨆ A` を iSup で分解。 -/
theorem thmA5_part1 [Finite G] (hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    {X : Subgroup G}
    (hX : X ≤ ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧ IsPGroup p ↥A ∧
        P ≤ Subgroup.normalizer (A : Set G)}, A) :
    X.map (QuotientGroup.mk' (Subgroup.centralizer (P : Set G)))
      ≤ OddOrder.Isaacs.Ch01.opCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
  haveI : IsSolvable G := hsolv
  refine le_trans (Subgroup.map_mono hX) ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  obtain ⟨hAcomm, hA_pg, hA_norm⟩ := hA
  have hPAA : ⁅⁅P, A⁆, A⁆ = (⊥ : Subgroup G) := by
    have hPA_le : ⁅P, A⁆ ≤ A := by
      rw [Subgroup.commutator_comm]
      exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hA_norm
    have hAA : ⁅A, A⁆ = (⊥ : Subgroup G) := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hAcomm.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    exact le_bot_iff.mp (le_trans (Subgroup.commutator_mono hPA_le le_rfl) hAA.le)
  exact stabilityLiftAux hp_odd hodd hP hA_pg hPAA rfl

/-- **BG Theorem A.5(2)** (mmd L4488, part 2): `p` odd, `G` solvable odd order, `P ◁ G` a `p`-group,
`X` generated by `P`-normalized abelian `p`-groups. If `O_{p'}(G) = 1` and `C_{O_p(G)}(P) ⊆ P`,
then `X ⊆ O_p(G)`.

`Q := O_p(G)`, `C := C_G(P)`. (1) `P ≤ Q` (normal `p`-group). (2) `C_G(Q) ≤ Q`
(Hall-Higman, Prop 1.15(b)). (3) every `p'`-element `u ∈ C` centralizes `Q` via Prop 1.10
(`⟨u⟩` acts on `Q` by conjugation; `C_Q(C_Q(u)) ⊆ C_Q(P) = C∩Q ⊆ P ⊆ C_Q(u)`), hence
`u ∈ C_G(Q) ⊆ Q` forces `u = 1`. (4) so `C` is a `p`-group (Cauchy), and `C ◁ G` gives `C ≤ Q`.
(5) `C ≤ Q` lets part (1)'s `XC/C ⊆ O_p(G/C)` pull back (`comap`, `ker(mk' C) = C` a `p`-group)
to `X ⊆ Q`. -/
theorem thmA5_part2 [Finite G] (hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    {X : Subgroup G}
    (hX : X ≤ ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧ IsPGroup p ↥A ∧
        P ≤ Subgroup.normalizer (A : Set G)}, A)
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (hCP : Subgroup.centralizer (P : Set G) ⊓ OddOrder.Isaacs.Ch01.opCore p G ≤ P) :
    X ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  haveI : IsSolvable G := hsolv
  classical
  set Q : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hQ
  set C : Subgroup G := Subgroup.centralizer (P : Set G) with hC
  -- Step 1: `P ≤ Q` (normal `p`-group).
  have hP_le_Q : P ≤ Q := OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hP
  -- Step 2: `C_G(Q) ≤ Q` (Hall-Higman, Prop 1.15(b)).
  have hset : {p_1 | p_1 ∉ ({p} : Set ℕ)} = {q | q ≠ p} := by ext q; simp
  have hCGQ_le_Q : Subgroup.centralizer (Q : Set G) ≤ Q := by
    have hHH := OddOrder.BG.Ch1.S01.hall_higman_solvable_specialization (p := p) (G := G)
      (by rw [hset]; exact hOp')
    rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore, ← hQ] at hHH
    exact hHH
  -- Step 3: every `p'`-element `u ∈ C` is trivial.
  have hstep3 : ∀ u : G, u ∈ C → (orderOf u).Coprime p → u = 1 := by
    intro u huC hu_cop
    -- conjugation action of `⟨u⟩` on `Q`
    set φ : ↥(Subgroup.zpowers u) →* MulAut ↥Q :=
      (MulAut.conjNormal (H := Q)).comp (Subgroup.zpowers u).subtype with hφ
    have hφcoe : ∀ (a : ↥(Subgroup.zpowers u)) (g : ↥Q),
        ((φ a) g : G) = (a : G) * (g : G) * (a : G)⁻¹ := by
      intro a g; rw [hφ]; simp [MulAut.conjNormal_apply]
    -- (i) `P.subgroupOf Q ≤ fixedPointsOfMulAut φ`  (`P ⊆ C_Q(u)`)
    have hPsub_le_fix : P.subgroupOf Q ≤ Subgroup.fixedPointsOfMulAut φ := by
      intro g hg
      rw [Subgroup.mem_subgroupOf] at hg
      rw [Subgroup.mem_fixedPointsOfMulAut]
      intro a
      refine Subtype.ext ?_
      rw [hφcoe]
      have hcu : Commute (g : G) u := Subgroup.mem_centralizer_iff.mp huC (g : G) hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have hcomm_a : Commute (a : G) (g : G) := by
        rw [← hk]; exact (hcu.symm).zpow_left k
      rw [hcomm_a.eq, mul_assoc, mul_inv_cancel, mul_one]
    -- (ii) `C_Q(P) ≤ P.subgroupOf Q`  (`= C∩Q ⊆ P`)
    have hCQP_le_Psub : Subgroup.centralizer ((P.subgroupOf Q : Subgroup ↥Q) : Set ↥Q)
        ≤ P.subgroupOf Q := by
      intro g hg
      rw [Subgroup.mem_subgroupOf]
      apply hCP
      rw [Subgroup.mem_inf]
      refine ⟨?_, g.2⟩
      rw [hC, Subgroup.mem_centralizer_iff]
      intro x hxP
      have hxQ : x ∈ Q := hP_le_Q hxP
      have hx'_mem : (⟨x, hxQ⟩ : ↥Q) ∈ (P.subgroupOf Q : Subgroup ↥Q) := by
        rw [Subgroup.mem_subgroupOf]; exact hxP
      have h := Subgroup.mem_centralizer_iff.mp hg ⟨x, hxQ⟩ hx'_mem
      have h2 := congrArg Subtype.val h
      simpa using h2
    -- combine: `C_Q(C_Q(u)) ⊆ C_Q(u)`
    have hCC : Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥Q)
        ≤ Subgroup.fixedPointsOfMulAut φ :=
      calc Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥Q)
          ≤ Subgroup.centralizer ((P.subgroupOf Q : Subgroup ↥Q) : Set ↥Q) :=
            Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPsub_le_fix)
        _ ≤ P.subgroupOf Q := hCQP_le_Psub
        _ ≤ Subgroup.fixedPointsOfMulAut φ := hPsub_le_fix
    -- coprimality + nilpotence for Prop 1.10
    haveI : Group.IsNilpotent ↥Q := (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).isNilpotent
    have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers u)) (Nat.card ↥Q) := by
      obtain ⟨n, hn⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).exists_card_eq
      rw [Nat.card_zpowers, hQ, hn]
      exact hu_cop.pow_right n
    -- Prop 1.10: `⟨u⟩` acts trivially on `Q`
    have htrivφ := OddOrder.BG.Ch1.S01.coprime_nilpotent_acts_trivially_of_centralizer_self
      (A := ↥(Subgroup.zpowers u)) (G := ↥Q) (φ := φ) hcop hCC
    -- `u` centralizes `Q`
    have hu_cent_Q : u ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxQ
      have h := htrivφ ⟨u, Subgroup.mem_zpowers u⟩ ⟨x, hxQ⟩
      have hco := congrArg Subtype.val h
      rw [hφcoe] at hco
      have hco' : u * x * u⁻¹ = x := hco
      have hux : u * x = x * u := by
        have := congrArg (· * u) hco'
        simpa [mul_assoc] using this
      exact hux.symm
    -- `u ∈ C_G(Q) ⊆ Q`, and `u` is both a `p`- and `p'`-element ⇒ `u = 1`
    have huQ : u ∈ Q := hCGQ_le_Q hu_cent_Q
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (OddOrder.Isaacs.Ch01.opCore_isPGroup p G))
      ⟨u, huQ⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk1 : orderOf u = 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa using hk
      · exact absurd (Nat.eq_one_of_dvd_coprimes hu_cop
          (by rw [hk]; exact dvd_pow_self p hkpos.ne') (dvd_refl p)) (Fact.out : p.Prime).ne_one
    exact orderOf_eq_one_iff.mp hk1
  -- Step 4: `C` is a `p`-group (no nontrivial `p'`-element, via Cauchy).
  have hC_pg : IsPGroup p ↥C := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro q hq hqdvd
    by_contra hqp
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqdvd
    have hg_cop : (orderOf (g : G)).Coprime p := by
      rw [Subgroup.orderOf_coe, hg]
      exact (Nat.coprime_primes hq Fact.out).mpr hqp
    have hg1 : (g : G) = 1 := hstep3 (g : G) g.2 hg_cop
    have hq1 : q = 1 := by rw [← hg, ← Subgroup.orderOf_coe, hg1, orderOf_one]
    exact hq.ne_one hq1
  -- Step 5: pull back part (1) through `mk' C` (since `C ≤ Q` and `ker(mk' C) = C` a `p`-group).
  have hPart1 := thmA5_part1 hp_odd hsolv hodd hP hX
  have hcomap_pg : IsPGroup p
      ((OddOrder.Isaacs.Ch01.opCore p (G ⧸ C)).comap (QuotientGroup.mk' C)) := by
    refine (OddOrder.Isaacs.Ch01.opCore_isPGroup p _).comap_of_ker_isPGroup
      (QuotientGroup.mk' C) ?_
    rw [QuotientGroup.ker_mk']
    exact hC_pg
  have hcomap_le_Q :
      (OddOrder.Isaacs.Ch01.opCore p (G ⧸ C)).comap (QuotientGroup.mk' C) ≤ Q :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hcomap_pg
  have hX_comap : X ≤ (OddOrder.Isaacs.Ch01.opCore p (G ⧸ C)).comap (QuotientGroup.mk' C) :=
    Subgroup.map_le_iff_le_comap.mp hPart1
  exact le_trans hX_comap hcomap_le_Q

end PStability

end OddOrder.BG.AppA

