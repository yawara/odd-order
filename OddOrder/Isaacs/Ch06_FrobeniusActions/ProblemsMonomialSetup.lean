/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch01_Sylow.ProblemsOrder120
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6A

/-!
# Isaacs Problems 6A.2 / 6A.3 の共通土台 — モノミアル行列による Frobenius complement

Isaacs Problem 6A.2 (`GL(3,43)` の位数 `7·3²` の群) と 6A.3 (`GL(5,p)` の位数 `11·5²` の群)
は同じ構成の `n = 3, 5` の場合である:

* `a = diag(α, α^r, α^{r²}, …, α^{r^{n-1}})` (`α` の位数は素数 `q`, `r` の位数は `n` mod `q`)
* `b` = 巡回シフト行列の隅に `ε` (位数 `n`) を置いたもの ⟹ `bⁿ = ε · 1` (スカラー)
* `A = ⟨a, b⟩` は位数 `q n²` の非巡回群で, `Fⁿ` への作用が Frobenius

本ファイルには **両方に共通する一般補題**を置く。行列そのものの関係式 (`bⁿ = ε·1`,
`a b = b a^{r⁻¹}`) は次元ごとに個別ファイルで計算する。

## 内容

**2 生成群の一般論** (`b` が `⟨a⟩` を正規化するとき):
`coe_sup_eq_mul_of_le_normalizer` / `card_sup_of_le_normalizer_of_coprime` /
`card_closure_pair_of_mem_normalizer` / `exists_pow_mul_pow_of_mem_closure_pair` /
`not_isCyclic_closure_pair`。

**`b a = a^c b` からの冪計算**: `mul_pow_eq_pow_mul` / `pow_mul_pow_eq_pow_mul_pow` /
**`pow_mul_pow_pow`** (`(aⁱ b)^n = a^{(1 + c + ⋯ + c^{n-1})·i} bⁿ`) — 幾何級数の和が `q` の
倍数になることで `aⁱ` の寄与が消える, というのが Frobenius 性の核。

**行列とベクトルの不動点**: `unitsMatrixDistribMulAction` (`GL(n,R)` の `n → R` への作用) /
`scalar_mulVec_ne_of_ne_one` / `exists_diagonal_eq_one_of_mulVec_eq` / `diagonal_mul_scalar` /
`eq_one_of_pow_eq_one_of_coprime`。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.2 / 6A.3 共通土台 -/

/-! ### 2 生成群 `⟨a, b⟩` (`b ∈ N_G(⟨a⟩)`) -/

/-- `K ≤ N_G(H)` なら `H ⊔ K` の台集合は積集合 `H · K`
(`Subgroup.mul_normal` の「`N` が `G` で正規」を「`K` が `H` を正規化」に緩めた版)。 -/
theorem coe_sup_eq_mul_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer H) :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) := by
  refine le_antisymm ?_ ?_
  · let P : Subgroup G :=
      { carrier := (H : Set G) * (K : Set G)
        one_mem' := ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
        mul_mem' := by
          rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
          exact ⟨h₁ * (k₁ * h₂ * k₁⁻¹),
            Subgroup.mul_mem _ hh₁ (((Subgroup.mem_normalizer_iff.mp (hK hk₁)) h₂).mp hh₂),
            k₁ * k₂, Subgroup.mul_mem _ hk₁ hk₂, by group⟩
        inv_mem' := by
          rintro _ ⟨h, hh, k, hk, rfl⟩
          exact ⟨k⁻¹ * h⁻¹ * (k⁻¹)⁻¹,
            ((Subgroup.mem_normalizer_iff.mp (hK (inv_mem hk))) h⁻¹).mp (inv_mem hh),
            k⁻¹, inv_mem hk, by group⟩ }
    exact (sup_le (fun h hh => ⟨h, hh, 1, one_mem _, mul_one h⟩)
      (fun k hk => ⟨1, one_mem _, k, hk, one_mul k⟩) : H ⊔ K ≤ P)
  · rintro _ ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem _ ((le_sup_left : H ≤ H ⊔ K) hh) ((le_sup_right : K ≤ H ⊔ K) hk)

/-- `S ≤ N_G(N)` かつ位数が互いに素なら `|N ⊔ S| = |N| · |S|`。

`Ch01.card_sup_of_normal_of_coprime` (Problem 1C.4 の helper) の「`N` が `G` で正規」という
仮定を「`S` が `N` を正規化する」に緩めた版 (`N ⊔ S` の中に降りて適用する)。 -/
theorem card_sup_of_le_normalizer_of_coprime {G : Type*} [Group G] [Finite G]
    {N S : Subgroup G} (hnorm : S ≤ Subgroup.normalizer N)
    (h : Nat.Coprime (Nat.card ↥N) (Nat.card ↥S)) :
    Nat.card ↥(N ⊔ S) = Nat.card ↥N * Nat.card ↥S := by
  have hNL : N ≤ N ⊔ S := le_sup_left
  have hSL : S ≤ N ⊔ S := le_sup_right
  haveI hnormal : (N.subgroupOf (N ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr (sup_le Subgroup.le_normalizer hnorm)
  have hcN : Nat.card ↥(N.subgroupOf (N ⊔ S)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hcS : Nat.card ↥(S.subgroupOf (N ⊔ S)) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  have hsup : N.subgroupOf (N ⊔ S) ⊔ S.subgroupOf (N ⊔ S) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNL hSL, Subgroup.subgroupOf_self]
  have hres := Ch01.card_sup_of_normal_of_coprime (N := N.subgroupOf (N ⊔ S))
    (S := S.subgroupOf (N ⊔ S)) hnormal (by rw [hcN, hcS]; exact h)
  rw [hsup, Subgroup.card_top, hcN, hcS] at hres
  exact hres

theorem closure_pair_eq_sup {G : Type*} [Group G] (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [show ({a, b} : Set G) = {a} ∪ {b} from rfl, Subgroup.closure_union,
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]

/-- `b` が `⟨a⟩` を正規化し位数が互いに素なら `|⟨a, b⟩| = |a| · |b|`。 -/
theorem card_closure_pair_of_mem_normalizer {G : Type*} [Group G] [Finite G] {a b : G}
    (hnorm : b ∈ Subgroup.normalizer (Subgroup.zpowers a))
    (hcop : Nat.Coprime (orderOf a) (orderOf b)) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = orderOf a * orderOf b := by
  rw [closure_pair_eq_sup, card_sup_of_le_normalizer_of_coprime
    (Subgroup.zpowers_le.mpr hnorm) (by rwa [Nat.card_zpowers, Nat.card_zpowers]),
    Nat.card_zpowers, Nat.card_zpowers]

/-- **正規形**: `b` が `⟨a⟩` を正規化するとき, `⟨a, b⟩` の元はすべて `aⁱ bʲ` (`i j : ℕ`)。 -/
theorem exists_pow_mul_pow_of_mem_closure_pair {G : Type*} [Group G] [Finite G] {a b : G}
    (hnorm : b ∈ Subgroup.normalizer (Subgroup.zpowers a)) {x : G}
    (hx : x ∈ Subgroup.closure ({a, b} : Set G)) : ∃ i j : ℕ, x = a ^ i * b ^ j := by
  rw [closure_pair_eq_sup] at hx
  have hmem : x ∈ ((Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G)) := by
    rw [← coe_sup_eq_mul_of_le_normalizer (Subgroup.zpowers_le.mpr hnorm)]
    exact hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hmem
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  exact ⟨i, j, by rw [hi, hj]⟩

/-- `a` と `b` が可換でなければ `⟨a, b⟩` は巡回群でない。 -/
theorem not_isCyclic_closure_pair {G : Type*} [Group G] {a b : G} (hne : a * b ≠ b * a) :
    ¬ IsCyclic ↥(Subgroup.closure ({a, b} : Set G)) := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hamem : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hbmem : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm : (⟨a, hamem⟩ : ↥(Subgroup.closure ({a, b} : Set G))) * ⟨b, hbmem⟩
      = ⟨b, hbmem⟩ * ⟨a, hamem⟩ := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, hamem⟩)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hbmem⟩)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  exact hne (congrArg Subtype.val hcomm)

/-! ### `b a = a^c b` からの冪計算 -/

theorem mul_pow_eq_pow_mul {G : Type*} [Group G] {a b : G} {c : ℕ} (h : b * a = a ^ c * b)
    (i : ℕ) : b * a ^ i = a ^ (c * i) * b := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc b * a ^ (i + 1) = (b * a ^ i) * a := by rw [pow_succ, mul_assoc]
      _ = a ^ (c * i) * (b * a) := by rw [ih, mul_assoc]
      _ = a ^ (c * i) * (a ^ c * b) := by rw [h]
      _ = a ^ (c * (i + 1)) * b := by
          rw [← mul_assoc, ← pow_add, show c * i + c = c * (i + 1) by ring]

theorem pow_mul_pow_eq_pow_mul_pow {G : Type*} [Group G] {a b : G} {c : ℕ} (h : b * a = a ^ c * b)
    (m i : ℕ) : b ^ m * a ^ i = a ^ (c ^ m * i) * b ^ m := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
    calc b ^ (m + 1) * a ^ i = b ^ m * (b * a ^ i) := by rw [pow_succ, mul_assoc]
      _ = b ^ m * (a ^ (c * i) * b) := by rw [mul_pow_eq_pow_mul h]
      _ = (b ^ m * a ^ (c * i)) * b := by rw [mul_assoc]
      _ = (a ^ (c ^ m * (c * i)) * b ^ m) * b := by rw [ih]
      _ = a ^ (c ^ (m + 1) * i) * b ^ (m + 1) := by
          rw [mul_assoc, ← pow_succ, show c ^ m * (c * i) = c ^ (m + 1) * i by ring]

/-- **核となる冪計算**: `b a = a^c b` なら `(aⁱ b)^n = a^{(1 + c + ⋯ + c^{n-1})·i} bⁿ`。

`c` の位数が `n` (mod `q = |a|`) のとき幾何級数の和 `∑_{k<n} c^k` は `q` で割り切れるので,
`aⁱ` の寄与が消えて `(aⁱ b)^n = bⁿ` になる — これが Frobenius 性の核。 -/
theorem pow_mul_pow_pow {G : Type*} [Group G] {a b : G} {c : ℕ} (h : b * a = a ^ c * b)
    (i n : ℕ) : (a ^ i * b) ^ n = a ^ ((∑ k ∈ Finset.range n, c ^ k) * i) * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (a ^ i * b) ^ (n + 1) = (a ^ i * b) ^ n * (a ^ i * b) := by rw [pow_succ]
      _ = a ^ ((∑ k ∈ Finset.range n, c ^ k) * i) * (b ^ n * a ^ i) * b := by
          rw [ih]; simp only [mul_assoc]
      _ = a ^ ((∑ k ∈ Finset.range n, c ^ k) * i) * (a ^ (c ^ n * i) * b ^ n) * b := by
          rw [pow_mul_pow_eq_pow_mul_pow h]
      _ = a ^ ((∑ k ∈ Finset.range (n + 1), c ^ k) * i) * b ^ (n + 1) := by
          rw [Finset.sum_range_succ, ← mul_assoc, ← pow_add,
            show (∑ k ∈ Finset.range n, c ^ k) * i + c ^ n * i
              = ((∑ k ∈ Finset.range n, c ^ k) + c ^ n) * i by ring]
          simp only [mul_assoc, ← pow_succ]

/-! ### 行列とベクトルの不動点 -/

/-- `GL(n, R)` (= 行列環の単元群) は `n → R` に `mulVec` で線形に作用する。 -/
instance unitsMatrixDistribMulAction {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] : DistribMulAction ((Matrix n n R)ˣ) (n → R) where
  smul a v := (a : Matrix n n R).mulVec v
  one_smul v := by
    change ((1 : (Matrix n n R)ˣ) : Matrix n n R).mulVec v = v
    rw [Units.val_one, Matrix.one_mulVec]
  mul_smul a b v := by
    change ((a * b : (Matrix n n R)ˣ) : Matrix n n R).mulVec v
      = (a : Matrix n n R).mulVec ((b : Matrix n n R).mulVec v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]
  smul_zero a := by
    change (a : Matrix n n R).mulVec 0 = 0
    exact Matrix.mulVec_zero _
  smul_add a u v := by
    change (a : Matrix n n R).mulVec (u + v)
      = (a : Matrix n n R).mulVec u + (a : Matrix n n R).mulVec v
    exact Matrix.mulVec_add _ _ _

theorem unitsMatrix_smul_def {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (a : (Matrix n n R)ˣ) (v : n → R) : a • v = (a : Matrix n n R).mulVec v := rfl

instance finiteMatrixUnits {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    [Finite R] : Finite (Matrix n n R)ˣ :=
  Finite.of_injective _ Units.val_injective

variable {F : Type*} [Field F]

/-- 非単位スカラー行列は非零ベクトルを固定しない。 -/
theorem scalar_mulVec_ne_of_ne_one {n : Type*} [Fintype n] [DecidableEq n] {c : F} (hc : c ≠ 1)
    {v : n → F} (hv : v ≠ 0) : (c • (1 : Matrix n n F)).mulVec v ≠ v := by
  intro hfix
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hk
  have h := congrFun hfix k
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h
  exact hc (mul_right_cancel₀ hk (by simpa using h))

/-- 対角行列が非零ベクトルを固定するなら, ある対角成分が `1`。 -/
theorem exists_diagonal_eq_one_of_mulVec_eq {n : Type*} [Fintype n] [DecidableEq n]
    {d v : n → F} (hv : v ≠ 0) (hfix : (Matrix.diagonal d).mulVec v = v) :
    ∃ k, d k = 1 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hk
  exact ⟨k, mul_right_cancel₀ hk (by rw [← Matrix.mulVec_diagonal d v k, hfix, one_mul])⟩

/-- スカラー倍と対角行列: `diag(d) · (c • 1) = diag(k ↦ d k · c)`。 -/
theorem diagonal_mul_scalar {n : Type*} [Fintype n] [DecidableEq n] (d : n → F) (c : F) :
    Matrix.diagonal d * (c • (1 : Matrix n n F)) = Matrix.diagonal (fun k => d k * c) := by
  have hscal : (c • (1 : Matrix n n F)) = Matrix.diagonal (fun _ => c) := by
    ext p q
    by_cases h : p = q <;> simp [h]
  rw [hscal, Matrix.diagonal_mul_diagonal]

/-- 互いに素な冪で `1` になる元は `1` (`⟨ε⟩ ⊓ ⟨α⟩ = 1` の元形)。 -/
theorem eq_one_of_pow_eq_one_of_coprime {M : Type*} [Monoid M] {c : M} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : c ^ m = 1) (hn : c ^ n = 1) : c = 1 := by
  have hd : orderOf c ∣ Nat.gcd m n :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)
  rw [hmn] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

end

end OddOrder.Isaacs.Ch06
