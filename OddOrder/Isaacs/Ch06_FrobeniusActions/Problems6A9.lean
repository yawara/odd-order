/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.ProblemsTIHypothesis

/-!
# Isaacs Problem 6A.9 の準備 — TI 仮説の下での `X` の構造 (書籍 p. 186)

`A` が `G` で Lemma 6.5 の TI 仮説をみたし `X = notConjugateSet A`, `t ∈ A` を involution とする
(書籍の Note: 6A.9 は **`|A|` が偶数の場合の Frobenius の定理**の証明を与える)。

本ファイルでは 6A.9 の各パートで繰り返し使う構造的な補題を用意する。

* `centralizer_le_of_TI` — 6A.11 の系: `1 ≠ a ∈ A` なら `C_G(a) ≤ N_G(⟨a⟩) ≤ A`。
* `inv_mem_notConjugateSet` / `zpow_mem_notConjugateSet` — `X` は逆元・冪で閉じる。
* `eq_one_of_mem_notConjugateSet_of_mem` — `X ⊓ A = {1}`。
* `conj_mem_iff_of_TI` — `1 ≠ a ∈ A` について `g a g⁻¹ ∈ A ⟺ g ∈ A`。
* **`mem_notConjugateSet_of_conj_eq_inv`** — 鍵: `t` に反転される `A` の外の元は `X` に入る。
  (`x = g a g⁻¹` と共役なら `u := g⁻¹ t g` が `a` を反転するので `u ∈ N_G(⟨a⟩) ≤ A`,
  つまり `t ∈ A ⊓ A^g` で TI から `g ∈ A`, これは `x ∈ A` を与えて矛盾。)
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.9 の準備: `X` の構造 (p. 186) -/

variable {G : Type*} [Group G]

/-- `u` が `a` を反転すれば `u` は `⟨a⟩` を正規化する。 -/
theorem mem_normalizer_zpowers_of_conj_eq_inv {a u : G} (h : u * a * u⁻¹ = a⁻¹) :
    u ∈ Subgroup.normalizer (Subgroup.zpowers a) := by
  have hinv : u⁻¹ * a * u = a⁻¹ := by
    have h1 : u⁻¹ * a⁻¹ * u = a := by rw [← h]; group
    have h2 := congrArg (fun z : G => z⁻¹) h1
    simpa [mul_assoc] using h2
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨-n, ?_⟩
    show a ^ (-n) = u * a ^ n * u⁻¹
    rw [← conj_zpow (i := n) (a := u) (b := a), h, zpow_neg, ← inv_zpow]
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨-n, ?_⟩
    show a ^ (-n) = y
    have hcj := conj_zpow (i := n) (a := u⁻¹) (b := a)
    rw [inv_inv] at hcj
    have h2 : u⁻¹ * (a ^ n) * u = y := by rw [hn]; group
    rw [← h2, ← hcj, hinv, zpow_neg, ← inv_zpow]

/-- 6A.11 の系: TI 仮説の下で `1 ≠ a ∈ A` の中心化群は `A` に含まれる。 -/
theorem centralizer_le_of_TI {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥)
    {a : G} (ha : a ∈ A) (hane : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≤ A := by
  have hz : Subgroup.zpowers a ≠ ⊥ := by
    intro h
    exact hane (by simpa [h] using Subgroup.mem_zpowers a)
  refine le_trans ?_ (normalizer_le_of_TI hATI hz (Subgroup.zpowers_le.mpr ha))
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hcomm : Commute c a := hc
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hfix : c * a ^ n * c⁻¹ = a ^ n := by rw [(hcomm.zpow_right n).eq]; group
    rw [hfix]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) n
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    show a ^ n = y
    have h3 : c⁻¹ * (a ^ n) * c = y := by rw [hn]; group
    rw [← h3, ((hcomm.zpow_right n).inv_left).eq]
    group

/-- `1 ≠ a ∈ A` について `g a g⁻¹ ∈ A ⟺ g ∈ A` (TI 仮説)。 -/
theorem conj_mem_iff_of_TI {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥)
    {a : G} (ha : a ∈ A) (hane : a ≠ 1) (g : G) :
    g * a * g⁻¹ ∈ A ↔ g ∈ A := by
  refine ⟨fun h => ?_, fun h => A.mul_mem (A.mul_mem h ha) (A.inv_mem h)⟩
  by_contra hgA
  have hmem : g * a * g⁻¹ ∈ A ⊓ (MulAut.conj g • A) := by
    refine Subgroup.mem_inf.mpr ⟨h, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj g).symm (g * a * g⁻¹) ∈ A
    rw [MulAut.conj_symm_apply]
    simpa [mul_assoc] using ha
  rw [hATI g hgA, Subgroup.mem_bot] at hmem
  exact hane (by
    have := congrArg (fun y : G => g⁻¹ * y * g) hmem
    simpa [mul_assoc] using this)

/-- `X` は逆元で閉じる。 -/
theorem inv_mem_notConjugateSet {A : Subgroup G} {x : G} (hx : x ∈ notConjugateSet A) :
    x⁻¹ ∈ notConjugateSet A := by
  intro a ha hane hconj
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  refine hx a⁻¹ (A.inv_mem ha) (by simpa using hane) (isConj_iff.mpr ⟨c, ?_⟩)
  have h2 := congrArg (fun z : G => z⁻¹) hc
  simpa [mul_assoc] using h2

/-- `X ⊓ A = {1}`。 -/
theorem eq_one_of_mem_notConjugateSet_of_mem {A : Subgroup G} {x : G}
    (hx : x ∈ notConjugateSet A) (hxA : x ∈ A) : x = 1 := by
  by_contra hne
  exact hx x hxA hne (isConj_iff.mpr ⟨1, by group⟩)

/-- TI 仮説の下で `X` は冪で閉じる。 -/
theorem zpow_mem_notConjugateSet {A : Subgroup G}
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {x : G} (hx : x ∈ notConjugateSet A) (k : ℤ) : x ^ k ∈ notConjugateSet A := by
  intro a ha hane hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hxne : x ≠ 1 := by
    intro h
    rw [h, one_zpow] at hg
    exact hane (by
      have h2 := congrArg (fun y : G => g⁻¹ * y * g) hg
      simpa [mul_assoc] using h2)
  -- `b := g⁻¹ x g` は `a = b^k` と可換なので `b ∈ C_G(a) ≤ A`
  have hab : a = (g⁻¹ * x * g) ^ k := by
    have h1 : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
      simpa using conj_zpow (i := k) (a := g⁻¹) (b := x)
    rw [h1, ← hg]
    group
  have hbc : g⁻¹ * x * g ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hab]
    exact ((Commute.refl (g⁻¹ * x * g)).zpow_right k).eq
  have hbA : g⁻¹ * x * g ∈ A := centralizer_le_of_TI hATI ha hane hbc
  have hbne : g⁻¹ * x * g ≠ 1 := by
    intro h
    exact hxne (by
      have h2 := congrArg (fun y : G => g * y * g⁻¹) h
      simpa [mul_assoc] using h2)
  exact hx (g⁻¹ * x * g) hbA hbne (isConj_iff.mpr ⟨g, by group⟩)

/-- **6A.9 の鍵**: `t ∈ A` が involution のとき, `t` に反転される `A` の外の元は `X` に入る。 -/
theorem mem_notConjugateSet_of_conj_eq_inv {A : Subgroup G}
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1)
    {x : G} (hxA : x ∉ A) (hinv : t * x * t = x⁻¹) : x ∈ notConjugateSet A := by
  intro a ha hane hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have htinv : t⁻¹ = t := by
    rw [← mul_one t⁻¹, ← ht2, ← mul_assoc, inv_mul_cancel, one_mul]
  -- `u := g⁻¹ t g` は `a` を反転する
  have hu : (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹ = a⁻¹ := by
    have hstep : (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹
        = g⁻¹ * (t * (g * a * g⁻¹) * t⁻¹) * g := by group
    rw [hstep, htinv, hg, hinv, ← hg]
    group
  -- `u ∈ N_G(⟨a⟩) ≤ A`
  have hz : Subgroup.zpowers a ≠ ⊥ := by
    intro h
    exact hane (by simpa [h] using Subgroup.mem_zpowers a)
  have huA : g⁻¹ * t * g ∈ A :=
    normalizer_le_of_TI hATI hz (Subgroup.zpowers_le.mpr ha)
      (mem_normalizer_zpowers_of_conj_eq_inv hu)
  -- `t ∈ A ⊓ A^g` ⟹ `g ∈ A` ⟹ `x ∈ A` で矛盾
  have hune : g⁻¹ * t * g ≠ 1 := by
    intro hone
    refine htne ?_
    have h2 := congrArg (fun y : G => g * y * g⁻¹) hone
    simpa [mul_assoc] using h2
  have hgA : g ∈ A := (conj_mem_iff_of_TI hATI huA hune g).mp (by simpa [mul_assoc] using htA)
  exact hxA (by rw [← hg]; exact A.mul_mem (A.mul_mem hgA ha) (A.inv_mem hgA))

end

end OddOrder.Isaacs.Ch06
