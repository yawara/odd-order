/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CentralCommutatorPower
import OddOrder.Isaacs.Ch05_Transfer.ProblemsSchurMultiplier

/-!
# Isaacs Problem 5A.8(b) — 互いに素な直積の Schur 乗数

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 5A.8(b) (書籍 p. 153):
`|A|` と `|B|` が互いに素なら `M(A × B) ≅ M(A) × M(B)`。

`M(G)` の universal object は未実装 (issue 9206) なので, 上界側は
`ProblemsSchurMultiplier.lean` と同じく **stem extension の ∀-形**で述べる:

> `h : Γ →* A × B` が stem extension で `|A|`, `|B|` が互いに素なら, `A` の stem extension
> `f` と `B` の stem extension `g` が存在して `|ker h| = |ker f| · |ker g|`。

5A.8(a) (`isStemExtension_prodMap` / `card_ker_prodMap`) と合わせて位数版の等式になる。

## 分解の骨格

`Z := ker h`, `Γ_A := h⁻¹(A × 1) = ker (snd ∘ h)`, `Γ_B := h⁻¹(1 × B) = ker (fst ∘ h)`。

1. `Γ_A ⊓ Γ_B = Z` (`inf_ker_snd_ker_fst`)。
2. `Γ = Γ_A · Γ_B` (`exists_mem_ker_snd_mul_mem_ker_fst`)。
3. ⭐ **`⁅Γ_A, Γ_B⁆ = ⊥`** (`commutator_ker_snd_ker_fst_eq_bot`) — ここが coprime を使う要。

本ファイルは 1-3 を提供する。残り (`Γ' = ⁅Γ_A,Γ_A⁆ ⊔ ⁅Γ_B,Γ_B⁆`, `Z = Z_A Z_B`,
`Z_A ⊓ Z_B = ⊥`, 商への降下) は issue 1055 の設計に従って続きを実装する。

## `⁅Γ_A, Γ_B⁆ = ⊥` の証明 (書籍の行間)

`x ∈ Γ_A`, `y ∈ Γ_B` なら `⁅x, y⁆ ∈ Γ_A ⊓ Γ_B = Z ≤ Z(Γ)`。
`h (x ^ |A|) = (h x) ^ |A| = ((h x).1 ^ |A|, 1) = 1` なので **`x ^ |A| ∈ Z`**
— 剰余群 `Γ_A/Z` を作らずに済むのがポイント。`⁅x,y⁆` が中心的なので
`⁅x,y⁆ ^ |A| = ⁅x ^ |A|, y⁆ = 1` (中心元との交換子は自明)。同様に `⁅x,y⁆ ^ |B| = 1`。
位数が `|A|` と `|B|` の両方を割るので coprime から `⁅x,y⁆ = 1`。
-/

open scoped commutatorElement

namespace OddOrder.Isaacs.Ch05

section /- 5A.8(b): coprime direct product (p. 153) -/

variable {Γ A B : Type*} [Group Γ] [Group A] [Group B]

/-- `Γ_A ⊓ Γ_B = Z`: 両成分が自明 ⟺ `h` の核。 -/
theorem inf_ker_snd_ker_fst (h : Γ →* A × B) :
    ((MonoidHom.snd A B).comp h).ker ⊓ ((MonoidHom.fst A B).comp h).ker = h.ker := by
  ext x
  simp [MonoidHom.mem_ker, Prod.ext_iff, and_comm]

/-- `Γ = Γ_A · Γ_B`: `h` が全射なら任意の `γ` は `Γ_A` の元と `Γ_B` の元の積。 -/
theorem exists_mem_ker_snd_mul_mem_ker_fst {h : Γ →* A × B} (hsurj : Function.Surjective h)
    (γ : Γ) :
    ∃ x ∈ ((MonoidHom.snd A B).comp h).ker, ∃ y ∈ ((MonoidHom.fst A B).comp h).ker,
      γ = x * y := by
  obtain ⟨x, hx⟩ := hsurj ((h γ).1, 1)
  refine ⟨x, ?_, x⁻¹ * γ, ?_, by group⟩
  · simp [MonoidHom.mem_ker, hx]
  · simp [MonoidHom.mem_ker, hx]

/-- ⭐ **`⁅Γ_A, Γ_B⁆ = ⊥`** (Problem 5A.8(b) の要): `ker h ≤ Z(Γ)` で `|A|`, `|B|` が
互いに素なら, `h⁻¹(A × 1)` と `h⁻¹(1 × B)` は元ごとに可換。

⚠ `h` の全射性は不要。 -/
theorem commutator_ker_snd_ker_fst_eq_bot [Finite A] [Finite B] {h : Γ →* A × B}
    (hker : h.ker ≤ Subgroup.center Γ)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    ⁅((MonoidHom.snd A B).comp h).ker, ((MonoidHom.fst A B).comp h).ker⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [MonoidHom.mem_ker] at hx hy
  have hx2 : (h x).2 = 1 := hx
  have hy1 : (h y).1 = 1 := hy
  rw [Subgroup.mem_bot]
  -- `⁅x, y⁆ ∈ ker h ≤ Z(Γ)`
  have hcxy : ⁅x, y⁆ ∈ h.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    simp [commutatorElement_def, Prod.ext_iff, hx2, hy1]
  have hcen : ⁅x, y⁆ ∈ Subgroup.center Γ := hker hcxy
  -- 中心元との交換子は自明
  have hkey : ∀ z : Γ, z ∈ h.ker → ⁅z, y⁆ = 1 ∧ ⁅x, z⁆ = 1 := by
    intro z hz
    have hzc := Subgroup.mem_center_iff.mp (hker hz)
    exact ⟨commutatorElement_eq_one_iff_mul_comm.mpr (hzc y).symm,
      commutatorElement_eq_one_iff_mul_comm.mpr (hzc x)⟩
  -- `x ^ |A| ∈ ker h` (剰余群を経由しない)
  have hxA : x ^ Nat.card A ∈ h.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    refine Prod.ext ?_ ?_
    · simp
    · simp [hx2]
  have hyB : y ^ Nat.card B ∈ h.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    refine Prod.ext ?_ ?_
    · simp [hy1]
    · simp
  -- 双線形性で位数を潰す
  have hpowA : ⁅x, y⁆ ^ Nat.card A = 1 := by
    rw [← OddOrder.GroupTheory.commutatorElement_pow_left_of_central hcen]
    exact (hkey _ hxA).1
  have hpowB : ⁅x, y⁆ ^ Nat.card B = 1 := by
    rw [← OddOrder.GroupTheory.commutatorElement_pow_right_of_central hcen]
    exact (hkey _ hyB).2
  have hone : orderOf ⁅x, y⁆ = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpowA)
      (orderOf_dvd_of_pow_eq_one hpowB))
  exact orderOf_eq_one_iff.mp hone

end

end OddOrder.Isaacs.Ch05
