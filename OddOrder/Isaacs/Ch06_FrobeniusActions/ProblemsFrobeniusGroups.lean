/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# Isaacs Problems 6A — Frobenius 群そのものの演習 (書籍 p. 185)

## 6A.4

**主張**: Frobenius 群 `G` (Frobenius 核 `N`) の, `N` 自身**以外**の剰余類 `Ng` は
`G` の**単一の共役類**に含まれる。

**証明**: `g ∉ N` とする。Thm 6.4 (4) (`IsFrobeniusGroup.centralizer_kernel_le`) より
`1 ≠ m ∈ N` なら `C_G(m) ⊆ N` なので, `g ∉ N` から **`C_N(g) = 1`**。したがって
`f : N → N`, `f(m) = m g m⁻¹ g⁻¹` は単射 (`f(m₁) = f(m₂)` ⟹ `m₂⁻¹m₁ ∈ C_N(g) = 1`)。
`N` は有限なので `f` は**全射**でもあり, 任意の `n ∈ N` に対し `m g m⁻¹ = n g` なる
`m ∈ N` が取れる — すなわち `n g` は `g` に共役。
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.4: `N` 以外の剰余類は単一の共役類 (p. 185) -/

variable {G : Type*} [Group G] [Finite G] {N A : Subgroup G}

/-- Frobenius 群の核 `N` の外の元 `g` は, `N` の非単位元と可換にならない (`C_N(g) = 1`)。

Thm 6.4 (4) (`centralizer_kernel_le`) の対偶。 -/
theorem eq_one_of_mem_kernel_of_commute (hF : IsFrobeniusGroup G N A) {g : G} (hg : g ∉ N)
    {m : G} (hm : m ∈ N) (hcomm : m * g = g * m) : m = 1 := by
  by_contra hmne
  exact hg (hF.centralizer_kernel_le m hm hmne
    (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm))

/-- **Isaacs Problem 6A.4** (p. 185) ⭐: Frobenius 群 `G` (核 `N`) で `g ∉ N` なら,
剰余類 `Ng` の元はすべて `g` に共役 — すなわち `Ng` は単一の共役類に含まれる。 -/
theorem isConj_mul_of_notMem_kernel (hF : IsFrobeniusGroup G N A) {g : G} (hg : g ∉ N)
    {n : G} (hn : n ∈ N) : IsConj g (n * g) := by
  classical
  haveI := hF.isNormal
  -- `m ↦ m g m⁻¹ g⁻¹` は `N` から `N` への写像
  have hmem : ∀ m : ↥N, (m : G) * g * (m : G)⁻¹ * g⁻¹ ∈ N := by
    intro m
    have h1 : g * ((m : G)⁻¹) * g⁻¹ ∈ N := hF.isNormal.conj_mem _ (inv_mem m.2) g
    have h2 : (m : G) * g * (m : G)⁻¹ * g⁻¹ = (m : G) * (g * (m : G)⁻¹ * g⁻¹) := by group
    rw [h2]
    exact Subgroup.mul_mem _ m.2 h1
  set f : ↥N → ↥N := fun m => ⟨(m : G) * g * (m : G)⁻¹ * g⁻¹, hmem m⟩ with hfdef
  -- `C_N(g) = 1` から単射
  have hinj : Function.Injective f := by
    intro m₁ m₂ h
    have hval : (m₁ : G) * g * (m₁ : G)⁻¹ * g⁻¹ = (m₂ : G) * g * (m₂ : G)⁻¹ * g⁻¹ :=
      congrArg Subtype.val h
    have h' : (m₁ : G) * g * (m₁ : G)⁻¹ = (m₂ : G) * g * (m₂ : G)⁻¹ := mul_right_cancel hval
    have hc : ((m₂ : G)⁻¹ * (m₁ : G)) * g = g * ((m₂ : G)⁻¹ * (m₁ : G)) := by
      calc ((m₂ : G)⁻¹ * (m₁ : G)) * g
          = (m₂ : G)⁻¹ * ((m₁ : G) * g * (m₁ : G)⁻¹) * (m₁ : G) := by group
        _ = (m₂ : G)⁻¹ * ((m₂ : G) * g * (m₂ : G)⁻¹) * (m₁ : G) := by rw [h']
        _ = g * ((m₂ : G)⁻¹ * (m₁ : G)) := by group
    have hone := eq_one_of_mem_kernel_of_commute hF hg
      (Subgroup.mul_mem _ (inv_mem m₂.2) m₁.2) hc
    exact (Subtype.ext (inv_mul_eq_one.mp hone)).symm
  -- 有限性から全射, その原像が求める共役元
  obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.mp hinj ⟨n, hn⟩
  refine isConj_iff.mpr ⟨(m : G), ?_⟩
  have hval : (m : G) * g * (m : G)⁻¹ * g⁻¹ = n := congrArg Subtype.val hm
  calc (m : G) * g * (m : G)⁻¹ = ((m : G) * g * (m : G)⁻¹ * g⁻¹) * g := by group
    _ = n * g := by rw [hval]

/-- **Isaacs Problem 6A.4** の集合形: `g ∉ N` なら剰余類 `N · g` は `g` の共役類に含まれる。 -/
theorem coset_subset_setOf_isConj (hF : IsFrobeniusGroup G N A) {g : G} (hg : g ∉ N) :
    (N : Set G) * {g} ⊆ {y | IsConj g y} := by
  rintro _ ⟨n, hn, _, rfl, rfl⟩
  exact isConj_mul_of_notMem_kernel hF hg hn

end

end OddOrder.Isaacs.Ch06
