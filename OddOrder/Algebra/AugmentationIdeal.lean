/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The augmentation ideal of an integral group ring

`OddOrder.Algebra` shared module: 整数群環 `ℤ[G] = MonoidAlgebra ℤ G` の
**augmentation 写像** `δ : ℤ[G] → ℤ` (係数和) と **augmentation ideal**
`Δ(G) = ker δ`。

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) §10C (pp. 307-324) の基盤:
principal ideal theorem (Thm 10.18, Furtwängler) と Alperin-Kuo (Cor 10.28) が
この API の上に立つ。mathlib v4.30.0-rc2 に群環の augmentation ideal は未収載
(claim = issue 9108; 将来 upstream 候補)。

## Main definitions

* `augmentation G : MonoidAlgebra ℤ G →ₐ[ℤ] ℤ` — 係数和の環準同型。
* `augmentationIdeal G : Submodule ℤ (MonoidAlgebra ℤ G)` — `Δ(G) = ker δ`。
  Isaacs の議論は加法群+積 (`Submodule.mul`) レベルなので、非可換群環でも
  扱える `ℤ`-submodule として持つ (two-sided ideal 性は補題で)。

## Main results

* **Isaacs Lemma 10.19** (`augmentationIdeal_eq_span`): `Δ(G)` は
  `{g - 1 | g ∈ G}` の張る `ℤ`-部分加群。(ℤ-basis 性は後続。)
-/

namespace OddOrder.Algebra

open MonoidAlgebra

variable (G : Type*) [Group G]

/-- The **augmentation homomorphism** `δ : ℤ[G] → ℤ`, summing the coefficients:
`δ (∑ e_g · g) = ∑ e_g`. Realized as the lift of the trivial homomorphism
`G →* ℤ`. -/
noncomputable def augmentation : MonoidAlgebra ℤ G →ₐ[ℤ] ℤ :=
  MonoidAlgebra.lift ℤ ℤ G 1

@[simp]
theorem augmentation_of (g : G) : augmentation G (MonoidAlgebra.of ℤ G g) = 1 := by
  simp [augmentation]

@[simp]
theorem augmentation_single (g : G) (c : ℤ) :
    augmentation G (MonoidAlgebra.single g c) = c := by
  rw [augmentation, MonoidAlgebra.lift_single]
  simp

/-- The **augmentation ideal** `Δ(G) = ker δ`, as a `ℤ`-submodule of `ℤ[G]`. -/
noncomputable def augmentationIdeal : Submodule ℤ (MonoidAlgebra ℤ G) :=
  LinearMap.ker (augmentation G).toLinearMap

theorem mem_augmentationIdeal_iff {G : Type*} [Group G] {α : MonoidAlgebra ℤ G} :
    α ∈ augmentationIdeal G ↔ augmentation G α = 0 := Iff.rfl

theorem sub_one_mem_augmentationIdeal (g : G) :
    MonoidAlgebra.of ℤ G g - 1 ∈ augmentationIdeal G := by
  rw [mem_augmentationIdeal_iff, map_sub, map_one, augmentation_of, sub_self]

/-- Every element of `ℤ[G]` differs from `(δ α) • 1` by an element of the span
of the `g - 1` (key computation for Lemma 10.19). -/
theorem sub_augmentation_smul_one_mem_span {G : Type*} [Group G]
    (α : MonoidAlgebra ℤ G) :
    α - (augmentation G α) • 1
      ∈ Submodule.span ℤ (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1) := by
  induction α using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have h1 : f + g - (augmentation G (f + g)) • 1
        = (f - (augmentation G f) • 1) + (g - (augmentation G g) • 1) := by
      rw [map_add, add_smul]
      abel
    rw [h1]
    exact Submodule.add_mem _ hf hg
  | single g c =>
    have h2 : c • MonoidAlgebra.of ℤ G g = MonoidAlgebra.single g c := by
      simp only [MonoidAlgebra.of_apply]
      exact (MonoidAlgebra.smul_single' c g 1).trans (by rw [mul_one])
    have h1 : MonoidAlgebra.single g c
        - (augmentation G (MonoidAlgebra.single g c)) • 1
        = c • (MonoidAlgebra.of ℤ G g - 1) := by
      rw [augmentation_single, ← h2]
      exact (smul_sub c _ _).symm
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/-- **Isaacs Lemma 10.19 (spanning half)**: `Δ(G)` is spanned over `ℤ` by the
elements `g - 1`, `g ∈ G`. -/
theorem augmentationIdeal_eq_span :
    augmentationIdeal G
      = Submodule.span ℤ (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1) := by
  apply le_antisymm
  · intro α hα
    rw [mem_augmentationIdeal_iff] at hα
    have hkey := sub_augmentation_smul_one_mem_span α
    rwa [hα, zero_smul, sub_zero] at hkey
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact sub_one_mem_augmentationIdeal G g

end OddOrder.Algebra
