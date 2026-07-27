/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Isaacs, Finite Group Theory — Problems 8B (pp. 248–249)

Isaacs §8B (block と原始性) の章末演習。**block** は mathlib の `MulAction.IsBlock` が
Isaacs の定義 (「`Δ` の translate は `Δ` 自身か, `Δ` と交わらないかのいずれか」) と
そのまま一致する (`IsBlock G B := ∀ g₁ g₂, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B)`)。

## Main results

- `blockCore`, `mem_blockCore`, `smul_blockCore_eq_of_mem`, `isBlock_blockCore` —
  **Problem 8B.1**: `α` を含む `X` の translate すべての共通部分は block。
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

section /- Problems 8B (pp. 248-249) -/

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-! ### Problem 8B.1 — translate の共通部分は block -/

variable (G) in
/-- **Isaacs Problem 8B.1** (p. 248) の `Δ`: `α` を含む `X` の translate すべての共通部分。 -/
def blockCore (α : Ω) (X : Set Ω) : Set Ω := ⋂ g ∈ {g : G | α ∈ g • X}, g • X

lemma mem_blockCore (α : Ω) (X : Set Ω) : α ∈ blockCore G α X := by
  simp only [blockCore, Set.mem_iInter]
  exact fun _ hg => hg

lemma smul_blockCore (h : G) (α : Ω) (X : Set Ω) :
    h • blockCore G α X = ⋂ g ∈ {g : G | α ∈ g • X}, (h * g) • X := by
  simp only [blockCore, Set.smul_set_iInter, ← mul_smul]

/-- `α ∈ h • Δ` は「`h` が `S = {g | α ∈ g • X}` を左から保つ」ことと同値。 -/
lemma mem_smul_blockCore_iff (h : G) (α : Ω) (X : Set Ω) :
    α ∈ h • blockCore G α X ↔ ∀ g : G, α ∈ g • X → α ∈ (h * g) • X := by
  rw [smul_blockCore]
  simp only [Set.mem_iInter, Set.mem_setOf_eq]

/-- **8B.1 の核心**: `α ∈ h • Δ` なら `h • Δ = Δ`。

`S := {g | α ∈ g • X}` とおくと `α ∈ h • Δ` は `h · S ⊆ S` を意味し, `G` が有限なので
左移動の単射性から `h · S = S`。したがって `h • Δ = ⋂_{g ∈ h·S} g • X = Δ`。 -/
lemma smul_blockCore_eq_of_mem [Finite G] {h : G} {α : Ω} {X : Set Ω}
    (hmem : α ∈ h • blockCore G α X) : h • blockCore G α X = blockCore G α X := by
  have hmaps : Set.MapsTo (fun g : G => h * g) {g : G | α ∈ g • X} {g : G | α ∈ g • X} :=
    fun g hg => (mem_smul_blockCore_iff h α X).mp hmem g hg
  have hbij : Set.BijOn (fun g : G => h * g) {g : G | α ∈ g • X} {g : G | α ∈ g • X} :=
    ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo hmaps).mp
      fun _ _ _ _ hab => mul_left_cancel hab
  rw [smul_blockCore]
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · simp only [blockCore, Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := hbij.surjOn (show g' ∈ {g : G | α ∈ g • X} from hg')
    exact hx g hg
  · simp only [blockCore, Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
    exact fun g hg => hx (h * g) (hmaps hg)

/-- **Isaacs Problem 8B.1** (p. 248) 🎉: `G` が `Ω` に推移的なとき, `α` を含む `X` の
translate すべての共通部分 `Δ` は **block**。

`α ∈ h • Δ ⟺ h • Δ = Δ` (`smul_blockCore_eq_of_mem`) から
`G_α ≤ G_{Δ}` かつ `Δ = orbit G_{Δ} α` が従い, 「点安定化群を含む部分群の軌道は block」
(`MulAction.IsBlock.of_orbit`) に帰着する。 -/
theorem isBlock_blockCore [Finite G] [IsPretransitive G Ω] (α : Ω) (X : Set Ω) :
    IsBlock G (blockCore G α X) := by
  have hstab : stabilizer G α ≤ stabilizer G (blockCore G α X) := by
    intro s hs
    refine mem_stabilizer_iff.mpr (smul_blockCore_eq_of_mem ?_)
    have : s • α ∈ s • blockCore G α X :=
      Set.smul_mem_smul_set (mem_blockCore (G := G) α X)
    rwa [mem_stabilizer_iff.mp hs] at this
  have horbit : orbit ↥(stabilizer G (blockCore G α X)) α = blockCore G α X := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨k, rfl⟩
      have hk : (k : G) • blockCore G α X = blockCore G α X := mem_stabilizer_iff.mp k.2
      have : (k : G) • α ∈ (k : G) • blockCore G α X :=
        Set.smul_mem_smul_set (mem_blockCore (G := G) α X)
      rwa [hk] at this
    · intro β hβ
      obtain ⟨k, hk⟩ := exists_smul_eq G α β
      have hmem : α ∈ k⁻¹ • blockCore G α X := by
        refine Set.mem_smul_set.mpr ⟨β, hβ, ?_⟩
        rw [← hk, inv_smul_smul]
      have hkinv : k⁻¹ ∈ stabilizer G (blockCore G α X) :=
        mem_stabilizer_iff.mpr (smul_blockCore_eq_of_mem hmem)
      exact ⟨⟨k, (Subgroup.inv_mem_iff _).mp hkinv⟩, hk⟩
  rw [← horbit]
  exact IsBlock.of_orbit hstab

end

end OddOrder.Isaacs.Ch08
