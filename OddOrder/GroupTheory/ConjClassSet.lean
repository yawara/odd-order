/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Conjugacy-closure of a subset `𝒞_G(T)`

`OddOrder.GroupTheory` shared module: the union of the `G`-conjugacy classes of the
elements of a subset `T ⊆ G`, written `𝒞_G(T)` in Bender–Glauberman.

BG uses `𝒞_G(T)` pervasively in the counting arguments of §14 (`|𝒞_G(M̃)| = (|M_σ|-1)|G:M|`)
and §16 (Theorems E, II). It lives in the shared `GroupTheory` namespace.

## Main definitions

* `conjClassSet T` (BG `𝒞_G(T)`): `{ g t g⁻¹ | t ∈ T, g ∈ G }`.

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
  Chapter IV §14 (counting), §16.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **BG `𝒞_G(T)`**: the union of the `G`-conjugacy classes of the elements of `T`,
i.e. `{ g * t * g⁻¹ | t ∈ T, g ∈ G }`. -/
def conjClassSet (T : Set G) : Set G :=
  {y | ∃ t ∈ T, ∃ g : G, g * t * g⁻¹ = y}

@[simp]
theorem mem_conjClassSet {T : Set G} {y : G} :
    y ∈ conjClassSet T ↔ ∃ t ∈ T, ∃ g : G, g * t * g⁻¹ = y :=
  Iff.rfl

/-- `T ⊆ 𝒞_G(T)` (take `g = 1`). -/
theorem subset_conjClassSet {T : Set G} : T ⊆ conjClassSet T :=
  fun t ht => ⟨t, ht, 1, by simp⟩

/-- `𝒞_G` is monotone in the subset. -/
theorem conjClassSet_mono {S T : Set G} (h : S ⊆ T) : conjClassSet S ⊆ conjClassSet T :=
  fun _ ⟨t, ht, g, hg⟩ => ⟨t, h ht, g, hg⟩

end OddOrder.GroupTheory
