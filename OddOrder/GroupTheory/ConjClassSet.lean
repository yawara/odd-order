/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Group

/-!
# Conjugacy-closure of a subset `𝒞_G(T)`

`OddOrder.GroupTheory` shared module: the union of the `G`-conjugacy classes of the
elements of a subset `T ⊆ G`, written `𝒞_G(T)` in Bender–Glauberman.

BG uses `𝒞_G(T)` pervasively in the counting arguments of §14 (`|𝒞_G(M̃)| = (|M_σ|-1)|G:M|`)
and §16 (Theorems E, II). It lives in the shared `GroupTheory` namespace.

## Main definitions

* `conjClassSet T` (BG `𝒞_G(T)`): `{ g t g⁻¹ | t ∈ T, g ∈ G }`.
* `conjClassSetIn H T` (Peterfalvi `T^H`, Coq `class_support T H`): the relative version
  `{ h t h⁻¹ | t ∈ T, h ∈ H }`, conjugating only by elements of a subgroup `H`.

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

/-- **`𝒞_G(T)` is invariant under conjugation by any element**: `g * h * g⁻¹ ∈ 𝒞_G(T) ↔ h ∈ 𝒞_G(T)`.
Conjugation by `g` permutes the `G`-conjugacy classes, fixing their union, so `𝒞_G(T)` is normalized
by all of `G` (`N_G(𝒞_G(T)) = G`). -/
theorem mem_conjClassSet_conj_iff {T : Set G} (g h : G) :
    g * h * g⁻¹ ∈ conjClassSet T ↔ h ∈ conjClassSet T := by
  constructor
  · rintro ⟨t, ht, b, hb⟩
    refine ⟨t, ht, g⁻¹ * b, ?_⟩
    have hconj : g * ((g⁻¹ * b) * t * (g⁻¹ * b)⁻¹) * g⁻¹ = g * h * g⁻¹ := by
      have e : g * ((g⁻¹ * b) * t * (g⁻¹ * b)⁻¹) * g⁻¹ = b * t * b⁻¹ := by group
      exact e.trans hb
    exact mul_left_cancel (mul_right_cancel hconj)
  · rintro ⟨t, ht, b, hb⟩
    refine ⟨t, ht, g * b, ?_⟩
    have e : g * b * t * (g * b)⁻¹ = g * (b * t * b⁻¹) * g⁻¹ := by group
    rw [e, hb]

/-! ## The relative conjugacy-closure `T^H` -/

/-- **Peterfalvi `T^H` / Coq `class_support T H`**: the union of the `H`-conjugacy classes of
the elements of a subset `T ⊆ G`, i.e. `{ h * t * h⁻¹ | t ∈ T, h ∈ H }` — the relative version
of `conjClassSet`, conjugating only by elements of the subgroup `H`.  Peterfalvi (8.10) uses
`A_0(M) = A(M) ∪ V^M` (conjugates by `M`, not by all of `G`). -/
def conjClassSetIn (H : Subgroup G) (T : Set G) : Set G :=
  {y | ∃ t ∈ T, ∃ h ∈ H, h * t * h⁻¹ = y}

@[simp]
theorem mem_conjClassSetIn {H : Subgroup G} {T : Set G} {y : G} :
    y ∈ conjClassSetIn H T ↔ ∃ t ∈ T, ∃ h ∈ H, h * t * h⁻¹ = y :=
  Iff.rfl

/-- `T ⊆ T^H` (take `h = 1`). -/
theorem subset_conjClassSetIn {H : Subgroup G} {T : Set G} : T ⊆ conjClassSetIn H T :=
  fun t ht => ⟨t, ht, 1, one_mem H, by simp⟩

/-- `T^H` is monotone in the subset. -/
theorem conjClassSetIn_mono {H : Subgroup G} {S T : Set G} (h : S ⊆ T) :
    conjClassSetIn H S ⊆ conjClassSetIn H T :=
  fun _ ⟨t, ht, b, hb, e⟩ => ⟨t, h ht, b, hb, e⟩

/-- The relative closure refines the absolute one: `T^H ⊆ 𝒞_G(T)`. -/
theorem conjClassSetIn_subset_conjClassSet {H : Subgroup G} {T : Set G} :
    conjClassSetIn H T ⊆ conjClassSet T :=
  fun _ ⟨t, ht, b, _, e⟩ => ⟨t, ht, b, e⟩

/-- If `T ⊆ H` then `T^H ⊆ H`: the `H`-conjugacy closure of a subset of `H` stays inside `H`.
This is the membership fact making `A_0(M) = A(M) ∪ V^M ⊆ M` (Peterfalvi (8.10)) compatible
with the Dade hypothesis requirement `A_0 ⊆ M` — the `G`-closure `𝒞_G(V)` has no such bound. -/
theorem conjClassSetIn_subset {H : Subgroup G} {T : Set G} (hT : T ⊆ (H : Set G)) :
    conjClassSetIn H T ⊆ (H : Set G) := fun _ ⟨_, ht, _, hb, e⟩ =>
  e ▸ mul_mem (mul_mem hb (hT ht)) (inv_mem hb)

/-- **`T^H` is invariant under conjugation by elements of `H`**: for `g ∈ H`,
`g * h * g⁻¹ ∈ T^H ↔ h ∈ T^H`.  The relative analogue of `mem_conjClassSet_conj_iff`. -/
theorem mem_conjClassSetIn_conj_iff {H : Subgroup G} {T : Set G} {g : G} (hg : g ∈ H) (h : G) :
    g * h * g⁻¹ ∈ conjClassSetIn H T ↔ h ∈ conjClassSetIn H T := by
  constructor
  · rintro ⟨t, ht, b, hb, hbe⟩
    refine ⟨t, ht, g⁻¹ * b, mul_mem (inv_mem hg) hb, ?_⟩
    have hconj : g * ((g⁻¹ * b) * t * (g⁻¹ * b)⁻¹) * g⁻¹ = g * h * g⁻¹ := by
      have e : g * ((g⁻¹ * b) * t * (g⁻¹ * b)⁻¹) * g⁻¹ = b * t * b⁻¹ := by group
      exact e.trans hbe
    exact mul_left_cancel (mul_right_cancel hconj)
  · rintro ⟨t, ht, b, hb, hbe⟩
    refine ⟨t, ht, g * b, mul_mem hg hb, ?_⟩
    have e : g * b * t * (g * b)⁻¹ = g * (b * t * b⁻¹) * g⁻¹ := by group
    rw [e, hbe]

end OddOrder.GroupTheory

/-!
## Conjugacy classes of inverses (relocated)

Extracted from `OddOrder/GroupTheory/RepresentationTheory/ClassSumCongruence.lean` (issue 0106):
generic material relocated to a light-import leaf so downstream consumers need not pull the
class-sum congruence machinery (rep theory + complex analysis + integral closure).  Declarations
keep their original `OddOrder.RepresentationTheory` namespace so existing call sites are unchanged.
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- Conjugacy of inverses is determined at the level of classes: `mk a = mk b ⟹ mk a⁻¹ = mk b⁻¹`.
(A two-line consequence of `IsConj a b ⟹ IsConj a⁻¹ b⁻¹`; relocated here from
`ClassSumCongruence` (issue 0106) so light consumers avoid its heavy import closure.) -/
theorem mk_inv_eq_of_mk_eq {a b : G} (h : ConjClasses.mk a = ConjClasses.mk b) :
    ConjClasses.mk a⁻¹ = ConjClasses.mk b⁻¹ := by
  rw [ConjClasses.mk_eq_mk_iff_isConj] at h ⊢
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨c, by group⟩



end OddOrder.RepresentationTheory
