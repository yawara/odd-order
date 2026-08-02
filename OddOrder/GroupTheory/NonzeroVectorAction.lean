/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Data.ZMod.Basic

/-!
# The action of the linear automorphism group on the non-zero vectors

`V ≃ₗ[K] V` acts on `{v : V // v ≠ 0}`, faithfully, and this action is the one an Iwasawa
structure for the linear groups is indexed by (`OddOrder/GroupTheory/Transvection.lean`).

Two non-zero vectors can be carried to two other non-zero vectors exactly when the two
pairs are linearly independent — `exists_linearEquiv_apply_eq_of_linearIndependent`.  Over
`𝔽₂` *every* pair of distinct non-zero vectors is independent (the only scalars are `0`
and `1`), so the action is `2`-transitive there, hence preprimitive and quasiprimitive.

Over a larger field the action is only transitive: `GL(V)` preserves the relation
"`b` is a scalar multiple of `a`", so it is never `2`-transitive on non-zero vectors once
`|K| > 2` and `dim V ≥ 1`.

The two-element hypothesis is carried as `∀ x : K, x = 0 ∨ x = 1` rather than by fixing
`K = ZMod 2`, so that no `Fact (Nat.Prime 2)` instance has to be in scope and the results
apply to any field the caller has already identified with `𝔽₂`.

## Main results

* `exists_linearEquiv_apply_eq_of_linearIndependent` — an automorphism carrying one
  independent pair to another.
* `linearIndependent_pair_of_ne_of_ne_zero` — over `𝔽₂`, distinct non-zero vectors are
  linearly independent.
* `isMultiplyPretransitive_two`, `isPreprimitive_nonzeroVector` — the action is
  `2`-transitive, hence preprimitive (and so quasiprimitive, by instance).
* `exists_dual_eq_zero_eq_one`, `exists_mem_ker_ne_zero_ne` — the two existence facts that
  turn `LinearMap.commutator_transvection` into perfectness of the linear group in
  dimension `≥ 3`.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

open MulAction Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The non-zero vectors of `V`, the point set of the linear group's natural action. -/
abbrev NonzeroVector (K V : Type*) [Field K] [AddCommGroup V] [Module K V] : Type _ :=
  {v : V // v ≠ 0}

instance : MulAction (V ≃ₗ[K] V) (NonzeroVector K V) where
  smul g v := ⟨g v, fun h => v.2 (by simpa using congrArg g.symm h)⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

@[simp]
theorem coe_smul_nonzeroVector (g : V ≃ₗ[K] V) (v : NonzeroVector K V) :
    ((g • v : NonzeroVector K V) : V) = g v := rfl

instance : FaithfulSMul (V ≃ₗ[K] V) (NonzeroVector K V) where
  eq_of_smul_eq_smul {g h} hgh := by
    ext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact congrArg Subtype.val (hgh ⟨x, hx⟩)

/-- **An automorphism carrying one independent pair onto another.**

Both pairs span a plane on which they are a basis, so they are matched by a linear
equivalence of the planes; `Submodule.exists_linearEquiv_restrict_eq` extends it to `V`
using a complement on either side. -/
theorem exists_linearEquiv_apply_eq_of_linearIndependent [FiniteDimensional K V]
    {a b c d : V} (hab : LinearIndependent K ![a, b])
    (hcd : LinearIndependent K ![c, d]) :
    ∃ g : V ≃ₗ[K] V, g a = c ∧ g b = d := by
  classical
  set Bab := Basis.span hab with hBab
  set Bcd := Basis.span hcd with hBcd
  obtain ⟨g, hg⟩ :=
    Submodule.exists_linearEquiv_restrict_eq (Bab.equiv Bcd (Equiv.refl (Fin 2)))
  refine ⟨g, ?_, ?_⟩
  · have h0 := hg (Bab 0)
    rw [Bab.equiv_apply] at h0
    have hb0 : ((Bab 0 : _) : V) = a := by rw [hBab, Basis.span_apply]; rfl
    have hc0 : ((Bcd (Equiv.refl (Fin 2) 0) : _) : V) = c := by
      rw [hBcd, Basis.span_apply]; rfl
    rw [← hb0, ← hc0]
    exact h0.symm
  · have h1 := hg (Bab 1)
    rw [Bab.equiv_apply] at h1
    have hb1 : ((Bab 1 : _) : V) = b := by rw [hBab, Basis.span_apply]; rfl
    have hc1 : ((Bcd (Equiv.refl (Fin 2) 1) : _) : V) = d := by
      rw [hBcd, Basis.span_apply]; rfl
    rw [← hb1, ← hc1]
    exact h1.symm

/-! ## Two existence facts used for perfectness of the linear group -/

/-- **A functional separating an independent pair**: `g w = 0` and `g v = 1`.

The pair is a basis of the plane it spans, so the second coordinate functional does the
job there; `LinearMap.exists_extend` extends it to `V`. -/
theorem exists_dual_eq_zero_eq_one {w v : V} (hwv : LinearIndependent K ![w, v]) :
    ∃ g : V →ₗ[K] K, g w = 0 ∧ g v = 1 := by
  classical
  set B := Basis.span hwv with hB
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.coord 1)
  have hval : ∀ i : Fin 2, g (![w, v] i) = B.coord 1 (B i) := by
    intro i
    have hi : ((B i : _) : V) = ![w, v] i := by rw [hB, Module.Basis.span_apply]
    rw [← hi]
    exact congrFun (congrArg (fun f : _ →ₗ[K] K => (f : _ → K)) hg) (B i)
  refine ⟨g, ?_, ?_⟩
  · have := hval 0
    simpa [Module.Basis.coord_apply, B.repr_self, Finsupp.single_apply] using this
  · have := hval 1
    simpa [Module.Basis.coord_apply, B.repr_self, Finsupp.single_apply] using this

/-- **The kernel of a functional contains a vector other than `0` and a given `w`**, as
soon as `dim V ≥ 3` and `w` is in the kernel.

`ker h` has dimension at least `dim V − 1 ≥ 2`, while `span {w}` has dimension at most `1`,
so the inclusion `span {w} ≤ ker h` is strict. -/
theorem exists_mem_ker_ne_zero_ne [FiniteDimensional K V] (h : V →ₗ[K] K) {w : V}
    (hw : h w = 0) (h3 : 3 ≤ Module.finrank K V) :
    ∃ v : V, h v = 0 ∧ v ≠ 0 ∧ v ≠ w := by
  classical
  have hrank := LinearMap.finrank_range_add_finrank_ker h
  have hle1 : Module.finrank K (LinearMap.range h) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range h)
    simpa using this
  have hker : 2 ≤ Module.finrank K (LinearMap.ker h) := by omega
  have hspan : (Submodule.span K {w}) ≤ LinearMap.ker h := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hw
  have hspanrank : Module.finrank K (Submodule.span K {w}) ≤ 1 := by
    rcases eq_or_ne w 0 with rfl | hw0
    · rw [Submodule.span_zero_singleton]
      simp
    · rw [finrank_span_singleton hw0]
  have hlt : (Submodule.span K {w}) < LinearMap.ker h :=
    Submodule.lt_of_le_of_finrank_lt_finrank hspan (by omega)
  obtain ⟨v, hvker, hvspan⟩ := SetLike.exists_of_lt hlt
  refine ⟨v, hvker, ?_, ?_⟩
  · rintro rfl
    exact hvspan (Submodule.zero_mem _)
  · rintro rfl
    exact hvspan (Submodule.mem_span_singleton_self _)

section TwoElementField

variable (K)

/-- In a field with only the scalars `0` and `1`, the characteristic is `2`. -/
theorem add_self_eq_zero_of_forall_eq_zero_or_one (hK : ∀ x : K, x = 0 ∨ x = 1) (v : V) :
    v + v = 0 := by
  have h2 : (1 : K) + 1 = 0 := by
    rcases hK (1 + 1) with h | h
    · exact h
    · exfalso
      refine one_ne_zero (α := K) (add_right_cancel (b := (1 : K)) ?_)
      rw [h, zero_add]
  calc v + v = ((1 : K) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [h2, zero_smul]

/-- **Over `𝔽₂`, distinct non-zero vectors are linearly independent** — the only scalars
are `0` and `1`, so a dependence `s • a + t • b = 0` forces `a = 0`, `b = 0` or `a = b`. -/
theorem linearIndependent_pair_of_ne_of_ne_zero (hK : ∀ x : K, x = 0 ∨ x = 1)
    {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) : LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rcases hK s with rfl | rfl <;> rcases hK t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact absurd (by simpa using hst) hb
  · exact absurd (by simpa using hst) ha
  · refine absurd ?_ hab
    have h2 : a + b = 0 := by simpa using hst
    calc a = a + (b + b) := by
          rw [add_self_eq_zero_of_forall_eq_zero_or_one K hK b, add_zero]
      _ = (a + b) + b := by abel
      _ = b := by rw [h2, zero_add]

/-- **The linear group is `2`-transitive on the non-zero vectors of an `𝔽₂`-space.** -/
theorem isMultiplyPretransitive_two [FiniteDimensional K V] (hK : ∀ x : K, x = 0 ∨ x = 1) :
    IsMultiplyPretransitive (V ≃ₗ[K] V) (NonzeroVector K V) 2 := by
  rw [is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g, hga, hgb⟩ :=
    exists_linearEquiv_apply_eq_of_linearIndependent
      (linearIndependent_pair_of_ne_of_ne_zero K hK a.2 b.2 fun h => hab (Subtype.ext h))
      (linearIndependent_pair_of_ne_of_ne_zero K hK c.2 d.2 fun h => hcd (Subtype.ext h))
  exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩

/-- The action is preprimitive, hence quasiprimitive — the hypothesis Iwasawa's criterion
takes. -/
theorem isPreprimitive_nonzeroVector [FiniteDimensional K V]
    (hK : ∀ x : K, x = 0 ∨ x = 1) : IsPreprimitive (V ≃ₗ[K] V) (NonzeroVector K V) :=
  isPreprimitive_of_is_two_pretransitive (isMultiplyPretransitive_two K hK)

end TwoElementField

end OddOrder.GroupTheory
