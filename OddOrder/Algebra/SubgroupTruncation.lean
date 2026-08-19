/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import OddOrder.Algebra.GroupAlgebraConjugation

/-!
# Splitting `R[G]` along a subgroup

For `H ≤ G` the group algebra `R[G]` splits, as an `R`-module, into the part supported on `H`
and the part supported on `G ∖ H`.  This file supplies the two halves and the elementary facts
about them that the block theory of Chapter 5 of Navarro needs:

* `inclusionHom H : R[H] →+* R[G]` — the (injective) ring map induced by `H ↪ G`;
* `subgroupTrunc H : R[G] → R[H]` — keep only the coefficients at the elements of `H`.

Navarro's proof of (5.6) writes the block idempotent `f_B ∈ Z(𝒪G)` as `a - c` with
`supp a ⊆ H` and `supp c ⊆ G ∖ H`; here `a = inclusionHom H (subgroupTrunc H f_B)` and
`c = a - f_B`.  The two facts that make the argument work are that the truncation of a central
element is central (`subgroupTrunc_mem_center`) and that the off-`H` part stays off `H` when
multiplied by anything coming from `R[H]` (`coeff_mul_inclusionHom_eq_zero`).

`subgroupTrunc` is the `P = ⊥` case of `OddOrder.RepresentationTheory.Modular.brauerTrunc`, but
that map is only available over a field and always carries the extra centraliser condition, so
the two are kept apart.

## Main results

* `OddOrder.GroupAlgebra.inclusionHom` — `R[H] ↪ R[G]`
* `OddOrder.GroupAlgebra.subgroupTrunc` — `R[G] → R[H]`
* `OddOrder.GroupAlgebra.subgroupTrunc_mem_center` — the truncation of a central element is central
* `OddOrder.GroupAlgebra.mapRingHom_subgroupTrunc` — truncation commutes with coefficient maps
* `OddOrder.GroupAlgebra.coeff_mul_inclusionHom_eq_zero` — `(G ∖ H)·H ⊆ G ∖ H`
* `OddOrder.GroupAlgebra.commute_single_inclusionHom` — `H` centralises `inclusionHom H a` for
  central `a`
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra

open scoped OddOrder.Conjugation

section Semiring

variable {R G : Type*} [Semiring R] [Group G] (H : Subgroup G)

/-! ### The inclusion `R[H] ↪ R[G]` -/

/-- The inclusion `R[H] ↪ R[G]` induced by `H ≤ G`. -/
noncomputable def inclusionHom : MonoidAlgebra R ↥H →+* MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainRingHom R H.subtype

theorem inclusionHom_injective : Function.Injective (inclusionHom (R := R) H) :=
  MonoidAlgebra.mapDomain_injective Subtype.val_injective

variable {H}

theorem coeff_inclusionHom_of_mem {n : G} (hn : n ∈ H) (a : MonoidAlgebra R ↥H) :
    (inclusionHom H a).coeff n = a.coeff ⟨n, hn⟩ :=
  Finsupp.mapDomain_apply Subtype.val_injective a.coeff ⟨n, hn⟩

theorem coeff_inclusionHom_of_notMem {n : G} (hn : n ∉ H) (a : MonoidAlgebra R ↥H) :
    (inclusionHom H a).coeff n = 0 :=
  Finsupp.mapDomain_of_notMem_range a.coeff n (by rintro ⟨y, rfl⟩; exact hn y.2)

@[simp]
theorem inclusionHom_single (h : ↥H) (r : R) :
    inclusionHom H (MonoidAlgebra.single h r) = MonoidAlgebra.single (h : G) r :=
  MonoidAlgebra.mapDomain_single

/-! ### The truncation `R[G] → R[H]` -/

variable (H)

/-- **The truncation `R[G] → R[H]`**: keep only the coefficients at the elements of `H`. -/
noncomputable def subgroupTrunc (x : MonoidAlgebra R G) : MonoidAlgebra R ↥H :=
  .ofCoeff (Finsupp.comapDomain H.subtype x.coeff Subtype.val_injective.injOn)

@[simp]
theorem coeff_subgroupTrunc (x : MonoidAlgebra R G) (h : ↥H) :
    (subgroupTrunc H x).coeff h = x.coeff (h : G) := rfl

variable {H}

@[simp]
theorem subgroupTrunc_zero : subgroupTrunc H (0 : MonoidAlgebra R G) = 0 :=
  MonoidAlgebra.ext (Finsupp.ext fun _ => rfl)

theorem subgroupTrunc_add (x y : MonoidAlgebra R G) :
    subgroupTrunc H (x + y) = subgroupTrunc H x + subgroupTrunc H y :=
  MonoidAlgebra.ext (Finsupp.ext fun _ => rfl)

@[simp]
theorem subgroupTrunc_one : subgroupTrunc H (1 : MonoidAlgebra R G) = 1 := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
  rw [coeff_subgroupTrunc, MonoidAlgebra.one_def, MonoidAlgebra.one_def,
    MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    Finsupp.single_apply]
  by_cases hn : (1 : ↥H) = n
  · subst hn; simp
  · rw [if_neg hn, if_neg fun h : (1 : G) = (n : G) => hn (Subtype.ext h)]

theorem inclusionHom_subgroupTrunc_coeff_eq (x : MonoidAlgebra R G) {n : G} (hn : n ∈ H) :
    (inclusionHom H (subgroupTrunc H x)).coeff n = x.coeff n := by
  rw [coeff_inclusionHom_of_mem hn, coeff_subgroupTrunc]

variable (H)

theorem mapRingHom_subgroupTrunc {R' : Type*} [Semiring R'] (φ : R →+* R')
    (x : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom (↥H) φ (subgroupTrunc H x)
      = subgroupTrunc H (MonoidAlgebra.mapRingHom G φ x) :=
  MonoidAlgebra.ext (Finsupp.ext fun n => by
    rw [MonoidAlgebra.coeff_mapRingHom, coeff_subgroupTrunc, coeff_subgroupTrunc,
      MonoidAlgebra.coeff_mapRingHom])

variable {H}

/-! ### The off-`H` part is a right `R[H]`-module -/

/-- **`(G ∖ H)·H ⊆ G ∖ H`.**  If `x` has no coefficients on `H`, neither does `x · ι b`. -/
theorem coeff_mul_inclusionHom_eq_zero {x : MonoidAlgebra R G}
    (hx : ∀ g ∈ H, x.coeff g = 0) (b : MonoidAlgebra R ↥H) {n : G} (hn : n ∈ H) :
    (x * inclusionHom H b).coeff n = 0 := by
  classical
  induction b using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, mul_zero]; rfl
  | add u v hu hv =>
    rw [map_add, mul_add,
      show ((x * inclusionHom H u + x * inclusionHom H v).coeff n)
        = (x * inclusionHom H u).coeff n + (x * inclusionHom H v).coeff n from rfl, hu, hv,
      add_zero]
  | single u r =>
    rw [inclusionHom_single, MonoidAlgebra.coeff_mul_single_apply,
      hx _ (H.mul_mem hn (H.inv_mem u.2)), zero_mul]

end Semiring

/-! ### Linearity and centrality -/

section CommSemiring

variable {R G : Type*} [CommSemiring R] [Group G] {H : Subgroup G}

theorem subgroupTrunc_smul (c : R) (x : MonoidAlgebra R G) :
    subgroupTrunc H (c • x) = c • subgroupTrunc H x :=
  MonoidAlgebra.ext (Finsupp.ext fun n => by
    rw [coeff_subgroupTrunc, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_smul_apply,
      coeff_subgroupTrunc])

variable (H) in
/-- The truncation as an `R`-linear map.  Bundling it is what lets `centerTrunc`, which is defined
on the class-sum basis, be identified with coefficient truncation. -/
noncomputable def subgroupTruncₗ : MonoidAlgebra R G →ₗ[R] MonoidAlgebra R ↥H where
  toFun := subgroupTrunc H
  map_add' := subgroupTrunc_add
  map_smul' := subgroupTrunc_smul

@[simp]
theorem subgroupTruncₗ_apply (x : MonoidAlgebra R G) :
    subgroupTruncₗ H x = subgroupTrunc H x := rfl

/-- **The truncation of a central element is central.**  Centrality means that the coefficient
function is constant on conjugacy classes; conjugating inside `H` is conjugating inside `G`, so
the restricted coefficient function is constant on `H`-classes. -/
theorem subgroupTrunc_mem_center {x : MonoidAlgebra R G}
    (hx : x ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    subgroupTrunc H x ∈ Subalgebra.center R (MonoidAlgebra R ↥H) := by
  have hfix : ∀ g : G, g • x = x :=
    forall_smul_eq_iff_mem_center.mpr fun z => ((Subalgebra.mem_center_iff.mp hx) z).symm
  have hfixH : ∀ u : ↥H, u • subgroupTrunc H x = subgroupTrunc H x := by
    intro u
    refine (smul_eq_self_iff_coeff u _).mpr fun n => ?_
    rw [coeff_subgroupTrunc, coeff_subgroupTrunc]
    have hcoe : ((u⁻¹ * n * u : ↥H) : G) = (u : G)⁻¹ * (n : G) * (u : G) := by push_cast; rfl
    rw [hcoe]
    exact (smul_eq_self_iff_coeff (u : G) x).mp (hfix (u : G)) (n : G)
  exact Subalgebra.mem_center_iff.mpr fun z =>
    (forall_smul_eq_iff_mem_center.mp hfixH z).symm

/-- **`H` centralises the image of `Z(R[H])`.**  This is the form in which Navarro's (5.6) uses
that `H` centralises the off-`H` part of a block idempotent. -/
theorem commute_single_inclusionHom {a : MonoidAlgebra R ↥H}
    (ha : a ∈ Subalgebra.center R (MonoidAlgebra R ↥H)) (h : ↥H) (r : R) :
    MonoidAlgebra.single (h : G) r * inclusionHom H a
      = inclusionHom H a * MonoidAlgebra.single (h : G) r := by
  rw [← inclusionHom_single (R := R) h r, ← map_mul, ← map_mul]
  exact congrArg _ (Subalgebra.mem_center_iff.mp ha _)

end CommSemiring

/-! ### The complement -/

section Ring

variable {R G : Type*} [Ring R] [Group G] {H : Subgroup G}

/-- **The complement of `H` really is a complement**: subtracting the `H`-part of `x` leaves an
element supported on `G ∖ H`. -/
theorem coeff_inclusionHom_subgroupTrunc_sub (x : MonoidAlgebra R G) {n : G} (hn : n ∈ H) :
    (inclusionHom H (subgroupTrunc H x) - x).coeff n = 0 := by
  rw [show ((inclusionHom H (subgroupTrunc H x) - x).coeff n)
      = (inclusionHom H (subgroupTrunc H x)).coeff n - x.coeff n from rfl,
    inclusionHom_subgroupTrunc_coeff_eq x hn, sub_self]

end Ring

end OddOrder.GroupAlgebra
