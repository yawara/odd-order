/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Centralizer
import OddOrder.Algebra.GroupAlgebraConjugation
import OddOrder.Algebra.PGroupOrbitSum

/-!
# The Brauer homomorphism

For a `p`-subgroup `P ≤ G` and a coefficient ring `k` of characteristic `p`, the **Brauer
homomorphism** truncates an element of `k[G]` to the part supported on the centraliser `C_G(P)`:

`Br_P (∑_g a_g g) = ∑_{g ∈ C_G(P)} a_g g`.

On the fixed ring `(k[G])^P` — the elements invariant under `P`-conjugation — this truncation is
a *ring* homomorphism.  That is the content of `brauerProj_mul_of_invariant`, and it is the
gateway to the Brauer correspondence between blocks of `G` and blocks of `N_G(P)`.

The proof is the orbit-counting argument of `OddOrder.sum_eq_sum_fixedPoints`: the coefficient of
a central element `c ∈ C_G(P)` in `x * y` is `∑_{a ∈ G} x_a y_{a⁻¹ c}`, the summand is constant
on `P`-conjugation orbits, and the orbits that are not singletons have size divisible by `p`.

## Main definitions

* `OddOrder.GroupAlgebra.brauerProj` — the truncation `Br_P`.

## Main results

* `OddOrder.GroupAlgebra.brauerProj_mul_of_invariant` — `Br_P` is multiplicative on `(k[G])^P`.
* `OddOrder.GroupAlgebra.brauerProj_one`, `brauerProj_add`, `brauerProj_smul`.
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra

open scoped OddOrder.Conjugation

variable {k : Type*} [CommRing k] {G : Type*} [Group G]

section Defs

open scoped Classical in
/-- The **Brauer homomorphism** `Br_P` : truncate `x ∈ k[G]` to its part supported on the
centraliser of `P`.  It is only a ring homomorphism on the `P`-fixed elements
(`brauerProj_mul_of_invariant`); as a map on all of `k[G]` it is merely `k`-linear. -/
noncomputable def brauerProj (P : Subgroup G) (x : MonoidAlgebra k G) : MonoidAlgebra k G :=
  Finsupp.filter (fun g => g ∈ Subgroup.centralizer (P : Set G)) x

open scoped Classical in
theorem brauerProj_apply (P : Subgroup G) (x : MonoidAlgebra k G) (g : G) :
    brauerProj P x g = if g ∈ Subgroup.centralizer (P : Set G) then x g else 0 := by
  rw [brauerProj, Finsupp.filter_apply]

theorem brauerProj_apply_of_mem {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (P : Set G)) (x : MonoidAlgebra k G) :
    brauerProj P x g = x g := by
  classical rw [brauerProj_apply, if_pos hg]

theorem brauerProj_apply_of_notMem {P : Subgroup G} {g : G}
    (hg : g ∉ Subgroup.centralizer (P : Set G)) (x : MonoidAlgebra k G) :
    brauerProj P x g = 0 := by
  classical rw [brauerProj_apply, if_neg hg]

@[simp]
theorem brauerProj_zero (P : Subgroup G) : brauerProj P (0 : MonoidAlgebra k G) = 0 := by
  classical exact Finsupp.filter_zero _

theorem brauerProj_add (P : Subgroup G) (x y : MonoidAlgebra k G) :
    brauerProj P (x + y) = brauerProj P x + brauerProj P y := by
  classical exact Finsupp.filter_add

theorem brauerProj_smul (P : Subgroup G) (r : k) (x : MonoidAlgebra k G) :
    brauerProj P (r • x) = r • brauerProj P x := by
  classical exact Finsupp.filter_smul

@[simp]
theorem brauerProj_one (P : Subgroup G) : brauerProj P (1 : MonoidAlgebra k G) = 1 := by
  classical
  refine Finsupp.ext fun g => ?_
  rw [brauerProj_apply]
  by_cases hg : g ∈ Subgroup.centralizer (P : Set G)
  · rw [if_pos hg]
  · rw [if_neg hg, MonoidAlgebra.one_def, MonoidAlgebra.single_apply, if_neg]
    rintro rfl
    exact hg (Subgroup.centralizer (P : Set G)).one_mem

end Defs

section Mul

/-- The coefficient of a product, as a sum over the whole group. -/
theorem mul_apply_sum [Fintype G] (x y : MonoidAlgebra k G) (c : G) :
    (x * y) c = ∑ a : G, x a * y (a⁻¹ * c) := by
  rw [MonoidAlgebra.mul_apply_left]
  exact Finsupp.sum_fintype _ _ fun _ => by simp

variable {p : ℕ}

/-- **The Brauer homomorphism is multiplicative on the `P`-fixed elements.**

`P` is a `p`-subgroup of `G` and the coefficient ring has characteristic `p`. -/
theorem brauerProj_mul_of_invariant [Finite G] (hp : p.Prime) (hchar : (p : k) = 0)
    {P : Subgroup G}
    (hP : IsPGroup p ↥P) {x y : MonoidAlgebra k G} (hx : ∀ g ∈ P, g • x = x)
    (hy : ∀ g ∈ P, g • y = y) :
    brauerProj P (x * y) = brauerProj P x * brauerProj P y := by
  classical
  letI := Fintype.ofFinite G
  -- `P` acts on `G` by conjugation.
  letI : MulAction ↥P G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp P.subtype)
  have hsmul : ∀ (u : ↥P) (a : G), u • a = (u : G) * a * (u : G)⁻¹ := fun _ _ => rfl
  -- The fixed points of that action are the centraliser.
  set C : Finset G := Finset.univ.filter fun g => g ∈ Subgroup.centralizer (P : Set G) with hC
  have hCmem : ∀ g : G, g ∈ C ↔ ∀ u : ↥P, u • g = g := by
    intro g
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and,
      Subgroup.mem_centralizer_iff, hsmul]
    constructor
    · intro h u
      rw [h (u : G) u.2, mul_assoc, mul_inv_cancel, mul_one]
    · intro h u hu
      have hthis : u * g * u⁻¹ = g := h ⟨u, hu⟩
      calc u * g = u * g * u⁻¹ * u := by group
        _ = g * u := by rw [hthis]
  have hchar' : ∀ v : k, p • v = 0 := fun v => by
    rw [nsmul_eq_mul, hchar, zero_mul]
  -- Coefficient-wise invariance of `x` and `y`.
  have hxc : ∀ (u : G), u ∈ P → ∀ n : G, x (u * n * u⁻¹) = x n :=
    (forall_mem_smul_eq_iff_apply P x).mp hx
  have hyc : ∀ (u : G), u ∈ P → ∀ n : G, y (u * n * u⁻¹) = y n :=
    (forall_mem_smul_eq_iff_apply P y).mp hy
  refine Finsupp.ext fun c => ?_
  by_cases hc : c ∈ Subgroup.centralizer (P : Set G)
  · -- The interesting case.
    rw [brauerProj_apply_of_mem hc, mul_apply_sum, mul_apply_sum]
    have hRHS : ∀ a : G, brauerProj P x a * brauerProj P y (a⁻¹ * c)
        = if a ∈ C then x a * y (a⁻¹ * c) else 0 := by
      intro a
      by_cases ha : a ∈ Subgroup.centralizer (P : Set G)
      · have hac : a⁻¹ * c ∈ Subgroup.centralizer (P : Set G) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hc
        rw [brauerProj_apply_of_mem ha, brauerProj_apply_of_mem hac, if_pos]
        simpa [hC] using ha
      · rw [brauerProj_apply_of_notMem ha, zero_mul, if_neg]
        simpa [hC] using ha
    rw [Finset.sum_congr rfl fun a _ => hRHS a, Finset.sum_ite_mem, Finset.univ_inter]
    -- Now apply the orbit-counting lemma.
    refine sum_eq_sum_fixedPoints hp hP hchar' (fun a => x a * y (a⁻¹ * c)) ?_ C hCmem
    intro u a
    rw [hsmul]
    have h1 : x ((u : G) * a * (u : G)⁻¹) = x a := hxc (u : G) u.2 a
    have h2 : ((u : G) * a * (u : G)⁻¹)⁻¹ * c = (u : G) * (a⁻¹ * c) * (u : G)⁻¹ := by
      have hcu : (u : G)⁻¹ * c = c * (u : G)⁻¹ := by
        exact (Subgroup.mem_centralizer_iff.mp hc) (u : G)⁻¹ (P.inv_mem u.2)
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc, mul_assoc, hcu]
      group
    rw [h1, h2, hyc (u : G) u.2]
  · -- Outside the centraliser both sides vanish.
    rw [brauerProj_apply_of_notMem hc, mul_apply_sum]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    by_cases ha : a ∈ Subgroup.centralizer (P : Set G)
    · have hac : a⁻¹ * c ∉ Subgroup.centralizer (P : Set G) := by
        intro hmem
        exact hc (by simpa using Subgroup.mul_mem _ ha hmem)
      rw [brauerProj_apply_of_notMem hac, mul_zero]
    · rw [brauerProj_apply_of_notMem ha, zero_mul]

end Mul

end OddOrder.GroupAlgebra
