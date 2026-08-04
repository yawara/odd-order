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
* `OddOrder.GroupAlgebra.brauerProjHom` — the same map bundled as an additive homomorphism.

## Main results

* `OddOrder.GroupAlgebra.brauerProj_mul_of_invariant` — `Br_P` is multiplicative on `(k[G])^P`.
* `OddOrder.GroupAlgebra.exists_forall_smul_eq_brauerProj_eq` — `Br_P` is onto `k[C_G(P)]`, with
  a section landing in `(k[G])^P`.
* `OddOrder.GroupAlgebra.brauerProj_conj_smul` — `Br_P` is `N_G(P)`-equivariant.
* `OddOrder.GroupAlgebra.brauerProj_one`, `brauerProj_add`, `brauerProj_smul`.
* `OddOrder.GroupAlgebra.coeff_brauerProj` — 係数での記述 (`MonoidAlgebra` は v4.32 で
  `Finsupp` の別名でなく `coeff` フィールドを持つ構造体になった)。
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
  .ofCoeff <| Finsupp.filter (fun g => g ∈ Subgroup.centralizer (P : Set G)) x.coeff

open scoped Classical in
theorem coeff_brauerProj (P : Subgroup G) (x : MonoidAlgebra k G) (g : G) :
    (brauerProj P x).coeff g
      = if g ∈ Subgroup.centralizer (P : Set G) then x.coeff g else 0 := by
  rw [brauerProj, MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply]

theorem coeff_brauerProj_of_mem {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (P : Set G)) (x : MonoidAlgebra k G) :
    (brauerProj P x).coeff g = x.coeff g := by
  classical rw [coeff_brauerProj, if_pos hg]

theorem coeff_brauerProj_of_notMem {P : Subgroup G} {g : G}
    (hg : g ∉ Subgroup.centralizer (P : Set G)) (x : MonoidAlgebra k G) :
    (brauerProj P x).coeff g = 0 := by
  classical rw [coeff_brauerProj, if_neg hg]

@[simp]
theorem brauerProj_zero (P : Subgroup G) : brauerProj P (0 : MonoidAlgebra k G) = 0 := by
  classical exact congrArg MonoidAlgebra.ofCoeff (Finsupp.filter_zero _)

theorem brauerProj_add (P : Subgroup G) (x y : MonoidAlgebra k G) :
    brauerProj P (x + y) = brauerProj P x + brauerProj P y := by
  classical exact congrArg MonoidAlgebra.ofCoeff Finsupp.filter_add

theorem brauerProj_smul (P : Subgroup G) (r : k) (x : MonoidAlgebra k G) :
    brauerProj P (r • x) = r • brauerProj P x := by
  classical exact congrArg MonoidAlgebra.ofCoeff Finsupp.filter_smul

/-- `Br_P` as an additive homomorphism, so that its kernel is an `AddSubgroup`. -/
noncomputable def brauerProjHom (P : Subgroup G) : MonoidAlgebra k G →+ MonoidAlgebra k G where
  toFun := brauerProj P
  map_zero' := brauerProj_zero P
  map_add' := brauerProj_add P

@[simp]
theorem brauerProjHom_apply (P : Subgroup G) (x : MonoidAlgebra k G) :
    brauerProjHom P x = brauerProj P x := rfl

@[simp]
theorem brauerProj_one (P : Subgroup G) : brauerProj P (1 : MonoidAlgebra k G) = 1 := by
  classical
  ext g
  rw [coeff_brauerProj]
  by_cases hg : g ∈ Subgroup.centralizer (P : Set G)
  · rw [if_pos hg]
  · rw [if_neg hg, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    rintro rfl
    exact hg (Subgroup.centralizer (P : Set G)).one_mem

end Defs

section Section

/-- **Conjugation by a normaliser element permutes the centraliser.** -/
theorem conj_mem_centralizer_iff {P : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer P)
    (c : G) : n⁻¹ * c * n ∈ Subgroup.centralizer (P : Set G)
      ↔ c ∈ Subgroup.centralizer (P : Set G) := by
  have key : ∀ m : G, m ∈ Subgroup.normalizer P → ∀ c : G,
      c ∈ Subgroup.centralizer (P : Set G) → m⁻¹ * c * m ∈ Subgroup.centralizer (P : Set G) := by
    intro m hm c hc
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hvP : m * v * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hm v).mp hv
    have hcv := Subgroup.mem_centralizer_iff.mp hc (m * v * m⁻¹) hvP
    calc v * (m⁻¹ * c * m) = m⁻¹ * ((m * v * m⁻¹) * c) * m := by group
      _ = m⁻¹ * (c * (m * v * m⁻¹)) * m := by rw [hcv]
      _ = (m⁻¹ * c * m) * v := by group
  refine ⟨fun h => ?_, key n hn c⟩
  have h' := key n⁻¹ (Subgroup.inv_mem _ hn) _ h
  have hrw : n⁻¹⁻¹ * (n⁻¹ * c * n) * n⁻¹ = c := by group
  rwa [hrw] at h'

/-- **An element supported on `C_G(P)` is `P`-fixed.**  Together with `brauerProj_eq_self` this
says that `Br_P` maps `(k[G])^P` *onto* the elements supported on the centraliser: the Brauer
quotient `(k[G])^P / ∑_{Q<P} Tr^P_Q` is `k[C_G(P)]`. -/
theorem forall_smul_eq_of_support_subset {P : Subgroup G} {x : MonoidAlgebra k G}
    (hx : ∀ g : G, g ∉ Subgroup.centralizer (P : Set G) → x.coeff g = 0) : ∀ u ∈ P, u • x = x := by
  intro u hu
  ext n
  rw [coeff_conj_smul]
  by_cases hn : n ∈ Subgroup.centralizer (P : Set G)
  · congr 1
    have hcomm := Subgroup.mem_centralizer_iff.mp hn u hu
    calc u⁻¹ * n * u = u⁻¹ * (u * n) := by rw [hcomm]; group
      _ = n := by group
  · rw [hx _ hn, hx _ ?_]
    rw [conj_mem_centralizer_iff (Subgroup.le_normalizer hu)]
    exact hn

/-- `Br_P` is the identity on elements supported on the centraliser. -/
theorem brauerProj_eq_self {P : Subgroup G} {x : MonoidAlgebra k G}
    (hx : ∀ g : G, g ∉ Subgroup.centralizer (P : Set G) → x.coeff g = 0) : brauerProj P x = x := by
  classical
  ext g
  rw [coeff_brauerProj]
  by_cases hg : g ∈ Subgroup.centralizer (P : Set G)
  · rw [if_pos hg]
  · rw [if_neg hg, hx g hg]

/-- `Br_P` is idempotent. -/
theorem brauerProj_brauerProj (P : Subgroup G) (x : MonoidAlgebra k G) :
    brauerProj P (brauerProj P x) = brauerProj P x :=
  brauerProj_eq_self fun _ hg => coeff_brauerProj_of_notMem hg x

/-- **`Br_P` is surjective onto `k[C_G(P)]`, with a section inside `(k[G])^P`.** -/
theorem exists_forall_smul_eq_brauerProj_eq {P : Subgroup G} {y : MonoidAlgebra k G}
    (hy : ∀ g : G, g ∉ Subgroup.centralizer (P : Set G) → y.coeff g = 0) :
    ∃ x : MonoidAlgebra k G, (∀ u ∈ P, u • x = x) ∧ brauerProj P x = y :=
  ⟨y, forall_smul_eq_of_support_subset hy, brauerProj_eq_self hy⟩

/-- **`Br_P` is `N_G(P)`-equivariant.**  So it carries `(k[G])^{N_G(P)}` — in particular the
centre `Z(k[G])` — into the `N_G(P)`-fixed part of `k[C_G(P)]`, which is where the Brauer
correspondence of blocks takes place. -/
theorem brauerProj_conj_smul {P : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer P)
    (x : MonoidAlgebra k G) : brauerProj P (n • x) = n • brauerProj P x := by
  classical
  ext c
  rw [coeff_brauerProj, coeff_conj_smul, coeff_conj_smul, coeff_brauerProj]
  by_cases hc : c ∈ Subgroup.centralizer (P : Set G)
  · rw [if_pos hc, if_pos ((conj_mem_centralizer_iff hn c).mpr hc)]
  · rw [if_neg hc, if_neg fun h => hc ((conj_mem_centralizer_iff hn c).mp h)]

end Section

section Mul

/-- The coefficient of a product, as a sum over the whole group. -/
theorem coeff_mul_sum [Fintype G] (x y : MonoidAlgebra k G) (c : G) :
    (x * y).coeff c = ∑ a : G, x.coeff a * y.coeff (a⁻¹ * c) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
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
  have hxc : ∀ (u : G), u ∈ P → ∀ n : G, x.coeff (u * n * u⁻¹) = x.coeff n :=
    (forall_mem_smul_eq_iff_coeff P x).mp hx
  have hyc : ∀ (u : G), u ∈ P → ∀ n : G, y.coeff (u * n * u⁻¹) = y.coeff n :=
    (forall_mem_smul_eq_iff_coeff P y).mp hy
  ext c
  by_cases hc : c ∈ Subgroup.centralizer (P : Set G)
  · -- The interesting case.
    rw [coeff_brauerProj_of_mem hc, coeff_mul_sum, coeff_mul_sum]
    have hRHS : ∀ a : G, (brauerProj P x).coeff a * (brauerProj P y).coeff (a⁻¹ * c)
        = if a ∈ C then x.coeff a * y.coeff (a⁻¹ * c) else 0 := by
      intro a
      by_cases ha : a ∈ Subgroup.centralizer (P : Set G)
      · have hac : a⁻¹ * c ∈ Subgroup.centralizer (P : Set G) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hc
        rw [coeff_brauerProj_of_mem ha, coeff_brauerProj_of_mem hac, if_pos]
        simpa [hC] using ha
      · rw [coeff_brauerProj_of_notMem ha, zero_mul, if_neg]
        simpa [hC] using ha
    rw [Finset.sum_congr rfl fun a _ => hRHS a, Finset.sum_ite_mem, Finset.univ_inter]
    -- Now apply the orbit-counting lemma.
    refine sum_eq_sum_fixedPoints hp hP hchar' (fun a => x.coeff a * y.coeff (a⁻¹ * c)) ?_ C hCmem
    intro u a
    rw [hsmul]
    have h1 : x.coeff ((u : G) * a * (u : G)⁻¹) = x.coeff a := hxc (u : G) u.2 a
    have h2 : ((u : G) * a * (u : G)⁻¹)⁻¹ * c = (u : G) * (a⁻¹ * c) * (u : G)⁻¹ := by
      have hcu : (u : G)⁻¹ * c = c * (u : G)⁻¹ := by
        exact (Subgroup.mem_centralizer_iff.mp hc) (u : G)⁻¹ (P.inv_mem u.2)
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc, mul_assoc, hcu]
      group
    rw [h1, h2, hyc (u : G) u.2]
  · -- Outside the centraliser both sides vanish.
    rw [coeff_brauerProj_of_notMem hc, coeff_mul_sum]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    by_cases ha : a ∈ Subgroup.centralizer (P : Set G)
    · have hac : a⁻¹ * c ∉ Subgroup.centralizer (P : Set G) := by
        intro hmem
        exact hc (by simpa using Subgroup.mul_mem _ ha hmem)
      rw [coeff_brauerProj_of_notMem hac, mul_zero]
    · rw [coeff_brauerProj_of_notMem ha, zero_mul]

end Mul

end OddOrder.GroupAlgebra
