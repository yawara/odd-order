/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BrauerHomomorphism
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCorrespondence

/-!
# The Brauer homomorphism as a map into `k[H]`

`OddOrder.GroupAlgebra.brauerProj P` truncates `k[G]` to the part supported on `C_G(P)`, staying
inside `k[G]`.  For the Brauer correspondence one wants the result in `k[H]`, where `H` is a
subgroup containing `C_G(P)`; that is what `brauerTrunc P H` is.  The two agree under the
inclusion `k[H] ↪ k[G]`, which is injective, so every identity proved for `brauerProj` transfers —
in particular multiplicativity on `P`-invariant elements.

This is the second half of Navarro (4.14): once `λ_b^G` is known to be `λ_b ∘ Br_P`
(`OddOrder.RepresentationTheory.Modular.blockCharacter_truncClassSumCenter_eq`), it is an algebra
homomorphism, hence the induced block `b^G` is defined.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.brauerTrunc` — `Br_P : k[G] → k[H]`
* `OddOrder.RepresentationTheory.Modular.inclusionHom` — `k[H] ↪ k[G]`

## Main results

* `OddOrder.RepresentationTheory.Modular.inclusionHom_brauerTrunc` — the two truncations agree
* `OddOrder.RepresentationTheory.Modular.brauerTrunc_mem_center`
* `OddOrder.RepresentationTheory.Modular.brauerTrunc_mul_of_mem_center` — multiplicativity
* `OddOrder.RepresentationTheory.Modular.brauerTrunc_classSum`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.GroupAlgebra
open OddOrder.GroupTheory.CenterClassSum

open scoped OddOrder.Conjugation

variable {k G : Type*} [Field k] [Group G]
variable (P H : Subgroup G) [Fintype H]
  [DecidablePred fun g : G => g ∈ Subgroup.centralizer (P : Set G)]

/-! ### The truncation -/

/-- **The Brauer homomorphism landing in `k[H]`**: keep only the coefficients at the elements of
`H` that centralise `P`.  When `C_G(P) ≤ H` this loses nothing compared with
`OddOrder.GroupAlgebra.brauerProj P` (`inclusionHom_brauerTrunc`). -/
noncomputable def brauerTrunc (x : MonoidAlgebra k G) : MonoidAlgebra k ↥H :=
  ∑ h : ↥H, if (h : G) ∈ Subgroup.centralizer (P : Set G)
    then MonoidAlgebra.single h (x.coeff (h : G)) else 0

theorem coeff_brauerTrunc (x : MonoidAlgebra k G) (y : ↥H) :
    (brauerTrunc P H x).coeff y
      = if (y : G) ∈ Subgroup.centralizer (P : Set G) then x.coeff (y : G) else 0 := by
  classical
  have hsum : (brauerTrunc P H x).coeff y
      = ∑ h : ↥H, (if (h : G) ∈ Subgroup.centralizer (P : Set G)
          then MonoidAlgebra.single h (x.coeff (h : G)) else 0).coeff y := by
    rw [brauerTrunc]; exact MonoidAlgebra.coeff_finsetSum _ _ _
  have hzero : ((0 : MonoidAlgebra k ↥H)).coeff y = 0 := rfl
  have hterm : ∀ h : ↥H,
      (if (h : G) ∈ Subgroup.centralizer (P : Set G)
          then MonoidAlgebra.single h (x.coeff (h : G)) else 0).coeff y
        = if h = y then (if (h : G) ∈ Subgroup.centralizer (P : Set G)
            then x.coeff (h : G) else 0) else 0 := by
    intro h
    rw [apply_ite (fun f : MonoidAlgebra k ↥H => f.coeff y), MonoidAlgebra.coeff_single,
      Finsupp.single_apply, hzero]
    by_cases hh : h = y
    · rw [if_pos hh, if_pos hh]
    · rw [if_neg hh, if_neg hh, ite_self]
  rw [hsum, Finset.sum_congr rfl (fun h _ => hterm h),
    Finset.sum_ite_eq' Finset.univ y
      (fun h : ↥H => if (h : G) ∈ Subgroup.centralizer (P : Set G) then x.coeff (h : G) else 0)]
  simp

variable {P H}

@[simp]
theorem brauerTrunc_zero : brauerTrunc P H (0 : MonoidAlgebra k G) = 0 := by
  refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
  rw [coeff_brauerTrunc]
  simp

theorem brauerTrunc_add (x y : MonoidAlgebra k G) :
    brauerTrunc P H (x + y) = brauerTrunc P H x + brauerTrunc P H y := by
  refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
  rw [show ((brauerTrunc P H x + brauerTrunc P H y).coeff n)
      = (brauerTrunc P H x).coeff n + (brauerTrunc P H y).coeff n from rfl,
    coeff_brauerTrunc, coeff_brauerTrunc, coeff_brauerTrunc]
  by_cases hn : (n : G) ∈ Subgroup.centralizer (P : Set G)
  · rw [if_pos hn, if_pos hn, if_pos hn]; rfl
  · rw [if_neg hn, if_neg hn, if_neg hn, add_zero]

theorem brauerTrunc_smul (c : k) (x : MonoidAlgebra k G) :
    brauerTrunc P H (c • x) = c • brauerTrunc P H x := by
  refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
  rw [MonoidAlgebra.coeff_smul_apply, coeff_brauerTrunc, coeff_brauerTrunc,
    MonoidAlgebra.coeff_smul_apply]
  by_cases hn : (n : G) ∈ Subgroup.centralizer (P : Set G)
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn, smul_zero]

@[simp]
theorem brauerTrunc_one : brauerTrunc P H (1 : MonoidAlgebra k G) = 1 := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
  rw [coeff_brauerTrunc]
  have hone : ∀ m : G, (1 : MonoidAlgebra k G).coeff m = if m = 1 then (1 : k) else 0 := by
    intro m
    rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hm : m = 1
    · rw [if_pos hm, if_pos hm.symm]
    · rw [if_neg hm, if_neg fun h => hm h.symm]
  have honeH : (1 : MonoidAlgebra k ↥H).coeff n = if n = 1 then (1 : k) else 0 := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hn : n = 1
    · rw [if_pos hn, if_pos hn.symm]
    · rw [if_neg hn, if_neg fun h => hn h.symm]
  rw [hone, honeH]
  by_cases hn : n = 1
  · subst hn
    simp
  · have hn' : (n : G) ≠ 1 := fun h => hn (Subtype.ext h)
    rw [if_neg hn', if_neg hn, ite_self]

/-! ### Comparison with `brauerProj` through the inclusion `k[H] ↪ k[G]` -/

variable (H) in
/-- The inclusion `k[H] ↪ k[G]` induced by `H ≤ G`. -/
noncomputable def inclusionHom : MonoidAlgebra k ↥H →+* MonoidAlgebra k G :=
  MonoidAlgebra.mapDomainRingHom k H.subtype

omit [Fintype ↥H] in
theorem inclusionHom_injective : Function.Injective (inclusionHom (k := k) H) :=
  MonoidAlgebra.mapDomain_injective Subtype.val_injective

omit [Fintype ↥H] in
theorem coeff_inclusionHom_of_mem {n : G} (hn : n ∈ H) (a : MonoidAlgebra k ↥H) :
    (inclusionHom H a).coeff n = a.coeff ⟨n, hn⟩ :=
  Finsupp.mapDomain_apply Subtype.val_injective a.coeff ⟨n, hn⟩

omit [Fintype ↥H] in
theorem coeff_inclusionHom_of_notMem {n : G} (hn : n ∉ H) (a : MonoidAlgebra k ↥H) :
    (inclusionHom H a).coeff n = 0 :=
  Finsupp.mapDomain_notin_range a.coeff n (by rintro ⟨y, rfl⟩; exact hn y.2)

/-- **The two Brauer truncations agree.**  Under `C_G(P) ≤ H` the image of `brauerTrunc P H x` in
`k[G]` is exactly `brauerProj P x`. -/
theorem inclusionHom_brauerTrunc (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (x : MonoidAlgebra k G) :
    inclusionHom H (brauerTrunc P H x) = brauerProj P x := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
  by_cases hn : n ∈ Subgroup.centralizer (P : Set G)
  · rw [coeff_inclusionHom_of_mem (hCH hn), coeff_brauerTrunc, if_pos hn,
      coeff_brauerProj_of_mem hn]
  · rw [coeff_brauerProj_of_notMem hn]
    by_cases hnH : n ∈ H
    · rw [coeff_inclusionHom_of_mem hnH, coeff_brauerTrunc, if_neg hn]
    · rw [coeff_inclusionHom_of_notMem hnH]

/-! ### Centrality and multiplicativity -/

/-- The truncation of a central element is central: `H` normalises `P`, hence `C_G(P)`, and the
coefficient function of a central element is constant on `G`-classes. -/
theorem brauerTrunc_mem_center (hHN : H ≤ Subgroup.normalizer (P : Set G))
    {x : MonoidAlgebra k G} (hx : x ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    brauerTrunc P H x ∈ Subalgebra.center k (MonoidAlgebra k ↥H) := by
  have hxfix : ∀ g n : G, x.coeff (g⁻¹ * n * g) = x.coeff n := fun g n =>
    (smul_eq_self_iff_coeff g x).mp
      (forall_smul_eq_iff_mem_center.mpr
        (fun z => ((Subalgebra.mem_center_iff.mp hx) z).symm) g) n
  have hfix : ∀ u : ↥H, u • brauerTrunc P H x = brauerTrunc P H x := by
    intro u
    refine (smul_eq_self_iff_coeff u _).mpr fun y => ?_
    have hcoe : ((u⁻¹ * y * u : ↥H) : G) = (u : G)⁻¹ * (y : G) * (u : G) := by push_cast; rfl
    have hmem : ((u : G)⁻¹ * (y : G) * (u : G) ∈ Subgroup.centralizer (P : Set G))
        ↔ ((y : G) ∈ Subgroup.centralizer (P : Set G)) := by
      have h := mem_centralizer_conj_iff (P := P)
        ((Subgroup.normalizer (P : Set G)).inv_mem (hHN u.2)) (y : G)
      simpa using h
    rw [coeff_brauerTrunc, coeff_brauerTrunc, hcoe,
      if_congr hmem (hxfix (u : G) (y : G)) rfl]
  rw [Subalgebra.mem_center_iff]
  exact fun b => (forall_smul_eq_iff_mem_center.mp hfix b).symm

variable (P H) in
/-- The truncation of a central element, bundled into `Z(k[H])`. -/
noncomputable def brauerTruncCenter (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (x : ↥(Subalgebra.center k (MonoidAlgebra k G))) :
    ↥(Subalgebra.center k (MonoidAlgebra k ↥H)) :=
  ⟨brauerTrunc P H (x : MonoidAlgebra k G), brauerTrunc_mem_center hHN x.2⟩

/-- **Multiplicativity of the Brauer truncation on the centre.**  Central elements are
`P`-invariant, so `OddOrder.GroupAlgebra.brauerProj_mul_of_invariant` applies; the identity
transfers back along the injective inclusion `k[H] ↪ k[G]`. -/
theorem brauerTrunc_mul_of_mem_center [Finite G] {p : ℕ} (hp : p.Prime) (hchar : (p : k) = 0)
    (hP : IsPGroup p ↥P) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    {x y : MonoidAlgebra k G} (hx : x ∈ Subalgebra.center k (MonoidAlgebra k G))
    (hy : y ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    brauerTrunc P H (x * y) = brauerTrunc P H x * brauerTrunc P H y := by
  refine inclusionHom_injective (H := H) ?_
  have hxP : ∀ g ∈ P, g • x = x := fun g _ =>
    forall_smul_eq_iff_mem_center.mpr
      (fun z => ((Subalgebra.mem_center_iff.mp hx) z).symm) g
  have hyP : ∀ g ∈ P, g • y = y := fun g _ =>
    forall_smul_eq_iff_mem_center.mpr
      (fun z => ((Subalgebra.mem_center_iff.mp hy) z).symm) g
  rw [map_mul, inclusionHom_brauerTrunc hCH, inclusionHom_brauerTrunc hCH,
    inclusionHom_brauerTrunc hCH, brauerProj_mul_of_invariant hp hchar hP hxP hyP]

/-! ### The truncation of a class sum -/

variable [DecidableEq (ConjClasses G)] [Fintype G]

/-- The Brauer truncation of a class sum is the `C_G(P)`-part of `K ∩ H`. -/
theorem brauerTrunc_classSum (C : ConjClasses G) :
    brauerTrunc P H (classSum (k := k) C) = centralizerTruncClassSum P H C := by
  classical
  rw [brauerTrunc, centralizerTruncClassSum]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hcent : (h : G) ∈ Subgroup.centralizer (P : Set G)
  · rw [if_pos hcent, coeff_classSum]
    by_cases hclass : ConjClasses.mk (h : G) = C
    · rw [if_pos hclass, if_pos ⟨hclass, hcent⟩, MonoidAlgebra.of_apply]
    · rw [if_neg hclass, if_neg (by tauto)]
      exact MonoidAlgebra.single_zero h
  · rw [if_neg hcent, if_neg (by tauto)]

end OddOrder.RepresentationTheory.Modular
