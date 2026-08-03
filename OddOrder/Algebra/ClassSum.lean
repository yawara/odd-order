/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import OddOrder.Algebra.GroupAlgebraConjugation

/-!
# Class sums and the centre of the group algebra

The **class sum** of `g ∈ G` is `K̂ = ∑_{x ∼ g} x ∈ k[G]`.  Class sums are exactly the natural
basis of the centre `Z(k[G]) = (k[G])^G`, and in block theory they are the elements on which the
central characters `ω_B` are evaluated.

The link with the relative trace machinery is

`K̂ = Tr^G_{C_G(g)} (g)`,

which is `relTrace_single_eq_classSum` below: the conjugates of `g` are indexed by the cosets of
its centraliser, which is exactly the index set of the relative trace.  This is the identity that
turns statements about defect groups (`e_B ∈ Tr^G_D((𝒪G)^D)`) into statements about class sums.

## Main definitions

* `OddOrder.GroupAlgebra.classSum` — the class sum `K̂`.

## Main results

* `OddOrder.GroupAlgebra.relTrace_single_eq_classSum` — `K̂ = Tr^G_{C_G(g)}(g)`.
* `OddOrder.GroupAlgebra.smul_classSum` — class sums are central.
* `OddOrder.GroupAlgebra.mem_span_classSum` — the centre is spanned by the class sums.
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra

open scoped OddOrder.Conjugation

variable (k : Type*) [CommRing k] {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- The **class sum** `K̂ = ∑_{x ∼ g} x` of the conjugacy class of `g`, as an element of `k[G]`. -/
noncomputable def classSum (g : G) : MonoidAlgebra k G :=
  ∑ x ∈ Finset.univ.filter fun x => IsConj g x, single x 1

open scoped Classical in
theorem classSum_apply (g n : G) :
    (classSum k g : MonoidAlgebra k G) n = if IsConj g n then 1 else 0 := by
  have h : (classSum k g : MonoidAlgebra k G) n
      = ∑ x ∈ Finset.univ.filter fun x => IsConj g x, (single x (1 : k) : MonoidAlgebra k G) n :=
    Finsupp.finsetSum_apply _ _ _
  rw [h]
  simp [MonoidAlgebra.single_apply]

variable {k}

theorem classSum_apply_of_isConj {g n : G} (h : IsConj g n) :
    (classSum k g : MonoidAlgebra k G) n = 1 := by
  classical rw [classSum_apply, if_pos h]

theorem classSum_apply_of_not_isConj {g n : G} (h : ¬ IsConj g n) :
    (classSum k g : MonoidAlgebra k G) n = 0 := by
  classical rw [classSum_apply, if_neg h]

/-- Class sums are invariant under conjugation, i.e. they lie in the centre. -/
theorem smul_classSum (h g : G) : h • (classSum k g : MonoidAlgebra k G) = classSum k g := by
  classical
  refine Finsupp.ext fun n => ?_
  rw [conj_smul_apply, classSum_apply, classSum_apply]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro hc
    obtain ⟨c, hcc⟩ := isConj_iff.mp hc
    have hn : n = h * (c * g * c⁻¹) * h⁻¹ := by rw [hcc]; group
    exact isConj_iff.mpr ⟨h * c, by rw [hn]; group⟩
  · intro hc
    obtain ⟨c, hcc⟩ := isConj_iff.mp hc
    exact isConj_iff.mpr ⟨h⁻¹ * c, by rw [← hcc]; group⟩

omit [Fintype G] in
/-- A monomial is fixed by the centraliser of its exponent. -/
theorem smul_single_of_mem_centralizer {g u : G} (hu : u ∈ Subgroup.centralizer ({g} : Set G))
    (r : k) : u • (single g r : MonoidAlgebra k G) = single g r := by
  rw [conj_smul_single]
  congr 1
  have h := Subgroup.mem_centralizer_iff.mp hu g (Set.mem_singleton g)
  rw [← h, mul_assoc, mul_inv_cancel, mul_one]

/-- **The class sum is a relative trace**: `K̂ = Tr^G_{C_G(g)}(g)`. -/
theorem relTrace_single_eq_classSum (g : G) :
    GAlgebra.relTrace (Subgroup.centralizer ({g} : Set G)) ⊤ (single g (1 : k))
      = classSum k g := by
  classical
  letI : Fintype (G ⧸ Subgroup.centralizer ({g} : Set G)) := Fintype.ofFinite _
  have hfix : ∀ u ∈ Subgroup.centralizer ({g} : Set G),
      u • (single g (1 : k) : MonoidAlgebra k G) = single g 1 :=
    fun _ hu => smul_single_of_mem_centralizer hu 1
  rw [← GAlgebra.sum_out_smul_eq_relTrace_top hfix]
  refine Finsupp.ext fun n => ?_
  have hterm : ∀ x : G ⧸ Subgroup.centralizer ({g} : Set G),
      ((x.out : G) • (single g (1 : k) : MonoidAlgebra k G)) n
        = if (x.out : G) * g * (x.out : G)⁻¹ = n then 1 else 0 := by
    intro x
    rw [conj_smul_single, MonoidAlgebra.single_apply]
  have hsplit : (∑ x : G ⧸ Subgroup.centralizer ({g} : Set G),
        ((x.out : G) • (single g (1 : k) : MonoidAlgebra k G))) n
      = ∑ x : G ⧸ Subgroup.centralizer ({g} : Set G),
        ((x.out : G) • (single g (1 : k) : MonoidAlgebra k G)) n :=
    Finsupp.finsetSum_apply _ _ _
  rw [hsplit, Finset.sum_congr rfl fun x _ => hterm x, classSum_apply]
  -- Distinct cosets give distinct conjugates, so at most one term survives.
  have huniq : ∀ x y : G ⧸ Subgroup.centralizer ({g} : Set G),
      (x.out : G) * g * (x.out : G)⁻¹ = (y.out : G) * g * (y.out : G)⁻¹ → x = y := by
    intro x y hxy
    have hmem : (x.out : G)⁻¹ * (y.out : G) ∈ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      have h1 : (x.out : G)⁻¹ * ((y.out : G) * g * (y.out : G)⁻¹) * (x.out : G) = g := by
        rw [← hxy]; group
      calc g * ((x.out : G)⁻¹ * (y.out : G))
          = ((x.out : G)⁻¹ * ((y.out : G) * g * (y.out : G)⁻¹) * (x.out : G))
            * ((x.out : G)⁻¹ * (y.out : G)) := by rw [h1]
        _ = ((x.out : G)⁻¹ * (y.out : G)) * g := by group
    have := QuotientGroup.eq.mpr hmem
    simpa only [QuotientGroup.out_eq'] using this
  by_cases hc : IsConj g n
  · rw [if_pos hc]
    obtain ⟨c, hcn⟩ := isConj_iff.mp hc
    set x₀ : G ⧸ Subgroup.centralizer ({g} : Set G) := QuotientGroup.mk c with hx₀
    have hx₀val : (x₀.out : G) * g * (x₀.out : G)⁻¹ = n := by
      have hmem : c⁻¹ * (x₀.out : G) ∈ Subgroup.centralizer ({g} : Set G) :=
        QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
      have hg := Subgroup.mem_centralizer_iff.mp hmem g (Set.mem_singleton g)
      have hstep : (x₀.out : G) * g * (x₀.out : G)⁻¹ = c * g * c⁻¹ := by
        have : c * (c⁻¹ * (x₀.out : G)) = (x₀.out : G) := by group
        calc (x₀.out : G) * g * (x₀.out : G)⁻¹
            = (c * (c⁻¹ * (x₀.out : G))) * g * (c * (c⁻¹ * (x₀.out : G)))⁻¹ := by rw [this]
          _ = c * ((c⁻¹ * (x₀.out : G)) * g * (c⁻¹ * (x₀.out : G))⁻¹) * c⁻¹ := by group
          _ = c * g * c⁻¹ := by rw [← hg]; group
      rw [hstep, hcn]
    refine (Finset.sum_eq_single x₀ (fun y _ hy => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans (by rw [if_pos hx₀val])
    exact if_neg fun hyn => hy (huniq y x₀ (hyn.trans hx₀val.symm))
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun x _ => if_neg fun hxn => hc ?_
    exact isConj_iff.mpr ⟨(x.out : G), hxn⟩

section Span

/-- **The centre of `k[G]` is spanned by the class sums.** -/
theorem mem_span_classSum {x : MonoidAlgebra k G} (hx : ∀ g : G, g • x = x) :
    x ∈ Submodule.span k (Set.range (classSum k : G → MonoidAlgebra k G)) := by
  classical
  haveI : Finite (ConjClasses G) := Quotient.finite _
  letI : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hxconj : ∀ a b : G, IsConj a b → x a = x b := by
    intro a b hab
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    rw [← hc, ← (smul_eq_self_iff_apply c x).mp (hx c) (c * a * c⁻¹)]
    congr 1
    group
  have hsum : x = ∑ C : ConjClasses G, x C.out • classSum k C.out := by
    refine Finsupp.ext fun n => ?_
    have hsplit : (∑ C : ConjClasses G, x C.out • (classSum k C.out : MonoidAlgebra k G)) n
        = ∑ C : ConjClasses G, (x C.out • (classSum k C.out : MonoidAlgebra k G)) n :=
      Finsupp.finsetSum_apply _ _ _
    rw [hsplit]
    have hmkout : ∀ C : ConjClasses G, ConjClasses.mk C.out = C := fun C => by
      rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq C
    have hterm : ∀ C : ConjClasses G,
        (x C.out • (classSum k C.out : MonoidAlgebra k G)) n
          = if C = ConjClasses.mk n then x n else 0 := by
      intro C
      rw [MonoidAlgebra.smul_apply, smul_eq_mul, classSum_apply]
      by_cases hC : C = ConjClasses.mk n
      · have hcn : IsConj C.out n := by
          rw [← ConjClasses.mk_eq_mk_iff_isConj, hmkout]; exact hC
        rw [if_pos hcn, if_pos hC, mul_one, hxconj _ _ hcn]
      · have hcn : ¬ IsConj C.out n := by
          intro h
          exact hC (by rw [← hmkout C, ConjClasses.mk_eq_mk_iff_isConj]; exact h)
        rw [if_neg hcn, if_neg hC, mul_zero]
    rw [Finset.sum_congr rfl fun C _ => hterm C]
    simp
  rw [hsum]
  exact Submodule.sum_mem _ fun C _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨C.out, rfl⟩)

end Span

end OddOrder.GroupAlgebra
