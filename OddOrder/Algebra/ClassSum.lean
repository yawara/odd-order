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

* `OddOrder.GroupAlgebra.relTrace_single_apply` — `Tr^P_{P ∩ C_G(g)}(c·g)` is the `P`-orbit sum.
* `OddOrder.GroupAlgebra.relTrace_single_eq_classSum` — `K̂ = Tr^G_{C_G(g)}(g)`, the case `P = ⊤`.
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

open scoped Classical in
/-- **The relative trace of a monomial is its orbit sum.**  Under the conjugation action of a
subgroup `P`, the stabiliser of `g` is `P ∩ C_G(g)`, and the trace from it spreads the
coefficient `c` evenly over the `P`-conjugates of `g`:

`Tr^P_{P ∩ C_G(g)} (c · g) = c · ∑_{u ∈ P} ᵘg`.

For `P = ⊤` this is the class sum identity `K̂ = Tr^G_{C_G(g)}(g)`
(`relTrace_single_eq_classSum`); for a `p`-subgroup `P` it is what identifies the kernel of the
Brauer homomorphism. -/
theorem relTrace_single_apply (P : Subgroup G) (g : G) (c : k) (n : G) :
    GAlgebra.relTrace (P ⊓ Subgroup.centralizer ({g} : Set G)) P (single g c) n
      = if ∃ u ∈ P, u * g * u⁻¹ = n then c else 0 := by
  classical
  set Q : Subgroup G := P ⊓ Subgroup.centralizer ({g} : Set G) with hQ
  letI : Fintype (↥P ⧸ Q.subgroupOf P) := Fintype.ofFinite _
  set rep : ↥P ⧸ Q.subgroupOf P → G := fun x => ((x.out : ↥P) : G) with hrep
  have hrepP : ∀ x, rep x ∈ P := fun x => (x.out : ↥P).2
  -- Membership in the stabiliser, stated so that `Q` never has to be rewritten (it occurs in the
  -- type of the quotient, so `rw` would break the motive).
  have hQmem : ∀ w : G, w ∈ P → g * w = w * g → w ∈ Q := fun w hw hcomm =>
    Subgroup.mem_inf.mpr ⟨hw, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact hcomm⟩
  have hQcomm : ∀ w : G, w ∈ Q → g * w = w * g := fun w hw =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 g (Set.mem_singleton g)
  have hR : GAlgebra.relTrace Q P (single g c : MonoidAlgebra k G)
      = ∑ x : ↥P ⧸ Q.subgroupOf P, rep x • (single g c : MonoidAlgebra k G) := rfl
  have hsplit : (∑ x : ↥P ⧸ Q.subgroupOf P, rep x • (single g c : MonoidAlgebra k G)) n
      = ∑ x : ↥P ⧸ Q.subgroupOf P, (rep x • (single g c : MonoidAlgebra k G)) n :=
    Finsupp.finsetSum_apply _ _ _
  have hterm : ∀ x : ↥P ⧸ Q.subgroupOf P,
      (rep x • (single g c : MonoidAlgebra k G)) n
        = if rep x * g * (rep x)⁻¹ = n then c else 0 :=
    fun x => by rw [conj_smul_single, MonoidAlgebra.single_apply]
  rw [hR, hsplit, Finset.sum_congr rfl fun x _ => hterm x]
  -- Distinct cosets of the stabiliser give distinct conjugates, so at most one term survives.
  have huniq : ∀ x y : ↥P ⧸ Q.subgroupOf P,
      rep x * g * (rep x)⁻¹ = rep y * g * (rep y)⁻¹ → x = y := by
    intro x y hxy
    have hmem : ((x.out : ↥P)⁻¹ * (y.out : ↥P)) ∈ Q.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf]
      refine hQmem _ (P.mul_mem (P.inv_mem (hrepP x)) (hrepP y)) ?_
      have h1 : (rep x)⁻¹ * (rep y * g * (rep y)⁻¹) * rep x = g := by rw [← hxy]; group
      calc g * ((rep x)⁻¹ * rep y)
          = ((rep x)⁻¹ * (rep y * g * (rep y)⁻¹) * rep x) * ((rep x)⁻¹ * rep y) := by rw [h1]
        _ = ((rep x)⁻¹ * rep y) * g := by group
    have := QuotientGroup.eq.mpr hmem
    simpa only [QuotientGroup.out_eq'] using this
  by_cases hc : ∃ u ∈ P, u * g * u⁻¹ = n
  · rw [if_pos hc]
    obtain ⟨u, hu, hun⟩ := hc
    set x₀ : ↥P ⧸ Q.subgroupOf P := QuotientGroup.mk ⟨u, hu⟩ with hx₀
    have hx₀val : rep x₀ * g * (rep x₀)⁻¹ = n := by
      have hmem : (⟨u, hu⟩ : ↥P)⁻¹ * (x₀.out : ↥P) ∈ Q.subgroupOf P :=
        QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
      rw [Subgroup.mem_subgroupOf] at hmem
      have hg : g * (u⁻¹ * rep x₀) = (u⁻¹ * rep x₀) * g := hQcomm _ hmem
      have hstep : rep x₀ * g * (rep x₀)⁻¹ = u * g * u⁻¹ := by
        have hu' : u * (u⁻¹ * rep x₀) = rep x₀ := by group
        calc rep x₀ * g * (rep x₀)⁻¹
            = (u * (u⁻¹ * rep x₀)) * g * (u * (u⁻¹ * rep x₀))⁻¹ := by rw [hu']
          _ = u * ((u⁻¹ * rep x₀) * g * (u⁻¹ * rep x₀)⁻¹) * u⁻¹ := by group
          _ = u * g * u⁻¹ := by rw [← hg]; group
      rw [hstep, hun]
    refine (Finset.sum_eq_single x₀ (fun y _ hy => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans (by rw [if_pos hx₀val])
    exact if_neg fun hyn => hy (huniq y x₀ (hyn.trans hx₀val.symm))
  · rw [if_neg hc]
    exact Finset.sum_eq_zero fun x _ => if_neg fun hxn => hc ⟨rep x, hrepP x, hxn⟩

/-- **The class sum is a relative trace**: `K̂ = Tr^G_{C_G(g)}(g)`.  This is the case `P = ⊤` of
`relTrace_single_apply`. -/
theorem relTrace_single_eq_classSum (g : G) :
    GAlgebra.relTrace (Subgroup.centralizer ({g} : Set G)) ⊤ (single g (1 : k))
      = classSum k g := by
  classical
  refine Finsupp.ext fun n => ?_
  have hQ : (⊤ : Subgroup G) ⊓ Subgroup.centralizer ({g} : Set G)
      = Subgroup.centralizer ({g} : Set G) := top_inf_eq _
  rw [← hQ, relTrace_single_apply, classSum_apply]
  have hiff : (∃ u ∈ (⊤ : Subgroup G), u * g * u⁻¹ = n) ↔ IsConj g n := by
    simp only [Subgroup.mem_top, true_and, isConj_iff]
  by_cases h : IsConj g n
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg fun hh => h (hiff.mp hh)]

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
