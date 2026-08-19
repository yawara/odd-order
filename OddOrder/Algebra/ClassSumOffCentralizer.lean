/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockIdempotent
import OddOrder.Algebra.NormalPSubgroupTrivialAction
import OddOrder.Algebra.PGroupOrbitSum
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis

/-!
# Class sums that miss `C_G(O_p(G))` are killed by every central character

**Navarro Lemma (4.7)**.  Let `char k = p`, let `N ⊴ G` be a `p`-subgroup and let `K` be a
conjugacy class of `G` with `K ∩ C_G(N) = ∅`.  Then the class sum `K̂` is annihilated by the
splitting `π : kG ↠ ∏_j M_{n_j}(k)`; equivalently every block character kills `K̂`.  (Navarro
states this as `K̂ ∈ J(Z(kG))`, which is the same thing here: the kernel of `π` is the radical.)

The proof is the orbit-counting argument.  `N` acts on `K` by conjugation, and `π (single · 1) i`
is constant on the orbits because `N` acts trivially on every simple module — Navarro (2.32),
`OddOrder.GroupAlgebra.pi_single_eq_one_of_mem_normal_pSubgroup`.  An orbit has length `1`
exactly when its point centralises `N`, which by hypothesis never happens inside `K`; so every
orbit has length divisible by `p` and the whole sum collapses to `0` in characteristic `p`
(`OddOrder.sum_eq_sum_fixedPoints`).

This is the ingredient Navarro (4.14) needs: for `P C_G(P) ≤ H ≤ N_G(P)` the truncated class sum
`∑_{x ∈ K ∩ H} x` splits into the part inside `C_G(P)` and a union of `H`-classes missing
`C_H(O_p(H))`, and the latter is invisible to `λ_b`.

## Main results

* `OddOrder.GroupAlgebra.pi_classSum_eq_zero_of_notMem_centralizer`
* `OddOrder.GroupAlgebra.blockCharacter_classSumCenter_eq_zero`
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra OddOrder.MatrixModule OddOrder.GroupTheory.CenterClassSum

variable {k ι G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k)

omit [DecidableEq (ConjClasses G)] in
/-- **The engine of Navarro (4.7).**  Let `N ⊴ G` be a `p`-subgroup and `char k = p`.  If a set
`S ⊆ G` is stable under `N`-conjugation and misses `C_G(N)`, then `π` kills `∑_{x ∈ S} x`.

The `N`-orbits on `S` all have length divisible by `p` — a length-one orbit would be a point of
`C_G(N)` — and `π (single · 1)` is constant along them because `N` acts trivially on every simple
module (Navarro (2.32)).  So the sum collapses.

Navarro states only the case where `S` is a conjugacy class
(`pi_classSum_eq_zero_of_notMem_centralizer`), but (4.14) applies it to the part of `K ∩ H` lying
off `C_G(P)`, which is a *union* of classes; keeping `S` general avoids decomposing it. -/
theorem pi_sum_ite_single_eq_zero {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p ↥N)
    (S : G → Prop) [DecidablePred S]
    (hinv : ∀ u ∈ N, ∀ x : G, S (u * x * u⁻¹) ↔ S x)
    (hdisj : ∀ x : G, S x → x ∉ Subgroup.centralizer (N : Set G)) :
    π (∑ x : G, if S x then single x (1 : k) else 0) = 0 := by
  classical
  funext i
  -- `N` acts on `G` by conjugation; its fixed points are the centraliser.
  let : MulAction ↥N G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp N.subtype)
  have hsmul : ∀ (u : ↥N) (a : G), u • a = (u : G) * a * (u : G)⁻¹ := fun _ _ => rfl
  set D : Finset G := Finset.univ.filter fun g => g ∈ Subgroup.centralizer (N : Set G) with hD
  have hDmem : ∀ g : G, g ∈ D ↔ ∀ u : ↥N, u • g = g := by
    intro g
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and,
      Subgroup.mem_centralizer_iff, hsmul]
    constructor
    · intro h u
      rw [h (u : G) u.2, mul_assoc, mul_inv_cancel, mul_one]
    · intro h u hu
      have hthis : u * g * u⁻¹ = g := h ⟨u, hu⟩
      calc u * g = u * g * u⁻¹ * u := by group
        _ = g * u := by rw [hthis]
  -- The summand, as a function on `G`.
  set F : G → Matrix (nn i) (nn i) k := fun g =>
    if S g then π (single g (1 : k)) i else 0 with hF
  have hFapply : ∀ g : G, F g = if S g then π (single g (1 : k)) i else 0 := fun _ => rfl
  have hexpand : π (∑ x : G, if S x then single x (1 : k) else 0) i = ∑ g : G, F g := by
    rw [map_sum]
    rw [show (∑ g : G, π (if S g then single g (1 : k) else 0)) i
        = ∑ g : G, π (if S g then single g (1 : k) else 0) i from Finset.sum_apply _ _ _]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hFapply]
    by_cases hg : S g
    · rw [if_pos hg, if_pos hg]
    · rw [if_neg hg, if_neg hg, map_zero, Pi.zero_apply]
  -- `p` annihilates the matrix ring.
  have hchar' : ∀ a : Matrix (nn i) (nn i) k, p • a = 0 := by
    intro a
    ext r c
    simp [nsmul_eq_mul]
  -- Navarro (2.32): `N` acts trivially, so `F` is constant on `N`-orbits.
  have hconjπ : ∀ (u : G), u ∈ N → ∀ x : G,
      π (single (u * x * u⁻¹) (1 : k)) i = π (single x (1 : k)) i := by
    intro u hu x
    have h1 : π (single u (1 : k)) i = 1 :=
      pi_single_eq_one_of_mem_normal_pSubgroup π hπ hlin hN i hu
    have h2 : π (single u⁻¹ (1 : k)) i = 1 :=
      pi_single_eq_one_of_mem_normal_pSubgroup π hπ hlin hN i (N.inv_mem hu)
    have hsplit : (single (u * x * u⁻¹) (1 : k) : MonoidAlgebra k G)
        = single u (1 : k) * single x (1 : k) * single u⁻¹ (1 : k) := by
      rw [single_mul_single, single_mul_single, one_mul, one_mul]
    rw [hsplit, map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, h1, h2, one_mul, mul_one]
  have hFconst : ∀ (u : ↥N) (x : G), F (u • x) = F x := by
    intro u x
    rw [hsmul, hFapply, hFapply, hconjπ (u : G) u.2 x, if_congr (hinv (u : G) u.2 x) rfl rfl]
  -- Orbit counting: only the fixed points survive, and `S` has none.
  rw [hexpand, sum_eq_sum_fixedPoints Fact.out hN hchar' F hFconst D hDmem]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hgc : g ∈ Subgroup.centralizer (N : Set G) := by
    simpa [hD] using hg
  rw [hFapply, if_neg fun hS => hdisj g hS hgc]

/-- **Navarro (4.7).**  If `N ⊴ G` is a `p`-subgroup, `char k = p`, and the conjugacy class `C`
avoids `C_G(N)`, then `π` kills the class sum `Ĉ`. -/
theorem pi_classSum_eq_zero_of_notMem_centralizer {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p ↥N) {C : ConjClasses G}
    (hC : ∀ x : G, ConjClasses.mk x = C → x ∉ Subgroup.centralizer (N : Set G)) :
    π (classSum (k := k) C) = 0 := by
  classical
  have hrw : (classSum (k := k) C : MonoidAlgebra k G)
      = ∑ x : G, if ConjClasses.mk x = C then single x (1 : k) else 0 := by
    rw [classSum]
    exact Finset.sum_congr rfl fun g _ => by rw [of_apply]
  rw [hrw]
  refine pi_sum_ite_single_eq_zero π hπ hlin hN _ (fun u _ x => ?_) hC
  have hclass : ConjClasses.mk (u * x * u⁻¹) = ConjClasses.mk x :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨u⁻¹, by group⟩)
  rw [hclass]

/-- **Navarro (4.7)**, block form: every block character kills such a class sum. -/
theorem blockCharacter_classSumCenter_eq_zero [Finite ι] {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p ↥N) {C : ConjClasses G}
    (hC : ∀ x : G, ConjClasses.mk x = C → x ∉ Subgroup.centralizer (N : Set G))
    (b : Block π hπ hlin) :
    blockCharacter π hπ hlin b (classSumCenter (k := k) C) = 0 := by
  have hzero : blockCharacterPi π hπ hlin (classSumCenter (k := k) C) = 0 :=
    (blockCharacterPi_eq_zero_iff π hπ hlin).mpr
      (pi_classSum_eq_zero_of_notMem_centralizer π hπ hlin hN hC)
  have := congrFun hzero b
  simpa using this

end OddOrder.GroupAlgebra
