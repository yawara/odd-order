/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularCosetSubgroup
import OddOrder.GroupTheory.RepresentationTheory.InducedAdjoinSpan
import OddOrder.GroupTheory.RepresentationTheory.PRegularCosetInduction

/-!
# Gorenstein Lemma 7.6, packaged

The consumers of Lemma 7.6 (Lemmas 7.7 and 7.8, issue 9508, 段 F) only ever use it in one shape:
given a prime `p`, a `p`-regular element `u` and a `p`-subgroup `P` centralising `u`, there is an
element of `v_R(G)` which is integer-valued, vanishes off the `p`-class of `u`, and takes the value
`|C_G(u)| / |P|` at `u`.

This file assembles that statement once, choosing the root of unity `ζ = ω^{N/n}` (`n = orderOf u`)
inside the ambient primitive `N`-th root, and building `H = ⟨u⟩ P` with `pRegularProd`.

The family `𝒳` is required only to contain the subgroups `⟨u⟩ P` — that is `IsElementaryFamily`,
and it is exactly what a consumer of Brauer's characterization has to check its hypothesis for.

## Main definitions

* `OddOrder.RepresentationTheory.IsElementaryFamily`

## Main results

* `OddOrder.RepresentationTheory.exists_pClassIndicator` — **Lemma 7.6**, packaged

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.6 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G K : Type*} [Group G] [Fintype G] [Field K] [CharZero K]
  {N : ℕ} {ω : K} {𝒳 : Set (Subgroup G)}

variable (𝒳) in
/-- **The family contains every `⟨u⟩ P`** with `u` a `p`-regular element and `P` a `p`-subgroup
centralising it, for every prime `p`. -/
def IsElementaryFamily : Prop :=
  ∀ p : ℕ, p.Prime → ∀ u : G, IsPRegular p u → ∀ P : Subgroup G, IsPGroup p ↥P →
    ∀ hcomm : ∀ v ∈ P, Commute u v, pRegularProd u P hcomm ∈ 𝒳

/-- **Gorenstein Lemma 7.6, packaged.**  An element of `v_R(G)` supported on the `p`-class of `u`,
integer-valued, with value `|C_G(u)| / |P|` at `u`. -/
theorem exists_pClassIndicator (h𝒳 : IsElementaryFamily 𝒳) (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hω : IsPrimitiveRoot ω N)
    {p : ℕ} (hp : p.Prime) {u : G} (hu : IsPRegular p u)
    {P : Subgroup G} (hPp : IsPGroup p ↥P) (hcomm : ∀ v ∈ P, Commute u v) :
    ∃ χ : G → K, χ ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) ∧
      (∀ y : G, χ y = ((conjugateCount (leftCosetOf u P) y / Nat.card ↥P : ℕ) : K)) ∧
      (∀ y z : G, IsConj y z → χ y = χ z) ∧
      (∀ y : G, ¬ IsConj (pRegularPart p y) u → χ y = 0) ∧
      χ u = ((Nat.card ↥(Subgroup.centralizer ({u} : Set G)) / Nat.card ↥P : ℕ) : K) := by
  classical
  have hωint : IsIntegral ℤ ω := isIntegral_of_pow_eq_one hN hω.pow_eq_one
  have hnpos : 0 < orderOf u := orderOf_pos u
  have hdvd : orderOf u ∣ N := orderOf_dvd_of_pow_eq_one (hgN u)
  -- the root of unity of order `orderOf u`
  have hNfac : N = (N / orderOf u) * orderOf u := (Nat.div_mul_cancel hdvd).symm
  have hprim : IsPrimitiveRoot (ω ^ (N / orderOf u)) (orderOf u) :=
    hω.pow (Nat.pos_of_ne_zero hN) hNfac
  have hne : ω ^ (N / orderOf u) ≠ 0 := by
    intro h
    have := hprim.pow_eq_one
    rw [h, zero_pow hnpos.ne'] at this
    exact zero_ne_one this
  set ζ : Kˣ := Units.mk0 _ hne with hζ
  have hcoe : ((ζ : Kˣ) : K) = ω ^ (N / orderOf u) := rfl
  have hord : orderOf ζ = orderOf u := by
    refine (IsPrimitiveRoot.eq_orderOf ?_).symm
    exact IsPrimitiveRoot.coe_units_iff.mp (by rw [hcoe]; exact hprim)
  -- the subgroup and the class function
  set H : Subgroup G := pRegularProd u P hcomm with hH
  have hmemH : H ∈ 𝒳 := h𝒳 p hp u hu P hPp hcomm
  have hgen : ∀ h : G, h ∈ H → ∃ (a : ℕ) (v : G), v ∈ P ∧ h = u ^ a * v := fun h hh =>
    (mem_pRegularProd_nat hcomm).mp hh
  have hcard : Nat.card ↥H = orderOf u * Nat.card ↥P := card_pRegularProd hp hu hPp hcomm
  have hform : ∀ y : G, induceFun H (cosetIndicator u P H K) y
      = ((conjugateCount (leftCosetOf u P) y / Nat.card ↥P : ℕ) : K) :=
    fun y => induceFun_cosetIndicator hcomm (self_mem_pRegularProd hcomm)
      (le_pRegularProd hcomm) hcard y
  refine ⟨induceFun H (cosetIndicator u P H K), ?_, hform, ?_, ?_, ?_⟩
  · exact induceFun_mem_adjoinSpan_inducedVirtualCharacters hmemH
      (cosetIndicator_mem_adjoinSpan hp hu hPp hcomm hord hgen hωint
        (by rw [hcoe]; exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ω) _))
  · intro y z hyz
    obtain ⟨w, hw⟩ := isConj_iff.mp hyz
    rw [hform y, ← hw, hform, conjugateCount_conj]
  · exact fun y hy => induceFun_cosetIndicator_eq_zero hp hu hPp hcomm
      (self_mem_pRegularProd hcomm) (le_pRegularProd hcomm) hcard hy
  · exact induceFun_cosetIndicator_self hp hu hPp hcomm (self_mem_pRegularProd hcomm)
      (le_pRegularProd hcomm) hcard

end OddOrder.RepresentationTheory
