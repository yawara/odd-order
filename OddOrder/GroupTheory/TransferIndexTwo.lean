/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Transfer for a normal subgroup of index two

Peterfalvi Part II, Ch. II, (17) needs the Hall–Wielandt theorem only in the special
situation `N = N_G(R₂) = R₂⟨s⟩`, where the Sylow subgroup `R₂` is *normal of index `2`*
in `N`.  There the transfer can be computed by hand, and the classical focal-subgroup
machinery is not needed.

This file collects the elementary group theory of that situation.  The key consequence
is `le_commutator_of_conj_mul_mem`: if `s` inverts `P` modulo `⁅N, N⁆` — which is what
a trivial transfer says — and `|P|` is odd, then `P ≤ ⁅N, N⁆`, so the abelianisation of
`N` has no odd part.

See issue 9503.
-/

set_option autoImplicit false

open scoped commutatorElement

namespace OddOrder.GroupTheory

open Subgroup Subgroup.leftTransversals MulAction
open scoped Pointwise

variable {G : Type*} [Group G]

section Transfer

variable {H : Subgroup G} {A : Type*} [CommGroup A]

/-- `ϕ` identifies `H`-conjugate elements, because `A` is commutative. -/
lemma map_eq_of_conj_eq (ϕ : ↥H →* A) {a b h : G} (ha : a ∈ H) (hb : b ∈ H) (hh : h ∈ H)
    (heq : a = h⁻¹ * b * h) : ϕ ⟨a, ha⟩ = ϕ ⟨b, hb⟩ := by
  have hsub : (⟨a, ha⟩ : ↥H) = (⟨h, hh⟩ : ↥H)⁻¹ * ⟨b, hb⟩ * ⟨h, hh⟩ := Subtype.ext heq
  rw [hsub, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]

/-- **Transfer over a normal subgroup of index two.**

If `[G : H] = 2` and `s ∉ H`, then for `x ∈ H` whose `G`-conjugates all stay in `H`
(e.g. `H` normal) the transfer is the product of the `ϕ`-values of `x` and of its
`s`-conjugate:

`transfer ϕ x = ϕ x * ϕ (s⁻¹ x s)`.

Indeed left multiplication by `x` fixes both cosets of `H`, so the transfer product has
one factor per coset, namely `ϕ` of the conjugate of `x` by a representative; the two
representatives can be taken to be `1` and `s` since `ϕ` is constant on `H`-conjugacy
classes (`A` is commutative). -/
theorem transfer_eq_mul_conj_of_index_two [H.FiniteIndex] (ϕ : ↥H →* A) (hidx : H.index = 2)
    {x : G} (hx : x ∈ H) (hconj : ∀ g : G, g⁻¹ * x * g ∈ H) {s : G} (hs : s ∉ H) :
    MonoidHom.transfer ϕ x = ϕ ⟨x, hx⟩ * ϕ ⟨s⁻¹ * x * s, hconj s⟩ := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  set S : H.LeftTransversal := default with hS_def
  set rep : G ⧸ H → G := fun q => (S.2.leftQuotientEquiv q : G) with hrep_def
  -- The chosen representative of `q` lies in `q`.
  have hrep_mk : ∀ q : G ⧸ H, ((rep q : G) : G ⧸ H) = q := fun q =>
    S.2.quotientGroupMk_leftQuotientEquiv q
  -- Left multiplication by `x⁻¹` fixes every coset of `H`.
  have hfix : ∀ q : G ⧸ H, x⁻¹ • q = q := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    have h1 : (x⁻¹ * g)⁻¹ * g = g⁻¹ * x * g := by group
    rw [h1]
    exact hconj g
  -- Hence each factor of the transfer product is a conjugate of `x`.
  have hfactor : ∀ q : G ⧸ H,
      (rep q)⁻¹ * ((x • S).2.leftQuotientEquiv q : G) = (rep q)⁻¹ * x * rep q := by
    intro q
    rw [hrep_def]
    rw [smul_apply_eq_smul_apply_inv_smul x S q, smul_eq_mul, hfix q, mul_assoc]
  rw [MonoidHom.transfer_def ϕ S]
  have hprod : Subgroup.leftTransversals.diff ϕ S (x • S)
      = ∏ q : G ⧸ H, ϕ ⟨(rep q)⁻¹ * x * rep q, hconj (rep q)⟩ := by
    unfold Subgroup.leftTransversals.diff
    simp only
    exact Finset.prod_congr rfl fun q _ => congrArg ϕ (Subtype.ext (hfactor q))
  rw [hprod]
  -- The quotient has exactly the two elements `1` and `s`.
  have hne : ((1 : G) : G ⧸ H) ≠ ((s : G) : G ⧸ H) := by
    rw [Ne, QuotientGroup.eq]
    simpa using hs
  have hcard : Fintype.card (G ⧸ H) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hidx]
  have huniv : (Finset.univ : Finset (G ⧸ H)) = {((1 : G) : G ⧸ H), ((s : G) : G ⧸ H)} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])).symm
  rw [huniv, Finset.prod_pair hne]
  -- The representative of the trivial coset lies in `H`.
  have h1 : rep ((1 : G) : G ⧸ H) ∈ H := by
    have := hrep_mk ((1 : G) : G ⧸ H)
    rw [QuotientGroup.eq] at this
    simpa using this
  -- The representative of the other coset lies in `s * H`.
  have h2 : s⁻¹ * rep ((s : G) : G ⧸ H) ∈ H := by
    have := hrep_mk ((s : G) : G ⧸ H)
    rw [QuotientGroup.eq] at this
    simpa [mul_inv_rev] using H.inv_mem this
  congr 1
  · exact map_eq_of_conj_eq ϕ _ hx h1 rfl
  · refine map_eq_of_conj_eq ϕ _ (hconj s) h2 ?_
    group

end Transfer

/-- An element of odd order lies in every subgroup containing its square. -/
theorem mem_of_sq_mem_of_odd_orderOf {K : Subgroup G} {x : G} (hodd : Odd (orderOf x))
    (h : x ^ 2 ∈ K) : x ∈ K := by
  obtain ⟨k, hk⟩ := hodd
  have hx : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    calc x = x ^ (orderOf x) * x := by rw [pow_orderOf_eq_one, one_mul]
      _ = x ^ (orderOf x + 1) := by rw [pow_succ]
      _ = x ^ (2 * (k + 1)) := by rw [hk]; ring_nf
  rw [hx]
  exact K.pow_mem h _

/-- **Inverting modulo the derived subgroup absorbs an odd subgroup.**

If `x · x^s ∈ ⁅G, G⁆` for every `x` in a subgroup `P` of odd order, then `P ≤ ⁅G, G⁆`:
the commutator `⁅x⁻¹, s⁆ = x⁻¹·x^s` always lies in `⁅G, G⁆`, so `x²` does, and odd
order lets one take square roots.

This is the group-theoretic heart of "a trivial transfer kills the odd part of the
abelianisation" in the index-two situation. -/
theorem le_commutator_of_conj_mul_mem {P : Subgroup G} {s : G}
    (hodd : ∀ x ∈ P, Odd (orderOf x))
    (hs : ∀ x ∈ P, x * (s * x * s⁻¹) ∈ commutator G) : P ≤ commutator G := by
  intro x hx
  have h1 : x⁻¹ * (s * x * s⁻¹) ∈ commutator G := by
    have hc : ⁅x⁻¹, s⁆ = x⁻¹ * (s * x * s⁻¹) := by
      rw [commutatorElement_def]; group
    rw [← hc, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h2 : x ^ 2 ∈ commutator G := by
    have heq : x ^ 2 = (x * (s * x * s⁻¹)) * (x⁻¹ * (s * x * s⁻¹))⁻¹ := by
      rw [pow_two]; group
    rw [heq]
    exact Subgroup.mul_mem _ (hs x hx) (Subgroup.inv_mem _ h1)
  exact mem_of_sq_mem_of_odd_orderOf (hodd x hx) h2

/-- If a subgroup of index `2` is contained in the derived subgroup, the abelianisation
has order dividing `2`; in particular no odd prime divides it. -/
theorem not_dvd_card_abelianization_of_le_commutator [Finite G] {P : Subgroup G}
    (hidx : P.index = 2) (hle : P ≤ commutator G) {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ p ∣ Nat.card (Abelianization G) := by
  intro hdvd
  -- `|Ab G| = (commutator G).index` divides `P.index = 2`
  have hcard : Nat.card (Abelianization G) = (commutator G).index :=
    (Subgroup.index_eq_card _).symm
  have hdvd2 : (commutator G).index ∣ 2 := by
    rw [← hidx]
    exact Subgroup.index_dvd_of_le hle
  rw [hcard] at hdvd
  have hple : p ∣ 2 := dvd_trans hdvd hdvd2
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hple
  rw [hp2] at hodd
  exact (Nat.not_odd_iff_even.mpr even_two) hodd

end OddOrder.GroupTheory
