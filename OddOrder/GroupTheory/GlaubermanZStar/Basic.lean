/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.IsolatedInvolution
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# Glauberman's `Z*`-theorem: the statement and how its hypothesis travels

Navarro writes `Z*(G)` for the preimage of `Z(G/O_{2'}(G))`, so the conclusion of the
`Z*`-theorem, `u ∈ Z*(G)`, says that the image of `u` in `G/O_{2'}(G)` is central — the same
shape as the conclusion of Brauer–Suzuki (`brauerSuzuki_mk_mem_center`).  Concretely it says

`⁅u, g⁆ ∈ O_{2'}(G)` for every `g ∈ G`   (`mk_mem_center_iff_forall_commutator_mem`),

which is the form the induction of Navarro (7.9) actually manipulates.

The hypothesis — `u` is the only `G`-conjugate of itself inside a Sylow `2`-subgroup — travels
both to subgroups and to quotients, but only through its second form (`⁅u, g⁆` of odd order,
Navarro (7.8)): odd order is inherited by subgroups trivially and by quotients because the order
of an image divides the order of the element.  That is exactly why (7.8) is proved first.

## Main results

* `OddOrder.GroupTheory.mk_mem_center_iff_forall_commutator_mem`
* `OddOrder.GroupTheory.odd_orderOf_commutator_subgroup` — the hypothesis inside `H ≤ G`
* `OddOrder.GroupTheory.odd_orderOf_commutator_quotient` — the hypothesis inside `G ⧸ N`
-/

open OddOrder.Isaacs.Ch03

open scoped Pointwise commutatorElement

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **`u` is central mod `K` exactly when every commutator `⁅u, g⁆` lies in `K`.**  This is the
working form of `u ∈ Z*(G)` (take `K = O_{2'}(G)`). -/
theorem mk_mem_center_iff_forall_commutator_mem {K : Subgroup G} [K.Normal] {u : G} :
    QuotientGroup.mk' K u ∈ Subgroup.center (G ⧸ K) ↔ ∀ g : G, ⁅u, g⁆ ∈ K := by
  have hmap : ∀ g : G, ⁅(u : G ⧸ K), (g : G ⧸ K)⁆ = ((⁅u, g⁆ : G) : G ⧸ K) := by
    intro g
    rw [commutatorElement_def, commutatorElement_def]
    rfl
  simp only [QuotientGroup.mk'_apply, Subgroup.mem_center_iff]
  constructor
  · intro h g
    rw [← QuotientGroup.eq_one_iff, ← hmap, commutatorElement_eq_one_iff_commute]
    exact (h _).symm
  · intro h gg
    induction gg using QuotientGroup.induction_on with
    | H g =>
      have h1 : ⁅(u : G ⧸ K), (g : G ⧸ K)⁆ = 1 := by
        rw [hmap]; exact (QuotientGroup.eq_one_iff _).mpr (h g)
      exact (commutatorElement_eq_one_iff_commute.mp h1).symm

section Transport

variable {u : G}

/-- **The hypothesis restricts to a subgroup.**  Odd order of `⁅u, h⁆` for `h ∈ H` is a special
case of odd order for `h ∈ G`; the order is the same computed in `H` or in `G`. -/
theorem odd_orderOf_commutator_subgroup {H : Subgroup G} (hu : u ∈ H)
    (hodd : ∀ g : G, Odd (orderOf ⁅u, g⁆)) (h : ↥H) :
    Odd (orderOf ⁅(⟨u, hu⟩ : ↥H), h⁆) := by
  have hcoe : ((⁅(⟨u, hu⟩ : ↥H), h⁆ : ↥H) : G) = ⁅u, (h : G)⁆ := rfl
  rw [← Subgroup.orderOf_coe, hcoe]
  exact hodd _

/-- **The hypothesis passes to a quotient.**  The order of `⁅u, g⁆ N` divides the order of
`⁅u, g⁆`, so it stays odd. -/
theorem odd_orderOf_commutator_quotient {N : Subgroup G} [N.Normal]
    (hodd : ∀ g : G, Odd (orderOf ⁅u, g⁆)) (gg : G ⧸ N) :
    Odd (orderOf ⁅QuotientGroup.mk' N u, gg⁆) := by
  simp only [QuotientGroup.mk'_apply]
  induction gg using QuotientGroup.induction_on with
  | H g =>
    have hmap : ⁅(u : G ⧸ N), (g : G ⧸ N)⁆ = ((⁅u, g⁆ : G) : G ⧸ N) := by
      rw [commutatorElement_def, commutatorElement_def]
      rfl
    rw [hmap]
    have hdvd : orderOf ((⁅u, g⁆ : G) : G ⧸ N) ∣ orderOf ⁅u, g⁆ :=
      orderOf_dvd_of_pow_eq_one (by
        rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one])
    have hg := hodd g
    rw [Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd] at hg ⊢
    exact fun h2 => hg (h2.trans hdvd)

end Transport

end OddOrder.GroupTheory
