/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import OddOrder.GroupTheory.KleinFourAutomorphism
import OddOrder.GroupTheory.PRegularElement
import OddOrder.GroupTheory.SylowContaining
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# A single class of involutions for a Klein four Sylow `2`-subgroup

Navarro (7.2), first part: if the Sylow `2`-subgroup `P` of `G` is a Klein four group and
`N_G(P) ≠ C_G(P)`, then `G` has a single class of involutions.

Every involution of `G` is conjugate into `P` (Sylow), and an element of `N_G(P)` of odd order not
centralising `P` conjugates the three involutions of `P` cyclically
(`eq_or_eq_or_eq_iterate_of_odd_of_klein`).

The witness may be taken of odd order: the `2`-part of any `g ∈ N_G(P)` lies in `P`, because `P`
is the unique Sylow `2`-subgroup of `N_G(P)` (`mem_of_isPElement_of_mem_normalizer`), and `P` is
abelian — so it is the `2'`-part of `g` that moves the involutions.  This replaces the usual
appeal to "`|N_G(P) : C_G(P)|` is odd".

## Main results

* `OddOrder.GroupTheory.exists_conj_mem_sylow_of_mul_self_eq_one` — an involution is conjugate
  into any Sylow `2`-subgroup
* `OddOrder.GroupTheory.isConj_of_klein_sylow` — all involutions of `G` are conjugate
* `OddOrder.GroupTheory.mem_of_isPElement_of_mem_normalizer` — a `p`-element normalising a Sylow
  `p`-subgroup lies in it
* `OddOrder.GroupTheory.exists_odd_not_centralizes` — the witness may be taken of odd order
* `OddOrder.GroupTheory.isConj_of_klein_sylow_of_not_centralizes` — Navarro (7.2), first part
* `OddOrder.GroupTheory.hasNormalPComplement_of_klein_sylow_of_mem_center` — the converse reading
  used on p. 132: a *central* involution forces `N_G(P) = C_G(P)`, hence a normal `2`-complement
-/

namespace OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- **An involution is conjugate into any Sylow `2`-subgroup** — the `p = 2`, order-`2` case of
`exists_conj_mem_sylow`. -/
theorem exists_conj_mem_sylow_of_mul_self_eq_one (P : Sylow 2 G) {u : G} (hu : u ≠ 1)
    (hu2 : u * u = 1) : ∃ c : G, c * u * c⁻¹ ∈ (P : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp
        (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2))).resolve_left
      fun h => hu (orderOf_eq_one_iff.mp h)
  exact exists_conj_mem_sylow
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])) P

/-- **All involutions of `G` are conjugate** when the Sylow `2`-subgroup `P` is a Klein four group
and some odd-order `g ∈ N_G(P)` does not centralise `P`. -/
theorem isConj_of_klein_sylow (P : Sylow 2 G) (hcard : Nat.card ↥(P : Subgroup G) = 4)
    (hexp : ∀ x : ↥(P : Subgroup G), x * x = 1)
    {g : G} (hgN : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G)) (hgodd : Odd (orderOf g))
    (hgnc : ∃ x ∈ (P : Subgroup G), g * x * g⁻¹ ≠ x)
    {u v : G} (hu : u ≠ 1) (hu2 : u * u = 1) (hv : v ≠ 1) (hv2 : v * v = 1) :
    IsConj u v := by
  have hconj : ∀ x ∈ (P : Subgroup G), g * x * g⁻¹ ∈ (P : Subgroup G) := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
  -- conjugation by `g`, as an endomorphism of `P`
  let f : ↥(P : Subgroup G) →* ↥(P : Subgroup G) :=
    { toFun := fun x => ⟨g * (x : G) * g⁻¹, hconj (x : G) x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; push_cast; group }
  have hfval : ∀ x : ↥(P : Subgroup G), ((f x : ↥(P : Subgroup G)) : G) = g * (x : G) * g⁻¹ :=
    fun _ => rfl
  have hiter : ∀ (n : ℕ) (x : ↥(P : Subgroup G)),
      (((⇑f)^[n] x : ↥(P : Subgroup G)) : G) = g ^ n * (x : G) * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply, ih (f x), hfval x, pow_succ]
        group
  have hfm : ∀ x : ↥(P : Subgroup G), (⇑f)^[orderOf g] x = x := fun x => by
    refine Subtype.ext ?_
    rw [hiter, pow_orderOf_eq_one]
    group
  have hfne : ∃ x : ↥(P : Subgroup G), f x ≠ x := by
    obtain ⟨x, hxP, hxne⟩ := hgnc
    exact ⟨⟨x, hxP⟩, fun h => hxne (congrArg Subtype.val h)⟩
  -- the involutions of `P` are pairwise conjugate in `G`
  have key : ∀ a b : ↥(P : Subgroup G), a ≠ 1 → b ≠ 1 → IsConj (a : G) (b : G) := by
    intro a b ha hb
    rcases eq_or_eq_or_eq_iterate_of_odd_of_klein hcard hexp f hgodd hfm hfne ha hb with
      h | h | h
    · exact h ▸ IsConj.refl _
    · exact isConj_iff.mpr ⟨g, by rw [h, hfval]⟩
    · exact isConj_iff.mpr ⟨g * g, by
        rw [h, hfval, hfval]
        group⟩
  -- move both involutions into `P`
  obtain ⟨c, hcP⟩ := exists_conj_mem_sylow_of_mul_self_eq_one P hu hu2
  obtain ⟨d, hdP⟩ := exists_conj_mem_sylow_of_mul_self_eq_one P hv hv2
  have hcu : (⟨c * u * c⁻¹, hcP⟩ : ↥(P : Subgroup G)) ≠ 1 := fun h => hu (by
    have h' : c * u * c⁻¹ = 1 := congrArg Subtype.val h
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = 1 := by rw [h']; group)
  have hdv : (⟨d * v * d⁻¹, hdP⟩ : ↥(P : Subgroup G)) ≠ 1 := fun h => hv (by
    have h' : d * v * d⁻¹ = 1 := congrArg Subtype.val h
    calc v = d⁻¹ * (d * v * d⁻¹) * d := by group
      _ = 1 := by rw [h']; group)
  have hcc : IsConj u (c * u * c⁻¹) := isConj_iff.mpr ⟨c, rfl⟩
  have hdd : IsConj v (d * v * d⁻¹) := isConj_iff.mpr ⟨d, rfl⟩
  exact hcc.trans ((key _ _ hcu hdv).trans hdd.symm)

/-! ### From `N_G(P) ≠ C_G(P)` to an odd-order witness -/

variable {p : ℕ}

omit [Finite G] in
/-- **A `p`-element normalising a Sylow `p`-subgroup lies in it.**  `IsPGroup.inf_normalizer_sylow`
says a `p`-subgroup meets the normalizer of a Sylow `p`-subgroup inside that subgroup. -/
theorem mem_of_isPElement_of_mem_normalizer [Fact p.Prime] (Q : Sylow p G) {x : G}
    (hx : IsPElement p x) (hxN : x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) :
    x ∈ (Q : Subgroup G) := by
  obtain ⟨k, hk⟩ := hx
  have hzp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hinf := hzp.inf_normalizer_sylow Q
  have hmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer (Q : Set G) := by
    refine ⟨Subgroup.mem_zpowers x, ?_⟩
    rw [← Sylow.coe_coe]
    exact hxN
  rw [hinf] at hmem
  exact hmem.2

/-- **An element of `N_G(P)` not centralising a Klein four Sylow `2`-subgroup can be taken of odd
order.**  Its `2`-part lies in `P` (`mem_of_isPElement_of_mem_normalizer`) and so centralises the
abelian `P`, hence the `2'`-part is the one doing the moving. -/
theorem exists_odd_not_centralizes (P : Sylow 2 G) (hexp : ∀ x : ↥(P : Subgroup G), x * x = 1)
    {g : G} (hgN : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hgnc : ∃ x ∈ (P : Subgroup G), g * x * g⁻¹ ≠ x) :
    ∃ h ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), Odd (orderOf h) ∧
      ∃ x ∈ (P : Subgroup G), h * x * h⁻¹ ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  set g₂ : G := pPart 2 g with hg₂
  set g' : G := pRegularPart 2 g with hg'
  have hg₂N : g₂ ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [hg₂, pPart]; exact Subgroup.zpow_mem _ hgN _
  have hg'N : g' ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [hg', pRegularPart]; exact Subgroup.zpow_mem _ hgN _
  have hg₂P : g₂ ∈ (P : Subgroup G) :=
    mem_of_isPElement_of_mem_normalizer P (isPElement_pPart Nat.prime_two g) hg₂N
  -- `P` has exponent `2`, hence is abelian, so its elements centralise it
  have hcent : ∀ x ∈ (P : Subgroup G), g₂ * x * g₂⁻¹ = x := by
    intro x hx
    have hcomm : (⟨g₂, hg₂P⟩ : ↥(P : Subgroup G)) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨g₂, hg₂P⟩ := by
      have h1 := hexp (⟨g₂, hg₂P⟩ * ⟨x, hx⟩)
      have h2 := hexp (⟨g₂, hg₂P⟩ : ↥(P : Subgroup G))
      have h3 := hexp (⟨x, hx⟩ : ↥(P : Subgroup G))
      calc (⟨g₂, hg₂P⟩ : ↥(P : Subgroup G)) * ⟨x, hx⟩
          = (⟨g₂, hg₂P⟩ * ⟨x, hx⟩)⁻¹ := (inv_eq_of_mul_eq_one_left h1).symm
        _ = (⟨x, hx⟩ : ↥(P : Subgroup G))⁻¹ * (⟨g₂, hg₂P⟩ : ↥(P : Subgroup G))⁻¹ := mul_inv_rev _ _
        _ = (⟨x, hx⟩ : ↥(P : Subgroup G)) * ⟨g₂, hg₂P⟩ := by
              rw [inv_eq_of_mul_eq_one_left h3, inv_eq_of_mul_eq_one_left h2]
    have : g₂ * x = x * g₂ := congrArg Subtype.val hcomm
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨g', hg'N, ?_, ?_⟩
  · have hreg : IsPRegular 2 g' := isPRegular_pRegularPart Nat.prime_two hfin
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hreg)
  · obtain ⟨x, hxP, hxne⟩ := hgnc
    refine ⟨x, hxP, fun h => hxne ?_⟩
    have hfac : g = g₂ * g' := (pPart_mul_pRegularPart Nat.prime_two hfin).symm
    have hgx : g * x * g⁻¹ = g₂ * (g' * x * g'⁻¹) * g₂⁻¹ := by
      rw [hfac]; group
    rw [hgx, h, hcent x hxP]

/-- **Navarro (7.2), first part.**  If the Sylow `2`-subgroup `P` is a Klein four group and
`N_G(P)` does not centralise `P`, then `G` has a single class of involutions. -/
theorem isConj_of_klein_sylow_of_not_centralizes (P : Sylow 2 G)
    (hcard : Nat.card ↥(P : Subgroup G) = 4) (hexp : ∀ x : ↥(P : Subgroup G), x * x = 1)
    {g : G} (hgN : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hgnc : ∃ x ∈ (P : Subgroup G), g * x * g⁻¹ ≠ x)
    {u v : G} (hu : u ≠ 1) (hu2 : u * u = 1) (hv : v ≠ 1) (hv2 : v * v = 1) :
    IsConj u v := by
  obtain ⟨h, hhN, hhodd, hhnc⟩ := exists_odd_not_centralizes P hexp hgN hgnc
  exact isConj_of_klein_sylow P hcard hexp hhN hhodd hhnc hu hu2 hv hv2

/-! ### A central involution forces a normal `2`-complement

Navarro's proof of (7.2), p. 132: for `C = C_G(t)` with `t` central in `C` and Klein four Sylow
`P ≤ C`, the group `C` *cannot* have a unique class of involutions — the class of `t` is `{t}`,
while `P` has three involutions.  So `N_C(P) = C_C(P)` by the first part of (7.2), and Burnside's
transfer theorem gives `C` a normal `2`-complement.  This is what makes the Cartan matrix of the
principal block of `C` equal to `(4)`. -/

/-- **A Klein four Sylow `2`-subgroup with a central involution forces a normal `2`-complement.**
If some element of `N_G(P)` moved `P`, all involutions would be conjugate
(`isConj_of_klein_sylow_of_not_centralizes`) — impossible when one of the three involutions of `P`
is central.  So `N_G(P) ≤ C_G(P)` and Burnside applies. -/
theorem hasNormalPComplement_of_klein_sylow_of_mem_center (P : Sylow 2 G)
    (hcard : Nat.card ↥(P : Subgroup G) = 4) (hexp : ∀ x : ↥(P : Subgroup G), x * x = 1)
    {t : G} (htP : t ∈ (P : Subgroup G)) (ht1 : t ≠ 1) (htZ : t ∈ Subgroup.center G) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement 2 G := by
  classical
  let : Fintype ↥(P : Subgroup G) := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `P` has an involution other than the central `t`
  obtain ⟨u, huP, hu1, hut⟩ : ∃ u ∈ (P : Subgroup G), u ≠ 1 ∧ u ≠ t := by
    have hex : ∃ y : ↥(P : Subgroup G), y ∉ ({1, ⟨t, htP⟩} : Finset ↥(P : Subgroup G)) := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset ↥(P : Subgroup G)) ⊆ {1, ⟨t, htP⟩} := fun y _ => hcon y
      have hcnt := Finset.card_le_card hsub
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at hcnt
      have hle : ({1, ⟨t, htP⟩} : Finset ↥(P : Subgroup G)).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      omega
    obtain ⟨y, hy⟩ := hex
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    push Not at hy
    exact ⟨(y : G), y.2, fun h => hy.1 (Subtype.ext h), fun h => hy.2 (Subtype.ext h)⟩
  have ht2 : t * t = 1 := congrArg Subtype.val (hexp ⟨t, htP⟩)
  have hu2 : u * u = 1 := congrArg Subtype.val (hexp ⟨u, huP⟩)
  refine OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer P ?_
  intro g hgN
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  by_contra hne
  -- otherwise all involutions of `G` are conjugate, and `u` would equal the central `t`
  have hmove : ∃ x ∈ (P : Subgroup G), g * x * g⁻¹ ≠ x :=
    ⟨x, hx, fun h => hne (by
      calc x * g = (g * x * g⁻¹) * g := by rw [h]
        _ = g * x := by group)⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (isConj_of_klein_sylow_of_not_centralizes P hcard hexp hgN hmove hu1 hu2 ht1 ht2)
  have hcomm : c * t = t * c := Subgroup.mem_center_iff.mp htZ c
  refine hut ?_
  calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
    _ = c⁻¹ * t * c := by rw [hc]
    _ = c⁻¹ * (t * c) := by group
    _ = c⁻¹ * (c * t) := by rw [← hcomm]
    _ = t := by group

end OddOrder.GroupTheory
