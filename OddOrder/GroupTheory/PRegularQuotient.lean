/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.PRegularElement

/-!
# `p`-regular elements under a quotient by a normal `p`-subgroup

Navarro (7.6) opens with the claim that if `P ⊴ G` is a `p`-subgroup such that `G/C_G(P)` is a
`p`-group, then

`x ↦ xP` is a bijection from `G⁰` onto `(G/P)⁰`

(`G⁰` denotes the set of `p`-regular elements).  The two halves are independent:

* **surjectivity** holds for any normal subgroup — given `ȳ` `p`-regular, the `p`-part of any
  preimage `g` maps to a `p`-element that is also a power of `ȳ`, hence trivial, so `ȳ` is the
  image of the `p`-regular part of `g`;
* **injectivity** is where the hypothesis enters: it makes every `p`-regular element centralise
  `P` (`mem_of_isPRegular_of_isPGroup_quotient` applied to `C_G(P)`), and two commuting
  `p`-regular elements differ by a `p`-regular element of `P`, which is trivial.

The application in the Brauer–Suzuki argument has `P = ⟨t⟩` central in `C_G(t)`, where the
hypothesis is vacuous; `commute_of_isPRegular_of_le_center` is that case.

## Main results

* `OddOrder.GroupTheory.mem_of_isPRegular_of_isPGroup_quotient`
* `OddOrder.GroupTheory.exists_isPRegular_mk_eq` — surjectivity
* `OddOrder.GroupTheory.eq_of_isPRegular_of_mk_eq` — injectivity
* `OddOrder.GroupTheory.bijOn_mk_isPRegular` — the two packaged as a bijection
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] {p : ℕ}

/-! ### `p`-elements and `p`-regular elements under a homomorphism -/

section Hom

variable {H : Type*} [Group H]

/-- The image of a `p`-element is a `p`-element. -/
theorem IsPElement.map (hp : p.Prime) {g : G} (hg : IsPElement p g) (f : G →* H) :
    IsPElement p (f g) := by
  obtain ⟨k, hk⟩ := hg
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hk ▸ orderOf_map_dvd f g)
  exact ⟨j, hj⟩

/-- The image of a `p`-regular element is `p`-regular. -/
theorem IsPRegular.map {g : G} (hg : IsPRegular p g) (f : G →* H) : IsPRegular p (f g) :=
  fun hdvd => hg (hdvd.trans (orderOf_map_dvd f g))

/-- Every integer power of a `p`-regular element is `p`-regular. -/
theorem IsPRegular.zpow {g : G} (hg : IsPRegular p g) (m : ℤ) : IsPRegular p (g ^ m) := by
  have h : (g ^ m) ^ orderOf g = 1 := by
    rw [← zpow_natCast (g ^ m) (orderOf g), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, one_zpow]
  exact fun hdvd => hg (hdvd.trans (orderOf_dvd_of_pow_eq_one h))

end Hom

/-! ### The correspondence -/

section Quotient

variable {N : Subgroup G} [N.Normal]

/-- **A `p`-regular element lies in every normal subgroup with `p`-group quotient.**  Its image
has order dividing both a power of `p` and its own order, which is prime to `p`.

Applied to `N = C_G(P)` this is how Navarro's hypothesis "`G/C_G(P)` is a `p`-group" is used:
every `p`-regular element of `G` centralises `P`. -/
theorem mem_of_isPRegular_of_isPGroup_quotient (hp : p.Prime) (hN : IsPGroup p (G ⧸ N)) {x : G}
    (hx : IsPRegular p x) : x ∈ N := by
  obtain ⟨k, hk⟩ := hN (QuotientGroup.mk x)
  have hcop : Nat.Coprime (p ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k ((isPRegular_iff_coprime hp).mp hx)
  have h1 : orderOf (QuotientGroup.mk x : G ⧸ N) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk)
      (orderOf_map_dvd (QuotientGroup.mk' N) x))
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h1)

/-- **Every `p`-regular element of `G/P` comes from a `p`-regular element of `G`.**  This half
needs nothing of `N`: the `p`-part of a preimage maps to something that is both a `p`-element and
a power of the `p`-regular `ȳ`, hence trivial. -/
theorem exists_isPRegular_mk_eq [Finite G] (hp : p.Prime) {y : G ⧸ N} (hy : IsPRegular p y) :
    ∃ x : G, IsPRegular p x ∧ (QuotientGroup.mk x : G ⧸ N) = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  refine ⟨pRegularPart p g, isPRegular_pRegularPart hp hfin, ?_⟩
  have hone : (QuotientGroup.mk' N) (pPart p g) = 1 := by
    refine eq_one_of_isPElement_of_isPRegular ((isPElement_pPart hp g).map hp _) ?_
    rw [pPart, map_zpow]
    exact hy.zpow _
  calc (QuotientGroup.mk (pRegularPart p g) : G ⧸ N)
      = (QuotientGroup.mk' N) (pRegularPart p g) * (QuotientGroup.mk' N) (pPart p g) := by
        rw [hone, mul_one]; rfl
    _ = (QuotientGroup.mk' N) (pRegularPart p g * pPart p g) := (map_mul _ _ _).symm
    _ = QuotientGroup.mk g := by rw [pRegularPart_mul_pPart hp hfin]; rfl

omit [N.Normal] in
/-- **Two `p`-regular elements with the same image agree**, provided `N` is a `p`-group centralised
by the `p`-regular elements.  Their quotient is a `p`-element of `N` and — the two being commuting
`p`-regular elements — is itself `p`-regular, hence trivial. -/
theorem eq_of_isPRegular_of_mk_eq (hp : p.Prime) (hNp : IsPGroup p ↥N)
    (hcent : ∀ x : G, IsPRegular p x → ∀ z ∈ N, Commute x z) {x y : G} (hx : IsPRegular p x)
    (hy : IsPRegular p y) (h : (QuotientGroup.mk x : G ⧸ N) = QuotientGroup.mk y) : x = y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzN : x⁻¹ * y ∈ N := QuotientGroup.eq.mp h
  have hcomm : Commute x (x⁻¹ * y) := hcent x hx _ hzN
  have hxy : Commute x⁻¹ y := by
    refine Commute.inv_left ?_
    have hxz : x * (x⁻¹ * y) = y := mul_inv_cancel_left x y
    exact hxz ▸ (Commute.refl x).mul_right hcomm
  have hzreg : IsPRegular p (x⁻¹ * y) := by
    rw [isPRegular_iff_coprime hp]
    exact Nat.Coprime.coprime_dvd_right
      (hxy.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))
      (Nat.Coprime.mul_right ((isPRegular_iff_coprime hp).mp hx.inv)
        ((isPRegular_iff_coprime hp).mp hy))
  exact inv_mul_eq_one.mp
    (eq_one_of_isPElement_of_isPRegular (isPElement_of_mem_of_isPGroup hNp hzN) hzreg)

/-- **Navarro (7.6), the `p`-regular correspondence.**  `x ↦ xP` is a bijection from the
`p`-regular elements of `G` onto those of `G/P`. -/
theorem bijOn_mk_isPRegular [Finite G] (hp : p.Prime) (hNp : IsPGroup p ↥N)
    (hcent : ∀ x : G, IsPRegular p x → ∀ z ∈ N, Commute x z) :
    Set.BijOn (fun x : G => (QuotientGroup.mk x : G ⧸ N)) {x : G | IsPRegular p x}
      {y : G ⧸ N | IsPRegular p y} :=
  ⟨fun x hx => hx.map (QuotientGroup.mk' N),
    fun _ hx _ hy h => eq_of_isPRegular_of_mk_eq hp hNp hcent hx hy h,
    fun y hy => by
      obtain ⟨x, hx, hxy⟩ := exists_isPRegular_mk_eq hp hy
      exact ⟨x, hx, hxy⟩⟩

/-- **The `p'`-part of the group order is unchanged by a quotient by a `p`-subgroup.**  This is
what makes the Brauer characters of `G` and of `G/N` be taken at the *same* root of unity, so that
the correspondence `φ ↦ φ̄` is literally an equality of values. -/
theorem pRegularExponent_quotient [Finite G] [Fact p.Prime] (hN : IsPGroup p ↥N) :
    pRegularExponent p (G ⧸ N) = pRegularExponent p G := by
  obtain ⟨a, ha⟩ := hN.exists_card_eq
  have hcard : Nat.card G = Nat.card (G ⧸ N) * Nat.card ↥N :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup N)
  rw [pRegularExponent, pRegularExponent, hcard, ha, Nat.ordCompl_mul,
    Nat.Prime.factorization_pow (Fact.out : p.Prime), Finsupp.single_eq_same,
    Nat.div_self (pow_pos (Fact.out : p.Prime).pos a), mul_one]

omit [N.Normal] in
/-- The hypothesis of (7.6) in the shape the Brauer–Suzuki argument supplies it: a central
`p`-subgroup is centralised by everything. -/
theorem commute_of_isPRegular_of_le_center (hN : N ≤ Subgroup.center G) (x : G) :
    IsPRegular p x → ∀ z ∈ N, Commute x z :=
  fun _ _ hz => Subgroup.mem_center_iff.mp (hN hz) x

end Quotient

end OddOrder.GroupTheory
