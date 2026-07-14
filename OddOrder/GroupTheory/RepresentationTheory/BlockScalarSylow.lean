/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import OddOrder.GroupTheory.RepresentationTheory.SemilinearImprimitiveBound

/-!
# Sylow subgroups at the sharp two-block scalar bound

This file isolates the group-theoretic step in Peterfalvi (14.6).  If a finite group embeds in
two scalar coordinates, every coordinate has exponent dividing `n`, and the source has the sharp
order `n²`, then every Sylow subgroup for a prime divisor of `n` is noncyclic.

For the imprimitive branch (9.7.a), the scalar target is `(ZMod p)ˣ`, the source has odd order,
and `n = (p - 1) / 2`.  Oddness removes the factor `2` from the order of every scalar
coordinate.  Together with (13.13), this supplies the noncyclic Sylow subgroup to which BG
Proposition 1.16 is applied in (14.6).
-/

namespace OddOrder.RepresentationTheory

/-- A faithful two-coordinate representation of sharp square order cannot have a cyclic Sylow
subgroup at a prime dividing the coordinate exponent.

Indeed, injectivity makes every source element have `n`-th power one.  If a Sylow `r`-subgroup
`R` were cyclic, a generator would show `|R| ∣ n`.  Writing `n = |R| k` and
`|U| = n² = |R| [U:R]` would then force `r ∣ [U:R]`, contradicting the Sylow index theorem. -/
theorem sylow_not_isCyclic_of_card_eq_sq_of_injective_pi
    {U A : Type*} [Group U] [Finite U] [Group A] {n r : ℕ}
    (ψ : U →* (Fin 2 → A)) (hψ : Function.Injective ψ)
    (hcoord : ∀ (u : U) (i : Fin 2), (ψ u i) ^ n = 1)
    (hcard : Nat.card U = n ^ 2) (hr : r.Prime) (hrn : r ∣ n)
    (R : Sylow r U) :
    ¬ IsCyclic ↥(R : Subgroup U) := by
  letI : Fact r.Prime := ⟨hr⟩
  intro hRcyclic
  letI : IsCyclic ↥(R : Subgroup U) := hRcyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(R : Subgroup U))
  have hgpowU : ((g : U) ^ n) = 1 := by
    apply hψ
    rw [map_pow, map_one]
    ext i
    exact hcoord (g : U) i
  have hgpowR : g ^ n = 1 := Subtype.ext hgpowU
  have hRdvdn : Nat.card ↥(R : Subgroup U) ∣ n := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one hgpowR
  obtain ⟨k, hk⟩ := hRdvdn
  have hlagrange :
      Nat.card ↥(R : Subgroup U) * (R : Subgroup U).index = Nat.card U :=
    (R : Subgroup U).card_mul_index
  have hindex :
      (R : Subgroup U).index = Nat.card ↥(R : Subgroup U) * k ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left
      (show 0 < Nat.card ↥(R : Subgroup U) from Nat.card_pos)
    rw [hlagrange, hcard, hk]
    ring
  have hrU : r ∣ Nat.card U := by
    rw [hcard, pow_two]
    exact dvd_mul_of_dvd_left hrn n
  have hrR : r ∣ Nat.card ↥(R : Subgroup U) := by
    have hrprod :
        r ∣ Nat.card ↥(R : Subgroup U) * (R : Subgroup U).index := by
      rwa [hlagrange]
    exact (hr.dvd_mul.mp hrprod).resolve_right R.not_dvd_index
  apply R.not_dvd_index
  rw [hindex]
  exact dvd_mul_of_dvd_left hrR (k ^ 2)

/-- **Peterfalvi (14.6), sharp block-scalar Sylow bridge.**  Let the odd-order group `U`
embed faithfully in two copies of `(ZMod p)ˣ`, where `p` is odd prime, and suppose
`|U| = ((p - 1) / 2)²`.  Then every Sylow `r`-subgroup with
`r ∣ (p - 1) / 2` is noncyclic.

Each scalar coordinate has order dividing both `p - 1` and the odd number `|U|`; hence its
order divides `(p - 1) / 2`.  The preceding sharp-square lemma then applies. -/
theorem sylow_not_isCyclic_of_odd_blockScalarEmbedding
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Type*} [Group U] [Finite U]
    (hUodd : Odd (Nat.card U))
    (ψ : U →* (Fin 2 → (ZMod p)ˣ)) (hψ : Function.Injective ψ)
    (hcard : Nat.card U = ((p - 1) / 2) ^ 2)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (p - 1) / 2)
    (R : Sylow r U) :
    ¬ IsCyclic ↥(R : Subgroup U) := by
  letI : Fact p.Prime := ⟨hp⟩
  have heven : 2 ∣ p - 1 := even_iff_two_dvd.mp (hp.even_sub_one hp2)
  have hsplit : p - 1 = 2 * ((p - 1) / 2) :=
    (Nat.mul_div_cancel' heven).symm
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
  apply sylow_not_isCyclic_of_card_eq_sq_of_injective_pi ψ hψ
    (n := (p - 1) / 2) (r := r) ?_ hcard hr hrhalf R
  intro u i
  let χ : U →* (ZMod p)ˣ :=
    (Pi.evalMonoidHom (fun _ : Fin 2 => (ZMod p)ˣ) i).comp ψ
  have hordU : orderOf (χ u) ∣ orderOf u := orderOf_map_dvd χ u
  have hordCard : orderOf (χ u) ∣ Nat.card U :=
    hordU.trans (orderOf_dvd_natCard u)
  have hordOdd : Odd (orderOf (χ u)) := hUodd.of_dvd_nat hordCard
  have hordPred : orderOf (χ u) ∣ p - 1 := by
    rw [← hunits]
    exact orderOf_dvd_natCard (χ u)
  rw [hsplit] at hordPred
  have hordHalf : orderOf (χ u) ∣ (p - 1) / 2 :=
    (Nat.coprime_two_right.mpr hordOdd).dvd_of_dvd_mul_left hordPred
  simpa only [χ, MonoidHom.comp_apply, Pi.evalMonoidHom_apply] using
    (orderOf_dvd_iff_pow_eq_one.mp hordHalf)

end OddOrder.RepresentationTheory
