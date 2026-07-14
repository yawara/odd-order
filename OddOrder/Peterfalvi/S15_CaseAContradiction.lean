import OddOrder.Peterfalvi.S15_CaseAOmegaFixedPointFree

/-!
# Peterfalvi (14.6) — the final contradiction in case A

In case (9.7.a), choose a prime `r ∣ (p - 1) / 2`.  The Sylow-center argument and
the fixed-point-free action of `W₂^y` give `p ∣ r² - 1`.  Since both primes are
odd, the prime comparison from (12.10) gives `p < r`; but divisibility by
`(p - 1) / 2` gives `r < p`.  This contradiction eliminates case A.

The structural parameters `c = 1`, `q = 3`, and `u = (p - 1)² / 4` are explicit
inputs here.  This keeps the theorem independent of the analytic producer while
that producer is being relayered under issue 0116.

Peterfalvi, *Character Theory for the Odd Order Theorem*, (14.6).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-! ## The final prime comparison -/

/-- **Peterfalvi (14.6), final arithmetic contradiction.**  If odd primes `p` and
`r` satisfy both `r ∣ (p - 1) / 2` and `p ∣ r² - 1`, then the latter gives
`p < r`, whereas the former gives `r ≤ (p - 1) / 2 < p`. -/
theorem false_of_odd_primes_dvd_half_and_sq_sub_one
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hp_odd : Odd p) (hr_odd : Odd r) (hp_three : 3 ≤ p)
    (hr_dvd : r ∣ (p - 1) / 2) (hp_dvd : p ∣ r ^ 2 - 1) : False := by
  have hpr : p < r :=
    OddOrder.Peterfalvi.S14.prime_lt_of_odd_dvd_sq_sub_one
      hr hp hr_odd hp_odd hp_dvd
  have hhalf_pos : 0 < (p - 1) / 2 := by omega
  have hr_le : r ≤ (p - 1) / 2 := Nat.le_of_dvd hhalf_pos hr_dvd
  have hhalf_le : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  omega

/-! ## Assembly of case A -/

/-- **Peterfalvi (14.6), case (9.7.a) is impossible at the sharp parameters.**
Assume the explicit conclusions `c = 1`, `q = 3`, and
`u = (p - 1)² / 4` of (13.12)/(13.13), together with the type-I maximal subgroup
over `N_G(U)` constructed in (13.17)/(14.5).  A prime divisor
`r ∣ (p - 1) / 2` has a noncyclic Sylow subgroup `R₀` in `U`.  Extending it to
the Fitting kernel of the type-I subgroup traps the ambient Sylow center in
`R₀`; hence `|Ω₁(Z(R))|` is `r` or `r²`.  The conjugate `W₂^y` acts
fixed-point-freely on this layer and gives `p ∣ r² - 1`, contradicting the
preceding arithmetic theorem.

The three parameter equalities are deliberately explicit: no hidden analytic
producer is used by this theorem. -/
theorem caseA_false_of_parameters_and_typeIOverNormalizerData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData
      (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1) (hq : hyp.q = 3)
    (hu : hyp.u = (hyp.p - 1) ^ 2 / 4)
    (data : TypeIOverNormalizerData hyp) : False := by
  classical
  have hp_ne_three : hyp.p ≠ 3 := by
    intro hp_three
    exact hyp.p_ne_q (hp_three.trans hq.symm)
  have hp_three : 3 ≤ hyp.p := hyp.three_le_p
  obtain ⟨k, hk⟩ := hyp.p_odd
  have hp_five : 5 ≤ hyp.p := by
    clear hu
    omega
  have hhalf_ne_one : (hyp.p - 1) / 2 ≠ 1 := by
    clear hu
    omega
  obtain ⟨r, hr, hrhalf⟩ := Nat.exists_prime_and_dvd hhalf_ne_one
  letI : Fact r.Prime := ⟨hr⟩
  let R₀ : Sylow r ↥hyp.U := default
  have hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U) :=
    caseA_sylow_U_not_isCyclic_of_parameters
      hG hyp caseA hq hu hr hrhalf R₀
  obtain ⟨R, hR₀R, _x, _hxR₀, _hx1, _hxP, hcenter⟩ :=
    exists_sylow_over_U_with_trapped_center_of_not_isCyclic
      hG hyp hr hrhalf R₀ hR₀nc data.H data.U_le_H
  have hcard :=
    caseA_omega1Center_card_eq_prime_or_sq_of_parameters
      hG hyp caseA hc hq hr R₀ hR₀nc data.H data.U_le_H R hR₀R hcenter
  have hp_dvd : hyp.p ∣ r ^ 2 - 1 :=
    data.prime_dvd_sq_sub_one_of_omega1Center hr R hcard
  have hR₀card : r ∣ Nat.card ↥(R₀ : Subgroup ↥hyp.U) :=
    R₀.isPGroup'.card_eq_or_dvd.resolve_left fun hcard_one => hR₀nc <| by
      letI : Subsingleton ↥(R₀ : Subgroup ↥hyp.U) :=
        (Nat.card_eq_one_iff_unique.mp hcard_one).1
      exact isCyclic_of_subsingleton
  have hrU : r ∣ Nat.card ↥hyp.U :=
    hR₀card.trans (Subgroup.card_subgroup_dvd_card (R₀ : Subgroup ↥hyp.U))
  have hrG : r ∣ Nat.card G :=
    hrU.trans (Subgroup.card_subgroup_dvd_card hyp.U)
  have hr_odd : Odd r := hG.odd.of_dvd_nat hrG
  exact false_of_odd_primes_dvd_half_and_sq_sub_one
    hyp.p_prime hr hyp.p_odd hr_odd hyp.three_le_p hrhalf hp_dvd

end OddOrder.Peterfalvi.S15
