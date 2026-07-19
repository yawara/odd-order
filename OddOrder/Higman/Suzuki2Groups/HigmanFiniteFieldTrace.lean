/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.ChevalleyWarning
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Higman Lemma 10: finite-field trace

This file formalizes the finite-field calculation in G. Higman,
*Suzuki 2-groups*, Lemma 10, pp. 87--88. If `L / K` is a proper extension
of finite fields of characteristic two and odd degree, then for every
integer Frobenius power and every `ε : L` there is a nonzero `α : L` for
which

`Tr[L/K] (α * Frob₂^r(α) * ε) = 0`.

The first result below isolates Higman's easy case: when the relevant power
map on `Lˣ` is invertible, pull a nonzero element of the trace kernel back
through that power map.

For the full statement we use the coordinate-free Chevalley--Warning
consequence in `OddOrder.Algebra`: the trace expression is a quadratic map
from the underlying `𝔽₂`-space of `L` to that of `K`, and odd proper degree
forces the required dimension inequality. This proves exactly Higman's
statement, including negative integer Frobenius powers, while the first
result retains the opening case of Higman's direct field-theoretic proof.
-/

set_option autoImplicit false

noncomputable section

namespace OddOrder.Higman.Suzuki2Groups

/-- A finite field extension of degree greater than one has a nonzero element
of trace zero. This is the dimension count used in the first case of Higman
Lemma 10. -/
private theorem exists_ne_zero_trace_eq_zero
    {K L : Type*} [Field K] [Field L] [Finite L] [Algebra K L]
    (hdegree : 1 < Module.finrank K L) :
    ∃ z : L, z ≠ 0 ∧ Algebra.trace K L z = 0 := by
  have hrank :=
    (Algebra.trace K L).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L),
    finrank_top, CommSemiring.finrank_self] at hrank
  have hkerpos : 0 < Module.finrank K (LinearMap.ker (Algebra.trace K L)) := by
    omega
  letI : Nontrivial (LinearMap.ker (Algebra.trace K L)) :=
    Module.nontrivial_of_finrank_pos hkerpos
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker (Algebra.trace K L))
  exact ⟨z, by simpa using hz, z.property⟩

/-- On the units of a finite field, raising to an exponent coprime to the
group order is surjective. -/
private theorem units_pow_surjective_of_gcd_eq_one
    {L : Type*} [Field L] [Finite L] (d : ℕ)
    (hgcd : (Nat.card Lˣ).gcd d = 1) :
    Function.Surjective (fun a : Lˣ => a ^ d) := by
  classical
  have hindex : (powMonoidHom d : Lˣ →* Lˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, hgcd]
  have htop : (powMonoidHom d : Lˣ →* Lˣ).range = ⊤ :=
    Subgroup.index_eq_one.mp hindex
  intro x
  have hx : x ∈ (powMonoidHom d : Lˣ →* Lˣ).range := by
    rw [htop]
    exact trivial
  rcases hx with ⟨a, rfl⟩
  exact ⟨a, rfl⟩

/-- The first case of **Higman Lemma 10**: when the relevant power map on
the multiplicative group is invertible, a nonzero trace-zero element can be
pulled back through it. -/
theorem exists_ne_zero_pow_mul_trace_eq_zero_of_gcd_eq_one
    {K L : Type*} [Field K] [Field L] [Finite L] [Algebra K L]
    (hdegree : 1 < Module.finrank K L)
    (d : ℕ) (hgcd : (Nat.card Lˣ).gcd d = 1) (ε : L) :
    ∃ α : L, α ≠ 0 ∧ Algebra.trace K L (α ^ d * ε) = 0 := by
  obtain rfl | hε := eq_or_ne ε 0
  · exact ⟨1, one_ne_zero, by simp⟩
  obtain ⟨z, hz, htrace⟩ := exists_ne_zero_trace_eq_zero hdegree
  let u : Lˣ := Units.mk0 (z * ε⁻¹) (mul_ne_zero hz (inv_ne_zero hε))
  obtain ⟨a, ha⟩ := units_pow_surjective_of_gcd_eq_one d hgcd u
  have hpow : (a : L) ^ d = z * ε⁻¹ := by
    exact congrArg Units.val ha
  refine ⟨a, Units.ne_zero a, ?_⟩
  rw [hpow]
  convert htrace using 2
  field_simp

/-! ## The power-map gcd in Higman's direct proof -/

private lemma odd_two_pow_sub_one {m : ℕ} (hm : 0 < m) : Odd (2 ^ m - 1) := by
  rw [Nat.odd_iff]
  simpa using hm

private lemma gcd_two_two_pow_sub_one {m : ℕ} (hm : 0 < m) :
    Nat.gcd 2 (2 ^ m - 1) = 1 :=
  ((odd_two_pow_sub_one hm).coprime_two_left).gcd_eq_one

private lemma pow_add_one_dvd_pow_two_sub_one (r : ℕ) :
    1 + 2 ^ r ∣ 2 ^ (2 * r) - 1 := by
  refine ⟨2 ^ r - 1, ?_⟩
  rw [Nat.mul_comm 2 r, pow_mul, Nat.mul_sub_left_distrib]
  ring_nf
  omega

private lemma pow_two_sub_one_eq_mul (g : ℕ) :
    2 ^ (2 * g) - 1 = (2 ^ g - 1) * (1 + 2 ^ g) := by
  rw [Nat.mul_comm 2 g, pow_mul, Nat.sub_mul]
  ring_nf
  omega

private lemma odd_one_add_two_pow {r : ℕ} (hr : 0 < r) : Odd (1 + 2 ^ r) :=
  odd_one.add_even (even_two.pow_of_ne_zero hr.ne')

private lemma gcd_pow_add_one_pow_sub_one_eq_one_of_gcd
    (r m : ℕ) (hr : 0 < r)
    (hgcd : Nat.gcd (2 * r) m = Nat.gcd r m) :
    Nat.gcd (1 + 2 ^ r) (2 ^ m - 1) = 1 := by
  let d := Nat.gcd (1 + 2 ^ r) (2 ^ m - 1)
  have hdplus : d ∣ 1 + 2 ^ r := Nat.gcd_dvd_left _ _
  have hdminus : d ∣ 2 ^ m - 1 := Nat.gcd_dvd_right _ _
  have hd2r : d ∣ 2 ^ (2 * r) - 1 :=
    hdplus.trans (pow_add_one_dvd_pow_two_sub_one r)
  have hdcommon : d ∣ Nat.gcd (2 ^ (2 * r) - 1) (2 ^ m - 1) :=
    Nat.dvd_gcd hd2r hdminus
  have hdg : d ∣ 2 ^ Nat.gcd r m - 1 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hgcd] at hdcommon
    exact hdcommon
  have hdrminus : d ∣ 2 ^ r - 1 :=
    hdg.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_left r m))
  have hsum : d ∣ 2 + (2 ^ r - 1) := by
    have hp := Nat.two_pow_pos r
    have heq : 2 + (2 ^ r - 1) = 1 + 2 ^ r := by omega
    rwa [heq]
  have hd2 : d ∣ 2 := (Nat.dvd_add_iff_left hdrminus).mpr hsum
  exact Nat.eq_one_of_dvd_coprimes (odd_one_add_two_pow hr).coprime_two_right hdplus hd2

private lemma gcd_two_mul_eq_gcd_of_odd_div_gcd
    (r m : ℕ) (hm : 0 < m) (hodd : Odd (m / Nat.gcd r m)) :
    Nat.gcd (2 * r) m = Nat.gcd r m := by
  let g := Nat.gcd r m
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right r hm
  have hgr : g * (r / g) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r m)
  have hgm : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right r m)
  have h2r : 2 * r = g * (2 * (r / g)) := by
    calc
      2 * r = 2 * (g * (r / g)) := congrArg (2 * ·) hgr.symm
      _ = g * (2 * (r / g)) := by ac_rfl
  have hcop : Nat.Coprime (r / g) (m / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hprod : Nat.Coprime (2 * (r / g)) (m / g) :=
    hodd.coprime_two_left.mul_left hcop
  calc
    Nat.gcd (2 * r) m = Nat.gcd (g * (2 * (r / g))) (g * (m / g)) :=
      congrArg₂ Nat.gcd h2r hgm.symm
    _ = g * Nat.gcd (2 * (r / g)) (m / g) := Nat.gcd_mul_left _ _ _
    _ = g := by rw [hprod.gcd_eq_one, mul_one]

private lemma gcd_pow_add_one_pow_sub_one_eq_one_of_odd
    (r m : ℕ) (hm : 0 < m) (hodd : Odd (m / Nat.gcd r m)) :
    Nat.gcd (1 + 2 ^ r) (2 ^ m - 1) = 1 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · simpa using gcd_two_two_pow_sub_one hm
  · exact gcd_pow_add_one_pow_sub_one_eq_one_of_gcd r m hr
      (gcd_two_mul_eq_gcd_of_odd_div_gcd r m hm hodd)

private lemma gcd_two_mul_eq_two_mul_gcd_of_even_div_gcd
    (r m : ℕ) (hm : 0 < m) (heven : Even (m / Nat.gcd r m)) :
    Nat.gcd (2 * r) m = 2 * Nat.gcd r m := by
  let g := Nat.gcd r m
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right r hm
  have hgr : g * (r / g) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r m)
  have hgm : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right r m)
  have h2r : 2 * r = g * (2 * (r / g)) := by
    calc
      2 * r = 2 * (g * (r / g)) := congrArg (2 * ·) hgr.symm
      _ = g * (2 * (r / g)) := by ac_rfl
  have hcop : Nat.Coprime (r / g) (m / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hquotgcd : Nat.gcd (2 * (r / g)) (m / g) = 2 := by
    rw [mul_comm 2]
    exact Nat.gcd_mul_of_coprime_of_dvd hcop heven.two_dvd
  calc
    Nat.gcd (2 * r) m = Nat.gcd (g * (2 * (r / g))) (g * (m / g)) :=
      congrArg₂ Nat.gcd h2r hgm.symm
    _ = g * Nat.gcd (2 * (r / g)) (m / g) := Nat.gcd_mul_left _ _ _
    _ = g * 2 := congrArg (g * ·) hquotgcd
    _ = 2 * g := Nat.mul_comm _ _

private lemma pow_gcd_add_one_dvd_both_of_even
    (r m : ℕ) (hm : 0 < m) (heven : Even (m / Nat.gcd r m)) :
    1 + 2 ^ Nat.gcd r m ∣ 1 + 2 ^ r ∧
      1 + 2 ^ Nat.gcd r m ∣ 2 ^ m - 1 := by
  let g := Nat.gcd r m
  let a := r / g
  let b := m / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right r hm
  have hgr : g * a = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r m)
  have hgm : g * b = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right r m)
  have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hgpos
  have hodda : Odd a :=
    (Nat.Coprime.of_dvd_right heven.two_dvd hcop).odd_of_right
  have hplus : 1 + 2 ^ g ∣ 1 + 2 ^ r := by
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ g) 1 hodda
    simpa [← hgr, pow_mul, add_comm] using h
  have h2gm : 2 * g ∣ m := by
    rw [← hgm]
    simpa [mul_comm, mul_left_comm] using Nat.mul_dvd_mul_left g heven.two_dvd
  have hminus : 1 + 2 ^ g ∣ 2 ^ m - 1 :=
    (pow_add_one_dvd_pow_two_sub_one g).trans
      (Nat.pow_sub_one_dvd_pow_sub_one 2 h2gm)
  exact ⟨hplus, hminus⟩

private lemma gcd_pow_add_one_pow_sub_one_eq_pow_gcd_add_one_of_even
    (r m : ℕ) (hm : 0 < m) (heven : Even (m / Nat.gcd r m)) :
    Nat.gcd (1 + 2 ^ r) (2 ^ m - 1) = 1 + 2 ^ Nat.gcd r m := by
  let g := Nat.gcd r m
  let a := r / g
  let b := m / g
  let d := Nat.gcd (1 + 2 ^ r) (2 ^ m - 1)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right r hm
  have hgr : g * a = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r m)
  have hcopab : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hgpos
  have hodda : Odd a :=
    (Nat.Coprime.of_dvd_right heven.two_dvd hcopab).odd_of_right
  have hr : 0 < r := by
    rw [← hgr]
    exact Nat.mul_pos hgpos hodda.pos
  have hgdvr : g ∣ r := Nat.gcd_dvd_left r m
  have hgcd : Nat.gcd (2 * r) g = Nat.gcd r g := by
    calc
      Nat.gcd (2 * r) g = g := Nat.gcd_eq_right (hgdvr.mul_left 2)
      _ = Nat.gcd r g := (Nat.gcd_eq_right hgdvr).symm
  have hcop : Nat.Coprime (1 + 2 ^ r) (2 ^ g - 1) :=
    Nat.coprime_iff_gcd_eq_one.mpr
      (gcd_pow_add_one_pow_sub_one_eq_one_of_gcd r g hr hgcd)
  have hdplus : d ∣ 1 + 2 ^ r := Nat.gcd_dvd_left _ _
  have hdminus : d ∣ 2 ^ m - 1 := Nat.gcd_dvd_right _ _
  have hd2r : d ∣ 2 ^ (2 * r) - 1 :=
    hdplus.trans (pow_add_one_dvd_pow_two_sub_one r)
  have hdcommon : d ∣ Nat.gcd (2 ^ (2 * r) - 1) (2 ^ m - 1) :=
    Nat.dvd_gcd hd2r hdminus
  have hd2g : d ∣ 2 ^ (2 * g) - 1 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one,
      gcd_two_mul_eq_two_mul_gcd_of_even_div_gcd r m hm heven] at hdcommon
    exact hdcommon
  have hdmul : d ∣ (2 ^ g - 1) * (1 + 2 ^ g) := by
    rwa [← pow_two_sub_one_eq_mul]
  have hdcop : Nat.Coprime d (2 ^ g - 1) := Nat.Coprime.of_dvd_left hdplus hcop
  have hupper : d ∣ 1 + 2 ^ g := hdcop.dvd_of_dvd_mul_left hdmul
  have hlower : 1 + 2 ^ g ∣ d := by
    exact Nat.dvd_gcd
      (pow_gcd_add_one_dvd_both_of_even r m hm heven).1
      (pow_gcd_add_one_dvd_both_of_even r m hm heven).2
  exact Nat.dvd_antisymm hupper hlower

/-- The gcd dichotomy at the start of Higman's direct proof of Lemma 10.
For `g = gcd(r,m)`, the power map `a ↦ a^(1+2^r)` on the multiplicative
group of the field with `2^m` elements is invertible exactly when `m/g` is
odd; in the even case its kernel has order `1+2^g`. -/
theorem higmanPowerMapGcd (r m : ℕ) (hm : 0 < m) :
    Nat.gcd (1 + 2 ^ r) (2 ^ m - 1) =
      if Odd (m / Nat.gcd r m) then 1 else 1 + 2 ^ Nat.gcd r m := by
  split_ifs with hodd
  · exact gcd_pow_add_one_pow_sub_one_eq_one_of_odd r m hm hodd
  · exact gcd_pow_add_one_pow_sub_one_eq_pow_gcd_add_one_of_even r m hm
      (Nat.not_odd_iff_even.mp hodd)

/-- **Higman Lemma 10** (*Suzuki 2-groups*, pp. 87--88). Let `L / K` be a
proper odd-degree extension of finite fields of characteristic two. For every
integer `r` and every `ε : L`, some nonzero `α : L` makes
`Tr[L/K] (α * Frob₂^r(α) * ε)` vanish.

The integer power is taken in the group of ring automorphisms, so negative
values of `r` mean inverse Frobenius iterations, as in Higman's statement. -/
theorem higmanLemmaTen
    {K L : Type*} [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    (hdegree : 1 < Module.finrank K L)
    (hodd : Odd (Module.finrank K L)) (r : ℤ) (ε : L) :
    ∃ α : L, α ≠ 0 ∧
      Algebra.trace K L (α * ((frobeniusEquiv L 2) ^ r) α * ε) = 0 := by
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  letI : Algebra (ZMod 2) L := ZMod.algebra L 2
  letI : IsScalarTower (ZMod 2) K L := inferInstance
  let trF : L →ₗ[ZMod 2] K :=
    (Algebra.trace K L).restrictScalars (ZMod 2)
  let mulε : L →ₗ[ZMod 2] L := LinearMap.mulRight (ZMod 2) ε
  let B : L →ₗ[ZMod 2] L →ₗ[ZMod 2] K :=
    (LinearMap.mul (ZMod 2) L).compr₂ (trF.comp mulε)
  let T : L ≃ₗ[ZMod 2] L :=
    ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) L) ^ r).toLinearEquiv
  have hdegree' : 2 < Module.finrank K L := by
    have hne : Module.finrank K L ≠ 2 := by
      intro h
      rw [h] at hodd
      rcases hodd with ⟨k, hk⟩
      omega
    omega
  have hdim :
      2 * Module.finrank (ZMod 2) K < Module.finrank (ZMod 2) L := by
    rw [← Module.finrank_mul_finrank (ZMod 2) K L]
    have hpos : 0 < Module.finrank (ZMod 2) K := Module.finrank_pos
    nlinarith
  obtain ⟨α, hα, hzero⟩ :=
    OddOrder.Algebra.exists_ne_zero_bilinear_twist_zero B T hdim
  refine ⟨α, hα, ?_⟩
  have hbase :
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) L).toRingEquiv =
        frobeniusEquiv L 2 := by
    ext x
    rfl
  have hfrob (x : L) :
      ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) L) ^ r) x =
        ((frobeniusEquiv L 2) ^ r) x := by
    rw [← hbase]
    cases r with
    | ofNat n =>
        exact congrFun
          ((AlgEquiv.coe_pow
            (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) L) n).trans
            (RingAut.coe_pow
              (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) L).toRingEquiv n).symm) x
    | negSucc n =>
        simp only [zpow_negSucc]
        have hp :
            ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) L) ^ (n + 1)).toRingEquiv =
              (FiniteField.frobeniusAlgEquivOfAlgebraic
                (ZMod 2) L).toRingEquiv ^ (n + 1) := by
          ext y
          exact congrFun
            ((AlgEquiv.coe_pow
              (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) L) (n + 1)).trans
              (RingAut.coe_pow
                (FiniteField.frobeniusAlgEquivOfAlgebraic
                  (ZMod 2) L).toRingEquiv (n + 1)).symm) y
        exact congrArg (fun e : L ≃+* L => e.symm x) hp
  rw [← hfrob α]
  simpa [B, T, trF, mulε] using hzero

end OddOrder.Higman.Suzuki2Groups
