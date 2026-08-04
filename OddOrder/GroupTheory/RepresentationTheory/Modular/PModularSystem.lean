/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.CharP.Algebra
import OddOrder.GroupTheory.RepresentationTheory.Modular.RootsOfUnityLift

/-!
# `p`-modular systems

A **`p`-modular system** is the coefficient set-up of modular representation theory: a local ring
`𝒪` of characteristic `0` whose residue field `k = ResidueField 𝒪` has characteristic `p`, and
which is *Henselian* so that roots of unity of order prime to `p` lift from `k` to `𝒪`
(`RootsOfUnityLift`).  The fraction field of `𝒪` supplies the characteristic-`0` coefficients in
which Brauer characters take their values.

The classical definition asks for a **complete discrete valuation ring**.  We only require
Henselian: that is all that the lifting of `p'`-roots of unity needs, and mathlib turns
`IsAdicComplete (maximalIdeal 𝒪) 𝒪` into `HenselianLocalRing 𝒪`
(`OddOrder.RepresentationTheory.Modular.henselianLocalRing_of_isAdicComplete` below), so every
complete DVR is covered.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.IsPModularSystem`

## Main results

* `OddOrder.RepresentationTheory.Modular.henselianLocalRing_of_isAdicComplete` — a complete
  local ring is Henselian (mathlib only has the `HenselianRing` form of this)
* `OddOrder.RepresentationTheory.Modular.isUnit_natCast_of_not_dvd` — `p ∤ n` makes `n` a unit
* `OddOrder.RepresentationTheory.Modular.rootsOfUnityEquivResidue_of_not_dvd` — the transport of
  `n`-th roots of unity between `𝒪` and `k` for `p ∤ n`
* `OddOrder.RepresentationTheory.Modular.instIsPModularSystemPadicInt` — the `p`-adic integers
  `ℤ_[p]` are a `p`-modular system, so the notion is not vacuous
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing

/-- A local ring that is adically complete at its maximal ideal is Henselian.

mathlib provides `IsAdicComplete.henselianRing`, which gives `HenselianRing R (maximalIdeal R)`;
the only gap to `HenselianLocalRing R` is that the latter phrases simplicity of the root as
`IsUnit (f'.eval a₀)` in `R` rather than in the residue ring, and units map to units. -/
theorem henselianLocalRing_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk (maximalIdeal R)))

/-- A **`p`-modular system**: a Henselian local ring of characteristic `0` whose residue field
has characteristic `p`. -/
class IsPModularSystem (p : ℕ) (𝒪 : Type*) [CommRing 𝒪] [HenselianLocalRing 𝒪] : Prop where
  /-- The ring itself has characteristic zero. -/
  [charZero : CharZero 𝒪]
  /-- The residue field has characteristic `p`. -/
  [residueCharP : CharP (ResidueField 𝒪) p]

attribute [instance] IsPModularSystem.charZero IsPModularSystem.residueCharP

section

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]

/-- In a `p`-modular system a natural number prime to `p` is a unit: its residue is nonzero
because the residue field has characteristic `p`. -/
theorem isUnit_natCast_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : IsUnit ((n : ℕ) : 𝒪) := by
  rw [isUnit_iff_residue_ne_zero]
  have hres : residue 𝒪 (n : 𝒪) = (n : ResidueField 𝒪) := by
    rw [map_natCast]
  rw [hres]
  intro h
  exact hn ((CharP.cast_eq_zero_iff (ResidueField 𝒪) p n).mp h)

/-- `p` itself is not a unit: its residue is `0` because the residue field has characteristic
`p`. -/
theorem natCast_prime_mem_maximalIdeal : ((p : ℕ) : 𝒪) ∈ maximalIdeal 𝒪 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_residue_ne_zero, not_not, map_natCast]
  exact CharP.cast_eq_zero (ResidueField 𝒪) p

/-- **Divisibility by a power of `p` may be tested in `𝒪`.**  If `p^i` divides `n` after mapping
to `𝒪`, then it already divides `n` in `ℕ`.

This is what turns the ring-theoretic height inequality (`[G : D] ∣ χ(1)` in `𝒪`) into the
arithmetic statement `ν(χ(1)) ≥ ν(|G|) - d(B)`.  Only locality and characteristic `0` are used:
if `p^i ∤ n` then, after cancelling the exact `p`-power in `n` — whose cofactor is a unit — one
gets `p^e · (1 - p^{i-e}t) = 0` with `1 - p^{i-e}t` a unit, forcing `p^e = 0` in `𝒪`. -/
theorem pow_dvd_of_natCast_pow_dvd (hp : p.Prime) {i n : ℕ}
    (h : ((p ^ i : ℕ) : 𝒪) ∣ ((n : ℕ) : 𝒪)) : p ^ i ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  by_contra hcon
  have hlt : n.factorization p < i := by
    by_contra hle
    exact hcon ((Nat.Prime.pow_dvd_iff_le_factorization hp hn).mpr (not_lt.mp hle))
  -- cancel the unit `ordCompl[p] n`
  have hunit : IsUnit ((ordCompl[p] n : ℕ) : 𝒪) :=
    isUnit_natCast_of_not_dvd (p := p) (Nat.not_dvd_ordCompl hp hn)
  rw [← Nat.ordProj_mul_ordCompl_eq_self n p, Nat.cast_mul, hunit.dvd_mul_right] at h
  obtain ⟨t, ht⟩ := h
  push_cast at ht
  set e := n.factorization p with he
  -- `p^e = p^e * (p^(i-e) * t)`, and the second factor lies in the maximal ideal
  have hsplit : ((p : 𝒪)) ^ i = (p : 𝒪) ^ e * (p : 𝒪) ^ (i - e) := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le]
  rw [hsplit, mul_assoc] at ht
  have hmem : (p : 𝒪) ^ (i - e) * t ∈ maximalIdeal 𝒪 := by
    obtain ⟨j, hj⟩ : ∃ j, i - e = j + 1 := ⟨i - e - 1, by omega⟩
    rw [hj, pow_succ, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ natCast_prime_mem_maximalIdeal)
  have hu : IsUnit (1 - ((p : 𝒪) ^ (i - e) * t)) :=
    isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp hmem)
  have hcancel : (p : 𝒪) ^ e * (1 - ((p : 𝒪) ^ (i - e) * t)) = 0 := by linear_combination ht
  have hzero : ((p : 𝒪)) ^ e = 0 := hu.mul_left_eq_zero.mp hcancel
  have hne : ((p ^ e : ℕ) : 𝒪) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.pos.ne')
  exact hne (by push_cast; exact hzero)

/-- **Reduction transports `n`-th roots of unity** for every `n` prime to `p`.  This is the
device that lets a Brauer character read off eigenvalues in characteristic `p` and evaluate
them in characteristic `0`. -/
noncomputable def rootsOfUnityEquivResidue_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) (hn0 : n ≠ 0) :
    rootsOfUnity n 𝒪 ≃* rootsOfUnity n (ResidueField 𝒪) :=
  rootsOfUnityEquivResidue (isUnit_natCast_of_not_dvd (p := p) hn) hn0

end

/-! ### The `p`-adic integers form a `p`-modular system

This is the base example, and it shows the notion is not vacuous.  It is *not* a splitting
system (its residue field is the prime field `ZMod p`); constructing splitting systems — an
unramified extension whose residue field contains the `|G|_{p'}`-th roots of unity — is the next
step of issue 9506. -/

section PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

instance : HenselianLocalRing ℤ_[p] := henselianLocalRing_of_isAdicComplete ℤ_[p]

instance : CharP (ResidueField ℤ_[p]) p :=
  charP_of_injective_ringHom
    (PadicInt.residueField (p := p)).symm.toRingHom.injective p

instance instIsPModularSystemPadicInt : IsPModularSystem p ℤ_[p] where

end PadicInt

end OddOrder.RepresentationTheory.Modular
