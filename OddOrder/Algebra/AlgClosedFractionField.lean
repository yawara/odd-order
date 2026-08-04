/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integrally closed domains with an algebraically closed fraction field

Let `A` be an integrally closed domain whose fraction field `K` is algebraically closed.  Then a
monic polynomial over `A` already has all its roots in `A`: they are roots of a monic polynomial,
hence integral over `A`, hence in `A`.  Two consequences make such an `A` an unusually convenient
coefficient ring, and both are proved here for a *local* such `A`:

* its **residue field is algebraically closed** — lift a monic polynomial, find a root upstairs,
  reduce it;
* it is **Henselian** — split off the linear factors one at a time and use that the maximal ideal
  is prime to see which factor `f(a₀) ∈ 𝔪` came from.  No completeness and no Newton iteration
  is involved; the roots are already there and one only has to say which one is near `a₀`.

The application is the `p`-modular system `𝓞_ℂ_[p]` of `Modular/PadicComplexSystem.lean`, whose
fraction field `ℂ_[p]` is algebraically closed of characteristic `0` and whose residue field is
therefore algebraically closed of characteristic `p`.  Both splittings that modular representation
theory needs — of `K[G]` and of `k[G]` — then come from Wedderburn–Artin over an algebraically
closed field, with no appeal to Brauer's splitting field theorem.

`K` is an explicit argument throughout: it occurs in the hypotheses only, so it cannot be inferred.

## Main results

* `OddOrder.exists_isRoot_of_monic` — a monic polynomial of positive degree has a root in `A`
* `OddOrder.exists_isRoot_sub_mem_maximalIdeal` — the root can be chosen near a given `a₀`
* `OddOrder.isAlgClosed_residueField` — the residue field is algebraically closed
* `OddOrder.henselianLocalRing_of_isAlgClosed` — `A` is Henselian
-/

namespace OddOrder

open IsLocalRing Polynomial

variable {A : Type*} [CommRing A] [IsIntegrallyClosed A]

/-- **A monic polynomial of positive degree over `A` has a root in `A`**, when the fraction field
`K` is algebraically closed.  The root exists in `K`, and it is integral over `A` because it is a
root of a monic polynomial with coefficients in `A`; integral closedness puts it back in `A`. -/
theorem exists_isRoot_of_monic (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAlgClosed K] {f : A[X]} (hf : f.Monic) (hdeg : f.natDegree ≠ 0) : ∃ a : A, f.IsRoot a := by
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hdegK : (f.map (algebraMap A K)).degree ≠ 0 := by
    intro h
    exact hdeg (by
      rw [← hf.natDegree_map (algebraMap A K), natDegree_eq_of_degree_eq_some h]; rfl)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (f.map (algebraMap A K)) hdegK
  have hint : IsIntegral A r := ⟨f, hf, by rwa [← eval_map]⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨a, hinj ?_⟩
  have hev : (f.map (algebraMap A K)).eval (algebraMap A K a) = algebraMap A K (f.eval a) := by
    rw [eval_map, eval₂_at_apply]
  rw [ha] at hev
  rw [map_zero]
  exact hev.symm.trans hr

variable [IsLocalRing A]

/-- **A root can be chosen in a prescribed residue class.**  If `f` is monic and `f(a₀)` lies in
the maximal ideal, then `f` has a root `a` with `a ≡ a₀`.

Peeling off one linear factor at a time writes `f = (X - c) * g` with `c` a root in `A`; then
`f(a₀) = (a₀ - c) * g(a₀)` lies in the *prime* ideal `𝔪`, so either `a₀ - c ∈ 𝔪` — and `c` is the
root we want — or `g(a₀) ∈ 𝔪` and the degree has dropped.  The degree cannot reach `0`, because a
monic polynomial of degree `0` is `1` and `1 ∉ 𝔪`. -/
theorem exists_isRoot_sub_mem_maximalIdeal (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsAlgClosed K] {f : A[X]} (hf : f.Monic) (a₀ : A)
    (h : f.eval a₀ ∈ maximalIdeal A) : ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal A := by
  suffices H : ∀ n : ℕ, ∀ g : A[X], g.Monic → g.natDegree ≤ n → ∀ b : A,
      g.eval b ∈ maximalIdeal A → ∃ a : A, g.IsRoot a ∧ a - b ∈ maximalIdeal A from
    H f.natDegree f hf le_rfl a₀ h
  have hone : (1 : A) ∉ maximalIdeal A :=
    (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal A).ne_top
  intro n
  induction n with
  | zero =>
    intro g hg hdeg b hb
    rw [(Polynomial.Monic.natDegree_eq_zero hg).mp (Nat.le_zero.mp hdeg), eval_one] at hb
    exact absurd hb hone
  | succ n ih =>
    intro g hg hdeg b hb
    rcases Nat.eq_zero_or_pos g.natDegree with h0 | h0
    · rw [(Polynomial.Monic.natDegree_eq_zero hg).mp h0, eval_one] at hb
      exact absurd hb hone
    obtain ⟨c, hc⟩ := exists_isRoot_of_monic K hg h0.ne'
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hc
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C c) (hq ▸ hg)
    have hqdeg : q.natDegree ≤ n := by
      have hmul := Polynomial.Monic.natDegree_mul (monic_X_sub_C c) hqm
      rw [← hq, natDegree_X_sub_C] at hmul
      omega
    have hfac : g.eval b = (b - c) * q.eval b := by rw [hq]; simp
    rw [hfac] at hb
    rcases (maximalIdeal.isMaximal A).isPrime.mem_or_mem hb with h1 | h2
    · refine ⟨c, hc, ?_⟩
      simpa using (maximalIdeal A).neg_mem h1
    · obtain ⟨a, ha, hab⟩ := ih q hqm hqdeg b h2
      refine ⟨a, ?_, hab⟩
      rw [IsRoot, hq, eval_mul, ha, mul_zero]

/-- **The residue field is algebraically closed.**  A monic irreducible polynomial over `k` lifts
to a monic polynomial of the same degree over `A`, which has a root in `A`; its residue is a root
downstairs. -/
theorem isAlgClosed_residueField (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAlgClosed K] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun g hgm hgirr => ?_
  have hlifts : g ∈ lifts (residue A) := by
    obtain ⟨q, hq⟩ := map_surjective (residue A) Ideal.Quotient.mk_surjective g
    exact ⟨q, hq⟩
  obtain ⟨F, hFmap, hFdeg, hFm⟩ := lifts_and_natDegree_eq_and_monic hlifts hgm
  have hgdeg : g.natDegree ≠ 0 := fun h0 => hgirr.not_isUnit
    (by rw [(Polynomial.Monic.natDegree_eq_zero hgm).mp h0]; exact isUnit_one)
  obtain ⟨a, ha⟩ := exists_isRoot_of_monic K hFm (by rw [hFdeg]; exact hgdeg)
  exact ⟨residue A a, by rw [← hFmap, eval_map, eval₂_at_apply, ha, map_zero]⟩

/-- **`A` is Henselian.**  This needs no completeness: over an algebraically closed fraction field
the roots are already in `A`, and `exists_isRoot_sub_mem_maximalIdeal` picks the one congruent to
`a₀`.  The simplicity hypothesis on the root is not used. -/
theorem henselianLocalRing_of_isAlgClosed (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAlgClosed K] : HenselianLocalRing A :=
  { ‹IsLocalRing A› with
    is_henselian := fun f hf a₀ h₁ _ => exists_isRoot_sub_mem_maximalIdeal K hf a₀ h₁ }

end OddOrder
