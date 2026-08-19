/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Lifting roots of unity along the residue map of a Henselian local ring

Let `𝒪` be a local ring with residue field `k = ResidueField 𝒪` and let `n` be a natural number
that is a **unit of `𝒪`** (in the intended application `𝒪` has residue characteristic `p` and
`p ∤ n`).  Then the residue map induces an isomorphism

`μ_n(𝒪) ≃* μ_n(k)`

as soon as `𝒪` is Henselian.  Injectivity holds in any local ring and comes from the derivative
computation `f'(b) = n · b ^ (n-1)` for `f = X ^ n - 1`; surjectivity is Hensel's lemma.

This is the technical heart of a `p`-modular system: it is what lets a Brauer character lift the
eigenvalues of a `p`-regular element from characteristic `p` back to characteristic `0`
(issue 9506, the bottom-up first stage of issue 0147).

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_of_pow_eq_one_of_sub_mem` — uniqueness of lifts
* `OddOrder.RepresentationTheory.Modular.exists_pow_eq_one_residue_eq` — existence of lifts
* `OddOrder.RepresentationTheory.Modular.rootsOfUnityEquivResidue` — the isomorphism
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Polynomial

/-! ### Elementary local-ring facts -/

/-- An element with `a ^ n = 1` (`n ≠ 0`) is a unit.  (mathlib has this only through
`orderOf`-based API, which needs finiteness assumptions we do not want here.) -/
theorem isUnit_of_pow_eq_one {M : Type*} [CommMonoid M] {a : M} {n : ℕ} (h : a ^ n = 1)
    (hn : n ≠ 0) : IsUnit a := by
  have key : a * a ^ (n - 1) = 1 := by
    calc a * a ^ (n - 1) = a ^ (n - 1 + 1) := (pow_succ' a (n - 1)).symm
      _ = a ^ n := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      _ = 1 := h
  exact ⟨⟨a, a ^ (n - 1), key, by rw [mul_comm]; exact key⟩, rfl⟩

section LocalRing

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]

/-- In a local ring, a unit plus an element of the maximal ideal is a unit. -/
theorem isUnit_add_of_mem_maximalIdeal {u x : 𝒪} (hu : IsUnit u)
    (hx : x ∈ maximalIdeal 𝒪) : IsUnit (u + x) := by
  by_contra h
  have hmem : u + x ∈ maximalIdeal 𝒪 := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
  have hu' : u ∈ maximalIdeal 𝒪 := by
    have hsub := (maximalIdeal 𝒪).sub_mem hmem hx
    simpa using hsub
  exact (mem_nonunits_iff.mp ((mem_maximalIdeal u).mp hu')) hu

/-- An element of a local ring is a unit exactly when its residue is nonzero. -/
theorem isUnit_iff_residue_ne_zero {a : 𝒪} : IsUnit a ↔ residue 𝒪 a ≠ 0 := by
  rw [Ne, residue_eq_zero_iff]
  constructor
  · intro ha hmem
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal a).mp hmem)) ha
  · intro ha
    by_contra hcon
    exact ha ((mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hcon))

/-! ### Uniqueness of lifts -/

/-- **Uniqueness of root-of-unity lifts.**  In a local ring in which `n` is a unit, two `n`-th
roots of unity with the same residue are equal.

The proof is the first-order Taylor expansion of `f = X ^ n - 1` at `b`
(`Polynomial.binomExpansion`): writing `0 = f(a) = f(b) + f'(b)·(a-b) + k·(a-b)²` and using
`f'(b) = n·b^(n-1)` (a unit) together with `k·(a-b) ∈ 𝔪`, the coefficient of `a - b` is a unit. -/
theorem eq_of_pow_eq_one_of_sub_mem {n : ℕ} (hn : IsUnit ((n : ℕ) : 𝒪)) {a b : 𝒪}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : a - b ∈ maximalIdeal 𝒪) : a = b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [Nat.cast_zero] at hn
    have := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hn)
    exact Subsingleton.elim a b
  have hbu : IsUnit b := isUnit_of_pow_eq_one hb hn0.ne'
  obtain ⟨k, hk⟩ := (X ^ n - 1 : 𝒪[X]).binomExpansion b (a - b)
  have hba : b + (a - b) = a := by ring
  have hfa : (X ^ n - 1 : 𝒪[X]).eval a = 0 := by simp [ha]
  have hfb : (X ^ n - 1 : 𝒪[X]).eval b = 0 := by simp [hb]
  have hderiv : (derivative (X ^ n - 1 : 𝒪[X])).eval b = (n : 𝒪) * b ^ (n - 1) := by
    simp [derivative_X_pow]
  rw [hba, hfa, hfb, hderiv, zero_add] at hk
  have hfactor : ((n : 𝒪) * b ^ (n - 1) + k * (a - b)) * (a - b) = 0 := by
    have hexp : ((n : 𝒪) * b ^ (n - 1) + k * (a - b)) * (a - b)
        = (n : 𝒪) * b ^ (n - 1) * (a - b) + k * (a - b) ^ 2 := by ring
    rw [hexp, ← hk]
  have hunit : IsUnit ((n : 𝒪) * b ^ (n - 1) + k * (a - b)) :=
    isUnit_add_of_mem_maximalIdeal (hn.mul (hbu.pow _)) (Ideal.mul_mem_left _ k hab)
  obtain ⟨u, hu⟩ := hunit
  have hzero : a - b = 0 := by
    have h2 : (↑u⁻¹ : 𝒪) * (((n : 𝒪) * b ^ (n - 1) + k * (a - b)) * (a - b)) = 0 := by
      rw [hfactor, mul_zero]
    rwa [← hu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h2
  exact sub_eq_zero.mp hzero

end LocalRing

/-! ### Existence of lifts (Hensel) -/

section Henselian

variable {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪]

/-- **Existence of root-of-unity lifts.**  Over a Henselian local ring in which `n` is a unit,
every `n`-th root of unity of the residue field is the residue of an `n`-th root of unity. -/
theorem exists_pow_eq_one_residue_eq {n : ℕ} (hn : IsUnit ((n : ℕ) : 𝒪)) (hn0 : n ≠ 0)
    {c : ResidueField 𝒪} (hc : c ^ n = 1) :
    ∃ a : 𝒪, a ^ n = 1 ∧ residue 𝒪 a = c := by
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal 𝒪) c
  have hres : residue 𝒪 a₀ = c := ha₀
  have hval : (X ^ n - 1 : 𝒪[X]).eval a₀ ∈ maximalIdeal 𝒪 := by
    rw [← residue_eq_zero_iff]
    rw [eval_sub, eval_pow, eval_X, eval_one, map_sub, map_pow, map_one, hres, hc, sub_self]
  have ha₀u : IsUnit a₀ := by
    rw [isUnit_iff_residue_ne_zero, hres]
    intro h
    rw [h, zero_pow hn0] at hc
    exact zero_ne_one hc
  have hderivu : IsUnit ((derivative (X ^ n - 1 : 𝒪[X])).eval a₀) := by
    have hd : (derivative (X ^ n - 1 : 𝒪[X])).eval a₀ = (n : 𝒪) * a₀ ^ (n - 1) := by
      simp [derivative_X_pow]
    rw [hd]
    exact hn.mul (ha₀u.pow _)
  have hmonic : (X ^ n - 1 : 𝒪[X]).Monic := by
    simpa using monic_X_pow_sub_C (1 : 𝒪) hn0
  obtain ⟨a, hroot, hsub⟩ :=
    HenselianLocalRing.is_henselian (X ^ n - 1 : 𝒪[X]) hmonic a₀ hval hderivu
  refine ⟨a, ?_, ?_⟩
  · have h := hroot
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at h
    exact h
  · rw [← hres]
    exact Ideal.Quotient.eq.mpr hsub

/-- **Reduction is an isomorphism on `n`-th roots of unity** when `n` is a unit of the Henselian
local ring `𝒪`. -/
noncomputable def rootsOfUnityEquivResidue {n : ℕ} (hn : IsUnit ((n : ℕ) : 𝒪)) (hn0 : n ≠ 0) :
    rootsOfUnity n 𝒪 ≃* rootsOfUnity n (ResidueField 𝒪) := by
  refine MulEquiv.ofBijective (restrictRootsOfUnity (residue 𝒪) n) ⟨?_, ?_⟩
  · intro ζ ξ hzx
    have hval : residue 𝒪 (ζ : 𝒪ˣ) = residue 𝒪 (ξ : 𝒪ˣ) := by
      have h := congrArg (fun w : rootsOfUnity n (ResidueField 𝒪) => (w : (ResidueField 𝒪)ˣ)) hzx
      simpa only [restrictRootsOfUnity_coe_apply] using congrArg Units.val h
    refine Subtype.ext (Units.ext ?_)
    refine eq_of_pow_eq_one_of_sub_mem hn ?_ ?_ ?_
    · exact (mem_rootsOfUnity' n _).mp ζ.2
    · exact (mem_rootsOfUnity' n _).mp ξ.2
    · exact (residue_eq_zero_iff _).mp (by rw [map_sub, hval, sub_self])
  · intro η
    have hη : ((η : (ResidueField 𝒪)ˣ) : ResidueField 𝒪) ^ n = 1 :=
      (mem_rootsOfUnity' n _).mp η.2
    obtain ⟨a, hapow, hares⟩ := exists_pow_eq_one_residue_eq hn hn0 hη
    obtain ⟨u, hu⟩ := isUnit_of_pow_eq_one hapow hn0
    have humem : u ∈ rootsOfUnity n 𝒪 := by
      rw [mem_rootsOfUnity']
      rw [hu]
      exact hapow
    refine ⟨⟨u, humem⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [restrictRootsOfUnity_coe_apply]
    change residue 𝒪 (u : 𝒪) = _
    rw [hu, hares]

end Henselian

end OddOrder.RepresentationTheory.Modular
