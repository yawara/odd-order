/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.MixedTermValue

/-!
# Isomorphic summands force Frobenius-conjugate eigenvalues

G. Higman, *Suzuki 2-groups*; T. Peterfalvi, Appendix III, Theorem (e).

A `ZMod 2`-linear map intertwining multiplication by `λ` with multiplication
by `μ` on the Singer field is a Frobenius polynomial whose surviving
coefficients force `μ = λ^{2^i}`.  Hence a `K`-equivariant isomorphism
between two irreducible summands with Singer eigenvalues `λ`, `μ` makes the
eigenvalues Frobenius-conjugate — the arithmetic obstruction ruling out
isomorphic summands in the type-C and type-D groups.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

noncomputable section

universe uS

/-- **A `λ`-to-`μ` semiconjugating linear map forces `μ = λ^{2^i}`.**
Expand `f` in the Frobenius basis: the relation `f(λx) = μ·f(x)` reads
`cᵢ·λ^{2^i} = μ·cᵢ` on each coefficient, and some coefficient of a nonzero
map survives. -/
theorem exists_frobenius_conjugate_of_semiconj
    {n : ℕ} (hn : n ≠ 0) (lam mu : GaloisField 2 n)
    (f : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) (hf : f ≠ 0)
    (hsemi : ∀ x, f (lam * x) = mu * f x) :
    ∃ i : Fin n, mu = lam ^ 2 ^ (i : ℕ) := by
  classical
  set c := (frobeniusBasis n hn).repr f with hcdef
  have hzero : ∑ i : Fin n,
      (c i * lam ^ 2 ^ (i : ℕ) - mu * c i) • frobLin n i =
      (0 : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) := by
    ext x
    simp only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply,
      frobLin_apply, LinearMap.zero_apply, smul_eq_mul, sub_mul]
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ i : Fin n,
        c i * lam ^ 2 ^ (i : ℕ) *
          (frobeniusEquiv (GaloisField 2 n) 2 ^ (i : ℕ)) x =
        f (lam * x) := by
      rw [frobLin_repr n hn f (lam * x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, map_mul, frobeniusEquiv_pow_apply,
        frobeniusEquiv_pow_apply]
      ring
    have h2 : ∑ i : Fin n,
        mu * c i * (frobeniusEquiv (GaloisField 2 n) 2 ^ (i : ℕ)) x =
        mu * f x := by
      rw [frobLin_repr n hn f x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul]
      ring
    rw [h1, h2, hsemi x, sub_self]
  have hall := linearIndependent_iff'.mp (frobLin_linearIndependent n hn)
    Finset.univ _ hzero
  have hcne : ∃ i : Fin n, c i ≠ 0 := by
    by_contra hallzero
    push_neg at hallzero
    apply hf
    have hczero : c = 0 := Finsupp.ext hallzero
    have := congrArg (frobeniusBasis n hn).repr.symm
      (hcdef.symm.trans hczero)
    rwa [LinearEquiv.symm_apply_apply, map_zero] at this
  obtain ⟨i, hci⟩ := hcne
  have hi := hall i (Finset.mem_univ i)
  have hfactor : c i * (lam ^ 2 ^ (i : ℕ) - mu) = 0 := by
    linear_combination hi
  refine ⟨i, ?_⟩
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd h hci
  · exact (sub_eq_zero.mp h).symm

/-- **Equivariant isomorphic Singer summands have Frobenius-conjugate
eigenvalues.**  If two modules carry generator actions with Singer
coordinates `λ`, `μ` and are equivariantly isomorphic, then `μ = λ^{2^i}`. -/
theorem exists_frobenius_conjugate_of_equivariant_linearEquiv
    {V₁ : Type uS} {V₂ : Type uS} [AddCommGroup V₁] [AddCommGroup V₂]
    [Module (ZMod 2) V₁] [Module (ZMod 2) V₂]
    {n : ℕ} (hn : n ≠ 0)
    (e₁ : V₁ ≃ₗ[ZMod 2] GaloisField 2 n)
    (e₂ : V₂ ≃ₗ[ZMod 2] GaloisField 2 n)
    (lam mu : GaloisField 2 n)
    (T₁ : V₁ →ₗ[ZMod 2] V₁) (T₂ : V₂ →ₗ[ZMod 2] V₂)
    (h₁ : ∀ v, e₁ (T₁ v) = lam * e₁ v)
    (h₂ : ∀ v, e₂ (T₂ v) = mu * e₂ v)
    (e : V₁ ≃ₗ[ZMod 2] V₂) (hequiv : ∀ v, e (T₁ v) = T₂ (e v)) :
    ∃ i : Fin n, mu = lam ^ 2 ^ (i : ℕ) := by
  set f : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n :=
    e₂.toLinearMap.comp (e.toLinearMap.comp e₁.symm.toLinearMap) with hfdef
  have hfapply : ∀ x, f x = e₂ (e (e₁.symm x)) := fun x => rfl
  apply exists_frobenius_conjugate_of_semiconj hn lam mu f
  · intro h0
    have hone : f 1 = 0 := by rw [h0]; rfl
    rw [hfapply] at hone
    have h1 : e₁.symm 1 = 0 := by
      apply e.injective
      apply e₂.injective
      rw [hone, map_zero, map_zero]
    have : (1 : GaloisField 2 n) = 0 := by
      have := congrArg e₁ h1
      rwa [e₁.apply_symm_apply, map_zero] at this
    exact one_ne_zero this
  · intro x
    rw [hfapply, hfapply]
    have hs : e₁.symm (lam * x) = T₁ (e₁.symm x) := by
      apply e₁.injective
      rw [e₁.apply_symm_apply, h₁, e₁.apply_symm_apply]
    rw [hs, hequiv, h₂]

end

end OddOrder.Higman.Suzuki2Groups
