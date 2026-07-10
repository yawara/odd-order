/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_GridExpansion
import OddOrder.Peterfalvi.S16_PairingBessel

/-!
# Peterfalvi (13.19.c, pp. 85–87; 14.11.2, p. 89): coherent projection rigidity

This file isolates the Hilbert-space calculation used in Peterfalvi (13.19.c) and (14.11.2).
For an integer coefficient grid `m`, `etaGridProjection hyp m` is its expansion in the
orthonormal `eta`-grid.  The main results are:

* `etaGrid_projection_pythagorean`: the exact Pythagorean identity for this projection;
* `TypeICoherent78Data.etaGrid_projection_residual_bound`: the identity combined with the
  (7.8.b) bound on the coherent residual `Gamma`, retaining the norm of the perpendicular
  residual;
* `TypeICoherent78Data.etaGrid_projection_rigidity`: the equality case.  The four-corner
  relation and odd boundary coefficients make every coefficient odd.  If the complement
  index is at most the grid cardinality, the residual bound forces equality, all coefficients
  to be `+1` or `-1`, and the perpendicular residual to vanish.

The statements take the projection coefficient identity as an explicit hypothesis.  Thus they
are upstream of the separate Dade-support argument that proves orthogonality of the coherent
images to a particular `eta`-grid, and can be reused on both the `L`- and `M`-sides.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S09
open OddOrder.Peterfalvi.S09.Cert
open scoped BigOperators

variable {G : Type*} [Group G]

/-- The integer linear combination of the full `eta`-grid with coefficient matrix `m`. -/
noncomputable def etaGridProjection
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ) : ClassFunction G ℂ :=
  ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j : ℂ) • hyp.eta i j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Pythagoras for the full `eta`-grid.**  If the integer coefficients `m_ij` are the
Fourier coefficients of `phi` on the orthonormal grid, then the squared norm of `phi` is the
sum of their squares plus the squared norm of the perpendicular residual. -/
theorem etaGrid_projection_pythagorean [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (phi : ClassFunction G ℂ) (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner phi (hyp.eta i j) = (m i j : ℂ)) :
    ClassFunction.inner phi phi =
      ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) +
        ClassFunction.inner (phi - etaGridProjection hyp m)
          (phi - etaGridProjection hyp m) := by
  classical
  set X : ClassFunction G ℂ := etaGridProjection hyp m with hX
  set Y : ClassFunction G ℂ := phi - X with hY
  have hXeta : ∀ (k : Fin hyp.q) (l : Fin hyp.p),
      ClassFunction.inner X (hyp.eta k l) = (m k l : ℂ) := by
    intro k l
    rw [hX, etaGridProjection, inner_sum_left]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => ?_)]
    · rw [inner_sum_left,
        Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => ?_)]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_pos ⟨rfl, rfl⟩, mul_one]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_neg (by rintro ⟨-, rfl⟩; exact hjl rfl), mul_zero]
    · rw [inner_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
        if_neg (by rintro ⟨rfl, -⟩; exact hik rfl), mul_zero]
  have hsum_sq : ∀ psi : ClassFunction G ℂ,
      (∀ (k : Fin hyp.q) (l : Fin hyp.p),
        ClassFunction.inner psi (hyp.eta k l) = (m k l : ℂ)) ->
      ClassFunction.inner psi X =
        ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) := by
    intro psi hpsi
    rw [hX, etaGridProjection, inner_sum_right]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hpsi i j, star_intCast]
    ring
  have hXY : ClassFunction.inner X Y = 0 := by
    have hXX := hsum_sq X hXeta
    have hXphi : ClassFunction.inner X phi =
        ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hsum_sq phi hcoeff, star_intCast]
    rw [hY, ClassFunction.inner_sub_right, hXphi, hXX, sub_self]
  have hYX : ClassFunction.inner Y X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXY, star_zero]
  have hphiXY : phi = X + Y := by rw [hY]; abel
  have hsplit : ClassFunction.inner phi phi =
      ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) +
        ClassFunction.inner Y Y := by
    calc
      ClassFunction.inner phi phi = ClassFunction.inner (X + Y) (X + Y) := by rw [← hphiXY]
      _ = ClassFunction.inner X X + ClassFunction.inner X Y +
          (ClassFunction.inner Y X + ClassFunction.inner Y Y) := by
        rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
          ClassFunction.inner_add_right]
      _ = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) +
          ClassFunction.inner Y Y := by rw [hXY, hYX, hsum_sq X hXeta]; ring
  simpa [hX, hY] using hsplit

namespace TypeICoherent78Data

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), projection bound with its perpendicular residual retained.**
For `phi = 1_G + Gamma`, the exact grid projection identity and the (7.8.b) estimate
`||Gamma||^2 ≤ e - 1` give

`sum m_ij^2 + ||phi - sum m_ij eta_ij||^2 ≤ e`.

Unlike a bare Bessel inequality, retaining the second term exposes the equality case that
forces the grid expansion in (13.19.c). -/
theorem etaGrid_projection_residual_bound [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hcoeff : ∀ i j,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (data.betaDecomp hG).Gamma)
        (hyp.eta i j) = (m i j : ℂ)) :
    ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℝ) +
        (ClassFunction.inner
          ((OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (data.betaDecomp hG).Gamma) -
            etaGridProjection hyp m)
          ((OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (data.betaDecomp hG).Gamma) -
            etaGridProjection hyp m)).re
      ≤ ((data.h78 hG).complementIndex : ℝ) := by
  classical
  haveI := data.kernelIn_normal
  set BD := data.betaDecomp hG with hBD
  set phi : ClassFunction G ℂ :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + BD.Gamma with hphi
  set Y : ClassFunction G ℂ := phi - etaGridProjection hyp m with hY
  have hsplit := etaGrid_projection_pythagorean hyp phi m (by simpa [hphi, hBD] using hcoeff)
  have honeGamma : ClassFunction.inner
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) BD.Gamma = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, BD.Gamma_orth_one,
      star_zero]
  have hphiphi : ClassFunction.inner phi phi =
      (1 : ℂ) + ClassFunction.inner BD.Gamma BD.Gamma := by
    rw [hphi, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right,
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one,
      honeGamma, BD.Gamma_orth_one, add_zero, zero_add]
  have hGammaBound : (ClassFunction.inner BD.Gamma BD.Gamma).re <=
      ((data.h78 hG).complementIndex : ℝ) - 1 :=
    (data.normEstimates hG).gamma_norm_sq_le (data.smallIndex hG)
  have hre : ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℝ) +
      (ClassFunction.inner Y Y).re =
        1 + (ClassFunction.inner BD.Gamma BD.Gamma).re := by
    have hcs := congrArg Complex.re (hsplit.symm.trans hphiphi)
    rw [Complex.add_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at hcs
    simpa [hY, hphi, hBD] using hcs
  simpa [hY, hphi, hBD] using (show
    ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℝ) +
        (ClassFunction.inner Y Y).re ≤ ((data.h78 hG).complementIndex : ℝ) by
      linarith)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), equality-case rigidity of the coherent `eta`-projection.**
Assume the grid coefficients of `1_G + Gamma` are integral, satisfy the (3.7) four-corner
relation, have principal value one and odd off-principal boundary values.  If the coherent
complement index `e` is at most `p*q`, then:

* `e = p*q`;
* every grid coefficient is `+1` or `-1`;
* the perpendicular residual vanishes, so `1_G + Gamma` is exactly the signed grid sum.

This packages the tight `lower bound ≤ Bessel bound ≤ e ≤ p*q` argument while keeping the
Dade-support orthogonality needed for `hcoeff` outside the theorem. -/
theorem etaGrid_projection_rigidity [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hcoeff : ∀ i j,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (data.betaDecomp hG).Gamma)
        (hyp.eta i j) = (m i j : ℂ))
    (hprincipal : m ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ = 1)
    (hrelation : ∀ i j,
      m i j + m ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ =
        m i ⟨0, hyp.p_prime.pos⟩ + m ⟨0, hyp.q_prime.pos⟩ j)
    (hrow : ∀ j, j ≠ ⟨0, hyp.p_prime.pos⟩ ->
      Odd (m ⟨0, hyp.q_prime.pos⟩ j))
    (hcol : ∀ i, i ≠ ⟨0, hyp.q_prime.pos⟩ ->
      Odd (m i ⟨0, hyp.p_prime.pos⟩))
    (he : (data.h78 hG).complementIndex ≤ hyp.p * hyp.q) :
    (data.h78 hG).complementIndex = hyp.p * hyp.q ∧
      (∀ i j, m i j = 1 ∨ m i j = -1) ∧
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (data.betaDecomp hG).Gamma =
        etaGridProjection hyp m := by
  classical
  set i0 : Fin hyp.q := ⟨0, hyp.q_prime.pos⟩ with hi0
  set j0 : Fin hyp.p := ⟨0, hyp.p_prime.pos⟩ with hj0
  set S : ℤ := ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 with hS
  set phi : ClassFunction G ℂ :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (data.betaDecomp hG).Gamma with hphi
  set Y : ClassFunction G ℂ := phi - etaGridProjection hyp m with hY
  have hodd : ∀ x : Fin hyp.q × Fin hyp.p, Odd (m x.1 x.2) := by
    rintro ⟨i, j⟩
    by_cases hi : i = i0 <;> by_cases hj : j = j0
    · subst i; subst j; rw [hprincipal]; exact ⟨0, rfl⟩
    · subst i; exact hrow j (by simpa [j0] using hj)
    · subst j; exact hcol i (by simpa [i0] using hi)
    · have hrel := hrelation i j
      rw [hprincipal] at hrel
      have hval : m i j = m i j0 + m i0 j - 1 := by
        omega
      obtain ⟨r, hr⟩ := hcol i (by simpa [i0] using hi)
      obtain ⟨s, hs⟩ := hrow j (by simpa [j0] using hj)
      refine ⟨r + s, ?_⟩
      rw [hval, hr, hs]
      ring
  have hge1 : ∀ x : Fin hyp.q × Fin hyp.p, (1 : ℤ) ≤ (m x.1 x.2) ^ 2 := by
    intro x
    have hne : m x.1 x.2 ≠ 0 := by rcases hodd x with ⟨a, ha⟩; omega
    nlinarith [Int.one_le_abs hne, sq_abs (m x.1 x.2)]
  have hcard : Fintype.card (Fin hyp.q × Fin hyp.p) = hyp.p * hyp.q := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]
  have hsum_ge : ((hyp.p * hyp.q : ℕ) : ℤ) ≤ S := by
    calc
      ((hyp.p * hyp.q : ℕ) : ℤ) =
          (Fintype.card (Fin hyp.q × Fin hyp.p) : ℤ) := by rw [hcard]
      _ =
          ∑ _x : Fin hyp.q × Fin hyp.p, (1 : ℤ) := by
        rw [Finset.sum_const, Finset.card_univ]; ring
      _ ≤ ∑ x : Fin hyp.q × Fin hyp.p, (m x.1 x.2) ^ 2 :=
        Finset.sum_le_sum (fun x _ => hge1 x)
      _ = S := by rw [Fintype.sum_prod_type, ← hS]
  have hres := data.etaGrid_projection_residual_bound hG hyp m hcoeff
  have hYY_nonneg : (0 : ℝ) ≤ (ClassFunction.inner Y Y).re :=
    OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_self_re_nonneg Y
  have hsum_le_e : S ≤ ((data.h78 hG).complementIndex : ℤ) := by
    have hreal : (S : ℝ) ≤ ((data.h78 hG).complementIndex : ℝ) := by
      rw [hS]
      have hres' : ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℝ) +
          (ClassFunction.inner Y Y).re ≤ ((data.h78 hG).complementIndex : ℝ) := by
        simpa [hY, hphi] using hres
      linarith
    exact_mod_cast hreal
  have heZ : ((data.h78 hG).complementIndex : ℤ) ≤ ((hyp.p * hyp.q : ℕ) : ℤ) := by
    exact_mod_cast he
  have heqZ : ((data.h78 hG).complementIndex : ℤ) = ((hyp.p * hyp.q : ℕ) : ℤ) := by omega
  have heq : (data.h78 hG).complementIndex = hyp.p * hyp.q := by exact_mod_cast heqZ
  have hsum_eq : S = ((hyp.p * hyp.q : ℕ) : ℤ) := by omega
  have heach : ∀ x : Fin hyp.q × Fin hyp.p, (m x.1 x.2) ^ 2 = 1 := by
    have hz : ∑ x : Fin hyp.q × Fin hyp.p, ((m x.1 x.2) ^ 2 - 1) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
      rw [Fintype.sum_prod_type, ← hS, hsum_eq, hcard]
      push_cast
      ring
    have hnn : ∀ x ∈ (Finset.univ : Finset (Fin hyp.q × Fin hyp.p)),
        (0 : ℤ) ≤ (m x.1 x.2) ^ 2 - 1 := fun x _ => by linarith [hge1 x]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
    intro x
    have hx := hall x (Finset.mem_univ x)
    linarith
  have hpm : ∀ i j, m i j = 1 ∨ m i j = -1 := by
    intro i j
    have hfac : (m i j - 1) * (m i j + 1) = 0 := by nlinarith [heach (i, j)]
    rcases mul_eq_zero.mp hfac with h | h
    · left; linarith
    · right; linarith
  have hYY_zero : (ClassFunction.inner Y Y).re = 0 := by
    have hres' : (S : ℝ) + (ClassFunction.inner Y Y).re <=
        ((data.h78 hG).complementIndex : ℝ) := by
      rw [hS]
      simpa [hY, hphi] using hres
    have hcast : (S : ℝ) = ((data.h78 hG).complementIndex : ℝ) := by
      rw [hsum_eq, heq]
      norm_cast
    linarith
  have hY_zero : Y = 0 :=
    OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero hYY_zero
  refine ⟨heq, hpm, ?_⟩
  exact sub_eq_zero.mp (by simpa [hY] using hY_zero)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2), unit norm of the removed character.**
Let `X = Σ m_ij eta_ij` be the rigid signed grid projection and
`chi = X - beta`.  If every `m_ij` is `+1` or `-1`, the complement index is
`p*q`, and `m_ij = ⟨beta, eta_ij⟩`, then orthonormality gives
`⟨X,X⟩ = ⟨beta,X⟩ = ⟨X,beta⟩ = p*q`.  The Dade source-norm
evaluation gives `⟨beta,beta⟩ = p*q + 1`, hence `⟨chi,chi⟩ = 1`.

This is the norm-one input used to classify `chi` as the coherent image of
the distinguished character or the negative image of its conjugate. -/
theorem etaGrid_projection_sub_beta_norm_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hpm : ∀ i j, m i j = 1 ∨ m i j = -1)
    (heq : (data.h78 hG).complementIndex = hyp.p * hyp.q)
    (hcoeff : ∀ i j,
      ClassFunction.inner (data.h78 hG).beta (hyp.eta i j) = (m i j : ℂ)) :
    ClassFunction.inner
        (etaGridProjection hyp m - (data.h78 hG).beta)
        (etaGridProjection hyp m - (data.h78 hG).beta) = 1 := by
  classical
  haveI := data.kernelIn_normal
  set H78 := data.h78 hG with hH78
  set X : ClassFunction G ℂ := etaGridProjection hyp m with hX
  set S : ℤ := ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 with hS
  have hsquare : ∀ i j, (m i j) ^ 2 = 1 := by
    intro i j
    rcases hpm i j with h | h <;> rw [h] <;> norm_num
  have hsum : S = (hyp.p * hyp.q : ℕ) := by
    rw [hS]
    simp_rw [hsquare]
    simp [Nat.mul_comm]
  have hXeta : ∀ (k : Fin hyp.q) (l : Fin hyp.p),
      ClassFunction.inner X (hyp.eta k l) = (m k l : ℂ) := by
    intro k l
    rw [hX, etaGridProjection, inner_sum_left]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => ?_)]
    · rw [inner_sum_left,
        Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => ?_)]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_pos ⟨rfl, rfl⟩, mul_one]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_neg (by rintro ⟨-, rfl⟩; exact hjl rfl), mul_zero]
    · rw [inner_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
        if_neg (by rintro ⟨rfl, -⟩; exact hik rfl), mul_zero]
  have hsum_sq : ∀ psi : ClassFunction G ℂ,
      (∀ (k : Fin hyp.q) (l : Fin hyp.p),
        ClassFunction.inner psi (hyp.eta k l) = (m k l : ℂ)) →
      ClassFunction.inner psi X = (S : ℂ) := by
    intro psi hpsi
    rw [hX, etaGridProjection, inner_sum_right, hS]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hpsi i j, star_intCast]
    ring
  have hXX : ClassFunction.inner X X = (S : ℂ) := hsum_sq X hXeta
  have hbetaX : ClassFunction.inner H78.beta X = (S : ℂ) := by
    apply hsum_sq H78.beta
    simpa [hH78] using hcoeff
  have hXbeta : ClassFunction.inner X H78.beta = (S : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hbetaX, star_intCast]
  have hbetaRe := H78.betaNormSq_eq_complementIndex_add_one
    (data.sourceDiffNormEvaluation hG)
  change (ClassFunction.inner H78.beta H78.beta).re =
      (H78.complementIndex : ℝ) + 1 at hbetaRe
  have hbeta : ClassFunction.inner H78.beta H78.beta =
      (((H78.complementIndex : ℝ) + 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa using hbetaRe
    · rw [OddOrder.RepresentationTheory.inner_self_eq_realCast]
      simp
  change ClassFunction.inner (X - H78.beta) (X - H78.beta) = 1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hXX, hXbeta, hbetaX, hbeta]
  rw [hsum, heq]
  push_cast
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2), classification of the removed unit-norm character.**
Let `X` be an integral `eta`-grid sum and `chi = X - beta`.  If every coherent family image is
orthogonal to the grid and `chi` has norm one, then `chi` is the distinguished coherent image or
the negative coherent image of its conjugate.  The proof pairs `chi` with the orthonormal
conjugate pair.  The (7.8.a) decomposition gives pairings `a - 1` and `a` against `beta`, so their
difference pairs with `chi` as one; norm-one rigidity in `Z[Irr G]` then gives the two alternatives.
-/
theorem etaGrid_projection_sub_beta_classification [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (heta : ∀ (t : Fin (data.n + 1)), t ≠ data.ind1H →
      ∀ i j, ClassFunction.inner
        ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta t)) (hyp.eta i j) = 0)
    (hchi1 : ClassFunction.inner
      (etaGridProjection hyp m - (data.h78 hG).beta)
      (etaGridProjection hyp m - (data.h78 hG).beta) = 1) :
    let χ := etaGridProjection hyp m - (data.h78 hG).beta
    χ = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) ∨
    χ = -((data.h78 hG).nu
      ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj) := by
  classical
  letI := data.kernelIn_normal
  let H78 := data.h78 hG
  let A : ClassFunction G ℂ := H78.nu (H78.hyp76.zeta H78.zetaDistinct)
  obtain ⟨j₁, hj₁ne, hj₁⟩ := data.exists_conjIndex hG
  let B : ClassFunction G ℂ := H78.nu (H78.hyp76.zeta j₁)
  let X : ClassFunction G ℂ := etaGridProjection hyp m
  let χ : ClassFunction G ℂ := X - H78.beta
  let BD := data.betaDecomp hG
  have hzd_ne : H78.zetaDistinct ≠ data.ind1H := by
    rw [← data.h78_ind1H_eq hG]
    exact H78.zetaDistinct_ne_ind1H
  have hj₁ne_data : j₁ ≠ data.ind1H := by
    rw [← data.h78_ind1H_eq hG]
    exact hj₁ne
  have hAZ : A ∈ ZIrr G := by
    change H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G
    exact H78.nu_zetaDistinct_mem_ZIrr_of_isCoherent
      (data.isCoherentSourceSet hG) rfl
  have hBZ : B ∈ ZIrr G := by
    change H78.nu (H78.hyp76.zeta j₁) ∈ ZIrr G
    exact H78.nu_zeta_mem_ZIrr_of_isCoherent
      (data.isCoherentSourceSet hG) rfl hj₁ne
  have hA1 : ClassFunction.inner A A = 1 := by
    change ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1
    exact data.nu_zeta_norm_one hG H78.zetaDistinct_ne_ind1H
  have hB1 : ClassFunction.inner B B = 1 := by
    change ClassFunction.inner (H78.nu (H78.hyp76.zeta j₁))
      (H78.nu (H78.hyp76.zeta j₁)) = 1
    exact data.nu_zeta_norm_one hG hj₁ne
  have hAB : ClassFunction.inner A B = 0 := by
    change ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (H78.nu (H78.hyp76.zeta j₁)) = 0
    exact data.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hzd_ne hj₁ne hj₁
  have hXZ : X ∈ ZIrr G := by
    change etaGridProjection hyp m ∈ ZIrr G
    rw [etaGridProjection]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    rw [Int.cast_smul_eq_zsmul]
    exact (ZIrr G).smul_mem (m i j) (eta_mem_ZIrr hyp i j)
  have hbetaZ : H78.beta ∈ ZIrr G :=
    H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (data.h78_ind_mem_ZIrr hG) (data.h78_zeta_irreducible hG)
  have hchiZ : χ ∈ ZIrr G := Submodule.sub_mem (ZIrr G) hXZ hbetaZ
  have hchi1' : ClassFunction.inner χ χ = 1 := by
    change ClassFunction.inner (etaGridProjection hyp m - H78.beta)
      (etaGridProjection hyp m - H78.beta) = 1
    exact hchi1
  have hAX : ClassFunction.inner A X = 0 := by
    change ClassFunction.inner A (etaGridProjection hyp m) = 0
    rw [etaGridProjection, inner_sum_right]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_sum_right]
    apply Finset.sum_eq_zero
    intro j _
    rw [ClassFunction.inner_smul_right,
      heta H78.zetaDistinct hzd_ne i j, mul_zero]
  have hBX : ClassFunction.inner B X = 0 := by
    change ClassFunction.inner B (etaGridProjection hyp m) = 0
    rw [etaGridProjection, inner_sum_right]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_sum_right]
    apply Finset.sum_eq_zero
    intro j _
    rw [ClassFunction.inner_smul_right, heta j₁ hj₁ne_data i j, mul_zero]
  have hsource_orth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0 := by
    intro i j hij
    rw [data.h78_zeta_eq hG, data.h78_zeta_eq hG]
    exact (induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj) i j hij
  have hsource_nonzero : ∀ i : Fin (H78.hyp76.n + 1),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 := by
    intro i
    rw [data.h78_zeta_eq hG]
    exact induce_norm_ne_zero data.kernelIn (data.θ i)
  have hzeta0_ne : H78.hyp76.zeta 0 (1 : ↥L) ≠ 0 := by
    obtain ⟨θ0, hθ0⟩ := H78.hyp76.zeta_induced 0
    rw [hθ0]
    exact induce_apply_one_ne_zero _ θ0
  have hzd0 : H78.zetaDistinct = 0 := data.h78_zetaDistinct_eq hG
  have hconj_degree : H78.hyp76.zeta j₁ (1 : ↥L) =
      H78.hyp76.zeta 0 (1 : ↥L) := by
    rw [hj₁, ClassFunction.conj_apply, hzd0, data.h78_zeta_eq hG]
    exact induce_apply_one_star data.kernelIn (data.θ 0)
  have hWA : ClassFunction.inner H78.weightedNuSum A = 1 := by
    have h := inner_weightedNuSum_nu_gen H78.hyp76.zeta hsource_orth
      hsource_nonzero hzeta0_ne H78.nu H78.nu_isometry
      (j := H78.zetaDistinct) H78.zetaDistinct_ne_ind1H
    rw [hzd0] at h
    change ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1
    rw [Hypothesis78.weightedNuSum, hzd0, h, div_self hzeta0_ne]
  have hWB : ClassFunction.inner H78.weightedNuSum B = 1 := by
    have h := inner_weightedNuSum_nu_gen H78.hyp76.zeta hsource_orth
      hsource_nonzero hzeta0_ne H78.nu H78.nu_isometry (j := j₁) hj₁ne
    change ClassFunction.inner H78.weightedNuSum (H78.nu (H78.hyp76.zeta j₁)) = 1
    rw [Hypothesis78.weightedNuSum, hzd0, h, hconj_degree, div_self hzeta0_ne]
  have hOneA : ClassFunction.inner (Hypothesis71.constOne G) A = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    change star (ClassFunction.inner
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) (Hypothesis71.constOne G)) = 0
    rw [BD.orth_one H78.zetaDistinct H78.zetaDistinct_ne_ind1H, star_zero]
  have hOneB : ClassFunction.inner (Hypothesis71.constOne G) B = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    change star (ClassFunction.inner
      (H78.nu (H78.hyp76.zeta j₁)) (Hypothesis71.constOne G)) = 0
    rw [BD.orth_one j₁ hj₁ne, star_zero]
  have hGammaA : ClassFunction.inner BD.Gamma A = 0 := by
    change ClassFunction.inner BD.Gamma
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0
    exact BD.Gamma_orth_nu H78.zetaDistinct H78.zetaDistinct_ne_ind1H
  have hGammaB : ClassFunction.inner BD.Gamma B = 0 := by
    change ClassFunction.inner BD.Gamma (H78.nu (H78.hyp76.zeta j₁)) = 0
    exact BD.Gamma_orth_nu j₁ hj₁ne
  have hbetaA : ClassFunction.inner H78.beta A = (BD.a : ℂ) - 1 := by
    rw [BD.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
      ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      hOneA, hA1, hWA, hGammaA]
    ring
  have hbetaB : ClassFunction.inner H78.beta B = (BD.a : ℂ) := by
    rw [BD.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
      ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      hOneB, hAB, hWB, hGammaB]
    ring
  have hbetaBA : ClassFunction.inner H78.beta (B - A) = 1 := by
    rw [ClassFunction.inner_sub_right, hbetaB, hbetaA]
    ring
  have hABbeta : ClassFunction.inner (A - B) H78.beta = -1 := by
    have hBA : ClassFunction.inner (B - A) H78.beta = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hbetaBA, star_one]
    rw [show A - B = -(B - A) by abel, ClassFunction.inner_neg_left, hBA]
  have hpair : ClassFunction.inner (A - B) χ = 1 := by
    change ClassFunction.inner (A - B) (X - H78.beta) = 1
    rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left,
      hAX, hBX, sub_zero, hABbeta]
    norm_num
  have hclass := eq_left_or_neg_right_of_inner_sub_eq_one
    hAZ hBZ hchiZ hA1 hB1 hchi1' hAB hpair
  have hBconj : B = H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj := by
    change H78.nu (H78.hyp76.zeta j₁) =
      H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj
    exact congrArg H78.nu hj₁
  simpa [χ, X, A, B, H78, hBconj] using hclass

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16
