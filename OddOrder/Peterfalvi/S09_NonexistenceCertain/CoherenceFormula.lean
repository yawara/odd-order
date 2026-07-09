import OddOrder.Peterfalvi.S09_NonexistenceCertain.QuadraticTerm

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S09_NonexistenceCertain.CoherenceFormula` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S09
open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open OddOrder.GroupTheory (IsTISubset)
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]


section Section_7_8
namespace Hypothesis78
variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype L]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

set_option linter.style.longLine false
set_option linter.style.longLine true


/-- Arithmetic core of Peterfalvi (7.8.b): if `2e + 1 ≤ h`, then the
quadratic correction `u a² - 2 v a` is nonnegative for every integer `a`, where
`u = (1/e)(1 - 1/h)` and `v = 1/h`. -/
lemma quadraticTerm_nonneg_of_smallIndex {e h : ℝ} (a : ℤ)
    (he : 0 < e) (hsmall : 2 * e + 1 ≤ h) :
    0 ≤ (1 / e) * (1 - 1 / h) * (a : ℝ) ^ 2 - 2 * (1 / h) * (a : ℝ) := by
  have hh_pos : 0 < h := by linarith
  have he_ne : e ≠ 0 := ne_of_gt he
  have hh_ne : h ≠ 0 := ne_of_gt hh_pos
  have hsmall' : 2 * e ≤ h - 1 := by linarith
  have hu_eq : (1 / e) * (1 - 1 / h) = (h - 1) / (e * h) := by
    field_simp [he_ne, hh_ne]
  have hkey : 2 * (1 / h) ≤ (1 / e) * (1 - 1 / h) := by
    rw [hu_eq]
    rw [show 2 * (1 / h) = 2 / h by ring]
    rw [div_le_div_iff₀ hh_pos (mul_pos he hh_pos)]
    nlinarith
  have hv_nonneg : 0 ≤ 2 * (1 / h) := by
    rw [one_div]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hh_pos.le)
  have hu_nonneg : 0 ≤ (1 / e) * (1 - 1 / h) := le_trans hv_nonneg hkey
  by_cases ha_nonpos_int : a ≤ 0
  · have ha_nonpos : (a : ℝ) ≤ 0 := by exact_mod_cast ha_nonpos_int
    have hsq_nonneg : 0 ≤ (a : ℝ) ^ 2 := sq_nonneg _
    have hterm1 : 0 ≤ (1 / e) * (1 - 1 / h) * (a : ℝ) ^ 2 :=
      mul_nonneg hu_nonneg hsq_nonneg
    have hprod_nonpos : 2 * (1 / h) * (a : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hv_nonneg ha_nonpos
    nlinarith
  · have ha_ge_one_int : 1 ≤ a := by omega
    have ha_ge_one : (1 : ℝ) ≤ a := by exact_mod_cast ha_ge_one_int
    have ha_nonneg : 0 ≤ (a : ℝ) := by linarith
    have ha_sq_ge : (a : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
    have hmul1 : 2 * (1 / h) * (a : ℝ) ≤
        ((1 / e) * (1 - 1 / h)) * (a : ℝ) :=
      mul_le_mul_of_nonneg_right hkey ha_nonneg
    have hmul2 : ((1 / e) * (1 - 1 / h)) * (a : ℝ) ≤
        ((1 / e) * (1 - 1 / h)) * (a : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left ha_sq_ge hu_nonneg
    nlinarith

/-- **Peterfalvi (7.8.b) target.**  Under `2e + 1 ≤ h`, the coherent
`ζ`-image satisfies `‖(ζ^ν)^ρ‖² ≥ 1 - e/h`, and the residual term from
(7.8.a) satisfies `‖Γ‖² ≤ e - 1`.

As with `BetaDecomp`, this is a standalone future-proof target rather than a
new field of `Hypothesis78`. -/
structure NormEstimates (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : Prop where
  /-- `‖(ζ^ν)^ρ‖² ≥ 1 - e/h`. -/
  zetaNuRho_norm_sq_ge :
    H78.smallIndex →
      1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
        H78.zetaNuRhoNormSq
  /-- `‖Γ‖² ≤ e - 1`. -/
  gamma_norm_sq_le :
    H78.smallIndex → H78.gammaNormSq hBD ≤ (H78.complementIndex : ℝ) - 1

/-- Raw class-function form of the `(ζ^ν)^ρ` lower bound supplied by
`NormEstimates`.  This is the input shape used by the later (7.5)/(7.10)
assembly, with `zetaNuRhoNormSq` unfolded. -/
theorem zetaNuRho_inner_self_re_ge_of_normEstimates
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hNE : H78.NormEstimates hBD) (hsmall : H78.smallIndex) :
    1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
      (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re := by
  simpa [zetaNuRhoNormSq] using hNE.zetaNuRho_norm_sq_ge hsmall

/-- Raw class-function form of the residual `Γ` upper bound supplied by
`NormEstimates`.  This is the `Γ` norm-bound shape consumed by the final
orthogonal-integer decomposition bridge for (7.10). -/
theorem gamma_inner_self_re_le_of_normEstimates
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hNE : H78.NormEstimates hBD) (hsmall : H78.smallIndex) :
    (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤
      (H78.complementIndex : ℝ) - 1 := by
  simpa [gammaNormSq] using hNE.gamma_norm_sq_le hsmall

/-- Under `2e + 1 ≤ h`, Peterfalvi's quadratic correction is nonnegative. -/
theorem normQuadraticCorrection_nonneg_of_smallIndex
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    H78.smallIndex → 0 ≤ H78.normQuadraticCorrection hBD := by
  intro hsmall
  rw [normQuadraticCorrection]
  have he : 0 < (H78.complementIndex : ℝ) := by
    exact_mod_cast H78.complementIndex_pos
  exact quadraticTerm_nonneg_of_smallIndex hBD.a he (H78.smallIndex_real hsmall)

/-- If `(ζ^ν)^ρ` has Peterfalvi's quadratic norm formula, its lower bound follows. -/
theorem zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.smallIndex →
      1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
        H78.zetaNuRhoNormSq := by
  intro hsmall
  rw [hzeta]
  exact le_add_of_nonneg_left (H78.normQuadraticCorrection_nonneg_of_smallIndex hBD hsmall)

/-- If `Γ` has Peterfalvi's residual norm formula, its upper bound follows. -/
theorem gammaNormSq_le_of_normQuadraticCorrection_eq
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hgamma : H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD) :
    H78.smallIndex → H78.gammaNormSq hBD ≤ (H78.complementIndex : ℝ) - 1 := by
  intro hsmall
  rw [hgamma]
  have hh_nonneg : 0 ≤ (H78.kernelOrder : ℝ) := by positivity
  have hquad := H78.normQuadraticCorrection_nonneg_of_smallIndex hBD hsmall
  have hprod : 0 ≤ (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD :=
    mul_nonneg hh_nonneg hquad
  linarith

/-- Exact quadratic norm formulas are enough to package Peterfalvi (7.8.b)'s
`NormEstimates`.  This isolates the remaining character-theoretic work to proving
those two formulas from (7.7.b), `BetaDecomp`, and `‖β‖² = e + 1`. -/
theorem normEstimates_of_normQuadraticCorrection_eqs
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hgamma : H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD) :
    H78.NormEstimates hBD where
  zetaNuRho_norm_sq_ge :=
    H78.zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq hBD hzeta
  gamma_norm_sq_le :=
    H78.gammaNormSq_le_of_normQuadraticCorrection_eq hBD hgamma

/-- Once the orthogonal expansion of `‖β‖²` is known, the residual norm formula
for `Γ` is just the arithmetic rearrangement in Peterfalvi (7.8.b). -/
theorem gammaNormSq_eq_of_betaNormSq_expand
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hbetaNorm : H78.betaNormSq = (H78.complementIndex : ℝ) + 1)
    (hexpand : H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD) :
    H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD := by
  have hh_ne : (H78.kernelOrder : ℝ) ≠ 0 := by
    exact_mod_cast H78.kernelOrder_pos.ne'
  have he_ne : (H78.complementIndex : ℝ) ≠ 0 := by
    exact_mod_cast H78.complementIndex_pos.ne'
  rw [hbetaNorm] at hexpand
  have hquad :
      (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD =
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) := by
    rw [normQuadraticCorrection]
    field_simp [hh_ne, he_ne]
  rw [hquad]
  linarith

/-- The distinguished `νζ` is orthogonal to `1_G`, in the displayed direction. -/
theorem zetaImage_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (Hypothesis71.constOne G) = 0 :=
  hBD.orth_one H78.zetaDistinct H78.zetaDistinct_ne_ind1H

/-- Hermitian-symmetric form of `zetaImage_orth_one`. -/
theorem constOne_orth_zetaImage (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G)
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.zetaImage_orth_one hBD, star_zero]

/-- The residual `Γ` is orthogonal to the distinguished `νζ`, in the displayed direction. -/
theorem gamma_orth_zetaImage (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner hBD.Gamma (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0 :=
  hBD.Gamma_orth_nu H78.zetaDistinct H78.zetaDistinct_ne_ind1H

/-- Hermitian-symmetric form of `gamma_orth_zetaImage`. -/
theorem zetaImage_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.gamma_orth_zetaImage hBD, star_zero]

/-- Hermitian-symmetric form of `BetaDecomp.Gamma_orth_one`. -/
theorem constOne_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, hBD.Gamma_orth_one, star_zero]

/-- Each coherent image in `S^ν` is orthogonal to `Γ`, in the opposite direction. -/
theorem nu_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (i : Fin (H78.hyp76.n + 1)) (hi : i ≠ H78.ind1H) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i)) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, hBD.Gamma_orth_nu i hi, star_zero]

/-- The weighted `S^ν`-sum is orthogonal to `1_G`. -/
theorem weightedNuSum_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.weightedNuSum (Hypothesis71.constOne G) = 0 := by
  classical
  rw [weightedNuSum, inner_sum_left]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi_ne : i ≠ H78.ind1H := (Finset.mem_erase.mp hi).1
  rw [ClassFunction.inner_smul_left, hBD.orth_one i hi_ne, mul_zero]

/-- Hermitian-symmetric form of `weightedNuSum_orth_one`. -/
theorem constOne_orth_weightedNuSum
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) H78.weightedNuSum = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.weightedNuSum_orth_one hBD, star_zero]

/-- The weighted `S^ν`-sum is orthogonal to the residual `Γ`. -/
theorem weightedNuSum_orth_gamma
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.weightedNuSum hBD.Gamma = 0 := by
  classical
  rw [weightedNuSum, inner_sum_left]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi_ne : i ≠ H78.ind1H := (Finset.mem_erase.mp hi).1
  rw [ClassFunction.inner_smul_left, H78.nu_orth_gamma hBD i hi_ne, mul_zero]

/-- Hermitian-symmetric form of `weightedNuSum_orth_gamma`. -/
theorem gamma_orth_weightedNuSum
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner hBD.Gamma H78.weightedNuSum = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.weightedNuSum_orth_gamma hBD, star_zero]

/-- `BetaDecomp` identifies the (7.9) residual `Δ` with the weighted part plus
`Γ`. -/
theorem delta_eq_weightedNuSum_add_gamma
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    H78.delta = (hBD.a : ℂ) • H78.weightedNuSum + hBD.Gamma := by
  rw [delta, hBD.beta_eq]
  abel

/-- The residual `Δ` is orthogonal to `1_G`. -/
theorem delta_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.delta (Hypothesis71.constOne G) = 0 := by
  rw [H78.delta_eq_weightedNuSum_add_gamma hBD, ClassFunction.inner_add_left,
    ClassFunction.inner_smul_left, H78.weightedNuSum_orth_one hBD,
    hBD.Gamma_orth_one, mul_zero, add_zero]

/-- Hermitian-symmetric form of `delta_orth_one`. -/
theorem constOne_orth_delta (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) H78.delta = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.delta_orth_one hBD, star_zero]

/-- Orthogonal expansion of the beta decomposition in Peterfalvi (7.8.a).

After the remaining source-side computation of `‖Σ‖² = (h - 1)/e`, the displayed
decomposition of `β` gives the real norm formula used in (7.8.b). -/
theorem betaNormSq_eq_of_weightedNuSum_norm
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta_norm :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted_zeta :
      ClassFunction.inner H78.weightedNuSum
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted_norm :
      ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
        ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ)) :
    H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD := by
  have hzeta_weighted :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        H78.weightedNuSum = 1 := by
    rw [Hypothesis71.ClassFunction.inner_symm, hweighted_zeta, star_one]
  have hinner :
      ClassFunction.inner H78.beta H78.beta =
        2 +
          (hBD.a : ℂ) * (hBD.a : ℂ) *
            ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ) -
          2 * (hBD.a : ℂ) +
          ClassFunction.inner hBD.Gamma hBD.Gamma := by
    rw [hBD.beta_eq]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      Hypothesis71.constOne_inner_self_eq_one, H78.zetaImage_orth_one hBD,
      H78.constOne_orth_zetaImage hBD, H78.weightedNuSum_orth_one hBD,
      H78.constOne_orth_weightedNuSum hBD, hBD.Gamma_orth_one,
      H78.constOne_orth_gamma hBD, H78.gamma_orth_zetaImage hBD,
      H78.zetaImage_orth_gamma hBD, H78.weightedNuSum_orth_gamma hBD,
      H78.gamma_orth_weightedNuSum hBD, hzeta_norm, hweighted_zeta, hzeta_weighted,
      hweighted_norm, star_intCast, mul_zero, add_zero, sub_zero, zero_add]
    ring
  rw [betaNormSq, hinner, gammaNormSq]
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- Any indexed coherent image `νζᵢ` has norm one once the source `ζᵢ` does. -/
theorem nu_zeta_inner_self_eq_one (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
        (H78.nu (H78.hyp76.zeta i)) = 1 := by
  rw [H78.nu_isometry i i hi hi, hzeta_norm]

/-- Any indexed coherent image `νζᵢ` has norm one once the source `ζᵢ` is irreducible. -/
theorem nu_zeta_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
        (H78.nu (H78.hyp76.zeta i)) = 1 :=
  H78.nu_zeta_inner_self_eq_one hi
    (H78.zeta_inner_self_eq_one_of_irreducible hzeta_irr)

/-- The distinguished image `νζ` has norm one once the source `ζ` has norm one. -/
theorem zetaImage_inner_self_eq_one (H78 : Hypothesis78 G A L)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
  H78.nu_zeta_inner_self_eq_one H78.zetaDistinct_ne_ind1H hzeta_norm

/-- The source irreducibility of the distinguished `ζ` gives `‖νζ‖² = 1`. -/
theorem zetaImage_inner_self_eq_one_of_irreducible (H78 : Hypothesis78 G A L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
  H78.nu_zeta_inner_self_eq_one_of_irreducible H78.zetaDistinct_ne_ind1H hzeta_irr

/-- Coherence makes an indexed image `νζᵢ` a signed irreducible character once
the source `ζᵢ` is irreducible.  This records exactly the sign ambiguity left by
the virtual-character norm-one criterion. -/
theorem exists_zsmul_irreducibleCharacter_nu_zeta_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ∃ (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
        H78.nu (H78.hyp76.zeta i) = ε • (ξ : ClassFunction G ℂ) :=
  OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one
    (H78.nu_zeta_mem_ZIrr_of_isCoherent hcoh hnu hi)
    (H78.nu_zeta_inner_self_eq_one_of_irreducible hi hzeta_irr)

/-- Distinguished-`ζ` specialization of the signed image criterion. -/
theorem exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ∃ (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
        H78.nu (H78.hyp76.zeta H78.zetaDistinct) = ε • (ξ : ClassFunction G ℂ) :=
  H78.exists_zsmul_irreducibleCharacter_nu_zeta_of_isCoherent hcoh hnu
    H78.zetaDistinct_ne_ind1H hzeta_irr

/-- If the coherent image `νζᵢ` has positive degree, the signed ambiguity collapses
and `νζᵢ` is an irreducible character. -/
theorem nu_zeta_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hpos : ∃ d : ℕ, 0 < d ∧
      (H78.nu (H78.hyp76.zeta i) : G → ℂ) 1 = (d : ℂ)) :
    IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta i)) :=
  OddOrder.RepresentationTheory.isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos
    (H78.nu_zeta_mem_ZIrr_of_isCoherent hcoh hnu hi)
    (H78.nu_zeta_inner_self_eq_one_of_irreducible hi hzeta_irr)
    hpos

/-- Distinguished-`ζ` specialization of the positive-degree image criterion. -/
theorem zetaImage_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    (hpos : ∃ d : ℕ, 0 < d ∧
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct) : G → ℂ) 1 = (d : ℂ)) :
    IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) :=
  H78.nu_zeta_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos hcoh hnu
    H78.zetaDistinct_ne_ind1H hzeta_irr hpos

/-- Irreducibility and distinctness of the source `S`-family give its
orthogonality matrix. -/
theorem sourceZeta_orthogonal_of_irreducible_distinct (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0 := by
  intro i hi j hj
  by_cases hij : i = j
  · rw [if_pos hij, hij]
  · rw [if_neg hij]
    let χ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
      ⟨H78.hyp76.zeta i, hirr i hi⟩
    let ψ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
      ⟨H78.hyp76.zeta j, hirr j hj⟩
    have hne : χ ≠ ψ := by
      intro hχψ
      exact hdistinct i hi j hj hij (congrArg
        (fun θ : OddOrder.RepresentationTheory.IrreducibleCharacter L =>
          (θ : ClassFunction L ℂ)) hχψ)
    simpa [χ, ψ, hne] using
      (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite χ ψ)

/-- Natural distinguished-column form of the source `S` orthogonality matrix. -/
theorem sourceZeta_inner_zetaDistinct_eq_ite_of_irreducible_distinct
    (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i)
        (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0 := by
  intro i hi
  have hzeta_mem : H78.zetaDistinct ∈ (Finset.univ.erase H78.ind1H) := by
    simp [H78.zetaDistinct_ne_ind1H]
  have horth := H78.sourceZeta_orthogonal_of_irreducible_distinct hirr hdistinct
  have hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1 :=
    H78.zetaDistinct_inner_self_eq_one_of_irreducible
      (hirr H78.zetaDistinct hzeta_mem)
  rw [horth i hi H78.zetaDistinct hzeta_mem]
  by_cases hiz : i = H78.zetaDistinct
  · subst i
    rw [if_pos rfl, if_pos rfl]
    exact hzeta_norm
  · simp [hiz]

/-- Irreducibility of the source `S`-family makes every source norm nonzero. -/
theorem sourceZeta_norm_ne_of_irreducible (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i)) :
    ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 := by
  intro i hi
  let χ : OddOrder.RepresentationTheory.IrreducibleCharacter L :=
    ⟨H78.hyp76.zeta i, hirr i hi⟩
  have hχ : ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1 := by
    simpa [χ] using
      (OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite χ χ)
  rw [hχ]
  norm_num

/-- If the source `ζ_i` are orthogonal to the distinguished `ζ`, the weighted
`S^ν`-sum has inner product `1` with `νζ`.

This is the coefficient computation in Peterfalvi (7.8.a) that feeds the
`(β, ζ^ν) = a - 1` identity used in (7.8.b). -/
theorem weightedNuSum_inner_zetaImage_eq_one (H78 : Hypothesis78 G A L)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0)
    (hzeta_one_ne_zero : H78.hyp76.zeta H78.zetaDistinct (1 : L) ≠ 0) :
    ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  have hzeta_mem : H78.zetaDistinct ∈ s := by
    simp [hs, H78.zetaDistinct_ne_ind1H]
  rw [weightedNuSum, ← hs, inner_sum_left]
  have hsum :
      (∑ i ∈ s,
        ClassFunction.inner
          ((H78.hyp76.zeta i (1 : L) /
            (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
              ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))) •
            H78.nu (H78.hyp76.zeta i))
          (H78.nu (H78.hyp76.zeta H78.zetaDistinct))) =
        ∑ i ∈ s,
          if i = H78.zetaDistinct then
            H78.hyp76.zeta i (1 : L) /
              (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
                ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
          else 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ClassFunction.inner_smul_left,
      H78.nu_isometry i H78.zetaDistinct (Finset.ne_of_mem_erase (hs ▸ hi))
        H78.zetaDistinct_ne_ind1H, horth i hi]
    by_cases hiz : i = H78.zetaDistinct
    · rw [if_pos hiz, if_pos hiz, mul_one]
    · rw [if_neg hiz, if_neg hiz, mul_zero]
  rw [hsum, Finset.sum_ite_eq' s H78.zetaDistinct
    (fun i =>
      H78.hyp76.zeta i (1 : L) /
        (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))),
    if_pos hzeta_mem, horth H78.zetaDistinct hzeta_mem]
  rw [if_pos rfl]
  field_simp [hzeta_one_ne_zero]

/-- Natural source-data version of `weightedNuSum_inner_zetaImage_eq_one`. -/
theorem weightedNuSum_inner_zetaImage_eq_one_of_irreducible_source_data
    (H78 : Hypothesis78 G A L)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ)) :
    ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
  H78.weightedNuSum_inner_zetaImage_eq_one
    (H78.sourceZeta_inner_zetaDistinct_eq_ite_of_irreducible_distinct
      hirr hdistinct)
    (by
      rw [hzeta_degree]
      exact_mod_cast H78.complementIndex_pos.ne')

/-- Source orthogonality and the Burnside degree sum evaluate the norm of the
weighted `S^ν`-sum in Peterfalvi (7.8.a).

This is the source-side computation of `‖Σ‖² = (h - 1) / e`: after `ν` transports
orthogonality from `L` to `G`, only diagonal terms remain, and the degree sum
collapses to the non-principal part of the kernel. -/
theorem weightedNuSum_inner_self_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ)) :
    ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
      ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ) := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  let coeff : Fin (H78.hyp76.n + 1) → ℂ := fun i =>
    H78.hyp76.zeta i (1 : L) /
      (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
  have he_ne : (H78.complementIndex : ℂ) ≠ 0 := by
    exact_mod_cast H78.complementIndex_pos.ne'
  have hinner :
      ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
        ∑ i ∈ s, ∑ j ∈ s,
          coeff i * star (coeff j) *
            ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
              (H78.nu (H78.hyp76.zeta j)) := by
    rw [weightedNuSum, ← hs]
    change ClassFunction.inner
        (∑ i ∈ s, coeff i • H78.nu (H78.hyp76.zeta i))
        (∑ i ∈ s, coeff i • H78.nu (H78.hyp76.zeta i)) = _
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    ring
  have hcollapse :
      (∑ i ∈ s, ∑ j ∈ s,
        coeff i * star (coeff j) *
          ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
            (H78.nu (H78.hyp76.zeta j))) =
        ∑ i ∈ s,
          coeff i * star (coeff i) *
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hine : i ≠ H78.ind1H := Finset.ne_of_mem_erase (hs ▸ hi)
    rw [Finset.sum_eq_single i]
    · rw [H78.nu_isometry i i hine hine,
        horth i (by simpa [hs] using hi) i (by simpa [hs] using hi), if_pos rfl]
    · intro j hj hji
      rw [H78.nu_isometry i j hine (Finset.ne_of_mem_erase (hs ▸ hj)),
        horth i (by simpa [hs] using hi) j (by simpa [hs] using hj),
        if_neg (Ne.symm hji), mul_zero]
    · intro hnot
      exact False.elim (hnot hi)
  have hdiag :
      (∑ i ∈ s,
        coeff i * star (coeff i) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        (∑ i ∈ s,
          H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) /
          (H78.complementIndex : ℂ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn_star :
        star (ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) :=
      Hypothesis71.ClassFunction.star_inner_self _
    have hn_ne : ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 :=
      hnorm_ne i (by simpa [hs] using hi)
    simp only [coeff, hzeta_degree]
    rw [star_div₀, star_mul', hn_star]
    simp only [star_natCast]
    field_simp [he_ne, hn_ne]
  rw [hinner, hcollapse, hdiag, show
      (∑ i ∈ s,
          H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) from by
        simpa [hs] using hdegree_sum]
  field_simp [he_ne]
  norm_num [Complex.ofReal_div, Complex.ofReal_sub]
  ring

/-- Source orthogonality and the kernel degree sum give the full orthogonal
expansion of `‖β‖²` in Peterfalvi (7.8.b). -/
theorem betaNormSq_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  have hzeta_mem : H78.zetaDistinct ∈ s := by
    simp [hs, H78.zetaDistinct_ne_ind1H]
  have hzeta_src_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1 :=
    H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr
  have horth_zeta : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0 := by
    intro i hi
    have hi_s : i ∈ s := by simpa [hs] using hi
    rw [horth i hi H78.zetaDistinct (by simpa [hs] using hzeta_mem)]
    by_cases hiz : i = H78.zetaDistinct
    · rw [if_pos hiz, if_pos hiz, hiz, hzeta_src_norm]
    · rw [if_neg hiz, if_neg hiz]
  have hzeta_one_ne_zero : H78.hyp76.zeta H78.zetaDistinct (1 : L) ≠ 0 := by
    rw [hzeta_degree]
    exact_mod_cast H78.complementIndex_pos.ne'
  exact H78.betaNormSq_eq_of_weightedNuSum_norm hBD
    (H78.zetaImage_inner_self_eq_one hzeta_src_norm)
    (H78.weightedNuSum_inner_zetaImage_eq_one horth_zeta hzeta_one_ne_zero)
    (H78.weightedNuSum_inner_self_eq_of_source_orthogonal
      horth hnorm_ne hzeta_degree hdegree_sum)

/-- Source-side beta norm data give Peterfalvi's residual norm formula for `Γ`. -/
theorem gammaNormSq_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.gammaNormSq hBD =
      (H78.complementIndex : ℝ) - 1 -
        (H78.kernelOrder : ℝ) * H78.normQuadraticCorrection hBD :=
  H78.gammaNormSq_eq_of_betaNormSq_expand hBD
    (H78.betaNormSq_eq_complementIndex_add_one hsrc)
    (H78.betaNormSq_eq_of_source_orthogonal hBD
      horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr)

/-- Once the remaining `(ζ^ν)^ρ` quadratic formula is supplied, the source-side
beta norm data package Peterfalvi (7.8.b)'s `NormEstimates`. -/
theorem normEstimates_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD :=
  H78.normEstimates_of_normQuadraticCorrection_eqs hBD hzeta
    (H78.gammaNormSq_eq_of_source_orthogonal hBD hsrc
      horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr)

/-- Textbook `u,v,w` form of the `(ζ^ν)^ρ` norm rewrites to the internal
`normQuadraticCorrection + (1 - e / h)` form.

This is the arithmetic bridge from the (7.7.b) double-sum evaluation in
Peterfalvi (7.8.b), where
`u = (1/e)(1 - 1/h)`, `v = 1/h`, and `w = 1 - e/h`. -/
theorem zetaNuRhoNormSq_eq_normQuadraticCorrection_of_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)) := by
  rw [hzeta, normQuadraticCorrection]

/-- Source-side beta norm data plus the textbook `u,v,w` formula package
Peterfalvi (7.8.b)'s `NormEstimates`.

The remaining character-theoretic input is now exactly the (7.7.b) evaluation
of `‖(ζ^ν)^ρ‖²` in `u,v,w` form; this theorem performs the API conversion and
reuses the already proved source-side `Γ` norm formula. -/
theorem normEstimates_of_source_orthogonal_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD :=
  H78.normEstimates_of_source_orthogonal hBD hsrc
    horth hnorm_ne hzeta_degree hdegree_sum hzeta_irr
    (H78.zetaNuRhoNormSq_eq_normQuadraticCorrection_of_uv_formula hBD hzeta_uv)

/-- Version of `normEstimates_of_source_orthogonal` using the natural source
hypotheses that the `S`-family consists of distinct irreducible characters. -/
theorem normEstimates_of_irreducible_source_data
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD := by
  have hzeta_mem : H78.zetaDistinct ∈ (Finset.univ.erase H78.ind1H) := by
    simp [H78.zetaDistinct_ne_ind1H]
  exact H78.normEstimates_of_source_orthogonal hBD hsrc
    (H78.sourceZeta_orthogonal_of_irreducible_distinct hirr hdistinct)
    (H78.sourceZeta_norm_ne_of_irreducible hirr)
    hzeta_degree hdegree_sum (hirr H78.zetaDistinct hzeta_mem) hzeta

/-- Source irreducibility data plus the textbook `u,v,w` formula give
Peterfalvi (7.8.b)'s `NormEstimates`.

This is the natural source-data version of
`normEstimates_of_source_orthogonal_and_uv_formula`: it converts the `u,v,w`
formula to the internal quadratic-correction API and derives the source
orthogonality matrix from irreducibility and distinctness. -/
theorem normEstimates_of_irreducible_source_data_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hsrc : H78.SourceDiffNormEvaluation)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD :=
  H78.normEstimates_of_irreducible_source_data hBD hsrc hirr hdistinct
    hzeta_degree hdegree_sum
    (H78.zetaNuRhoNormSq_eq_normQuadraticCorrection_of_uv_formula hBD hzeta_uv)

/-- Source inner-product values, source irreducibility data, and the textbook
`u,v,w` formula give Peterfalvi (7.8.b)'s `NormEstimates`.

This removes the standalone `SourceDiffNormEvaluation` premise by using the
already isolated source computation
`‖Ind 1_H - ζ‖² = e + 1` from the three source-side inputs
`⟨Ind1H,Ind1H⟩ = e`, `⟨ζ,Ind1H⟩ = 0`, and irreducibility of `ζ`. -/
theorem normEstimates_of_inner_values_irreducible_source_data_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.NormEstimates hBD := by
  have hzeta_mem : H78.zetaDistinct ∈ (Finset.univ.erase H78.ind1H) := by
    simp [H78.zetaDistinct_ne_ind1H]
  exact H78.normEstimates_of_irreducible_source_data_and_uv_formula hBD
    (H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
      hind_norm hzeta_ind (hirr H78.zetaDistinct hzeta_mem))
    hirr hdistinct hzeta_degree hdegree_sum hzeta_uv

/-- Source inner-product values, source irreducibility data, and the textbook
`u,v,w` formula give the raw `(ζ^ν)^ρ` lower bound used downstream. -/
theorem zetaNuRho_inner_self_re_ge_of_inner_values_irreducible_source_data_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hsmall : H78.smallIndex) :
    1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
      (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re :=
  H78.zetaNuRho_inner_self_re_ge_of_normEstimates hBD
    (H78.normEstimates_of_inner_values_irreducible_source_data_and_uv_formula hBD
      hind_norm hzeta_ind hirr hdistinct hzeta_degree hdegree_sum hzeta_uv)
    hsmall

/-- Source inner-product values, source irreducibility data, and the textbook
`u,v,w` formula give the raw `Γ` norm-bound consumed by the (7.10)
orthogonal-integer decomposition bridge. -/
theorem gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hsmall : H78.smallIndex) :
    (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤
      (H78.complementIndex : ℝ) - 1 :=
  H78.gamma_inner_self_re_le_of_normEstimates hBD
    (H78.normEstimates_of_inner_values_irreducible_source_data_and_uv_formula hBD
      hind_norm hzeta_ind hirr hdistinct hzeta_degree hdegree_sum hzeta_uv)
    hsmall

/-- With the weighted-sum coefficient normalized, `BetaDecomp` gives
`(β, ζ^ν) = a - 1`. -/
theorem beta_inner_zetaImage_eq_int_sub_one_of_weighted
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzetaImage_norm :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted :
      ClassFunction.inner H78.weightedNuSum
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1) :
    ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
      (hBD.a : ℂ) - 1 := by
  rw [hBD.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    H78.constOne_orth_zetaImage hBD, hzetaImage_norm, hweighted,
    H78.gamma_orth_zetaImage hBD]
  ring

/-- Source-side orthogonality plus source irreducibility gives the coefficient
identity `(β, ζ^ν) = a - 1`. -/
theorem beta_inner_zetaImage_eq_int_sub_one
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0)
    (hzeta_one_ne_zero : H78.hyp76.zeta H78.zetaDistinct (1 : L) ≠ 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
      (hBD.a : ℂ) - 1 :=
  H78.beta_inner_zetaImage_eq_int_sub_one_of_weighted hBD
    (H78.zetaImage_inner_self_eq_one_of_irreducible hzeta_irr)
    (H78.weightedNuSum_inner_zetaImage_eq_one horth hzeta_one_ne_zero)

/-- Natural source-data version of `(β, ζ^ν) = a - 1`. -/
theorem beta_inner_zetaImage_eq_int_sub_one_of_irreducible_source_data
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ)) :
    ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
      (hBD.a : ℂ) - 1 :=
  H78.beta_inner_zetaImage_eq_int_sub_one hBD
    (H78.sourceZeta_inner_zetaDistinct_eq_ite_of_irreducible_distinct
      hirr hdistinct)
    (by
      rw [hzeta_degree]
      exact_mod_cast H78.complementIndex_pos.ne')
    (hirr H78.zetaDistinct (by simp [H78.zetaDistinct_ne_ind1H]))

/-- **Peterfalvi (7.8.c.i).**  For χ ∈ Irr G orthogonal to `S^ν` and `x ∈ A`,
`χ^ρ(x) = star (β, χ)_G`. -/
theorem chiRho_eq_inner_beta_on_A (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0)
    {x : L} (hx : (x : G) ∈ A) :
    H78.hyp76.hyp71.chiRho χ x = star (ClassFunction.inner H78.beta χ) := by
  rw [beta_def]
  exact H78.chiRho_eq_inner_beta χ hχ_irr hχ_orth hx

/-- **Peterfalvi (7.8.c.ii).**  For χ ∈ Irr G orthogonal to `S^ν`,
`‖χ^ρ‖² = (|A|/|L|) · (β, χ)_G · star (β, χ)_G`.

Proof: the inner-product `(χ^ρ, χ^ρ)_L = (1/|L|) Σ_{l : L} χ^ρ(l) · star (χ^ρ(l))`.
By (7.8.c.i), on `{l ∈ L | (l:G) ∈ A}` each summand equals
`star (β,χ) · (β,χ)`; off it the summand vanishes since `chiRho` is supported
on `A`.  The count of `l : L` with `(l : G) ∈ A` equals `|A|` since `A ⊆ L`
(by `Hypothesis71.card_supportInSubgroup_eq_card_A`). -/
theorem chiRho_norm_sq_eq_card_ratio_mul (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0) :
    ClassFunction.inner (H78.hyp76.hyp71.chiRhoCF χ) (H78.hyp76.hyp71.chiRhoCF χ) =
      ((Nat.card A : ℂ) / (Nat.card L : ℂ)) *
        (ClassFunction.inner H78.beta χ *
          star (ClassFunction.inner H78.beta χ)) := by
  classical
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, invOf_eq_inv,
      ClassFunction.innerSum]
  -- Pointwise: each summand is a constant on `{l | (l:G) ∈ A}` and zero off it.
  have hpt : ∀ l : L,
      H78.hyp76.hyp71.chiRhoCF χ l * star (H78.hyp76.hyp71.chiRhoCF χ l) =
        if (l : G) ∈ A then
          star (ClassFunction.inner H78.beta χ) *
            ClassFunction.inner H78.beta χ
        else 0 := by
    intro l
    rw [Hypothesis71.chiRhoCF_apply]
    by_cases hl : (l : G) ∈ A
    · rw [if_pos hl,
          H78.chiRho_eq_inner_beta_on_A χ hχ_irr hχ_orth hl, star_star]
    · rw [if_neg hl, H78.hyp76.hyp71.chiRho_of_not_mem χ hl, star_zero,
          mul_zero]
  -- Aggregate the pointwise rewrite, then convert the indicator sum to a count.
  rw [show ∑ l : L,
        H78.hyp76.hyp71.chiRhoCF χ l * star (H78.hyp76.hyp71.chiRhoCF χ l) =
      ∑ l : L,
        if (l : G) ∈ A then
          star (ClassFunction.inner H78.beta χ) *
            ClassFunction.inner H78.beta χ
        else 0 from
    Finset.sum_congr rfl (fun l _ => hpt l)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- The filter count equals `Nat.card A` via `card_supportInSubgroup_eq_card_A`.
  have hcard :
      ((Finset.univ.filter (fun l : L => (l : G) ∈ A)).card : ℂ) =
        (Nat.card A : ℂ) := by
    have hset_eq :
        Finset.univ.filter (fun l : L => (l : G) ∈ A) =
          (OddOrder.Peterfalvi.S04.supportInSubgroup A L).toFinset := by
      ext l
      simp
    rw [hset_eq, Set.toFinset_card, ← Nat.card_eq_fintype_card,
        Hypothesis71.card_supportInSubgroup_eq_card_A
          H78.hyp76.hyp71.hyp.subset_L]
  rw [hcard]
  ring

/-- Specialization of (7.8.c.ii) to the distinguished image `νζ`. -/
theorem zetaNuRhoNormSq_eq_card_ratio_mul (H78 : Hypothesis78 G A L)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta i)) = 0) :
    H78.zetaNuRhoNormSq =
      (((Nat.card A : ℂ) / (Nat.card L : ℂ)) *
        (ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) *
          star (ClassFunction.inner H78.beta
            (H78.nu (H78.hyp76.zeta H78.zetaDistinct))))).re := by
  rw [zetaNuRhoNormSq, zetaNuRho]
  exact congrArg Complex.re (H78.chiRho_norm_sq_eq_card_ratio_mul
    (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) hnu_irr hnu_orth)

/-- Combined (7.8.b) bridge: after the coefficient computation
`(β, ζ^ν) = a - 1`, the norm of `(ζ^ν)^ρ` is the card-ratio multiple of
`(a - 1)^2`. -/
theorem zetaNuRhoNormSq_eq_card_ratio_mul_int_sub_one
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta i)) = 0)
    (hbeta :
      ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
        (hBD.a : ℂ) - 1) :
    H78.zetaNuRhoNormSq =
      (((Nat.card A : ℂ) / (Nat.card L : ℂ)) *
        (((hBD.a : ℂ) - 1) * ((hBD.a : ℂ) - 1))).re := by
  rw [H78.zetaNuRhoNormSq_eq_card_ratio_mul hnu_irr hnu_orth, hbeta]
  rw [show star ((hBD.a : ℂ) - 1) = (hBD.a : ℂ) - 1 by simp]

/-- The same `(ζ^ν)^ρ` norm formula with `|A|/|L|` rewritten as `(h-1)/(he)`. -/
theorem zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta i)) = 0)
    (hbeta :
      ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) =
        (hBD.a : ℂ) - 1) :
    H78.zetaNuRhoNormSq =
      (((H78.kernelOrder : ℝ) - 1) /
          ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ))) *
        (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1)) := by
  rw [H78.zetaNuRhoNormSq_eq_card_ratio_mul_int_sub_one hBD hnu_irr hnu_orth hbeta]
  rw [H78.card_A_div_card_L_eq_kernel_sub_one_div_kernel_mul_complementIndex_complex]
  let r : ℝ :=
    ((H78.kernelOrder : ℝ) - 1) /
      ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ)) *
    (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1))
  have hprodCast :
      ((H78.kernelOrder : ℂ) - 1) /
            ((H78.kernelOrder : ℂ) * (H78.complementIndex : ℂ)) *
          (((hBD.a : ℂ) - 1) * ((hBD.a : ℂ) - 1)) = (r : ℂ) := by
    norm_num [r, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]
  change
    (((H78.kernelOrder : ℂ) - 1) /
          ((H78.kernelOrder : ℂ) * (H78.complementIndex : ℂ)) *
        (((hBD.a : ℂ) - 1) * ((hBD.a : ℂ) - 1))).re = r
  exact (congrArg Complex.re hprodCast).trans (Complex.ofReal_re r)

/-- **Peterfalvi (7.8.c.ii).** Source-data bridge for the `(ζ^ν)^ρ` norm
formula.  The source irreducibility/distinctness data supplies the coefficient
`(β, ζ^ν) = a - 1`, while irreducibility and orthogonality of the image
`νζ` remain explicit inputs to the character-ρ norm formula. -/
theorem zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one_of_irreducible_source_data
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hnu_irr : IsIrreducibleCharacter (H78.nu (H78.hyp76.zeta H78.zetaDistinct)))
    (hnu_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta i)) = 0)
    (hirr : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta i))
    (hdistinct : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H), i ≠ j →
        H78.hyp76.zeta i ≠ H78.hyp76.zeta j)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ)) :
    H78.zetaNuRhoNormSq =
      (((H78.kernelOrder : ℝ) - 1) /
          ((H78.kernelOrder : ℝ) * (H78.complementIndex : ℝ))) *
        (((hBD.a : ℝ) - 1) * ((hBD.a : ℝ) - 1)) :=
  H78.zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one hBD hnu_irr hnu_orth
    (H78.beta_inner_zetaImage_eq_int_sub_one_of_irreducible_source_data
      hBD hirr hdistinct hzeta_degree)

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

