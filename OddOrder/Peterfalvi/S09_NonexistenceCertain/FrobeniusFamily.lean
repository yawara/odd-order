import OddOrder.Peterfalvi.S09_NonexistenceCertain.CharacterEstimate

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S09_NonexistenceCertain.FrobeniusFamily` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S09
open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open OddOrder.GroupTheory (IsTISubset)
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]


namespace FrobeniusFamily
variable {k : ℕ}


/-- **Peterfalvi (7.10) character-estimate target.**  This is the exact data
still to be built from the character-theoretic inputs (7.5), (7.8), (7.9), and
(6.8): a minimal kernel index, the corresponding `𝓑`-set, the unweighted
`𝓑`-sum bound, and the base estimate before the final arithmetic rearrangement.

It is standalone target data, not a field of `FrobeniusFamily`. -/
structure CharacterEstimateData [Finite G] (F : FrobeniusFamily G k) where
  /-- The index with minimal kernel order. -/
  i : Fin k
  /-- Minimality of `h_i`. -/
  hmin : ∀ l : Fin k, F.h i ≤ F.h l
  /-- The Peterfalvi `𝓑`-set of non-minimal indices. -/
  B : Finset (Fin k)
  /-- The chosen `𝓑`-indices avoid the minimal index. -/
  B_avoids_min : ∀ j ∈ B, i ≠ j
  /-- The unweighted `𝓑`-sum bound coming from (7.8.b) and (7.9). -/
  Bsum_le :
    (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1
  /-- The base estimate isolated from (7.5), before bounding the `𝓑`-sum. -/
  base_estimate :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ)))

/-- Direct `𝓑`-sum bridge for Peterfalvi (7.10): an orthogonal integer
combination with diagonal weights `(h_j - 1) / e_j` and norm at most `e_i - 1`
gives exactly the `Bsum_le` field required by `CharacterEstimateData`. -/
lemma Bsum_le_of_orthogonal_integer_decomposition [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k} (B : Finset (Fin k))
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1) :
    (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1 := by
  classical
  have horth' : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        @ite ℂ (j = l) (Classical.propDecidable (j = l))
          (F.BsumWeight j : ℂ) 0 := by
    intro j hj l hl
    by_cases h : j = l
    · simpa [h] using horth j hj l hl
    · simpa [h] using horth j hj l hl
  have hm_nonneg : ∀ j ∈ B, 0 ≤ F.BsumWeight j := by
    intro j _hj
    simpa [BsumWeight] using F.h_sub_one_div_e_nonneg j
  let M : ℚ := (F.e i : ℚ) - 1
  have hM_eq : (M : ℝ) = (F.e i : ℝ) - 1 := by
    dsimp [M]
    norm_num
  have hbound : (ClassFunction.inner Γ Γ).re ≤ (M : ℝ) := by
    rw [hM_eq]
    exact hΓ_bound
  have hrat := sum_rat_weights_le_of_orthogonal_integer_decomposition
    B v x F.BsumWeight Γ Γ₁ M hΓ horth' hΓ₁ hm_nonneg hx_nonzero hbound
  simpa [BsumWeight, M] using hrat

/-- The reduced output of Peterfalvi (7.5), after inserting the (7.8) lower
bounds and the identity contribution on `G₀`, is exactly the `base_estimate`
field of `CharacterEstimateData`.  This is the algebraic bridge from the real
family inequality to the rational display used in (7.10). -/
lemma base_estimate_of_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) (B : Finset (Fin k))
    (hred :
      ((1 - (Nat.card F.G0 : ℚ)) / (Nat.card G : ℚ)) +
        (1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) /
            ((F.e j : ℚ) * (F.h j : ℚ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) := by
  have hG_ne : (Nat.card G : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hneg :
      (1 - (Nat.card F.G0 : ℚ)) / (Nat.card G : ℚ) =
        -(((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ)) := by
    field_simp [hG_ne]
    ring
  rw [hneg] at hred
  linarith

/-- Real-valued input form of `base_estimate_of_reduced_family_inequality`.
This matches the actual codomain of (7.5), (7.8.b), and the norm estimates before
the final rational display of Peterfalvi (7.10). -/
lemma base_estimate_of_real_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) (i : Fin k) (B : Finset (Fin k))
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) := by
  have hG_ne : (Nat.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hneg :
      (1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ) =
        -(((Nat.card F.G0 : ℝ) - 1) / (Nat.card G : ℝ)) := by
    field_simp [hG_ne]
    ring
  rw [hneg] at hred
  have hreal :
      1 - (F.e i : ℝ) / (F.h i : ℝ) -
        (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
        (∑ j ∈ B, ((F.h j : ℝ) - 1) /
          ((F.e j : ℝ) * (F.h j : ℝ))) ≤
        ((Nat.card F.G0 : ℝ) - 1) / (Nat.card G : ℝ) := by
    linarith
  rw [ge_iff_le]
  rw [← Rat.cast_le (K := ℝ)]
  norm_num
  have hG0_ncard : (F.G0.ncard : ℝ) = Nat.card F.G0 := by
    exact_mod_cast (Nat.card_coe_set_eq F.G0)
  rw [hG0_ncard]
  linarith

/-- Constructor form of `CharacterEstimateData` from the reduced family
inequality and the separately proved `𝓑`-sum bound. -/
noncomputable def characterEstimateData_of_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℚ)) / (Nat.card G : ℚ)) +
        (1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (∑ j ∈ B, ((F.h j : ℚ) - 1) /
            ((F.e j : ℚ) * (F.h j : ℚ)))) ≤ 0) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate := F.base_estimate_of_reduced_family_inequality i B hred

/-- Real-valued constructor form of `CharacterEstimateData` from the reduced
family inequality and the separately proved `𝓑`-sum bound.  This is the direct
interface for the estimates produced by Peterfalvi (7.5), (7.8.b), and (7.9). -/
noncomputable def characterEstimateData_of_real_reduced_family_inequality [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate := F.base_estimate_of_real_reduced_family_inequality i B hred

open scoped Classical in
/-- Base-estimate form of Peterfalvi (7.10) obtained directly from the (7.5)
family inequality package and the per-index lower bounds.

This removes the former standalone `hred` input for the base estimate: the caller
only supplies the actual (7.5) family package, the identity contribution on
`G₀`, the selected (7.8.b) lower bound, and the nonnegative outside-`𝓑`
contributions.  The cardinality hypotheses identify the (7.5) local data with
the Frobenius-family notation used in (7.10). -/
lemma base_estimate_of_family71_reduced_estimates
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (B : Finset (Fin k))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hG0sum :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
          ‖(χ : G → ℂ) g‖ ^ 2)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) := by
  classical
  have hratio : ∀ j : Fin k,
      (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ) =
        ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) := by
    intro j
    rw [hA j, hL j]
    exact F.card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real j
  have hgood' : ∀ j : Fin k, i ≠ j → j ∉ B →
      (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ) ≤
        P.chiRhoNormSq χ j := by
    intro j hij hjB
    rw [hratio j]
    exact hgood j hij hjB
  have hG0sumP :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ P.G0),
          ‖(χ : G → ℂ) g‖ ^ 2 := by
    rw [hG0]
    exact hG0sum
  have hredP :=
    reduced_inequality_of_estimates P χ hχ i B
      (1 - (F.e i : ℝ) / (F.h i : ℝ))
      hB_ne hG0sumP hi hgood'
  have hredF :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0 := by
    have hredP' :
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ) -
            (Nat.card (P.A i) : ℝ) / (Nat.card (P.L i) : ℝ) -
            (∑ j ∈ B,
              (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ))) ≤ 0 := by
      rw [← hG0]
      exact hredP
    have hsum_ratio :
        (∑ j ∈ B, (Nat.card (P.A j) : ℝ) / (Nat.card (P.L j) : ℝ)) =
          ∑ j ∈ B, ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) :=
      Finset.sum_congr rfl (fun j _ => hratio j)
    rwa [hratio i, hsum_ratio] at hredP'
  exact F.base_estimate_of_real_reduced_family_inequality i B hredF

open scoped Classical in
/-- Constructor form of `CharacterEstimateData` from a concrete (7.5) family
package, per-index lower bounds, and the separately proved `𝓑`-sum bound. -/
noncomputable def characterEstimateData_of_family71_reduced_estimates
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hG0sum :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
          ‖(χ : G → ℂ) g‖ ^ 2)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate :=
    F.base_estimate_of_family71_reduced_estimates P χ hχ B hL hA hG0
      hB_ne hG0sum hi hgood

open scoped Classical in
/-- Signed-irreducible variant of
`base_estimate_of_family71_reduced_estimates`.

This packages the exact first inequality in Peterfalvi (7.10):
`(|G₀|-1)/|G| ≥ (|G₀|-χ₁(1)^2)/|G|`, using that the selected `χ₁` is a signed
irreducible character and `1 ∈ G₀`. -/
lemma base_estimate_of_family71_reduced_estimates_of_signed_irreducible
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (B : Finset (Fin k))
    (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_signed : χ = ε • (ξ : ClassFunction G ℂ))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      1 - (F.e i : ℚ) / (F.h i : ℚ) -
        (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
        (∑ j ∈ B, ((F.h j : ℚ) - 1) /
          ((F.e j : ℚ) * (F.h j : ℚ))) :=
  F.base_estimate_of_family71_reduced_estimates P χ hχ B hL hA hG0 hB_ne
    (F.one_le_G0_norm_sum_of_signed_irreducible χ ε ξ hε hχ_signed)
    hi hgood

open scoped Classical in
/-- Constructor form of the signed-irreducible `(7.5)` base assembly, retaining
only the `𝓑`-sum bound as a separate final-assembly input. -/
noncomputable def characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_signed : χ = ε • (ξ : ClassFunction G ℂ))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum :
      (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤ (F.e i : ℚ) - 1)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    F.CharacterEstimateData where
  i := i
  hmin := hmin
  B := B
  B_avoids_min := hB_ne
  Bsum_le := hBsum
  base_estimate :=
    F.base_estimate_of_family71_reduced_estimates_of_signed_irreducible
      P χ hχ B ε ξ hε hχ_signed hL hA hG0 hB_ne hi hgood

open scoped Classical in
/-- Constructor form of `CharacterEstimateData` from the concrete (7.5) family
estimates, a signed-irreducible selected character, and Peterfalvi's orthogonal
integer decomposition for the `𝓑`-sum.

Compared with `characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible`,
this no longer asks for the final `𝓑`-sum bound as an external input: it derives
that bound from the orthogonal decomposition used in (7.9). -/
noncomputable def characterEstimateData_of_family71_signed_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (ε : ℤ) (ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hε : ε = 1 ∨ ε = -1)
    (hχ_signed : χ = ε • (ξ : ClassFunction G ℂ))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤ P.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq χ j) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible
    P χ hχ hmin B ε ξ hε hχ_signed hL hA hG0 hB_ne
    (F.Bsum_le_of_orthogonal_integer_decomposition
      B v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound)
    hi hgood

open scoped Classical in
/-- Coherence-source form of the concrete (7.5)+(7.9) final-assembly
constructor.

Here the selected character is the coherent image `νζ`.  The source
irreducibility of `ζ` and the coherence witness produce the signed-irreducible
witness internally, so the caller supplies neither `hG0sum` nor an explicit
`νζ = ±ξ` certificate. -/
noncomputable def characterEstimateData_of_family71_coherent_zeta_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    {i : Fin k} (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hL : ∀ j : Fin k, P.L j = F.L j)
    (hA : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hG0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) j) :
    F.CharacterEstimateData := by
  classical
  let hsig :=
    H78.exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent hcoh hnu hzeta_irr
  let ε : ℤ := Classical.choose hsig
  let hsigξ := Classical.choose_spec hsig
  let ξ : OddOrder.RepresentationTheory.IrreducibleCharacter G := Classical.choose hsigξ
  have hχ_signed := Classical.choose_spec hsigξ
  exact F.characterEstimateData_of_family71_signed_decomposition
    P (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
    (H78.zetaImage_inner_self_eq_one_of_irreducible hzeta_irr)
    hmin B ε ξ hχ_signed.1 hχ_signed.2 hL hA hG0 hB_ne
    v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound hi hgood

open scoped Classical in
/-- Source-data form of the concrete (7.5)+(7.8.b)+(7.9) final-assembly
constructor.

This refines `characterEstimateData_of_family71_coherent_zeta_decomposition` by
deriving the residual `Γ` norm bound from the family-notated (7.8.b) source
data, rather than taking `hΓ_bound` as a separate input.  The selected character
is still the coherent image `νζ`, so the signed-irreducible witness and the
`G₀` identity contribution are also generated internally. -/
noncomputable def characterEstimateData_of_family71_coherent_zeta_source_data
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (P : FamilyHypothesis71 G k)
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    {i : Fin k} (hLocalL : L = F.L i) (hLocalH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hP_L : ∀ j : Fin k, P.L j = F.L j)
    (hP_A : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hP_G0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) j) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_family71_coherent_zeta_decomposition
    P H78 hcoh hnu hzeta_irr hmin B hP_L hP_A hP_G0 hB_ne
    v x hBD.Gamma Γ₁ hΓ horth hΓ₁ hx_nonzero
    (F.gamma_inner_self_re_le_of_family_source_data H78 hBD hLocalL hLocalH
      hind_norm hzeta_ind hirr hdistinct hzeta_degree hdegree_sum hzeta_uv hsmall)
    hi hgood

/-- Constructor form of `CharacterEstimateData` from the real reduced family
inequality and Peterfalvi's orthogonal integer decomposition for the `𝓑`-sum.

This combines the two final-assembly bridges: the norm bound on `Γ` gives the
`Bsum_le` field through `Bsum_le_of_orthogonal_integer_decomposition`, while the
real reduced family inequality supplies the `base_estimate` field. -/
noncomputable def characterEstimateData_of_real_reduced_family_inequality_and_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_real_reduced_family_inequality hmin B hB_ne
    (F.Bsum_le_of_orthogonal_integer_decomposition
      B v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound)
    hred

/-- Source-data constructor form of `CharacterEstimateData` from the real reduced
family inequality and Peterfalvi's orthogonal integer decomposition.

This is the same assembly as
`characterEstimateData_of_real_reduced_family_inequality_and_decomposition`, but
it obtains the required `Γ` norm-bound directly from the local (7.8.b) source
inputs for an `H78` package.  The only family/local cardinality bridge retained
as an explicit hypothesis is `H78.complementIndex = F.e i`. -/
noncomputable def characterEstimateData_of_real_reduced_family_inequality_and_source_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hindex : H78.complementIndex = F.e i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hsmall : H78.smallIndex)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_real_reduced_family_inequality_and_decomposition
    hmin B hB_ne v x hBD.Gamma Γ₁ hΓ horth hΓ₁ hx_nonzero
    (by
      simpa [hindex] using
        H78.gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
          hBD hind_norm hzeta_ind hirr hdistinct hzeta_degree hdegree_sum hzeta_uv hsmall)
    hred

/-- Source-data constructor with family-side cardinality hypotheses.

Compared with
`characterEstimateData_of_real_reduced_family_inequality_and_source_decomposition`,
this wrapper consumes the natural family/local identifications `L = L_i` and
`H = H_i`, and the family-side small-index hypothesis `2e_i + 1 ≤ h_i`, rather
than asking the caller to rewrite them into local (7.8.b) notation. -/
noncomputable def characterEstimateData_of_source_decomposition_of_family_cardinalities
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (H78.complementIndex : ℝ)) *
            (1 - 1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (H78.kernelOrder : ℝ)) * (hBD.a : ℝ) +
          (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_real_reduced_family_inequality_and_source_decomposition
    H78 hBD (F.localComplementIndex_eq_e H78 hL hH)
    hmin B hB_ne v x Γ₁ hΓ horth hΓ₁ hx_nonzero hind_norm hzeta_ind hirr hdistinct
    hzeta_degree hdegree_sum hzeta_uv
    (F.localSmallIndex_of_family_cardinalities H78 hL hH hsmall) hred

/-- Source-data constructor with all cardinal source estimates stated in family
notation.

This is the downstream-facing form of the source-data final assembly: the source
norm, degree sum, and `u,v,w` formula use the family quantities `e_i` and `h_i`.
The wrapper rewrites them into the local `H78` notation before applying the
local/family cardinality constructor. -/
noncomputable def characterEstimateData_of_family_source_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    F.CharacterEstimateData :=
  F.characterEstimateData_of_source_decomposition_of_family_cardinalities
    H78 hBD hL hH hmin B hB_ne v x Γ₁ hΓ horth hΓ₁ hx_nonzero
    (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hind_norm)
    hzeta_ind hirr hdistinct
    (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
    (by
      simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
        using hdegree_sum)
    (by
      simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
        using hzeta_uv)
    hsmall hred

/-- The named character-estimate data implies the displayed lower bound of
Peterfalvi (7.10). -/
lemma lowerBoundTerm_of_characterEstimateData [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : F.CharacterEstimateData) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hdata with ⟨i, hmin, B, hB_ne, hBsum, hbase⟩
  exact ⟨i, F.lowerBoundTerm_of_Bsum_bound hodd hmin B hB_ne hBsum hbase⟩


/-- Concrete (7.5)+(7.8.b)+(7.9) source-data form of the displayed (7.10)
lower bound.

This is the lower-bound consumer for
`characterEstimateData_of_family71_coherent_zeta_source_data`: the concrete
`FamilyHypothesis71` reduced family inequality, the coherent `ζ` image, the
family-notated (7.8.b) source estimates, and the orthogonal integer
decomposition are assembled internally into `CharacterEstimateData` and then
converted to Peterfalvi's displayed rational bound. -/
lemma lowerBoundTerm_of_family71_coherent_zeta_source_data
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (P : FamilyHypothesis71 G k)
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    {i : Fin k} (hLocalL : L = F.L i) (hLocalH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hP_L : ∀ j : Fin k, P.L j = F.L j)
    (hP_A : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hP_G0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) j) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) :=
  F.lowerBoundTerm_of_characterEstimateData hodd
    (F.characterEstimateData_of_family71_coherent_zeta_source_data P H78 hBD
      hcoh hnu hzeta_irr hLocalL hLocalH hmin B hP_L hP_A hP_G0 hB_ne
      v x Γ₁ hΓ horth hΓ₁ hx_nonzero hind_norm hzeta_ind hirr hdistinct
      hzeta_degree hdegree_sum hzeta_uv hsmall hi hgood)

/-- Real-valued form of `lowerBoundTerm_of_Bsum_bound`, matching the reduced
inequality produced before Peterfalvi's final rational display. -/
lemma lowerBoundTerm_of_real_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  exact F.lowerBoundTerm_of_Bsum_bound hodd hmin B hB_ne hBsum
    (F.base_estimate_of_real_reduced_family_inequality i B hred)

/-- Direct displayed-bound form from the real reduced family inequality and the
orthogonal integer decomposition controlling the `𝓑`-sum.

This is the non-existential consumer for the final (7.10) assembly after the
character theory has supplied the chosen minimal index, `𝓑`, the integer
coefficients, and the norm bound on `Γ`. -/
lemma lowerBoundTerm_of_real_reduced_family_inequality_and_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) :=
  F.lowerBoundTerm_of_real_Bsum_bound hodd hmin B hB_ne
    (F.Bsum_le_of_orthogonal_integer_decomposition
      B v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound)
    hred

/-- Source-data displayed-bound form for the final assembly step of Peterfalvi
(7.10).

This consumes the same family-notated local source data as
`characterEstimateData_of_family_source_decomposition`, but returns the displayed
lower bound for the chosen minimal index directly.  This is useful when the
caller wants the (7.10) bound without first packaging the intermediate
`CharacterEstimateData`. -/
lemma lowerBoundTerm_of_family_source_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
      ((F.e i : ℚ) - 1) *
        (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
            ((F.e i : ℚ) * (F.h i : ℚ)) +
          2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  refine F.lowerBoundTerm_of_real_reduced_family_inequality_and_decomposition hodd
    hmin B hB_ne v x hBD.Gamma Γ₁ hΓ horth hΓ₁ hx_nonzero ?_ hred
  have hΓ_bound_local :
      (ClassFunction.inner hBD.Gamma hBD.Gamma).re ≤
        (H78.complementIndex : ℝ) - 1 :=
    H78.gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
      hBD
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hind_norm)
      hzeta_ind hirr hdistinct
      (by simpa [F.localComplementIndex_eq_e H78 hL hH] using hzeta_degree)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hdegree_sum)
      (by
        simpa [F.localKernelOrder_eq_h H78 hH, F.localComplementIndex_eq_e H78 hL hH]
          using hzeta_uv)
      (F.localSmallIndex_of_family_cardinalities H78 hL hH hsmall)
  simpa [F.localComplementIndex_eq_e H78 hL hH] using hΓ_bound_local

/-- Existential real-valued wrapper for the final assembly step of Peterfalvi
(7.10).  The input shape matches the real reduced estimate before converting to
the rational displayed lower bound. -/
lemma exists_lowerBoundTerm_of_exists_real_Bsum_bound [Finite G]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : ∃ i : Fin k, (∀ l : Fin k, F.h i ≤ F.h l) ∧
      ∃ B : Finset (Fin k),
        (∀ j ∈ B, i ≠ j) ∧
        (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
          (F.e i : ℚ) - 1 ∧
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ) -
            (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
            (∑ j ∈ B, ((F.h j : ℝ) - 1) /
              ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  rcases hdata with ⟨i, hmin, B, hB_ne, hBsum, hred⟩
  exact ⟨i, F.lowerBoundTerm_of_real_Bsum_bound hodd hmin B hB_ne hBsum hred⟩

end FrobeniusFamily

/-- **Peterfalvi (7.10).** Under `FrobeniusFamily` with `G` of odd order, there is
an index `i` for which, writing `e = e_i` and `h = h_i`,

`(|G₀| - 1)/|G| ≥ (e - 1) · ((h - 2e - 1)/(e·h) + 2/(h·(h+2)))`.

This is the quantitative heart of §9; its proof uses the Dade isometry and the
coherence estimates (7.5)-(7.9). -/
theorem card_G0_lower_bound [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  have hdata : F.CharacterEstimateData := by
    -- TODO: assemble from (7.5), (7.8), (7.9), and (6.8).
    sorry
  exact F.lowerBoundTerm_of_characterEstimateData hodd hdata

/-- **Peterfalvi (7.11), displayed-bound form.**  The final contradiction from the
existential lower bound displayed in (7.10).

This isolates the terminal arithmetic of (7.11): any proof of the displayed (7.10) bound,
including the still-open theorem `card_G0_lower_bound` or the conditional §9 assembly lemmas,
can be consumed without duplicating the `G₀ = {1}` contradiction proof. -/
theorem not_trivial_G0_of_lowerBoundTerm [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G))
    (hbound :
      ∃ i : Fin k,
        ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
          ((F.e i : ℚ) - 1) *
            (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
                ((F.e i : ℚ) * (F.h i : ℚ)) +
              2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))))
    (hG0 : F.G0 = {(1 : G)}) : False := by
  obtain ⟨i, hi⟩ := hbound
  -- `G₀ = {1}` forces `|G₀| = 1`, so the left-hand side of (7.10) is `0`.
  have hcard : Nat.card F.G0 = 1 := by rw [hG0]; simp
  -- The right-hand side of (7.10) is strictly positive.
  have hRHS := F.lowerBoundTerm_pos hodd i
  -- But the conditional (7.10) lower bound says it is `≤ 0` — contradiction.
  rw [hcard] at hi
  have hlhs : ((1 : ℕ) : ℚ) - 1 = 0 := by norm_num
  rw [hlhs, zero_div] at hi
  linarith [hi, hRHS]

/-- **Peterfalvi (7.11), penultimate existential form.**  The penultimate
displayed lower bound from (7.10) already contradicts `G₀ = {1}`. -/
theorem not_trivial_G0_of_exists_penultimate [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hpen : ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        1 - (F.e i : ℚ) / (F.h i : ℚ) -
          (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
          (((F.e i : ℚ) - 1) / ((F.h i : ℚ) + 2)))
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.exists_lowerBoundTerm_of_exists_penultimate hpen) hG0

/-- **Peterfalvi (7.11), existential `𝓑`-sum form.**  If the final assembly
produces a minimal index, a `𝓑`-set, the unweighted `𝓑`-sum bound, and the
base estimate, then `G₀ = {1}` is impossible. -/
theorem not_trivial_G0_of_exists_Bsum_bound [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : ∃ i : Fin k, (∀ l : Fin k, F.h i ≤ F.h l) ∧
      ∃ B : Finset (Fin k),
        (∀ j ∈ B, i ≠ j) ∧
        (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
          (F.e i : ℚ) - 1 ∧
        ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
          1 - (F.e i : ℚ) / (F.h i : ℚ) -
            (((F.h i : ℚ) - 1) / ((F.e i : ℚ) * (F.h i : ℚ))) -
            (∑ j ∈ B, ((F.h j : ℚ) - 1) /
              ((F.e j : ℚ) * (F.h j : ℚ))))
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.exists_lowerBoundTerm_of_exists_Bsum_bound hodd hdata) hG0

/-- **Peterfalvi (7.11), existential real `𝓑`-sum form.**  This is the terminal
consumer for the real-valued reduced estimate produced before the rational
display of (7.10). -/
theorem not_trivial_G0_of_exists_real_Bsum_bound [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hdata : ∃ i : Fin k, (∀ l : Fin k, F.h i ≤ F.h l) ∧
      ∃ B : Finset (Fin k),
        (∀ j ∈ B, i ≠ j) ∧
        (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
          (F.e i : ℚ) - 1 ∧
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ) -
            (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
            (∑ j ∈ B, ((F.h j : ℝ) - 1) /
              ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.exists_lowerBoundTerm_of_exists_real_Bsum_bound hodd hdata) hG0

/-- **Peterfalvi (7.11), conditional form.**  The final contradiction from the named
`CharacterEstimateData` package used to prove (7.10).

This avoids routing through the still-open `card_G0_lower_bound`: once the §9 character theory has
constructed `F.CharacterEstimateData`, the terminal `G₀ ≠ {1}` contradiction is already closed by
the completed arithmetic and positivity lemmas. -/
theorem not_trivial_G0_of_characterEstimateData [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (hdata : F.CharacterEstimateData)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.lowerBoundTerm_of_characterEstimateData hodd hdata) hG0


/-- **Peterfalvi (7.11), concrete family/source-data form.**  The terminal
contradiction from the concrete (7.5) family inequality, coherent `ζ` image,
(7.8.b) source estimates, and the (7.9) orthogonal integer decomposition.

This bypasses the open top-level `card_G0_lower_bound`: once these textbook
source-data inputs are available, the displayed lower bound and the final
`G₀ = {1}` contradiction are already closed. -/
theorem not_trivial_G0_of_family71_coherent_zeta_source_data
    [Fintype G] [Invertible (Nat.card G : ℂ)] {k : ℕ}
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (P : FamilyHypothesis71 G k)
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct))
    {i : Fin k} (hLocalL : L = F.L i) (hLocalH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hP_L : ∀ j : Fin k, P.L j = F.L j)
    (hP_A : ∀ j : Fin k, P.A j = ((F.H j : Set G) \ ({1} : Set G)))
    (hP_G0 : P.G0 = F.G0)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hi :
      1 - (F.e i : ℝ) / (F.h i : ℝ) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
        P.chiRhoNormSq (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) j)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    (F.lowerBoundTerm_of_family71_coherent_zeta_source_data hodd P H78 hBD
      hcoh hnu hzeta_irr hLocalL hLocalH hmin B hP_L hP_A hP_G0 hB_ne
      v x Γ₁ hΓ horth hΓ₁ hx_nonzero hind_norm hzeta_ind hirr hdistinct
      hzeta_degree hdegree_sum hzeta_uv hsmall hi hgood)
    hG0

/-- **Peterfalvi (7.11), `𝓑`-sum-bound form.**  The terminal contradiction from
the separately established `𝓑`-sum bound and the real reduced family inequality.

This is the direct consumer for final-assembly work that has already converted the
orthogonal decomposition into the rational `𝓑`-sum estimate, but has not packaged the result
as `CharacterEstimateData`. -/
theorem not_trivial_G0_of_real_Bsum_bound [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hBsum : (∑ j ∈ B, ((F.h j : ℚ) - 1) / (F.e j : ℚ)) ≤
      (F.e i : ℚ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_characterEstimateData F hodd
    (F.characterEstimateData_of_real_reduced_family_inequality hmin B hB_ne hBsum hred)
    hG0

/-- **Peterfalvi (7.11), raw final-assembly form.**  The terminal contradiction from the
real reduced family inequality and Peterfalvi's orthogonal integer decomposition for the `𝓑`-sum.

This is the form closest to the outputs of (7.5), (7.8), and (7.9): it builds the named
`CharacterEstimateData` internally, then applies `not_trivial_G0_of_characterEstimateData`. -/
theorem not_trivial_G0_of_real_reduced_family_inequality_and_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) {i : Fin k}
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ Γ₁ : ClassFunction G ℂ)
    (hΓ : Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (F.e i : ℝ) - 1)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_characterEstimateData F hodd
    (F.characterEstimateData_of_real_reduced_family_inequality_and_decomposition
      hmin B hB_ne v x Γ Γ₁ hΓ horth hΓ₁ hx_nonzero hΓ_bound hred)
    hG0

/-- **Peterfalvi (7.11), family-source final-assembly form.**  The terminal
contradiction from the family-notated source data that produces the displayed
(7.10) lower bound.

This is the terminal consumer paired with
`FrobeniusFamily.lowerBoundTerm_of_family_source_decomposition`: once the
character-theoretic work has supplied the chosen local (7.8) source package, the
real reduced family inequality, and the orthogonal integer decomposition, the
case `G₀ = {1}` is already impossible without using the still-open
`card_G0_lower_bound`. -/
theorem not_trivial_G0_of_family_source_decomposition
    [Fintype G] [Invertible (Nat.card G : ℂ)] {k : ℕ}
    {A : Set G} {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G)) {i : Fin k}
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hL : L = F.L i) (hH : H78.hyp76.H = F.H i)
    (hmin : ∀ l : Fin k, F.h i ≤ F.h l) (B : Finset (Fin k))
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (v : Fin k → ClassFunction G ℂ) (x : Fin k → ℤ)
    (Γ₁ : ClassFunction G ℂ)
    (hΓ : hBD.Gamma = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁)
    (horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner (v j) (v l) =
        if j = l then (F.BsumWeight j : ℂ) else 0)
    (hΓ₁ : ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0)
    (hx_nonzero : ∀ j ∈ B, x j ≠ 0)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.ind1H) = (F.e i : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hirr : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      IsIrreducibleCharacter (H78.hyp76.zeta r))
    (hdistinct : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H), r ≠ s →
        H78.hyp76.zeta r ≠ H78.hyp76.zeta s)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) = (F.e i : ℂ))
    (hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : L) * star (H78.hyp76.zeta r (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((F.h i : ℂ) - 1) * (F.e i : ℂ))
    (hzeta_uv :
      H78.zetaNuRhoNormSq =
        (1 / (F.e i : ℝ)) *
            (1 - 1 / (F.h i : ℝ)) * (hBD.a : ℝ) ^ 2 -
          2 * (1 / (F.h i : ℝ)) * (hBD.a : ℝ) +
          (1 - (F.e i : ℝ) / (F.h i : ℝ)))
    (hsmall : 2 * F.e i + 1 ≤ F.h i)
    (hred :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (1 - (F.e i : ℝ) / (F.h i : ℝ) -
          (((F.h i : ℝ) - 1) / ((F.e i : ℝ) * (F.h i : ℝ))) -
          (∑ j ∈ B, ((F.h j : ℝ) - 1) /
            ((F.e j : ℝ) * (F.h j : ℝ)))) ≤ 0)
    (hG0 : F.G0 = {(1 : G)}) : False :=
  not_trivial_G0_of_lowerBoundTerm F hodd
    ⟨i, F.lowerBoundTerm_of_family_source_decomposition hodd H78 hBD hL hH hmin B
      hB_ne v x Γ₁ hΓ horth hΓ₁ hx_nonzero hind_norm hzeta_ind hirr hdistinct
      hzeta_degree hdegree_sum hzeta_uv hsmall hred⟩
    hG0

/-- **Peterfalvi (7.11)** — the §9 main theorem.

There is no odd-order group `G` admitting a family of `k ≥ 2` Frobenius subgroups
(as in `FrobeniusFamily`) whose kernels' conjugate-spreads cover everything except
the identity, i.e. with `G₀ = {1}`.

Proof (in the text): if `G₀ = {1}` then `|G₀| = 1`, so the left side of (7.10)
vanishes; but `e ≥ 2` (the Frobenius complement is nontrivial and `|G|` is odd)
and `e ∣ h - 1` with `h` odd give `(h - 2e - 1)/(eh) ≥ 0`, whence the right side
of (7.10) is strictly positive — a contradiction. -/
theorem not_trivial_G0 [Finite G] {k : ℕ} (F : FrobeniusFamily G k)
    (hodd : Odd (Nat.card G)) (hG0 : F.G0 = {(1 : G)}) : False := by
  exact not_trivial_G0_of_lowerBoundTerm F hodd (card_G0_lower_bound F hodd) hG0

end OddOrder.Peterfalvi.S09


