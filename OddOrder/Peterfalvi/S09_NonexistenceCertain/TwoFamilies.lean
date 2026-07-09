import OddOrder.Peterfalvi.S09_NonexistenceCertain.CoherenceFormula

/-!
# Peterfalvi (7.9) — two-family non-orthogonality + orthogonal integer decomposition

Split from the former monolithic `OddOrder.Peterfalvi.S09_NonexistenceCertain` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S09
open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)
open OddOrder.GroupTheory (IsTISubset)
open OddOrder.RepresentationTheory
open scoped Pointwise

variable {G : Type*} [Group G]


section Section_7_9

/-! ### (7.9): two-family non-orthogonality

Peterfalvi (7.9) is the final two-family character-theoretic input used in the
proof of (7.10).  The proof combines (7.8.a), (5.9), odd-order non-realness
(1.1), and the cross-family disjointness of Dade supports.  Here we name the
faithful hypothesis bundle and conclusion predicate, without adding it as a new
assumption to the group-theoretic `(7.10)` theorem. -/

/-- **Peterfalvi (7.9) hypothesis interface.**  Two instances of the (7.8)
coherence/norm setup over the same odd-order group, with disjoint Dade supports
`A₁^{τ₁}` and `A₂^{τ₂}` as in Hypothesis (7.4) for `I = {1,2}`. -/
structure Hypothesis79 (G : Type*) [Group G] [Fintype G]
    (A₁ : Set G) (L₁ : Subgroup G) [Fintype L₁]
    [Invertible (Nat.card L₁ : ℂ)]
    (A₂ : Set G) (L₂ : Subgroup G) [Fintype L₂]
    [Invertible (Nat.card L₂ : ℂ)]
    [Invertible (Nat.card G : ℂ)] where
  /-- The ambient group has odd order. -/
  odd_card : Odd (Nat.card G)
  /-- The first coherent normal-subgroup setup. -/
  first : Hypothesis78 G A₁ L₁
  /-- The second coherent normal-subgroup setup. -/
  second : Hypothesis78 G A₂ L₂
  /-- The Dade supports `A₁^{τ₁}` and `A₂^{τ₂}` are disjoint. -/
  dadeSupport_disjoint :
    Disjoint first.hyp76.hyp71.hyp.dadeSupport second.hyp76.hyp71.hyp.dadeSupport

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]
variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁]
variable [Invertible (Nat.card L₁ : ℂ)]
variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]
variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The image `ζ₁^{ν₁}` of the distinguished first `ζ`. -/
noncomputable def firstZetaImage (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction G ℂ :=
  H79.first.nu (H79.first.hyp76.zeta H79.first.zetaDistinct)

/-- The image `ζ₂^{ν₂}` of the distinguished second `ζ`. -/
noncomputable def secondZetaImage (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction G ℂ :=
  H79.second.nu (H79.second.hyp76.zeta H79.second.zetaDistinct)

/-- Coherence supplies virtual-character membership for the two distinguished
`ζ` images used in (7.9). -/
theorem zetaImages_mem_ZIrr_of_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension) :
    H79.firstZetaImage ∈ ZIrr G ∧ H79.secondZetaImage ∈ ZIrr G := by
  constructor
  · simpa [firstZetaImage] using
      H79.first.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh₁ hnu₁
  · simpa [secondZetaImage] using
      H79.second.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh₂ hnu₂

/-- Coherence plus virtual `Ind 1_H` sources package the four virtual-character
memberships used by the residual cross-term consumers. -/
theorem delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct)) :
    H79.first.delta ∈ ZIrr G ∧ H79.second.delta ∈ ZIrr G ∧
      H79.firstZetaImage ∈ ZIrr G ∧ H79.secondZetaImage ∈ ZIrr G := by
  have hδ₁ : H79.first.delta ∈ ZIrr G :=
    H79.first.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hind₁Z hzeta₁_irr
  have hδ₂ : H79.second.delta ∈ ZIrr G :=
    H79.second.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₂ hnu₂ hind₂Z hzeta₂_irr
  obtain ⟨hζ₁, hζ₂⟩ := H79.zetaImages_mem_ZIrr_of_isCoherent hcoh₁ hnu₁ hcoh₂ hnu₂
  exact ⟨hδ₁, hδ₂, hζ₁, hζ₂⟩

/-- **Peterfalvi (7.9) conclusion.**  The two cross inner products cannot both
vanish: `(β₁, ζ₂^{ν₂}) ≠ 0` or `(β₂, ζ₁^{ν₁}) ≠ 0`. -/
def conclusion (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) : Prop :=
  ClassFunction.inner H79.first.beta H79.secondZetaImage ≠ 0 ∨
    ClassFunction.inner H79.second.beta H79.firstZetaImage ≠ 0

/-- Swapping the two families preserves the (7.9) hypothesis interface. -/
def swap (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    Hypothesis79 G A₂ L₂ A₁ L₁ where
  odd_card := H79.odd_card
  first := H79.second
  second := H79.first
  dadeSupport_disjoint := H79.dadeSupport_disjoint.symm

/-- The (7.9) conclusion is symmetric in the two families. -/
theorem conclusion_swap (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    H79.swap.conclusion ↔ H79.conclusion := by
  simp [conclusion, swap, firstZetaImage, secondZetaImage, or_comm]

/-- The two `β` functions are orthogonal when their Dade supports are disjoint. -/
theorem beta_inner_beta_eq_zero (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction.inner H79.first.beta H79.second.beta = 0 := by
  have hdisj : Disjoint H79.first.beta.support H79.second.beta.support := by
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint
      (H79.first.beta_support_subset_dadeSupport hg₁)
      (H79.second.beta_support_subset_dadeSupport hg₂)
  exact ClassFunction.inner_eq_zero_of_disjoint_support hdisj

/-- If the two distinguished coherent images are supported in the corresponding
disjoint Dade supports, their cross inner product vanishes. -/
theorem zetaImage_cross_eq_zero_of_support_subset
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hζ₁_supp : H79.firstZetaImage.support ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)
    (hζ₂_supp : H79.secondZetaImage.support ⊆ H79.second.hyp76.hyp71.hyp.dadeSupport) :
    ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0 := by
  have hdisj : Disjoint H79.firstZetaImage.support H79.secondZetaImage.support := by
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint (hζ₁_supp hg₁) (hζ₂_supp hg₂)
  exact ClassFunction.inner_eq_zero_of_disjoint_support hdisj

/-- Expanding `β₁ = 1_G - ζ₁^ν + Δ₁` and `β₂ = 1_G - ζ₂^ν + Δ₂`
gives the displayed algebraic identity used in Peterfalvi (7.9). -/
theorem beta_inner_beta_expand_delta (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0) :
    ClassFunction.inner H79.first.beta H79.second.beta =
      1 - ClassFunction.inner H79.firstZetaImage H79.second.delta -
        ClassFunction.inner H79.first.delta H79.secondZetaImage +
          ClassFunction.inner H79.first.delta H79.second.delta := by
  have hzeta_cross' :
      ClassFunction.inner
        (H79.first.nu (H79.first.hyp76.zeta H79.first.zetaDistinct))
        (H79.second.nu (H79.second.hyp76.zeta H79.second.zetaDistinct)) = 0 := by
    simpa [firstZetaImage, secondZetaImage] using hzeta_cross
  rw [H79.first.beta_eq_constOne_sub_zetaImage_add_delta,
    H79.second.beta_eq_constOne_sub_zetaImage_add_delta]
  simp only [firstZetaImage, secondZetaImage, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, ClassFunction.inner_add_right,
    ClassFunction.inner_sub_right]
  rw [Hypothesis71.constOne_inner_self_eq_one,
    H79.second.constOne_orth_zetaImage hBD₂,
    H79.second.constOne_orth_delta hBD₂,
    H79.first.zetaImage_orth_one hBD₁,
    H79.first.delta_orth_one hBD₁,
    hzeta_cross']
  ring

/-- The support and `ζ`-orthogonality inputs reduce Peterfalvi (7.9) to the
parity/nonzero statement for the two residual cross terms. -/
theorem delta_cross_equation (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0) :
    0 = 1 - ClassFunction.inner H79.firstZetaImage H79.second.delta -
        ClassFunction.inner H79.first.delta H79.secondZetaImage +
          ClassFunction.inner H79.first.delta H79.second.delta := by
  rw [← H79.beta_inner_beta_expand_delta hBD₁ hBD₂ hzeta_cross,
    H79.beta_inner_beta_eq_zero]

/-- If one of the residual cross terms is nonzero, then the original (7.9)
non-orthogonality conclusion follows. -/
theorem conclusion_of_delta_cross_nonzero (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hdelta : ClassFunction.inner H79.first.delta H79.secondZetaImage ≠ 0 ∨
      ClassFunction.inner H79.firstZetaImage H79.second.delta ≠ 0) :
    H79.conclusion := by
  rcases hdelta with hdelta | hdelta
  · left
    rw [H79.first.beta_inner_eq_delta_inner_of_orthogonal H79.secondZetaImage
      (H79.second.constOne_orth_zetaImage hBD₂) hzeta_cross]
    exact hdelta
  · right
    have hleft : ClassFunction.inner H79.firstZetaImage H79.second.beta ≠ 0 := by
      rw [H79.second.inner_beta_eq_inner_delta_of_orthogonal H79.firstZetaImage
        (H79.first.zetaImage_orth_one hBD₁) hzeta_cross]
      exact hdelta
    intro hzero
    apply hleft
    rw [Hypothesis71.ClassFunction.inner_symm H79.second.beta H79.firstZetaImage,
      hzero, star_zero]

/-- Virtual-character residuals make the three residual cross terms integral. -/
theorem delta_cross_integral_of_ZIrr
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hδ₁ : H79.first.delta ∈ ZIrr G)
    (hδ₂ : H79.second.delta ∈ ZIrr G)
    (hζ₁ : H79.firstZetaImage ∈ ZIrr G)
    (hζ₂ : H79.secondZetaImage ∈ ZIrr G) :
    (∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ)) ∧
    (∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ)) ∧
    (∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ)) := by
  exact ⟨ClassFunction.inner_mem_ZIrr_int hδ₁ hζ₂,
    ClassFunction.inner_mem_ZIrr_int hζ₁ hδ₂,
    ClassFunction.inner_mem_ZIrr_int hδ₁ hδ₂⟩

/-- Coherence, virtual `Ind 1_H` sources, and irreducible distinguished source
terms make the three residual cross terms integral. -/
theorem delta_cross_integral_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct)) :
    (∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ)) ∧
    (∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ)) ∧
    (∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ)) := by
  obtain ⟨hδ₁, hδ₂, hζ₁, hζ₂⟩ :=
    H79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr
  exact H79.delta_cross_integral_of_ZIrr hδ₁ hδ₂ hζ₁ hζ₂

/-- Coherence and source irreducibility make the three residual cross terms integral. -/
theorem delta_cross_integral_of_irreducible_sourceDiff_and_isCoherent
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.ind1H))
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂_irr : IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.ind1H))
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct)) :
    (∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ)) ∧
    (∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ)) ∧
    (∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ)) :=
  H79.delta_cross_integral_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁_irr.mem_ZIrr hzeta₁_irr
    hind₂_irr.mem_ZIrr hzeta₂_irr

/-- Integer-parity form of the last step of Peterfalvi (7.9): once the two
residual cross terms are integers and `(Δ₁,Δ₂)` is an even integer, the displayed
`0 = 1 - ... + ...` equation forces one cross term to be nonzero. -/
theorem conclusion_of_delta_cross_integral_parity
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hx : ∃ x : ℤ,
      ClassFunction.inner H79.first.delta H79.secondZetaImage = (x : ℂ))
    (hy : ∃ y : ℤ,
      ClassFunction.inner H79.firstZetaImage H79.second.delta = (y : ℂ))
    (hz : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  rcases hx with ⟨x, hx⟩
  rcases hy with ⟨y, hy⟩
  rcases hz with ⟨z, hz, hz_even⟩
  have heqC := H79.delta_cross_equation hBD₁ hBD₂ hzeta_cross
  rw [hx, hy, hz] at heqC
  have heqZ : (0 : ℤ) = 1 - y - x + z := by
    have hcast : ((0 : ℤ) : ℂ) = ((1 - y - x + z : ℤ) : ℂ) := by
      simpa [Int.cast_sub, Int.cast_add] using heqC
    exact_mod_cast hcast
  have hnonzero : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hnot
    push Not at hnot
    rcases hz_even with ⟨t, ht⟩
    omega
  apply H79.conclusion_of_delta_cross_nonzero hBD₁ hBD₂ hzeta_cross
  rcases hnonzero with hx_ne | hy_ne
  · left
    rw [hx]
    exact_mod_cast hx_ne
  · right
    rw [hy]
    exact_mod_cast hy_ne

/-- Virtual-character inputs supply the two integer cross terms needed by the
parity form of Peterfalvi (7.9). -/
theorem conclusion_of_delta_cross_even_of_ZIrr
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hδ₁ : H79.first.delta ∈ ZIrr G)
    (hδ₂ : H79.second.delta ∈ ZIrr G)
    (hζ₁ : H79.firstZetaImage ∈ ZIrr G)
    (hζ₂ : H79.secondZetaImage ∈ ZIrr G)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  obtain ⟨hx, hy, _hz⟩ := H79.delta_cross_integral_of_ZIrr hδ₁ hδ₂ hζ₁ hζ₂
  exact H79.conclusion_of_delta_cross_integral_parity hBD₁ hBD₂ hzeta_cross hx hy
    hdelta_even

/-- Coherence, virtual `Ind 1_H` sources, and irreducible distinguished source
terms supply the integer cross terms needed by the parity form of Peterfalvi
(7.9). -/
theorem conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion := by
  obtain ⟨hδ₁, hδ₂, hζ₁, hζ₂⟩ :=
    H79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
      hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr
  exact H79.conclusion_of_delta_cross_even_of_ZIrr hBD₁ hBD₂ hzeta_cross hδ₁ hδ₂
    hζ₁ hζ₂ hdelta_even

/-- Support-subset form of the weak parity consumer: the `ζ^ν` cross
orthogonality is obtained from disjoint Dade supports. -/
theorem conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity_of_zeta_support
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁Z : H79.first.hyp76.zeta H79.first.ind1H ∈ ZIrr L₁)
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂Z : H79.second.hyp76.zeta H79.second.ind1H ∈ ZIrr L₂)
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hζ₁_supp : H79.firstZetaImage.support ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)
    (hζ₂_supp : H79.secondZetaImage.support ⊆ H79.second.hyp76.hyp71.hyp.dadeSupport)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion :=
  H79.conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁Z hzeta₁_irr hind₂Z hzeta₂_irr hBD₁ hBD₂
    (H79.zetaImage_cross_eq_zero_of_support_subset hζ₁_supp hζ₂_supp) hdelta_even

/-- Coherence and source irreducibility supply the integer cross terms needed by
the parity form of Peterfalvi (7.9). -/
theorem conclusion_of_irreducible_sourceDiff_and_isCoherent_parity
    (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁}
    {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    {A_prime₂ : Set L₂}
    {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hind₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.ind1H))
    (hzeta₁_irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hind₂_irr : IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.ind1H))
    (hzeta₂_irr :
      IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    (hBD₁ : H79.first.BetaDecomp) (hBD₂ : H79.second.BetaDecomp)
    (hzeta_cross : ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0)
    (hdelta_even : ∃ z : ℤ,
      ClassFunction.inner H79.first.delta H79.second.delta = (z : ℂ) ∧ Even z) :
    H79.conclusion :=
  H79.conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
    hcoh₁ hnu₁ hcoh₂ hnu₂ hind₁_irr.mem_ZIrr hzeta₁_irr
    hind₂_irr.mem_ZIrr hzeta₂_irr hBD₁ hBD₂ hzeta_cross hdelta_even

end Hypothesis79

end Section_7_9

section OrthogonalIntegerDecomposition

variable {ι : Type*}
variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- Integer-coefficient Pythagoras bridge used in Peterfalvi (7.10): if a class
function decomposes as an orthogonal integer combination plus an orthogonal
residual, then an upper bound on its norm bounds the sum of the diagonal weights
for every nonzero coefficient. -/
theorem sum_weights_le_of_orthogonal_integer_decomposition
    (B : Finset ι) (v : ι → ClassFunction G ℂ) (x : ι → ℤ) (m : ι → ℝ)
    (Γ Γ₁ : ClassFunction G ℂ) (M : ℝ)
    (hΓ : Γ = (∑ i ∈ B, (((x i : ℝ) : ℂ) • v i)) + Γ₁)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then (m i : ℂ) else 0)
    (hΓ₁ : ∀ i ∈ B, ClassFunction.inner Γ₁ (v i) = 0)
    (hm_nonneg : ∀ i ∈ B, 0 ≤ m i)
    (hx_nonzero : ∀ i ∈ B, x i ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ M) :
    (∑ i ∈ B, m i) ≤ M := by
  classical
  have hpyth := inner_self_orthogonalSum_add_re (G := G) B v
    (fun i => (x i : ℝ)) m Γ₁ horth hΓ₁
  have hΓ_norm : (ClassFunction.inner Γ Γ).re =
      (∑ i ∈ B, (x i : ℝ) ^ 2 * m i) +
        (ClassFunction.inner Γ₁ Γ₁).re := by
    rw [hΓ]
    exact hpyth
  have hsum_le_sq : (∑ i ∈ B, m i) ≤
      ∑ i ∈ B, (x i : ℝ) ^ 2 * m i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hcases : x i ≤ -1 ∨ 1 ≤ x i := by
      have hxi := hx_nonzero i hi
      omega
    have hx_sq : (1 : ℝ) ≤ (x i : ℝ) ^ 2 := by
      rcases hcases with hle | hge
      · have hle' : (x i : ℝ) ≤ -1 := by exact_mod_cast hle
        nlinarith
      · have hge' : (1 : ℝ) ≤ x i := by exact_mod_cast hge
        nlinarith
    simpa [one_mul] using mul_le_mul_of_nonneg_right hx_sq (hm_nonneg i hi)
  have hΓ₁_nonneg : 0 ≤ (ClassFunction.inner Γ₁ Γ₁).re :=
    inner_self_re_nonneg Γ₁
  rw [hΓ_norm] at hΓ_bound
  linarith

open scoped Classical in
/-- Rational-valued version of the integer-coefficient Pythagoras bridge.  This
matches the `𝓑`-sum in Peterfalvi (7.10), whose weights are rational ratios such
as `(h_j - 1) / e_j`, while the norm inequality lives in `ℝ`. -/
theorem sum_rat_weights_le_of_orthogonal_integer_decomposition
    (B : Finset ι) (v : ι → ClassFunction G ℂ) (x : ι → ℤ) (m : ι → ℚ)
    (Γ Γ₁ : ClassFunction G ℂ) (M : ℚ)
    (hΓ : Γ = (∑ i ∈ B, (((x i : ℝ) : ℂ) • v i)) + Γ₁)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then (m i : ℂ) else 0)
    (hΓ₁ : ∀ i ∈ B, ClassFunction.inner Γ₁ (v i) = 0)
    (hm_nonneg : ∀ i ∈ B, 0 ≤ m i)
    (hx_nonzero : ∀ i ∈ B, x i ≠ 0)
    (hΓ_bound : (ClassFunction.inner Γ Γ).re ≤ (M : ℝ)) :
    (∑ i ∈ B, m i) ≤ M := by
  have horth_real : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) =
        if i = j then (((m i : ℝ) : ℂ)) else 0 := by
    intro i hi j hj
    simpa using horth i hi j hj
  have hm_nonneg_real : ∀ i ∈ B, 0 ≤ (m i : ℝ) := by
    intro i hi
    exact_mod_cast hm_nonneg i hi
  have hreal := sum_weights_le_of_orthogonal_integer_decomposition
    B v x (fun i => (m i : ℝ)) Γ Γ₁ (M : ℝ) hΓ horth_real hΓ₁ hm_nonneg_real
    hx_nonzero hΓ_bound
  have hcast : ((∑ i ∈ B, m i) : ℝ) ≤ (M : ℝ) := by
    simpa using hreal
  exact_mod_cast hcast

end OrthogonalIntegerDecomposition

/- 7.10-7.11: the Frobenius-family non-existence theorem (pp. 42-43) -/

/-- **Peterfalvi (7.10) hypothesis.** A family of `k` Frobenius subgroups of `G`
whose kernels are pairwise-coprime TI-subsets.

This bundles conditions (a)-(c) of (7.10):
* `(a)` each `L i` is a Frobenius group with kernel `H i` (`isFrobenius`);
* `(b)` `H i` is `L i`-normal with `L i = N_G(H i)`, and `(H i)^#` is a TI-subset
  of `G` with normalizer `L i` (`normalizer_eq`, `isTI`);
* `(c)` the kernel orders `|H i|` are pairwise coprime (`coprime_kernel`),
together with `k ≥ 2` (`two_le`).  Condition (d) — the definition of `G₀` — is
recorded separately as `FrobeniusFamily.G0`. -/
structure FrobeniusFamily (G : Type*) [Group G] (k : ℕ) where
  /-- The Frobenius subgroups `L_i ≤ G`. -/
  L : Fin k → Subgroup G
  /-- The Frobenius kernels `H_i ⊴ L_i`. -/
  H : Fin k → Subgroup G
  /-- (7.10): the family has at least two members. -/
  two_le : 2 ≤ k
  /-- Each kernel sits inside its host. -/
  kernel_le : ∀ i, H i ≤ L i
  /-- (7.10)(a): each `L_i` is a Frobenius group with kernel `H_i`, for some
  Frobenius complement `C`. -/
  isFrobenius : ∀ i, ∃ C : Subgroup ↥(L i),
    IsFrobeniusGroup ↥(L i) ((H i).subgroupOf (L i)) C
  /-- (7.10)(b), host part: `L_i` is the normalizer of `H_i` in `G`. -/
  normalizer_eq : ∀ i, L i = Subgroup.normalizer (H i : Set G)
  /-- (7.10)(b), TI part: `H_i^#` is a TI-subset of `G` with normalizer `L_i`. -/
  isTI : ∀ i, IsTISubset ((H i : Set G) \ {1}) (L i)
  /-- (7.10)(c): the kernel orders are pairwise coprime. -/
  coprime_kernel : ∀ ⦃i j⦄, i ≠ j → Nat.Coprime (Nat.card (H i)) (Nat.card (H j))

end OddOrder.Peterfalvi.S09
