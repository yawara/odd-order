import OddOrder.Peterfalvi.S15_NuRowPin

/-!
# The bundled coherent extension `τ₁T` (Peterfalvi (13.2.d)/(13.3.c) at `T`)

The `T`-side mirror of the `tau1S_ofHonest` bundling (`S15_CaseACoherence`, issue 2035 #41
step 5): the pinned (9.11)-`T` coherence carrier `sSet_coherent_indT_A_pinned` packaged as

* `coherentIndT_pinned` — the `.choose` of the pinned carrier, an
  `IsCoherent (Ind_T^G) 𝒯 A(T)`;
* `tau1T_ofHonest` — its `.extension`, the (13.2.d) `τ₁T : IntegralCharacterMap ↥T G` that the
  `T`-side (13.4) θ-package threads;
* `tau1T_ofHonest_nuRow_formula` — the `.choose_spec` (13.3.c)-`T` pin: the ν-row images are
  the aligned `η`-rows, cleanly or with the `q = 3` sign-flip row swap;
* `tau1T_ofHonest_nuRow_eta_row` — the **per-row consumable form**: for each nonzero row `r`
  there are `r' ≠ 0` and `δ' = ±1` with `τ₁T(ν_r) = δ'·∑_j η_{r'j}` (clean: `r' = r, δ' = 1`;
  flip: `r'` = the other nonzero row, `δ' = −1`).  ⚠ The (13.4) θ-package's `β`-form must
  quantify the `η`-row separately from the θ-row: in the flip branch `τ₁T(ν_r)` is *not*
  `±∑_j η_{rj}` (the rows genuinely swap), so a same-index form is unprovable — the downstream
  `eta_cross_expansion` contradiction only needs *some* nonzero row, so the split
  quantification is faithful to the book;
* `tau1T_ofHonest_extends_on_supported` — `τ₁T = Ind_T^G` on the `A(T)`-supported span
  ((13.2.e) agreement, the conjunct-3 producer);
* `tau1T_ofHonest_image_inner_eta_eq_zero` — the (5.3.b)-`T` grid orthogonality of the
  `τ₁T`-images of irreducible `𝒯`-members (the conjunct-4 producer).

The pin is **bundled at construction** (`[[lean-nonempty-some-erases-witness-pin]]`): it is not
invariant across inhabitants (the `q = 3` flip), so it cannot be recovered from a bare
`Nonempty.some`.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The pinned (9.11)-`T` coherence carrier** (mirror of `coherent_H0Cprime_S`): the
`.choose` of `sSet_coherent_indT_A_pinned`.  Its `.extension` is `tau1T_ofHonest`; the pin
formula is `tau1T_ofHonest_nuRow_formula`. -/
noncomputable def Hypothesis.coherentIndT_pinned [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T) :=
  (hyp.sSet_coherent_indT_A_pinned hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief).choose

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The coherent extension `τ₁T` for the honest `T`-instance** (mirror of `tau1S_ofHonest`):
the `.extension` of the pinned (9.11)-`T` coherence.  This is the (13.2.d)
`τ₁T : IntegralCharacterMap ↥T G` that the `T`-side (13.4) θ-package threads. -/
noncomputable def Hypothesis.tau1T_ofHonest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G :=
  (hyp.coherentIndT_pinned hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief).extension

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c)-at-`T`, the ν-row formula for `τ₁T = tau1T_ofHonest`** (mirror of
`tau1S_ofHonest_muColumn_formula`; Coq `FTtypeP_coherence` with `typeP_TIred_coherent`'s
global-sign disjunction, transposed): the (9.11)-`T` coherent extension sends every reducible
ν-row sum `ν_i = ∑_j ν_{ij}` (`i ≠ 0`) to the aligned `η`-row sum `∑_j η_{ij}` — either
uniformly, or (the `q = 3` sign-flip exception) with a global negative sign and the two nonzero
rows swapped.  The `.choose_spec` of the pinned carrier. -/
theorem Hypothesis.tau1T_ofHonest_nuRow_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    (∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      hyp.tau1T_ofHonest hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu i j)
        = ∑ j : Fin hyp.p, hyp.eta i j) ∨
    (hyp.q = 3 ∧ ∀ i i' : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      i' ≠ ⟨0, hyp.q_prime.pos⟩ → i ≠ i' →
      hyp.tau1T_ofHonest hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu i j)
        = -∑ j : Fin hyp.p, hyp.eta i' j) :=
  (hyp.sSet_coherent_indT_A_pinned hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief).choose_spec

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The per-row (13.3.c)-`T` formula** (the row-transposed mirror of
`tau1S_ofHonest_mu_col_eta_col_one`'s shape, generalized to an arbitrary source row): for each
nonzero row `r` there are a nonzero row `r'` and a sign `δ' = ±1` with
`τ₁T(ν_r) = δ'·∑_j η_{r'j}` — clean: `r' = r`, `δ' = 1`; the `q = 3` flip: `r'` = the other
nonzero row, `δ' = −1`.  This is the exact `β`-form input of the (13.4) θ-package's conjunct 3
(where the `η`-row index must be quantified separately from the θ-row). -/
theorem Hypothesis.tau1T_ofHonest_nuRow_eta_row [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    {r : Fin hyp.q} (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) :
    ∃ (r' : Fin hyp.q) (δ' : ℤ), r' ≠ ⟨0, hyp.q_prime.pos⟩ ∧ (δ' = 1 ∨ δ' = -1) ∧
      hyp.tau1T_ofHonest hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu r j)
        = (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r' j := by
  classical
  rcases hyp.tau1T_ofHonest_nuRow_formula hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief with
    hclean | ⟨hq3, hflip⟩
  · -- clean branch: `r' = r`, `δ' = 1`
    exact ⟨r, 1, hr, Or.inl rfl, by rw [hclean r hr]; push_cast; rw [one_smul]⟩
  · -- `q = 3` sign-flip branch: `r'` = the other nonzero row, `δ' = −1`
    have h1lt : 1 < hyp.q := hyp.q_prime.one_lt
    have h2lt : 2 < hyp.q := by omega
    have hrval : r.val = 1 ∨ r.val = 2 := by
      have hlt := r.isLt
      have h0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
      omega
    rcases hrval with h1 | h2
    · -- `r.val = 1`: the other row is `⟨2⟩`
      have hr'0 : (⟨2, h2lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
        intro h; exact absurd (congrArg Fin.val h) (by norm_num)
      have hrne : r ≠ ⟨2, h2lt⟩ := by
        intro h
        have h2v : r.val = 2 := by rw [h]
        omega
      refine ⟨⟨2, h2lt⟩, -1, hr'0, Or.inr rfl, ?_⟩
      rw [hflip r ⟨2, h2lt⟩ hr hr'0 hrne]
      push_cast
      rw [neg_one_smul]
    · -- `r.val = 2`: the other row is `⟨1⟩`
      have hr'0 : (⟨1, h1lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
        intro h; exact absurd (congrArg Fin.val h) one_ne_zero
      have hrne : r ≠ ⟨1, h1lt⟩ := by
        intro h
        have h1v : r.val = 1 := by rw [h]
        omega
      refine ⟨⟨1, h1lt⟩, -1, hr'0, Or.inr rfl, ?_⟩
      rw [hflip r ⟨1, h1lt⟩ hr hr'0 hrne]
      push_cast
      rw [neg_one_smul]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁T = Ind_T^G` on the `A(T)`-supported span** (mirror of
`tau1S_ofHonest_extends_on_supported`; the (13.2.e) agreement, the conjunct-3 producer of the
(13.4) θ-package): the coherent extension agrees with plain induction on every `A(T)`-supported
lattice element of `ℤ[𝒯]`. -/
theorem Hypothesis.tau1T_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (φ : ClassFunction ↥hyp.T ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T)) :
    hyp.tau1T_ofHonest hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief φ
      = ClassFunction.induce hyp.T φ := by
  have h := (hyp.coherentIndT_pinned hG hnoV pins hvd hT2 Tdata hU hW1 hW2
    chief).extends_on_supported φ hφ
  simpa [Hypothesis.tau1T_ofHonest, Hypothesis.indT_apply] using h

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(5.3.b)-at-`T` for `τ₁T = tau1T_ofHonest`** (the conjunct-4 producer of the (13.4)
θ-package): the `τ₁T`-image of an irreducible `𝒯`-member is orthogonal to the entire `η`-grid.
The engine `coherentIndT_image_inner_eta_eq_zero` instantiated at the pinned carrier, with the
family inputs discharged from the landed `𝒯`-facts (conjugate-closure, no-real via `|T|` odd,
conjugate-difference `A(T)`-support). -/
theorem Hypothesis.tau1T_ofHonest_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    {ζ : ClassFunction ↥hyp.T ℂ} (hζ : ζ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief ζ)
        (hyp.eta i j) = 0 :=
  coherentIndT_image_inner_eta_eq_zero hG hnoV hyp hT2 Tdata hW1 hW2
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd))
    (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG))
    (fun ζ' hζ' => by
      rw [show ζ' - ζ'.conj = -(ζ'.conj - ζ') from by abel, ClassFunction.support_neg]
      exact hyp.sSet_member_conjDiff_supported_T hG hvd hζ')
    (hyp.coherentIndT_pinned hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief) hζ hζirr

end OddOrder.Peterfalvi.S15
