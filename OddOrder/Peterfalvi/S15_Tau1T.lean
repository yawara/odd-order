import OddOrder.Peterfalvi.S15_NuRowPin
import OddOrder.Peterfalvi.S15_CaseACoherence

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

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`ℤ[𝒯]`-elements are supported in `A(T) ∪ {1}`** (mirror of `zSpan_sSet_support_subset`):
the `zSpan`-closure of the member-level support fact `sSet_member_support_subset_T`. -/
theorem Hypothesis.zSpan_sSet_support_subset_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T ∪ {1} := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hyp.sSet_member_support_subset_T hG hvd hx
  | zero => simp
  | add x y _ _ hx hy =>
      exact (ClassFunction.support_add_subset x y).trans (Set.union_subset hx hy)
  | smul z x _ hx =>
      refine subset_trans ?_ hx
      rw [← Int.cast_smul_eq_zsmul ℂ z x]
      exact ClassFunction.support_smul_subset _ x

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Degree-`0` elements of `ℤ[𝒯]` are `A(T)`-supported** (mirror of
`zSpan_sSet_degree_zero_support`; the (13.2.e)-input support step for the
`tau1T_apply_induce_sub` supply). -/
theorem Hypothesis.zSpan_sSet_degree_zero_support_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd)))
    (hφ1 : φ (1 : ↥hyp.T) = 0) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.T) hyp.T := by
  intro z hz
  rcases hyp.zSpan_sSet_support_subset_T hG hvd hφ hz with h | h
  · exact h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact absurd hφ1 hz

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(1.5.a)-at-`T`, the `K`-induced membership** (mirror of `induce_H_mem_zSpan_S`): for an
irreducible `θ` of `K = QD` with `Q ⊄ Ker θ`, the induction `Ind_K^T θ` lies in `ℤ[𝒯]`.

Two-stage induction through `T' = huSub(setupT)` (`induce_induce_subgroupOf`, `K ≤ T'` from
`T' = QV`): the inner induction expands into `T'`-constituents with `ℕ`-coefficients, and each
constituent `s` with nonzero coefficient has `Q ⊄ Ker s` (the constituent kernel step
`constituent_P_not_subset_characterKernel` at `P := Q`), so `Ind_{T'}^T s ∈ 𝒯 = sSet(setupT)`
(the `xiSet` kernel filter is exactly `hInHu = Q.subgroupOf T'` by
`toTypesIIIIIIVSetupT_H_eq`). -/
theorem Hypothesis.induce_K_mem_zSpan_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ ∈
      OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.T).subgroupOf hyp.T) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.K.subgroupOf hyp.T) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hyp.K.subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set data := hyp.toTypesIIIIIIVSetupT hG hvd with hdata
  -- Work with the §9 induction carrier `HU = huSub data`, equal to `T' = derivedInG T` in `↥T`.
  set HU : Subgroup ↥hyp.T := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.T).subgroupOf hyp.T :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  letI : Fintype ↥HU := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `K = QD ≤ T' = HU`.
  have hKderiv : hyp.K ≤ derivedInG hyp.T := by
    show hyp.Q ⊔ hyp.D ≤ derivedInG hyp.T
    rw [hyp.T_deriv_eq_QV]
    exact sup_le le_sup_left (le_trans (hyp.D_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.K.subgroupOf hyp.T ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.T hKderiv
  letI : Fintype ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The transport `θ' = θ ∘ e` of `θ` onto `K' = K.subgroupOf HU ≤ HU`.
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  -- Two-stage induction: `Ind_K^T θ = Ind_{HU}^T (Ind_{K'}^{HU} θ')`.
  rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ]
  -- Expand the inner induction into `HU`-constituents and push `Ind_{HU}^T` inside.
  rw [OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
    ClassFunction.induce_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [ClassFunction.induce_smul]
  -- The coefficient `⟨θ', Res s⟩` is a non-negative integer `(k : ℂ)`.
  have hResChar : IsCharacter (ClassFunction.restrict
      ((hyp.K.subgroupOf hyp.T).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
  obtain ⟨k, hk⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
  have hc : ClassFunction.inner
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
      (ClassFunction.restrict ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
        (s : ClassFunction ↥HU ℂ)) = (k : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hk, star_natCast]
  rw [hc, Nat.cast_smul_eq_nsmul ℂ k (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · refine nsmul_mem ?_ k
    -- `Q (in HU) ⊄ ker s`: kernel step from `Q ⊄ ker θ'` (from `hθQ`) and constituent `θ'`.
    have hθ'Q : ¬ ((((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
          ((hyp.K.subgroupOf hyp.T).subgroupOf HU) :
        Set ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
      rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
      have himg : (((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
            ((hyp.K.subgroupOf hyp.T).subgroupOf HU)).map
            (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          = (hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) := by
        ext y
        rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        rfl
      rw [himg]; exact hθQ
    refine Submodule.subset_span ?_
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    -- `s ∈ xiSet data`: `hInHu data ⊄ ker s`, with `hInHu = (Q.subgroupOf T).subgroupOf HU`.
    show ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.Q.subgroupOf hyp.T).subgroupOf HU : Set ↥HU) := by
      congr 1
      show (data.H.subgroupOf hyp.T).subgroupOf HU = (hyp.Q.subgroupOf hyp.T).subgroupOf HU
      rw [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
    rw [hHInHu]
    -- The generic kernel step: `θ'` is a constituent of `Res s` (coefficient `k > 0`), and
    -- `Q (in HU) ⊄ ker θ'` (`hθ'Q`), so `Q (in HU) ⊄ ker s`.
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hc]; exact_mod_cast hk0.ne'
    exact constituent_P_not_subset_characterKernel ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
      ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'Q s hs

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(1.5.a)-at-`T`, `ℤ[𝒯 ∩ Irr T]` membership for irreducible `K`-inductions** (mirror of
`induce_H_mem_zSpan_sSet_irr`; Coq `S1cases` irreducible branch at `T`): if additionally
`Ind_K^T θ` is itself irreducible, every nonzero-coefficient `T'`-constituent induction is an
*irreducible* member of `𝒯`.  Otherwise some constituent is a ν-row
(`sSet_reducible_eq_nuRowSum`) — but `⟨Ind_K θ, ν_i⟩ = 0` (distinct-source `K`-inductions of
the irreducible `Ind_K θ` vs the reducible `ν_i = Ind_K θ_i`, `nu_i_isIndQD`), while the
constituent expansion makes that inner product a sum of non-negative integers with the
offending term `k·p > 0`. -/
theorem Hypothesis.induce_K_mem_zSpan_sSet_irr_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) :
    ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ ∈
      OddOrder.Peterfalvi.S07.zSpan
        {ψ : ClassFunction ↥hyp.T ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.T := Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.T).subgroupOf hyp.T) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.K.subgroupOf hyp.T) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hyp.K.subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set data := hyp.toTypesIIIIIIVSetupT hG hvd with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  set HU : Subgroup ↥hyp.T := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.T).subgroupOf hyp.T :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  letI : Fintype ↥HU := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hKderiv : hyp.K ≤ derivedInG hyp.T := by
    show hyp.Q ⊔ hyp.D ≤ derivedInG hyp.T
    rw [hyp.T_deriv_eq_QV]
    exact sup_le le_sup_left (le_trans (hyp.D_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.K.subgroupOf hyp.T ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.T hKderiv
  letI : Fintype ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  have hθ'Q : ¬ ((((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
        ((hyp.K.subgroupOf hyp.T).subgroupOf HU) :
      Set ↥((hyp.K.subgroupOf hyp.T).subgroupOf HU)) ⊆
    OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
    rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
    have himg : (((hyp.Q.subgroupOf hyp.T).subgroupOf HU).subgroupOf
          ((hyp.K.subgroupOf hyp.T).subgroupOf HU)).map
          (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) := by
      ext y
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      rfl
    rw [himg]; exact hθQ
  -- Two-stage constituent expansion with `ℕ`-coefficients `k s`.
  have hzeta : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      = ∑ s : IrreducibleCharacter ↥HU,
          ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
            (ClassFunction.restrict ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
              (s : ClassFunction ↥HU ℂ))
            • ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) := by
    rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ,
      OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
      ClassFunction.induce_sum]
    exact Finset.sum_congr rfl fun s _ => ClassFunction.induce_smul _ _ _
  have hcoefNat : ∀ s : IrreducibleCharacter ↥HU, ∃ n : ℕ,
      ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) = (n : ℂ) := by
    intro s
    have hResChar : IsCharacter (ClassFunction.restrict
        ((hyp.K.subgroupOf hyp.T).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
      OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
    obtain ⟨n, hn⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
    exact ⟨n, by rw [OddOrder.RepresentationTheory.inner_conj_symm, hn, star_natCast]⟩
  choose k hk using hcoefNat
  -- Nonzero-coefficient constituents give family members (`Q ⊄ Ker s`, membership by witness).
  have hmem : ∀ s : IrreducibleCharacter ↥HU, k s ≠ 0 →
      ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈ sSet data := by
    intro s hks
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    show ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.Q.subgroupOf hyp.T).subgroupOf HU : Set ↥HU) := by
      congr 1
      show (data.H.subgroupOf hyp.T).subgroupOf HU = (hyp.Q.subgroupOf hyp.T).subgroupOf HU
      rw [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
    rw [hHInHu]
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hk s]; exact_mod_cast hks
    exact constituent_P_not_subset_characterKernel ((hyp.Q.subgroupOf hyp.T).subgroupOf HU)
      ((hyp.K.subgroupOf hyp.T).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'Q s hs
  -- **The upgrade**: every nonzero-coefficient constituent induction is irreducible.
  have hirrall : ∀ s : IrreducibleCharacter ↥HU, k s ≠ 0 →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ)) := by
    intro s₀ hk₀
    by_contra hred
    -- a reducible member is a nonzero ν-row ((13.3.a)-at-`T` reverse dichotomy)
    obtain ⟨i, hi, hνeq₀⟩ := hyp.sSet_reducible_eq_nuRowSum hG pins hvd (hmem s₀ hk₀) hred
    obtain ⟨θi, hθiirr, -, hνeq⟩ := hyp.nu_i_isIndQD hG pins i hi
    -- `Ind θ ≠ ν_i` (irreducible vs. reducible), so the distinct `K`-inductions are orthogonal
    have hne' : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        ≠ ClassFunction.induce (hyp.K.subgroupOf hyp.T) θi := by
      intro h
      exact hyp.nuRow_not_irreducible pins i (by rw [hνeq, ← h]; exact hind)
    haveI hKnorm : (hyp.K.subgroupOf hyp.T).Normal := hyp.K_subgroupOf_T_normal hG
    have hzmu : ClassFunction.inner (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        (∑ j : Fin hyp.p, hyp.nu i j) = 0 := by
      rw [hνeq]
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj
        (⟨θ, hθ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _)
        (⟨θi, hθiirr⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _) ?_
      intro g hg
      apply hne'
      have h1 : ClassFunction.induce (hyp.K.subgroupOf hyp.T)
          ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g
              (⟨θ, hθ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter _) :
            OddOrder.RepresentationTheory.IrreducibleCharacter _) :
              ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
          = ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ := by
        rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
        exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
          (G := ↥hyp.T) (H := hyp.K.subgroupOf hyp.T) g _
      rw [← h1, hg]
    -- expand `⟨Ind θ, ν_i⟩` through the constituent sum: non-negative integer terms
    have hexp : ClassFunction.inner (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)
        (∑ j : Fin hyp.p, hyp.nu i j)
        = ∑ s : IrreducibleCharacter ↥HU, (k s : ℂ) *
            ClassFunction.inner (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
              (∑ j : Fin hyp.p, hyp.nu i j) := by
      rw [hzeta, OddOrder.RepresentationTheory.inner_sum_left]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hk s, OddOrder.RepresentationTheory.ClassFunction.inner_smul_left]
    have hνmem : (∑ j : Fin hyp.p, hyp.nu i j) ∈ sSet data :=
      OddOrder.Peterfalvi.S11.sOf_subset_sSet data chief.H0
        (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief i hi)
    have hterm : ∀ s : IrreducibleCharacter ↥HU, ∃ n : ℕ,
        (k s : ℂ) * ClassFunction.inner (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))
          (∑ j : Fin hyp.p, hyp.nu i j) = (n : ℂ) := by
      intro s
      rcases Nat.eq_zero_or_pos (k s) with h0 | hpos
      · exact ⟨0, by rw [h0]; simp⟩
      · by_cases heq : ClassFunction.induce HU (s : ClassFunction ↥HU ℂ)
            = ∑ j : Fin hyp.p, hyp.nu i j
        · refine ⟨k s * hyp.p, ?_⟩
          rw [heq, hyp.nuRow_inner pins i i, if_pos rfl]
          push_cast
          ring
        · refine ⟨0, ?_⟩
          rw [sSet_pairwiseOrthogonal data (hmem s hpos.ne') hνmem heq, mul_zero, Nat.cast_zero]
    choose n hn using hterm
    -- the total is `0`, so every `ℕ`-term vanishes — but the `s₀`-term is `k s₀ · p > 0`
    have hsumC : ∑ s : IrreducibleCharacter ↥HU, ((n s : ℕ) : ℂ) = 0 := by
      rw [Finset.sum_congr rfl fun s _ => (hn s).symm, ← hexp, hzmu]
    have hsumN : ∑ s : IrreducibleCharacter ↥HU, n s = 0 := by
      rw [← Nat.cast_sum] at hsumC
      exact_mod_cast hsumC
    have hn0 : n s₀ = 0 :=
      (Finset.sum_eq_zero_iff.mp hsumN) s₀ (Finset.mem_univ s₀)
    have hval : (k s₀ : ℂ) * ClassFunction.inner
        (ClassFunction.induce HU (s₀ : ClassFunction ↥HU ℂ))
        (∑ j : Fin hyp.p, hyp.nu i j) = (k s₀ : ℂ) * (hyp.p : ℂ) := by
      rw [hνeq₀, hyp.nuRow_inner pins i i, if_pos rfl]
    have : ((n s₀ : ℕ) : ℂ) ≠ 0 := by
      rw [← hn s₀, hval]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hk₀)
        (Nat.cast_ne_zero.mpr hyp.p_prime.pos.ne')
    exact this (by rw [hn0, Nat.cast_zero])
  -- assemble: the expansion lands in `ℤ[𝒯 ∩ Irr T]`
  rw [hzeta]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [hk s]
  rcases Nat.eq_zero_or_pos (k s) with h0 | hpos
  · rw [h0]; simp
  · rw [Nat.cast_smul_eq_nsmul ℂ (k s)]
    have hmemIrr : ClassFunction.induce HU (s : ClassFunction ↥HU ℂ) ∈
        {ψ : ClassFunction ↥hyp.T ℂ | ψ ∈ sSet data ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} :=
      ⟨hmem s hpos.ne', hirrall s hpos.ne'⟩
    exact nsmul_mem (Submodule.subset_span hmemIrr) (k s)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁T`-images of `ℤ[𝒯 ∩ Irr T]` are orthogonal to the `η`-grid** (mirror of
`tau1S_ofHonest_zSpanIrr_inner_eta`): span induction over the (5.3.b)-`T` crux. -/
theorem Hypothesis.tau1T_ofHonest_zSpanIrr_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (i : Fin hyp.q) (j : Fin hyp.p)
    {φ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥hyp.T ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) ∧
        OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ}) :
    ClassFunction.inner
      (hyp.tau1T_ofHonest hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief φ)
      (hyp.eta i j) = 0 := by
  haveI := hyp.finiteG
  induction hφ using Submodule.span_induction with
  | mem ζ hζ =>
      exact hyp.tau1T_ofHonest_image_inner_eta_eq_zero hG hnoV pins hvd hT2 Tdata hU hW1 hW2
        chief hζ.1 hζ.2 i j
  | zero => rw [map_zero, OddOrder.RepresentationTheory.ClassFunction.inner_zero_left]
  | add x y _ _ hx hy =>
      rw [map_add, OddOrder.RepresentationTheory.ClassFunction.inner_add_left, hx, hy, add_zero]
  | smul z x _ hx =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ z,
        OddOrder.RepresentationTheory.ClassFunction.inner_smul_left, hx, mul_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(4.1)+(5.3.b) conjunct-4 producer for the (13.4) θ-package** (mirror of
`tau1S_ofHonest_induce_inner_eta`): for an irreducible `θ` on `K = QD` (`Q ⊄ Ker θ`) whose
induction `Ind_K^T θ` is irreducible, the `τ₁T`-image is orthogonal to the whole `η`-grid.
Composition of the `ℤ[𝒯 ∩ Irr T]` membership (`induce_K_mem_zSpan_sSet_irr_T`) with the
span-level grid orthogonality (`tau1T_ofHonest_zSpanIrr_inner_eta`). -/
theorem Hypothesis.tau1T_ofHonest_induce_inner_eta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (i : Fin hyp.q) (j : Fin hyp.p)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) :
    ClassFunction.inner (hyp.eta i j)
      (hyp.tau1T_ofHonest hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) = 0 := by
  haveI := hyp.finiteG
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    hyp.tau1T_ofHonest_zSpanIrr_inner_eta hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief i j
      (hyp.induce_K_mem_zSpan_sSet_irr_T hG pins hvd θ hθ hθQ hind),
    star_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(13.2.e) conjunct-3 producer for the (13.4) θ-package** (mirror of
`tau1S_ofHonest_apply_induce_sub`, with the degree-`1` hypotheses explicit instead of routing
through `K`-commutativity): for degree-one irreducibles `θ, θ'` on `K = QD` with `Q ⊄ Ker`
both, `τ₁T` agrees with `Ind_T^G` on the difference `Ind_K θ − Ind_K θ'`.  Both inductions lie
in `ℤ[𝒯]` (`induce_K_mem_zSpan_T`); the difference vanishes at `1` (equal degrees `[T:K]`), so
it is `A(T)`-supported (`zSpan_sSet_degree_zero_support_T`) and `extends_on_supported`
evaluates `τ₁T` as `Ind_T^G` there. -/
theorem Hypothesis.tau1T_ofHonest_apply_induce_sub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (θ θ' : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθ1 : θ 1 = 1) (hθ'1 : θ' 1 = 1)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'Q : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    hyp.tau1T_ofHonest hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief
        (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
          - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ')
      = ClassFunction.induce hyp.T
          (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
            - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ') := by
  haveI := hyp.finiteG
  have hmem := hyp.induce_K_mem_zSpan_T hG hvd θ hθ hθQ
  have hmem' := hyp.induce_K_mem_zSpan_T hG hvd θ' hθ' hθ'Q
  have hsub : ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
        - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ'
      ∈ OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :=
    Submodule.sub_mem _ hmem hmem'
  have hdeg : (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ
      - ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ') (1 : ↥hyp.T) = 0 := by
    rw [ClassFunction.sub_apply,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
      OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, hθ'1, sub_self]
  exact hyp.tau1T_ofHonest_extends_on_supported hG hnoV pins hvd hT2 Tdata hU hW1 hW2 chief _
    ⟨hsub, hyp.zSpan_sSet_degree_zero_support_T hG hvd hsub hdeg⟩

/-! ### The (13.4) "pairwise orthogonal" dirr bricks (conjunct-5 producers)

Peterfalvi (13.4) needs `⟨λ^{τ₁S}, θ^{τ₁T}⟩ = 0` for the final `0 = ±(η_{rs}, η_{rs})`
contradiction; the book cites "(4.1) and (5.3.b): the functions `η_ij`, `λ^{τ₁}` and `θ^{τ₁}`
are pairwise orthogonal", with the cross-`τ` input being the disjoint-support orthogonality
`((λ−λ̄)^τ, (θ−θ̄)^τ) = 0`.  The two generic bricks: a norm-one `ℤ`-irreducible pair `A, B`
with `⟨A,B⟩ = 0` whose difference is conjugation-antisymmetric forces `B = Ā` with a non-real
constituent (`conj_eq_of_norm_one_conj_antisym`); two such pairs with orthogonal differences
have orthogonal leads (`inner_eq_zero_of_conj_diff_orthogonal`). -/

/-- Conjugation commutes with integer-cast scalars: `conj(ε•φ) = ε•conj(φ)` for `ε : ℤ`. -/
theorem ClassFunction.conj_intCast_smul {G : Type*} [Group G] (ε : ℤ)
    (φ : ClassFunction G ℂ) :
    ((ε : ℂ) • φ).conj = (ε : ℂ) • φ.conj :=
  ClassFunction.ext fun g => by
    rw [ClassFunction.conj_apply, ClassFunction.smul_apply, ClassFunction.smul_apply,
      ClassFunction.conj_apply, star_mul', star_intCast]

open scoped FiniteInduce in
/-- **The dirr conjugate identification** (the "(4.1)" step of Peterfalvi (13.4)): if `A, B`
are norm-one `ℤ`-irreducible virtual characters with `⟨A, B⟩ = 0` and the difference is
conjugation-antisymmetric (`Ā − B̄ = B − A` — automatic when `A − B` is a `conj`-negated
induced character), then `B = Ā`, and the common constituent is non-real (`⟨A, Ā⟩ = 0`). -/
theorem conj_eq_of_norm_one_conj_antisym {G : Type*} [Group G] [Finite G]
    {A B : ClassFunction G ℂ}
    (hAZ : A ∈ ZIrr G) (hBZ : B ∈ ZIrr G)
    (hA1 : ClassFunction.inner A A = 1) (hB1 : ClassFunction.inner B B = 1)
    (hAB : ClassFunction.inner A B = 0)
    (hconj : A.conj - B.conj = B - A) :
    B = A.conj ∧ ClassFunction.inner A A.conj = 0 := by
  classical
  obtain ⟨χA, εA, hεA, hAeq⟩ :=
    OddOrder.Peterfalvi.S16.exists_sign_irr_of_inner_self_one hAZ hA1
  obtain ⟨χB, εB, hεB, hBeq⟩ :=
    OddOrder.Peterfalvi.S16.exists_sign_irr_of_inner_self_one hBZ hB1
  have hεA0 : ((εA : ℂ)) ≠ 0 := by rcases hεA with h | h <;> rw [h] <;> norm_num
  have hεB0 : ((εB : ℂ)) ≠ 0 := by rcases hεB with h | h <;> rw [h] <;> norm_num
  -- distinct constituents: `χA ≠ χB`
  have hχne : (χA : ClassFunction G ℂ) ≠ (χB : ClassFunction G ℂ) := by
    intro h
    rw [hAeq, hBeq, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χB.isIrreducible,
      if_pos h, star_intCast, mul_one] at hAB
    exact (mul_ne_zero hεA0 hεB0) hAB
  -- the rearranged conjugation identity `Ā + A = B + B̄`
  rw [sub_eq_sub_iff_add_eq_add] at hconj
  -- inner the identity with `χA`
  have hkey := congrArg (fun f : ClassFunction G ℂ =>
    ClassFunction.inner f (χA : ClassFunction G ℂ)) hconj
  simp only [ClassFunction.inner_add_left] at hkey
  rw [hAeq, ClassFunction.conj_intCast_smul, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hBeq, ClassFunction.conj_intCast_smul,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible.conj χA.isIrreducible,
    OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χA.isIrreducible,
    OddOrder.RepresentationTheory.irr_cf_inner χB.isIrreducible χA.isIrreducible,
    OddOrder.RepresentationTheory.irr_cf_inner χB.isIrreducible.conj χA.isIrreducible,
    if_pos rfl,
    if_neg (show ¬ ((χB : ClassFunction G ℂ) = (χA : ClassFunction G ℂ)) from
      fun h => hχne h.symm)] at hkey
  -- case on the reality of `χA` and on the `χ̄B = χA` indicator
  by_cases hreal : ((χA : ClassFunction G ℂ)).conj = (χA : ClassFunction G ℂ)
  · -- real `χA`: `2εA = εB·[χ̄B = χA]`, impossible for `εA, εB = ±1`
    exfalso
    rw [if_pos hreal] at hkey
    by_cases hBcA : ((χB : ClassFunction G ℂ)).conj = (χA : ClassFunction G ℂ) <;>
      [rw [if_pos hBcA] at hkey; rw [if_neg hBcA] at hkey] <;>
      rcases hεA with h1 | h1 <;> rcases hεB with h2 | h2 <;>
      rw [h1, h2] at hkey <;> norm_num at hkey
  · -- non-real `χA`: `εA = εB·[χ̄B = χA]` forces the indicator `1` and `εA = εB`
    rw [if_neg hreal] at hkey
    by_cases hBcA : ((χB : ClassFunction G ℂ)).conj = (χA : ClassFunction G ℂ)
    · rw [if_pos hBcA] at hkey
      -- `χB = χ̄A` and `εA = εB`
      have hχBA : (χB : ClassFunction G ℂ) = ((χA : ClassFunction G ℂ)).conj := by
        rw [← hBcA, ClassFunction.conj_conj]
      have hεeq : (εA : ℂ) = (εB : ℂ) := by linear_combination hkey
      refine ⟨?_, ?_⟩
      · rw [hBeq, hχBA, ← hεeq, hAeq, ClassFunction.conj_intCast_smul]
      · rw [hAeq, ClassFunction.conj_intCast_smul, ClassFunction.inner_smul_left,
          OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χA.isIrreducible.conj,
          if_neg (fun h => hreal h.symm), star_intCast]
        ring
    · exfalso
      rw [if_neg hBcA] at hkey
      exact hεA0 (by linear_combination hkey)

open scoped FiniteInduce in
/-- **The (13.4) cross-`τ` orthogonality brick**: for two conjugation-antisymmetric norm-one
pairs `(A, B)` and `(C, D)` (each `B = Ā`, `D = C̄` by `conj_eq_of_norm_one_conj_antisym`) with
orthogonal differences `⟨A − B, C − D⟩ = 0` (the (13.2.e) disjoint-support input), the leads
are orthogonal: `⟨A, C⟩ = 0`.  This is the "pairwise orthogonality of `λ^{τ₁}` and `θ^{τ₁}`"
of Peterfalvi (13.4) — the conjunct-5 producer of the θ-package. -/
theorem inner_eq_zero_of_conj_diff_orthogonal {G : Type*} [Group G] [Finite G]
    {A B C D : ClassFunction G ℂ}
    (hAZ : A ∈ ZIrr G) (hBZ : B ∈ ZIrr G) (hCZ : C ∈ ZIrr G) (hDZ : D ∈ ZIrr G)
    (hA1 : ClassFunction.inner A A = 1) (hB1 : ClassFunction.inner B B = 1)
    (hC1 : ClassFunction.inner C C = 1) (hD1 : ClassFunction.inner D D = 1)
    (hAB : ClassFunction.inner A B = 0) (hCD : ClassFunction.inner C D = 0)
    (hABconj : A.conj - B.conj = B - A) (hCDconj : C.conj - D.conj = D - C)
    (h0 : ClassFunction.inner (A - B) (C - D) = 0) :
    ClassFunction.inner A C = 0 := by
  classical
  obtain ⟨hBeq, hAAc⟩ := conj_eq_of_norm_one_conj_antisym hAZ hBZ hA1 hB1 hAB hABconj
  obtain ⟨hDeq, hCCc⟩ := conj_eq_of_norm_one_conj_antisym hCZ hDZ hC1 hD1 hCD hCDconj
  subst hBeq
  subst hDeq
  obtain ⟨χA, εA, hεA, hAeq⟩ :=
    OddOrder.Peterfalvi.S16.exists_sign_irr_of_inner_self_one hAZ hA1
  obtain ⟨χC, εC, hεC, hCeq⟩ :=
    OddOrder.Peterfalvi.S16.exists_sign_irr_of_inner_self_one hCZ hC1
  have hεA0 : ((εA : ℂ)) ≠ 0 := by rcases hεA with h | h <;> rw [h] <;> norm_num
  have hεC0 : ((εC : ℂ)) ≠ 0 := by rcases hεC with h | h <;> rw [h] <;> norm_num
  -- non-realness of the constituents (from `⟨A, Ā⟩ = 0`, `⟨C, C̄⟩ = 0`)
  have hArealne : ((χA : ClassFunction G ℂ)) ≠ ((χA : ClassFunction G ℂ)).conj := by
    intro h
    rw [hAeq, ClassFunction.conj_intCast_smul, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χA.isIrreducible.conj,
      if_pos h, star_intCast, mul_one] at hAAc
    exact (mul_ne_zero hεA0 hεA0) hAAc
  have hCrealne : ((χC : ClassFunction G ℂ)) ≠ ((χC : ClassFunction G ℂ)).conj := by
    intro h
    rw [hCeq, ClassFunction.conj_intCast_smul, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner χC.isIrreducible χC.isIrreducible.conj,
      if_pos h, star_intCast, mul_one] at hCCc
    exact (mul_ne_zero hεC0 hεC0) hCCc
  by_cases hAC : (χA : ClassFunction G ℂ) = (χC : ClassFunction G ℂ)
  · -- shared constituent: `h0 = ±2 ≠ 0`, contradiction
    exfalso
    have hACc : ((χA : ClassFunction G ℂ)) ≠ ((χC : ClassFunction G ℂ)).conj := by
      intro h
      exact hCrealne (hAC.symm.trans h)
    have hAcC : ((χA : ClassFunction G ℂ)).conj ≠ (χC : ClassFunction G ℂ) := by
      intro h
      exact hArealne ((h.trans hAC.symm).symm)
    have hAcCc : ((χA : ClassFunction G ℂ)).conj = ((χC : ClassFunction G ℂ)).conj := by
      rw [hAC]
    rw [hAeq, hCeq, ClassFunction.conj_intCast_smul, ClassFunction.conj_intCast_smul,
      ← smul_sub, ← smul_sub, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χC.isIrreducible,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χC.isIrreducible.conj,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible.conj χC.isIrreducible,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible.conj
        χC.isIrreducible.conj,
      if_pos hAC, if_neg hACc, if_neg hAcC, if_pos hAcCc] at h0
    rcases hεA with h1 | h1 <;> rcases hεC with h2 | h2 <;>
      rw [h1, h2] at h0 <;> norm_num at h0
  · -- distinct constituents: the lead inner product vanishes
    rw [hAeq, hCeq, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χC.isIrreducible,
      if_neg hAC, star_intCast]
    ring

end OddOrder.Peterfalvi.S15
