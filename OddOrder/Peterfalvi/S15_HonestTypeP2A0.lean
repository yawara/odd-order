/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup
import OddOrder.Peterfalvi.S10_MinimalSimpleStructure

/-!
# Peterfalvi (8.10)/(8.15): the honest type-`P₂` `A₀`-support `A₀(S) = A(S) ∪ V^S`

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §8/§13.

For a type-`P₂` maximal `S`, the Dade support that the §13 machinery actually needs is the **full**
`'A0(S) = 'A(S) ∪ class_support(V_S)` (Coq `FTtypeP_supp0_def`), **not** the smaller `'A(S)`
(`honestTypeP2ASet`).  The `μ`-column differences `μ_{0j} − μ_{01}` are supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S = W ∖ (W₁ ∪ W₂)` has elements with nontrivial `W₂`-component,
hence lies **outside** `S' = derivedInG S ⊇ A(S)`.  So a Dade map built on `'A(S)` alone cannot see
the `V_S`-part of a `μ`-difference (it falls in the arbitrary linear-extension region), which is why
the row-`0` cross-relation `τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` (S15 `tauS_mu_row0_cross`) is not
provable with the `'A(S)`-Dade map (issue 9076).

This file defines the honest type-`P₂` `A₀`-support

`honestTypeP2A0Set M data = honestTypeP2ASet M ∪ conjClassSetIn M (typePV M data)`

using the **correct** `M_σ^#`-indexed `A(S)` (`honestTypeP2ASet`, avoiding the issue-9008 `typePA`
over-claim over `M^#` which includes the escaping non-`σ`-sharp `U^#`), together with the exceptional
`V^M = conjClassSetIn M (typePV M data)`.  The set-level facts (`⊆ M`, non-identity, `M`-conjugation
invariance, `A(S) ⊆ A₀(S)`) are assembled here from the corresponding `honestTypeP2ASet` and `typePV`
facts.  The Dade hypothesis (8.15) for this support — assembled through the `σ`-decomposition engine
`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`, whose `V`-part obligations are vacuous or
generic (`centralizer_typePV_le_M`, `coprime_FT_signalizer_centralizerIn_typePV`,
`conjClassSetIn_typePV_isConj_conj_in_M`) — is the next step (issue 9076 piece 4c).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **The honest type-`P₂` `A₀`-support**: `A₀(S) = A(S) ∪ V^S`, with `A(S) = honestTypeP2ASet S`
(the correct `M_σ^#`-indexed support) and `V^S = conjClassSetIn S (typePV S data)` the `S`-conjugacy
closure of the cyclic-`TI` regular set `V_S = W ∖ (W₁ ∪ W₂)`. -/
def honestTypeP2A0Set (M : Subgroup G) (data : TypePData M) : Set G :=
  honestTypeP2ASet M ∪ conjClassSetIn M (typePV M data)

/-- `A(S) ⊆ A₀(S)`: the honest type-`P₂` support is contained in its `A₀`-completion. -/
theorem honestTypeP2ASet_subset_A0Set {M : Subgroup G} (data : TypePData M) :
    honestTypeP2ASet M ⊆ honestTypeP2A0Set M data :=
  Set.subset_union_left

/-- `W ≤ M` for type-`P` data: the cyclic factor `W = W₁ ⊔ W₂` lands in `M`
(`W₁ ≤ M`; `W₂ ≤ H ⊓ M'' ≤ H ≤ M' ≤ M`). -/
theorem typePData_W_le_M {M : Subgroup G} (data : TypePData M) :
    (data.W : Subgroup G) ≤ M := by
  rw [data.W_eq]
  exact sup_le data.W1_le
    (data.W2_le.trans (le_trans inf_le_left
      (data.H_le.trans (Subgroup.map_subtype_le _))))

/-- `V_S ⊆ M`: the exceptional regular set lands in `M` (it is `⊆ W ≤ M`). -/
theorem typePV_subset_M {M : Subgroup G} (data : TypePData M) :
    typePV M data ⊆ (M : Set G) := fun _ hv =>
  typePData_W_le_M data (((Set.mem_diff _).mp hv).1)

/-- `A₀(S) ⊆ M`: both the `A(S)`-part (`honestTypeP2ASet_subset`) and the `V^S`-part
(`conjClassSetIn` of the `⊆ M` regular set) land in `M`. -/
theorem honestTypeP2A0Set_subset {M : Subgroup G} (data : TypePData M) :
    honestTypeP2A0Set M data ⊆ (M : Set G) := by
  rintro x (hx | hx)
  · exact honestTypeP2ASet_subset hx
  · exact conjClassSetIn_subset (typePV_subset_M data) hx

/-- A `V^M`-element is nonidentity: `V_S` avoids `1` (it is off `W₁ ∋ 1`), preserved under
`M`-conjugation. -/
theorem conjClassSetIn_typePV_one_not_mem {M : Subgroup G} (data : TypePData M) :
    (1 : G) ∉ conjClassSetIn M (typePV M data) := by
  rintro ⟨v, hv, h, -, hconj⟩
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact ((Set.mem_diff _).mp hv).2 (Or.inl (Subgroup.one_mem data.W1))
  exact hv1 (by
    have : v = h⁻¹ * (h * v * h⁻¹) * h := by group
    rw [this, hconj]; group)

/-- `1 ∉ A₀(S)`: both parts avoid the identity (`honestTypeP2ASet_one_not_mem` and
`conjClassSetIn_typePV_one_not_mem`). -/
theorem honestTypeP2A0Set_one_not_mem {M : Subgroup G} (data : TypePData M) :
    (1 : G) ∉ honestTypeP2A0Set M data := by
  rintro (h | h)
  · exact honestTypeP2ASet_one_not_mem h
  · exact conjClassSetIn_typePV_one_not_mem data h

/-- **`A₀(S)` is `M`-conjugation invariant**: both `A(S)` (`honestTypeP2ASet_conj_mem`) and `V^S`
(`mem_conjClassSetIn_conj_iff`) are stable under conjugation by `m ∈ M`. -/
theorem honestTypeP2A0Set_conj_mem [Finite G] {M : Subgroup G} (data : TypePData M) {m : G}
    (hm : m ∈ M) {x : G} :
    m * x * m⁻¹ ∈ honestTypeP2A0Set M data ↔ x ∈ honestTypeP2A0Set M data := by
  simp only [honestTypeP2A0Set, Set.mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inl (by
        have := honestTypeP2ASet_conj_mem (inv_mem hm) h
        rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at this)
    · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mp h)
  · rintro (h | h)
    · exact Or.inl (honestTypeP2ASet_conj_mem hm h)
    · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mpr h)

/-- `∀ x ∈ A₀(S), x ≠ 1` — the `≠ 1` form of `honestTypeP2A0Set_one_not_mem` (the shape the
`σ`-decomposition Dade engine's `hXsharp` obligation takes). -/
theorem honestTypeP2A0Set_ne_one {M : Subgroup G} (data : TypePData M) :
    ∀ x ∈ honestTypeP2A0Set M data, x ≠ (1 : G) :=
  fun _ hx h => honestTypeP2A0Set_one_not_mem data (h ▸ hx)

/-- **A `V^S`-point does not escape `M`**: its centralizer lies in `M`.  For `b = h·v·h⁻¹`
(`v ∈ V_S`, `h ∈ M`), `C_G(b) = h·C_G(v)·h⁻¹ ≤ h·M·h⁻¹ = M` (`centralizer_typePV_le_M`, `h ∈ M`).
This is what makes the `V`-part of the Dade engine's escaping-`σ`-sharp obligation **vacuous**. -/
theorem conjClassSetIn_typePV_centralizer_le_M {M : Subgroup G} (data : TypePData M)
    {b : G} (hb : b ∈ conjClassSetIn M (typePV M data)) :
    Subgroup.centralizer ({b} : Set G) ≤ M := by
  obtain ⟨v, hv, h, hhM, rfl⟩ := hb
  intro x hx
  have hcomm : x * (h * v * h⁻¹) = (h * v * h⁻¹) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  -- `h⁻¹ x h` commutes with `v`, hence lies in `C_G(v) ≤ M`.
  have hcv : (h⁻¹ * x * h) ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (h⁻¹ * x * h) * v
        = h⁻¹ * (x * (h * v * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * v * h⁻¹) * x) * h := by rw [hcomm]
      _ = v * (h⁻¹ * x * h) := by group
  have hxM : (h⁻¹ * x * h) ∈ M :=
    OddOrder.Peterfalvi.S10.centralizer_typePV_le_M data hv hcv
  have hxeq : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [hxeq]
  exact M.mul_mem (M.mul_mem hhM hxM) (M.inv_mem hhM)

/-- **Escaping `A₀(S)`-points come from the `A(S)`-part**: since `V^S`-points do not escape
(`conjClassSetIn_typePV_centralizer_le_M`), any escaping point of `A₀(S)` lies in `A(S)` and escapes
there too.  This reduces the Dade engine's escaping-`σ`-sharp and coprimality obligations for `A₀(S)`
to the already-established `honestTypeP2ASet` ones. -/
theorem escaping_honestTypeP2A0Set_mem_honestTypeP2ASet {M : Subgroup G} (data : TypePData M)
    {a : G} (ha : a ∈ escapingCentralizerSet M (honestTypeP2A0Set M data)) :
    a ∈ escapingCentralizerSet M (honestTypeP2ASet M) := by
  obtain ⟨haA0, haesc⟩ := ha
  rcases haA0 with hpa | hva
  · exact ⟨hpa, haesc⟩
  · exact absurd (conjClassSetIn_typePV_centralizer_le_M data hva) haesc

/-- **(8.13.a), the mixed `A(S)`–`V^S` case is vacuous**: an `A(S)`-point is never `G`-conjugate to a
`V^S`-point.  ⚠ DEEP `'A0(S)`-`normedTI` residual (issue 9076 piece 4c).  An `A(S) = honestTypeP2ASet`
element lies in `S' = derivedInG S`, while a `V^S`-point lies **outside** `S'`
(`typePData_typePV_not_mem_derived`, the nontrivial `W₁`-component).  If they were `G`-conjugate, the
`'A0(S)`-`normedTI` property would force the conjugator into `S` (`= N_G('A0(S))`), hence into
`N_M(S') = M`, so it would preserve `S'` — contradicting `a ∈ S'`, `b ∉ S'`.  But that argument
**uses** `normedTI 'A0(S)`, which is exactly what this datum is being built to establish, so the
vacuity must be shown directly from the type-`P₂` FT-support geometry (Coq `FTsupp0` / BG §16
Theorem II).  The `elementary` coprimality route fails here because `W₂ ⊆ M_σ` (`data.H ≤ M_σ`,
`data.W₂ ≤ data.H`), so `W` genuinely contains `σ`-elements — the pin is genuine deep content, not a
missing arithmetic step. -/
theorem not_isConj_honestTypeP2ASet_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {a b : G}
    (ha : a ∈ honestTypeP2ASet M) (hb : b ∈ conjClassSetIn M (typePV M data))
    (hab : IsConj a b) : False := sorry

/-- **Peterfalvi (8.15) for the honest type-`P₂` `A₀`-support**: the Dade (2.2) support hypotheses
hold for `A₀(S) = A(S) ∪ V^S`.  Assembled through the `σ`-decomposition engine
`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`:

* set-facts (`⊆ M`, `≠ 1`, `M`-conjugation-invariant, nonempty) — the `honestTypeP2A0Set_*` facts;
* escaping-`σ`-sharp and coprimality — reduced to the `A(S)`-part
  (`escaping_honestTypeP2A0Set_mem_honestTypeP2ASet`, since `V^S` does not escape) plus the generic
  `V`-part coprimality (`coprime_FT_signalizer_centralizerIn_typePV`);
* the `isConj → M`-conjugate obligation — the `A`–`A` and `V`–`V` cases are
  `honestTypeP2ASet_isConj_conj_in_M` / `conjClassSetIn_typePV_isConj_conj_in_M`, and the mixed case
  is the vacuity `not_isConj_honestTypeP2ASet_typePV` (the one deep `'A0`-`normedTI` pin).

This is the `S`-side Dade datum the (13.18) row-`0` cross-relation `τ_S(μ_{0j} − μ_{01}) =
η_{0j} − η_{01}` actually needs (the `μ`-differences are `A₀(S)`-supported, not `A(S)`-supported). -/
theorem dadeSupportHypothesisData_honestTypeP2A0Set [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 M) (data : TypePData M) :
    Nonempty (OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M (honestTypeP2A0Set M data)) := by
  classical
  obtain ⟨K₀, U₀, hKM, hUM, hUne, hK, hU, -, -⟩ :=
    OddOrder.BG.Ch4.S16.typeP2_exists_matched_kappa_hall_pair hG hM hP2
  have hKne : K₀ ≠ ⊥ := kappaHall_ne_bot_of_isTypeP2 hP2 hK
  refine OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_of_subset_escaping_sigmaSharp hG hM
    (honestTypeP2A0Set_subset data) (honestTypeP2A0Set_ne_one data)
    (fun a ha => escaping_honestTypeP2ASet_mem_sigmaSharp hG hM hKM hUM hKne hK hU
      (escaping_honestTypeP2A0Set_mem_honestTypeP2ASet data ha))
    ?_ ?_ ?_ ?_
  · -- `isConj → M`-conjugate: A–A / A–V (vacuous) / V–A (vacuous) / V–V.
    intro a ha b hb hab
    rcases ha with hpa | hva
    · rcases hb with hpb | hvb
      · exact honestTypeP2ASet_isConj_conj_in_M hG hM hKM hUM hKne hK hU hpa hpb hab
      · exact (not_isConj_honestTypeP2ASet_typePV hG hM data hpa hvb hab).elim
    · rcases hb with hpb | hvb
      · exact (not_isConj_honestTypeP2ASet_typePV hG hM data hpb hva hab.symm).elim
      · exact OddOrder.Peterfalvi.S10.conjClassSetIn_typePV_isConj_conj_in_M data hva hvb hab
  · -- coprimality: the escaping point is in `A(S)`; `b` is in `A(S)` or `V^S`.
    intro a ha b hb
    have haA := escaping_honestTypeP2A0Set_mem_honestTypeP2ASet data ha
    have haσ := escaping_honestTypeP2ASet_mem_sigmaSharp hG hM hKM hUM hKne hK hU haA
    rcases hb with hpb | hvb
    · exact coprime_FT_signalizer_centralizerIn_honestTypeP2ASet hG hM haσ ha.2 hpb
    · exact OddOrder.Peterfalvi.S10.coprime_FT_signalizer_centralizerIn_typePV hG hM data haσ
        ha.2 hvb
  · -- nonempty: `M_σ^# ⊆ A(S) ⊆ A₀(S)`.
    obtain ⟨a, ha1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haMσ : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := a.2
    have haM' : (a : G) ∈ derivedInG M := OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM haMσ
    exact ⟨a.1, Or.inl ⟨haM', ha1', a.1,
      (Set.mem_diff _).mpr ⟨SetLike.mem_coe.mpr haMσ, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩⟩
  · -- `M`-conjugation invariance.
    intro m x hm
    exact honestTypeP2A0Set_conj_mem data hm

/-- **(13.18) `S`-instance `'A0`-Dade hypothesis**: the `Hypothesis`-level instantiation of
`dadeSupportHypothesisData_honestTypeP2A0Set` at the type-`P₂` maximal `S` (via `hyp.S_maximal`/
`hyp.S_typeP2`/`hyp.Sdata`), packaging the honest full support `A₀(S) = A(S) ∪ V^S` as an
`S04.Hypothesis`.  This is the `S`-side Dade datum for the (13.18) cross-relation
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` — the `μ`-column differences are `A₀(S)`-supported (the
`V_S`-part falls outside `A(S) ⊆ S'`), so the `A(S)`-Dade `dadeHypS` cannot see them; `dadeHypS0`
is the correction.  (Its `.fullDadeIsometryData` inherits the one deep `'A0`-`normedTI` pin
`not_isConj_honestTypeP2ASet_typePV`.) -/
noncomputable def Hypothesis.dadeHypS0 [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S04.Hypothesis G (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S :=
  (dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.S_maximal hyp.S_typeP2 hyp.Sdata).some.dade

/-- **(13.18) `S`-instance `'A0`-Dade `H`-conjugation invariance**: the `HConjInvariant` of
`dadeHypS0`, carried by the underlying `DadeSupportHypothesisData` (Peterfalvi (8.14)/(8.15)).  This
is the `hconj` input for `dadeHypS0.fullDadeIsometryData`, so the `'A0`-Dade isometry
`τ_S = dadeIntegralCharacterMap (dadeHypS0 hG) …` is well-defined. -/
theorem Hypothesis.dadeHypS0_hconj [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (hyp.dadeHypS0 hG).HConjInvariant :=
  (dadeSupportHypothesisData_honestTypeP2A0Set hG hyp.S_maximal hyp.S_typeP2 hyp.Sdata).some.hconj

/-! ### Prime-`TI` pins for the (13.18) `S`-side cross-relation (issue 9076 piece 4c-4)

The three isolated prime-`TI` obligations behind `tauS_mu_row0_cross`
(`τ_S(μ_{0j} − μ_{0,#1}) = η_{0j} − η_{0,#1}`, `S15_SAndT.lean`).  Once these are discharged the
cross-relation is a pure assembly around the (3.8) rigidity engine `S16.eta_diff_rigidity` (issue
9076 piece 4b) + the `'A0(S)`-Dade isometry.  They are the `S`-side instances of the Coq prime-`TI`
lemmas (`prTIres`/`prDade_sub_TIirr_on`/`prTIirr_id`, `PFsection4.v`), the shared prime-`TI` residue
foundation tracked in issue 9014. -/

/-- **Prime-`TI` row-`0` cross-column distinctness** (issue 9076 piece 4c-4): distinct columns of
row `0` carry distinct `μ`-entries, `μ_{0j} ≠ μ_{0,#1}` for `j ≠ #1`.  This is the cross-column
injectivity of the prime-`TI` residue grid: the `μ_{ij}` are pairwise-distinct irreducibles across
the *whole* grid (Coq: the residues `prTIres i j` are distinct for distinct `(i, j)`).  The
`Hypothesis` structure records only the *within-column* distinctness `mu_col_injective`; this
row-direction distinctness is the missing prime-`TI` fact.  Prime-`TI` theory, cf. issue 9014. -/
theorem Hypothesis.mu_row0_ne [Finite G] (hyp : Hypothesis (G := G)) {j : Fin hyp.p}
    (hj : j ≠ ⟨1, by have := hyp.three_le_p; omega⟩) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j
      ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := sorry

/-- **Prime-`TI` support pin** (Coq `prDade_sub_TIirr_on`, `PFsection4.v`): the `μ`-column
difference `μ_{0j} − μ_{0,#1}` is supported inside `A₀(S) = A(S) ∪ V^S` — its support meets `S`
only in `P^# ∪ V_S`, because the two prime-`TI` residues share the same `1_S`-part off `A₀(S)` and
it cancels in the difference.  This is the `S`-side instance of Coq `prDade_sub_TIirr_on`
(`μ2_{ij} − μ2_{ik} ∈ 'CF(S, 'A0)`).  Prime-`TI` theory, cf. issue 9014. -/
theorem Hypothesis.tauS_mu_row0_diff_support [Finite G] (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) :
    (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S := sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Prime-`TI` `V`-value pin** (Coq `prTIirr_id` + Dade `Dade_id` on the regular set): on the
regular classes `conjClassSet(W \ (W₁ ∪ W₂)) = V^S`, the `'A0(S)`-Dade lift
`τ_S(μ_{0j} − μ_{0,#1})` agrees with the grid difference `η_{0j} − η_{0,#1}`.  Both reduce to the
same `ω`-value there: `τ_S = Ind_S^G` on `A₀(S)`-support (`normedTI 'A0`, `H = ⊥`) followed by the
prime-`TI` restriction identity `μ_{0j}|_V = ω`-value (Coq `prTIirr_id`), matching
`η_{0j}|_V = ω_{0j}|_V` (the (3.3) `τ₃ = Dade` identity on `V`).  Prime-`TI` theory, cf. issue
9014. -/
theorem Hypothesis.tauS_mu_row0_vanish_on_V [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
          (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
            - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
            - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := sorry

end OddOrder.Peterfalvi.S15
