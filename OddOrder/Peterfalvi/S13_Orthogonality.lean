/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_CoreStructure
import OddOrder.Peterfalvi.S11_NineElevenCaseA
import OddOrder.Peterfalvi.S11_NineElevenAlphaBound
import OddOrder.Peterfalvi.S11_NineElevenPairAdjoin
import OddOrder.Peterfalvi.S07_BridgeCoherent

/-!
# Peterfalvi Section 13: the (11.8.6) orthogonality endpoint — unconditional `𝒮(H₀C)` coherence

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §11, pp. 64-68.

This leaf sits **downstream of both Clifford branches** of the (9.11) `Ptype_core_coherence`
induction — caseA (`S11_NineElevenCaseA`) and caseB (`S13_CoreStructure`, issue 9075) are sibling
leaves, so the case *dispatch* needs this common downstream file.  It assembles the **unconditional**
`𝒮(H₀C)`-coherence (`coherent_sOf_H0C`) — the `X`-side input of the honest (11.8.6) world-bridge
union glue `S07.coherentUnion_of_glued_of_bridge` (Coq `bridge_coherent`, no generation hypothesis)
— which replaces the deprecated wide-`Sset \ SHCSet` uniform-degree route and the caseA-false
generation engine (both false for non-Galois type III/IV, issue 1019).

The sole sorried-cite is the caseA **refuter** (the (9.11.2) pair-adjoining non-coherence, lane-b's
active `S11_NineElevenCoherence` work); everything else — the caseB coherence, the (11.7) `H₀C′ ≤ H₀C`
transfer, the Clifford dispatch, and the reducible-μ-column witness — is landed.
-/

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **Every `inducedKernelFamily`-member has integer degree.**  A member `φ = Ind_K^L θ` has degree
`φ(1) = |L:K|·θ(1)`, a product of natural numbers (`induce_apply_one`,
`irreducibleCharacter_apply_one_eq_pos_natCast`), hence an integer.  This is the `hdegX`/`hdegY`
integer-degree (character) datum of the `bridge_coherent` union engine. -/
theorem inducedKernelFamily_mem_intDegree {M : Subgroup G} [Fintype ↥M]
    {K : Subgroup ↥M} [Invertible (Nat.card ↥K : ℂ)] {X : Subgroup ↥M} {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily K X) :
    ∃ n : ℤ, OddOrder.Peterfalvi.S03.characterDegree φ = (n : ℂ) := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  refine ⟨((K.index * d : ℕ) : ℤ), ?_⟩
  rw [OddOrder.Peterfalvi.S03.characterDegree_def, ClassFunction.induce_apply_one, hd]
  push_cast; ring

/-- **Every `inducedKernelFamily`-member has nonzero degree.**  `φ(1) = |L:K|·θ(1)` with both
factors positive naturals.  Supplies the `hdegχ` (nonzero anchor degree) input of `bridge_coherent`
for the reducible μ-column bridge. -/
theorem inducedKernelFamily_mem_apply_one_ne_zero {M : Subgroup G} [Fintype ↥M]
    {K : Subgroup ↥M} [Invertible (Nat.card ↥K : ℂ)] {X : Subgroup ↥M} {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily K X) :
    φ 1 ≠ 0 := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  rw [ClassFunction.induce_apply_one, hd]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite)
    (Nat.cast_ne_zero.mpr (by omega))

/-- **A degree-`0` element of `ℤ[inducedKernelFamily K X]` is `A₀`-supported** whenever `K^# ⊆ A₀`.
Every member `Ind_K^L θ` vanishes off the normal `K` (`induce_apply_eq_zero_of_not_mem_normal`),
so the whole integral span does; a span element with `φ(1) = 0` then has its support inside
`K ∖ {1} ⊆ A₀`.  This is the `hsuppX`/`hsuppY` degree/support dictionary of `bridge_coherent`,
uniform across the mixed degrees of `𝒮(H₀C)` (unlike `SHC_zSpan_vanish_support`, which anchors on a
fixed degree). -/
theorem inducedKernelFamily_zSpan_support_of_apply_one_eq_zero {M : Subgroup G} [Fintype ↥M]
    {K : Subgroup ↥M} [K.Normal] [Invertible (Nat.card ↥K : ℂ)] {X : Subgroup ↥M} {A0 : Set ↥M}
    (hKsupp : ∀ x : ↥M, x ∈ K → x ≠ 1 → x ∈ A0) {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S08.inducedKernelFamily K X)) (h1 : φ 1 = 0) :
    φ.support ⊆ A0 := by
  have hsuppK : ∀ g : ↥M, g ∉ K →
      ∀ ψ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S08.inducedKernelFamily K X), ψ g = 0 := by
    intro g hg ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨θ, -, -, rfl⟩ := hx
        exact ClassFunction.induce_apply_eq_zero_of_not_mem_normal K _ hg
    | zero => rw [ClassFunction.zero_apply]
    | add x y _ _ hx hy => rw [ClassFunction.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hx, mul_zero]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_cases hgK : g ∈ K
  · exact hKsupp g hgK (by rintro rfl; exact hg h1)
  · exact absurd (hsuppK g hgK φ hφ) hg

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), unconditional: `𝒮(H₀C)` is coherent on `A₀(M)`** — the Clifford dichotomy
`clifford_dichotomy` dispatches to caseB (landed `caseB_coherent_sOf_H0C`, issue 9075 via the (11.7)
transfer) and caseA (`caseA_coherent_sOf_H0Cprime_of_refuter` + the same transfer).  The caseA
**refuter** — the (9.11.2) pair-adjoining non-coherence supplied by lane-b's `S11_NineElevenCoherence`
induction — is the sole sorried-cite.  The `𝒮(H₀C)`-restriction witness (shared by the transfer) is
the conjugate difference `μ̄ − μ` of a reducible μ-column (`columnSum_muColumnChar_mem_sOf_H0C`,
`w₂ ≥ 2`), `A₀`-supported and nonzero (odd-order no-real-characters).

This is the unconditional `X`-side (𝒮(H₀C)-coherence) input of the honest (11.8.6) world-bridge union
glue `S07.coherentUnion_of_glued_of_bridge`; contradicting (11.3) `S_H0C_not_coherent` closes (11.8) without the
false wide uniform-degree route (issue 1019). -/
theorem coherent_sOf_H0C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0) := by
  haveI := hyp.base.finiteG
  classical
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) with hA | hB
  · -- **caseA**: (9.11) case-a coherence via the refuter (lane-b (9.11.2) active work, sorried-cite),
    -- then the (11.7) `H₀C′ ≤ H₀C` transfer with the reducible-μ-column witness.
    have caseA := hA.some
    have hw2 : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
    have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
      intro heq; have := congrArg Fin.val heq; simp at this
    set μ : ClassFunction ↥M ℂ := OddOrder.Peterfalvi.S06.columnSum
      (hyp.base.toHypothesis46 hG hG.odd) (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩) with hμdef
    have hμmem : μ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
      columnSum_muColumnChar_mem_sOf_H0C hG hyp ⟨1, hw2⟩ hk1
    have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
        x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
        x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
          ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
        (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
    have hμc : μ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
      Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hμmem
    -- the refuter is discharged through the (9.11.1) squeeze + the Phase-B/C/D/E layers;
    -- the (9.11.7)–(9.11.8) coherent-pair construction is `nineElevenSevenEightRefutation`
    -- (issue 9083 Phase E-final, `S11_NineElevenPairAdjoin`)
    refine ⟨coherent_sOf_H0C_of_coherent_sOf_H0Cprime hyp
      (OddOrder.Peterfalvi.S13.caseA_coherent_sOf_H0Cprime_of_refuter hG hyp caseA
        (caseA_refuter_of_equality_refutation hG hyp caseA
          (nineElevenPairBound hG hyp caseA)
          (nineElevenEqualityRefutation_of_sevenEightRefutation hG hyp caseA
            (nineElevenSevenEightRefutation hG hyp caseA)))).some
      ⟨μ.conj - μ, ⟨?_, ?_⟩, ?_⟩⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span hμc) (Submodule.subset_span hμmem)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 (hIKF hμmem)
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ (hIKF hμmem) (sub_eq_zero.mp h)
  · -- **caseB**: the landed norm-general coherence (issue 9075) transferred to `𝒮(H₀C)`.
    exact ⟨caseB_coherent_sOf_H0C hG hyp hB.some⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(11.8.6) narrow `τ₃` glue map `ν` exists** — the world-bridge analogue of
`S12.Hypothesis.exists_glue_nu`.  From the two coherences `coh` (`S₁ = S(HC)`) and `hY`
(`S₂ = 𝒮(H₀C)`) there is an integral map `ν` agreeing with `coh.extension` on `S(HC)` and with
`hY.extension` on `𝒮(H₀C)` (Peterfalvi's `τ₃`).

Both `S(HC)` and `𝒮(H₀C)` embed into the pairwise-orthogonal general family
`inducedKernelFamily ((derivedInG M).subgroupOf M) _` (`SOf_eq`, `sOf_subset_SOf`), whose members
have nonzero (positive real) norm (`inducedKernelFamily_inner_self_real_pos`) and are finite
(`inducedKernelFamily_finite`); and `S(HC) ⊥ 𝒮(H₀C)` (`SOf_HC_inner_sOf_H0C_eq_zero`).  So the S07
non-orthonormal glue `exists_integralCharacterMap_glue_of_orthogonal` applies directly, supplying
the `ν`/`hagreeX`/`hagreeY` input of the narrow union-glue
`S07.coherentUnion_of_glued_of_bridge`. -/
theorem exists_glue_nu_H0C [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0)
    (hY : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0) :
    ∃ ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G,
      (∀ x ∈ hyp.SOf hyp.HC, ν x = coh.extension x) ∧
      (∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C, ν y = hY.extension y) := by
  haveI := hyp.base.finiteG
  classical
  -- X-side bridge: `S(HC) = inducedKernelFamily K (HC.subgroupOf M)`
  have hXbridge : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ hyp.SOf hyp.HC →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.HC.subgroupOf M) := fun {x} hx => by
    rw [hyp.SOf_eq] at hx; exact hx
  -- Y-side bridge: `𝒮(H₀C) ⊆ inducedKernelFamily K ⊥`
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
  have hXfin : (hyp.SOf hyp.HC).Finite := by
    rw [hyp.SOf_eq]; exact OddOrder.Peterfalvi.S08.inducedKernelFamily_finite _
  have hYfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C).Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite (⊥ : Subgroup ↥M)).subset
      (fun _ hx => hIKF hx)
  exact OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthogonal
    hXfin hYfin
    (fun _ hx _ hx' hne => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hXbridge hx) (hXbridge hx') hne)
    (fun _ hx => by
      obtain ⟨he, hpos⟩ :=
        OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hXbridge hx)
      rw [he]; exact Complex.ofReal_ne_zero.mpr hpos.ne')
    (fun _ hy _ hy' hne => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hy) (hIKF hy') hne)
    (fun _ hy => by
      obtain ⟨he, hpos⟩ :=
        OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hIKF hy)
      rw [he]; exact Complex.ofReal_ne_zero.mpr hpos.ne')
    (fun _ hx _ hy => SOf_HC_inner_sOf_H0C_eq_zero hyp hx hy)
    coh.extension hY.extension

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **World-bridge for the σ-grids** (issue 1023 tick¹²): the §6 certain-type σ-image
`certainTypeOmegaSigma` of the `μ`-column character, dispatched by the `SOf_memberRFamily`
machinery over `h46 = hyp.toHypothesis46`, **is** the §10 `alignedOmegaSigmaGrid` entry.
Both are the (3.2) `σ` of the same TI-cyclic setup — `h46.tic` is *literally*
`typePData_toTICyclicHypothesis` (the `toHypothesis46` field), so `ticVdiff h46` and the
grid's `tic` agree definitionally — applied to pointwise-equal transported `ω`-characters
(`omegaProdCharTic_apply` vs the grid's `compHom e (chiColumn …)`; both transports are
carrier-identities, `coe_ticWEquivSdiffW`). -/
theorem certainTypeOmegaSigma_muColumnChar_eq_aligned [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (hcw1 : Nat.card ↥(hyp.toHypothesis46 hG hG.odd).W1 = hyp.w1)
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    OddOrder.Peterfalvi.S06.certainTypeOmegaSigma (hyp.toHypothesis46 hG hG.odd)
        (hyp.muColumnChar hG hG.odd j) (finCongr hcw1.symm i)
      = hyp.alignedOmegaSigmaGrid hG hG.odd i j := by
  haveI := hyp.finiteG
  classical
  -- the two setups agree definitionally (`toHypothesis46.tic` is the grid `tic` by field literal)
  show (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).sigma rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (hyp.toHypothesis46 hG hG.odd))
      ((OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).omega
        (OddOrder.Peterfalvi.S06.omegaProdCharTic (hyp.toHypothesis46 hG hG.odd)
          (hyp.muColumnChar hG hG.odd j) (finCongr hcw1.symm i)))
    = hyp.alignedOmegaSigmaGrid hG hG.odd i j
  -- unfold the grid to its `σ`-form (defeq through the def's `let`s)
  rw [show hyp.alignedOmegaSigmaGrid hG hG.odd i j
      = (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).sigma rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (hyp.toHypothesis46 hG hG.odd))
          (ClassFunction.compHom
            (((Subgroup.subgroupOfEquivOfLe (OddOrder.Peterfalvi.S12.typePData_W_le_self hyp.typeP)).symm.trans
              (MulEquiv.subgroupCongr
                (OddOrder.Peterfalvi.S12.typePData_sup_subgroupOf_eq hyp.typeP).symm)).toMonoidHom)
            ((hyp.toHypothesis46 hG hG.odd).chiColumn (hyp.muColumnChar hG hG.odd j)
              (finCongr hcw1.symm i)
              : ClassFunction
                  (hyp.toHypothesis46 hG hG.odd).sdiffTICyclicHypothesis.W ℂ)) from rfl]
  -- same σ of pointwise-equal inputs
  congr 1
  ext w
  -- LHS value: `ω(ω_{ij}^{tic})(w) = chiColumn χ₂ i (ticWEquivSdiffW w)`
  have hL : ((OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).omega
        (OddOrder.Peterfalvi.S06.omegaProdCharTic (hyp.toHypothesis46 hG hG.odd)
          (hyp.muColumnChar hG hG.odd j) (finCongr hcw1.symm i))
        : ClassFunction _ ℂ) w
      = ((hyp.toHypothesis46 hG hG.odd).chiColumn (hyp.muColumnChar hG hG.odd j)
          (finCongr hcw1.symm i)
          : ClassFunction (hyp.toHypothesis46 hG hG.odd).sdiffTICyclicHypothesis.W ℂ)
        (OddOrder.Peterfalvi.S06.ticWEquivSdiffW (hyp.toHypothesis46 hG hG.odd) w) := by
    rw [(OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).omega_apply]
    exact OddOrder.Peterfalvi.S06.omegaProdCharTic_apply (hyp.toHypothesis46 hG hG.odd)
      (hyp.muColumnChar hG hG.odd j) (finCongr hcw1.symm i) w
  refine hL.trans ?_
  -- RHS value: `compHom e (chiColumn)(w) = chiColumn (e w)`; the two transports of `w`
  -- share the ambient element (`coe_ticWEquivSdiffW`), so `chiColumn` agrees.
  rw [ClassFunction.compHom_apply]
  refine congrArg _ ?_
  apply Subtype.ext
  apply Subtype.ext
  have h1 := OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW (hyp.toHypothesis46 hG hG.odd) w
  rw [h1]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8.6) narrow union-coherence capstone** — targeting the *narrow* family `S(H₀C)`
via the `𝒮(H₀C)` coherence (contradicting (11.3)), NOT the deprecated wide `Sset \ SHCSet`
uniform-degree route (false for non-Galois type III/IV, issue 1019).

From the `S(HC)`-coherence `coh` (Peterfalvi's `τ₁`), the **unconditional** `𝒮(H₀C)`-coherence
`hsofC` (`coherent_sOf_H0C`, the `τ₂`), and the column identities `hcol`, the glued `τ₃` map
(`exists_glue_nu_H0C`) assembles a coherent extension of `S(H₀C) = 𝒮(H₀C) ∪ S(HC)` via **Coq's
`bridge_coherent`** engine `S07.coherentUnion_of_glued_of_bridge` (no generation hypothesis).

**Routed through `bridge_coherent`, the caseA-FALSE generation hypothesis `hgen` is gone.**  The old
generation engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` needed
`hgen : ℤ[𝒮(H₀C) ∪ S(HC)]_{A₀} ⊆ ℤ[…∪D]` with a single degree-`qu` diagonal — **FALSE in Clifford
caseA**, where `𝒮(H₀C)` is mixed degree `{qu, qa}` and `χ_qa − a·ζ` is `A₀`-supported yet outside
that span (issue 1019 update¹³).  `bridge_coherent` avoids generation entirely: it glues along a
**single** `A₀`-supported bridge `χ − φ = ∑ᵢ μ_{i1} − dζ` (`χ ∈ 𝒮(H₀C)`, `φ ∈ ℤ[S(HC)]`), the mixed
`qa` content living inside `hsofC`'s own coherence.  The structural inputs (source/image
orthogonality, integer degrees, the `A = L^#` degree/support dictionary) are all discharged here.

Remaining genuine §14/§9 character content (NONE of it the removed false `hgen`):
- `hmixed` — the (6.7) image-side orthogonality `⟨χ^{τ₂}, φ^{τ₁}⟩ = ⟨χ, φ⟩` (the `b ≡ 0` congruence,
  §14/Sibley-gated) — the SAME genuine content as the old `hmixed`;
- `hbridge_τ` — the (5.8) bridge `τ`-agreement `ν(∑ᵢ μ_{i1} − dζ) = τ(∑ᵢ μ_{i1} − dζ)`, which via the
  `ν`-agreements + `hcol` is `hsofC.extension (∑ᵢ μ_{i1}) = ∑ᵢ ω^σ_{i1}` (the `𝒮(H₀C)` coherent
  extension sends the reducible μ-column to the aligned ω^σ-column).  `coherent_sOf_H0C` carries no
  such μ-column image pin — this is the honest heir of the old `hDτ` sorry, §14/§9-gated.

Two further bridge inputs (`hφY : dζ ∈ ℤ[S(HC)]`, `hbridge_supp : ∑ᵢ μ_{i1} − dζ` `A₀`-supported)
are TRUE but currently `sorry`ed because they need `ζ ∈ S(HC)` and the degree match
`(∑ᵢ μ_{i1})(1) = d·ζ(1)`, which the *signature* does not carry (only `ζ ∈ inducedFamily M ⊋ S(HC)`);
both are caller-supplied facts (`ζ` irreducible of degree `w₁`; `secondDerived_eq_HC` +
`SOf_secondDerived_eq`; `degree_independent`).  Threading `ζ ∈ hyp.SOf hyp.HC` (+ degree) into the
signature closes them, leaving only `hmixed`/`hbridge_τ`.  See issue 1019 update¹³. -/
theorem coherent_SOf_H0C_of_column_identities [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M) {d : ℕ}
    (hζHC : ζ ∈ hyp.SOf hyp.HC)
    (hζdeg : ∀ j : Fin hyp.base.w2, j ≠ 0 →
      (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j) 1 = (d : ℂ) * ζ 1)
    (hcol : ∀ j : Fin hyp.base.w2, j ≠ 0 →
      hyp.base.tau ((∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j) - (d : ℂ) • ζ)
        = (∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i j)
          - (d : ℂ) • coh.extension ζ) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := by
  haveI := hyp.base.finiteG
  classical
  -- `hsofC` = the unconditional `𝒮(H₀C)`-coherence (this file's `coherent_sOf_H0C`) = the bridge
  -- engine's `X`-side coherence; `coh` (`S(HC)`) is the `Y`-side.  `ν` is the `τ₃` glue of the two.
  obtain ⟨hsofC⟩ := coherent_sOf_H0C hG hyp
  obtain ⟨ν, hagreeSHC, hagreeSof⟩ := exists_glue_nu_H0C hyp coh hsofC
  -- The reducible μ-column bridge anchor `χ = ∑ᵢ μ_{i1} ∈ 𝒮(H₀C)`, at the nonzero column `j = 1`.
  have hw2 : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
  have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
    intro heq; have := congrArg Fin.val heq; simp at this
  -- Kernel-family embeddings of both families into the pairwise-orthogonal `S((M')^#)`.
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
  have hXbridge : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ hyp.SOf hyp.HC →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.HC.subgroupOf M) := fun {x} hx => by
    rw [hyp.SOf_eq] at hx; exact hx
  have hχmem : (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
      ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C := by
    rw [hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd ⟨1, hw2⟩]
    exact columnSum_muColumnChar_mem_sOf_H0C hG hyp ⟨1, hw2⟩ hk1
  -- `d·ζ ∈ ℤ[S(HC)]`: `ζ ∈ S(HC)` (`hζHC`) plus `(d:ℂ)•ζ = (d:ℤ)•ζ` (a `zsmul` of a span member).
  have hdζspan : (d : ℂ) • ζ ∈ Submodule.span ℤ (hyp.SOf hyp.HC) := by
    have hcast : (d : ℂ) • ζ = (d : ℤ) • ζ := by
      rw [← Int.cast_smul_eq_zsmul ℂ (d : ℤ) ζ, Int.cast_natCast]
    rw [hcast]
    exact Submodule.smul_mem _ (d : ℤ) (Submodule.subset_span hζHC)
  refine ⟨?_⟩
  rw [hyp.SOf_H0C_eq_SOf_HC_union_sOf, Set.union_comm]
  -- **`bridge_coherent`** (no generation hypothesis) — engine `X = 𝒮(H₀C)`, `Y = S(HC)`.
  refine OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_bridge hsofC coh ν hagreeSof hagreeSHC
    (fun u hu v hv => by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        span_inner_SOf_HC_sOf_H0C_eq_zero hyp hv hu, star_zero])
    ?hmixed hyp.base.one_notMem_A0
    (fun x hx => inducedKernelFamily_mem_intDegree (hIKF hx))
    (fun y hy => inducedKernelFamily_mem_intDegree (hXbridge hy))
    (fun η hη hη0 => ⟨hη, inducedKernelFamily_zSpan_support_of_apply_one_eq_zero
      hyp.base.mderivSharp_subset_A0 (Submodule.span_mono (fun _ hx => hIKF hx) hη) hη0⟩)
    (fun η hη hη0 => ⟨hη, inducedKernelFamily_zSpan_support_of_apply_one_eq_zero
      hyp.base.mderivSharp_subset_A0 (Submodule.span_mono (fun _ hx => hXbridge hx) hη) hη0⟩)
    (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩) ((d : ℂ) • ζ)
    hχmem ?hφY (inducedKernelFamily_mem_apply_one_ne_zero (hIKF hχmem)) ?hbridge_supp ?hbridge_τ
  case hmixed =>
    -- **(6.7) image-side orthogonality** (the Coq `coherent_ortho`): after the `ν`-agreements
    -- the goal is `⟨χ^{τ₂}, φ^{τ₁}⟩ = ⟨χ, φ⟩` (`χ ∈ 𝒮(H₀C)`, `φ ∈ S(HC)`).  Both sides vanish:
    -- the characters are cross-orthogonal (`SOf_HC_inner_sOf_H0C_eq_zero`), and the coherent
    -- images are partial `R`-family sums over cross-orthogonal families
    -- (`SOf_coherent_extension_cross_orthogonal`, the two-stratum (5.5)+(5.2.e) engine,
    -- issue 1023).
    intro x hx y hy
    rw [hagreeSof x hx, hagreeSHC y hy]
    have hxc : x.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
      Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hx
    have hyc : y.conj ∈ hyp.SOf hyp.HC := by
      rw [hyp.SOf_eq] at hy ⊢
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hy
    have hxy0 : ClassFunction.inner x y = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        SOf_HC_inner_sOf_H0C_eq_zero hyp hy hx, star_zero]
    have hxyc0 : ClassFunction.inner x y.conj = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        SOf_HC_inner_sOf_H0C_eq_zero hyp hyc hx, star_zero]
    have hxx : ClassFunction.inner x x ≠ 0 := by
      obtain ⟨he, hpos⟩ :=
        OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hIKF hx)
      rw [he]; exact Complex.ofReal_ne_zero.mpr hpos.ne'
    have hne1 : x ≠ y := fun h => by cases h; exact hxx hxy0
    have hne2 : x ≠ y.conj := fun h => by cases h; exact hxx hxyc0
    rw [hxy0]
    exact SOf_coherent_extension_cross_orthogonal hG hyp
      (hyp.sOf_subset_SOf hyp.H0C) (le_refl (hyp.SOf hyp.HC)) hsofC coh
      hx hxc hy hyc hne1 hne2
  case hφY =>
    -- `(d:ℂ)•ζ ∈ ℤ[S(HC)]`: now discharged from `hζHC : ζ ∈ S(HC)` (threaded into the signature).
    exact hdζspan
  case hbridge_supp =>
    -- `∑ᵢ μ_{i1} − dζ ∈ ℤ[𝒮(H₀C) ∪ S(HC)]_{A₀}`.  The `ℤ`-span part is `hχmem` + `hdζspan`; the
    -- `A₀`-support part is `inducedKernelFamily_scaledDiff_support` from the degree match `hζdeg`
    -- (`(∑ᵢ μ_{i1})(1) = d·ζ(1)`).  Both are now threaded through the signature.
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_union_left _ hχmem))
        (Submodule.span_mono Set.subset_union_right hdζspan)
    · have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
        hyp.base.mderivSharp_subset_A0 (hIKF hχmem) (hXbridge hζHC) (hζdeg ⟨1, hw2⟩ hk1)
      rwa [← Nat.cast_smul_eq_nsmul ℂ d ζ] at h
  case hbridge_τ =>
    -- **(5.8) bridge `τ`-agreement `ν(∑ᵢ μ_{i1} − dζ) = τ(∑ᵢ μ_{i1} − dζ)`** (§14/§9 genuine
    -- content — the honest heir of the old `hDτ` sorry).  Via the `ν`-agreements and `hcol` this
    -- reduces to `hsofC.extension (∑ᵢ μ_{i1}) = ∑ᵢ ω^σ_{i1}`: the `𝒮(H₀C)` coherent extension sends
    -- the reducible μ-column to the aligned ω^σ-column.  `coherent_sOf_H0C` carries no such μ-column
    -- image pin (Peterfalvi (10.6.a) `muColumn_tau1_pin` gives it only for the `Sset`-coherence
    -- `CoherentHypothesis`, not the narrow `𝒮(H₀C)` one), so this is the residual §14/§9 gate.
    sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8), the genuine non-orthogonality — narrow `𝒮(H₀C)` route, refuter core**
(the honest replacement of `S12.exists_zeta_residual_not_orthogonal`, which routed through the
deprecated wide `Sset \ SHCSet` uniform-degree lemma, false for non-Galois type III/IV, issue
1019).  The closing (11.3) noncoherence is the `hrefute` hypothesis (issue 1020 Phase 3), so the
legacy `S_H0C_not_coherent` (via the partner-sorried `S12.S_not_coherent`) and the unconditional
heir (`S_H0C_not_coherent_unconditional`, `S13_TypeDetermination`) instantiate one proof.

Under Hypothesis (10.1), there is an irreducible `ζ ∈ S = inducedFamily M` of degree `w₁` for which
the residual `(μ₀ − ζ)^τ − ∑_i ω_{i0}^σ` is **not** orthogonal to `(Irr W)^σ`.  Same statement as the
S12 version; the proof reuses the S12 residual machinery (`exists_charParameters_full`,
`exists_coherent_extension_h114_of_orthogonal`, `tau_muColumnSum_sub_dzeta_eq_of_residualData`)
verbatim to build the coherent extension `ν` and the column identities `hcol` from the orthogonality
assumption, then closes via the **narrow** capstone `coherent_SOf_H0C_of_column_identities`
(coherence of `S(H₀C)`) contradicting (11.3) `S_H0C_not_coherent` — instead of the wide
`S12.coherent_Sset_of_column_identities`/`S_not_coherent`.

World-bridge threading: the residual machinery and the conclusion live in the §12 `hyp`-world, while
the narrow capstone/refuter (`coherent_sOf_H0C`, `S_H0C_not_coherent`) live in the §13 `s13hyp`-world
(`s13hyp.base = hyp` propositionally, via `exists_hypothesis_of_isTypeIIIorIV`).  Since `s13hyp.base =
hyp` holds only up to `hbase` (not definitionally), the whole goal is first `rw [← hbase]`-transported
into the `s13hyp.base`-world, so the S12 machinery and the narrow endpoint share one world and the
`isCoherent_of_subset ν` restriction keeps `coh.extension = ν.extension` definitionally (feeding `hcol`
into the capstone with no cast). -/
theorem exists_zeta_residual_not_orthogonal_H0C_of_refuter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1)
    (hrefute : ∀ s13hyp : Hypothesis M,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0)) :
    ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧
      IsIrreducibleCharacter ζ ∧ ζ 1 = (hyp.w1 : ℂ) ∧
      ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
        ClassFunction.inner
          ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
            - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
          (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0 := by
  -- Move the whole goal into the §13 `s13hyp.base`-world so the S12 residual machinery and the
  -- narrow (11.3) endpoint share one world (`s13hyp.base = hyp` only propositionally).
  obtain ⟨s13hyp, hbase⟩ := OddOrder.Peterfalvi.S13.exists_hypothesis_of_isTypeIIIorIV hG hyp htype
  rw [← hbase] at hM2 hHcard ⊢
  -- (10.2)/(10.3) character parameters (now on `s13hyp.base`).
  obtain ⟨params, hmu, -, hzS, hz1, -, hδpm, hδindep⟩ := s13hyp.base.exists_charParameters_full hG
  refine ⟨params.zeta, hzS, params.zeta_irreducible, hz1, ?_⟩
  intro h_orth
  -- (11.8.1) `δ = 1`; (11.8.4) the coherent extension `ν` and `h114` from orthogonality.
  have hδ1 : params.delta = 1 := s13hyp.base.charParam_delta_eq_one hG htype params hmu hδpm
  obtain ⟨ν, hνconj, h114⟩ :=
    s13hyp.base.exists_coherent_extension_h114_of_orthogonal hG hG.odd hzS params.zeta_irreducible
      hz1 h_orth
  -- (11.8.1)/(5.7) the orthonormal coherent image `R`, `|R| = n`.
  obtain ⟨R, hZ, hRorth, hRmem, hRrev, hRcard⟩ := s13hyp.base.exists_coherentImage_SHC ν
  have hRn : R.card = params.n :=
    hRcard.trans (s13hyp.base.card_SHCSet_filter_eq_charParam_n hG htype params hmu hδpm hM2 hHcard)
  have hnf : (params.n : ℤ) * (s13hyp.base.w1 : ℤ) = (params.d : ℤ) - 1 := by
    rw [← hδ1]; exact params.n_formula
  have hd : (params.d : ℂ) = (s13hyp.base.w1 : ℂ) * (params.n : ℂ) + 1 := by
    have h : (params.n : ℂ) * (s13hyp.base.w1 : ℂ) = (params.d : ℂ) - 1 := by exact_mod_cast hnf
    linear_combination -h
  have hμ0all : ∀ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i 0 1 = 1 :=
    fun i => s13hyp.base.muGrid_zero_column_apply_one hG hG.odd i
  -- (11.8.2)–(11.8.6 opening) the column identities `(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}`.
  have hcol : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      s13hyp.base.tau ((∑ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j)
          - (params.d : ℂ) • params.zeta)
        = (∑ i : Fin s13hyp.base.w1, s13hyp.base.alignedOmegaSigmaGrid hG hG.odd i j)
          - (params.d : ℂ) • ν.extension params.zeta := by
    intro j hj
    have hdegall : ∀ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    have hδjj : s13hyp.base.muColumnSign hG hG.odd j = 1 := (hδindep j hj).trans hδ1
    exact s13hyp.base.tau_muColumnSum_sub_dzeta_eq_of_residualData hG ν hνconj hG.odd hj hzS
      params.zeta_irreducible hz1 params.w2_prime hd hnf hdegall hμ0all hδjj params.two_le_n
      hRn hZ hRorth hRmem hRrev h114
  -- `ζ ∈ S(HC)`: `ζ` is a degree-`w₁` irreducible in `S`, i.e. a member of `S(M'') = S(HC)`
  -- (`SOf_secondDerived_eq` characterizes `S(M'')` as the degree-`w₁` irreducible subfamily;
  -- `secondDerived_eq_HC` (11.5) identifies `M'' = HC`).
  have hζHC : params.zeta ∈ s13hyp.SOf s13hyp.HC := by
    rw [← secondDerived_eq_HC hG s13hyp, s13hyp.SOf_secondDerived_eq hG]
    exact ⟨hzS, params.zeta_irreducible, hz1⟩
  -- Degree match `(∑ᵢ μ_{ij})(1) = d·ζ(1)`: each `μ_{ij}(1) = d` (`degree_independent`, `j ≠ 0`),
  -- so the `w₁`-term sum is `w₁·d = d·w₁ = d·ζ(1)` (`hz1 : ζ(1) = w₁`).
  have hζdeg : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      (∑ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j) 1
        = (params.d : ℂ) * params.zeta 1 := by
    intro j hj
    have hall : ∀ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    rw [ClassFunction.finset_sum_apply]
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hz1]
    ring
  -- (11.8.6) the narrow τ₃ union makes `S(H₀C)` coherent, contradicting (11.3) `S_H0C_not_coherent`.
  -- `coh` = the `ν` (h_orth-derived `S(HC)` coherence) restricted to `S(HC) ⊆ SHCSet`
  -- (`isCoherent_of_subset`, keeping `coh.extension = ν.extension`); the narrow capstone consumes
  -- `hcol` and the unconditional `𝒮(H₀C)`-coherence (`coherent_sOf_H0C`, threaded inside).
  haveI : NeZero (Nat.card (s13hyp.base.toHypothesis46 hG hG.odd).W1) :=
    ⟨by have := (s13hyp.base.toHypothesis46 hG hG.odd).one_lt_card_W1; omega⟩
  exact hrefute s13hyp (coherent_SOf_H0C_of_column_identities hG s13hyp
    (isCoherent_of_subset ν (SOf_HC_subset_SHCSet hG s13hyp)
      (coherent_SOf_HC hG s13hyp).some.nonzero) hzS hζHC hζdeg hcol)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), modulo the equality refutation: `𝒮(H₀C′)` is coherent on `A₀(M)`**
(issue 9083 Phase A, the dichotomy dispatch).

The full `Ptype_core_coherence` assembly with the two remaining honest caseA inputs taken as
hypotheses: the Clifford dichotomy (9.7) `clifford_dichotomy` splits into

* **caseB** — the landed norm-general coherence `caseB_coherent_sOf_H0Cprime` (issue 9075), and
* **caseA** — the maximality reduction `caseA_coherent_sOf_H0Cprime_of_refuter`, whose refuter
  clause is discharged by the (9.11.1) squeeze wiring `caseA_refuter_of_equality_refutation` from
  the (5.6) pair-bound bundle `hbound` (`NineElevenPairBound`) and the (9.11.2)–(9.11.8)
  equality-configuration refutation `hrefuteEq` (`NineElevenEqualityRefutation`), both quantified
  over the dichotomy's caseA datum.

Once the later 9083 phases discharge `hbound`/`hrefuteEq`, this becomes the unconditional (9.11);
composed with the (11.7) transfer (`coherent_sOf_H0C_of_coherent_sOf_H0Cprime` + the reducible
μ-column witness, as in `coherent_sOf_H0C`) it replaces the sole live sorry of that endpoint. -/
theorem coherent_sOf_H0Cprime_of_equality_refutation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (hbound : ∀ caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief),
      NineElevenPairBound hyp caseA)
    (hrefuteEq : ∀ caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief),
      NineElevenEqualityRefutation hyp caseA) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0) := by
  haveI := hyp.base.finiteG
  classical
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) with hA | hB
  · -- **caseA**: the (9.11.1) squeeze wiring discharges the maximality refuter.
    have caseA := hA.some
    exact caseA_coherent_sOf_H0Cprime_of_refuter hG hyp caseA
      (caseA_refuter_of_equality_refutation hG hyp caseA (hbound caseA) (hrefuteEq caseA))
  · -- **caseB**: the landed norm-general coherence (issue 9075).
    exact caseB_coherent_sOf_H0Cprime hG hyp hB.some

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), reduced to the single (9.11.7)–(9.11.8) residual** (issue 9083
Phase E): with the (5.6) pair bound (`nineElevenPairBound`, Phase E-PairBound), the
`𝒮₂ = 𝒮₁` extraction (`nineElevenSTwoExtraction`), the (9.11.2) TI-witness, the (9.11.3)
count, the (9.11.4) Mackey norm, and the (9.11.6) dichotomy
(`nineElevenNormBound_of_sevenEightRefutation`) all landed, the coherence of `𝒮(H₀C′)`
follows from the one remaining named input: the (9.11.7)–(9.11.8) coherent-pair
construction `NineElevenSevenEightRefutation`, quantified over the caseA datum.  Once that
is discharged, this becomes the unconditional (9.11) and replaces the live sorry of
`coherent_sOf_H0C`. -/
theorem coherent_sOf_H0Cprime_of_sevenEightRefutation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (h78 : ∀ caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief),
      NineElevenSevenEightRefutation hyp caseA) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0) :=
  coherent_sOf_H0Cprime_of_equality_refutation hG hyp
    (fun caseA => nineElevenPairBound hG hyp caseA)
    (fun caseA =>
      nineElevenEqualityRefutation_of_sevenEightRefutation hG hyp caseA (h78 caseA))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11)** (Coq `Ptype_core_coherence`, `PFsection9.v:1484`): the family
`𝒮(H₀C′)` is coherent — **unconditional**.  The (9.11.7)–(9.11.8) coherent-pair
construction (`nineElevenSevenEightRefutation`, issue 9083 Phase E-final) discharges the
last hypothesis of `coherent_sOf_H0Cprime_of_sevenEightRefutation`. -/
theorem coherent_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0) :=
  coherent_sOf_H0Cprime_of_sevenEightRefutation hG hyp
    (fun caseA => nineElevenSevenEightRefutation hG hyp caseA)

end OddOrder.Peterfalvi.S13
