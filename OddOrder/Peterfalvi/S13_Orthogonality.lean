/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_CoreStructure
import OddOrder.Peterfalvi.S11_NineElevenCaseA

/-!
# Peterfalvi Section 13: the (11.8.6) orthogonality endpoint — unconditional `𝒮(H₀C)` coherence

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §11, pp. 64-68.

This leaf sits **downstream of both Clifford branches** of the (9.11) `Ptype_core_coherence`
induction — caseA (`S11_NineElevenCaseA`) and caseB (`S13_CoreStructure`, issue 9075) are sibling
leaves, so the case *dispatch* needs this common downstream file.  It assembles the **unconditional**
`𝒮(H₀C)`-coherence (`coherent_sOf_H0C`) — the `hY` input of the honest (11.8.6) world-bridge union
glue `coherent_SOf_H0C_of_glued` — which replaces the deprecated wide-`Sset \ SHCSet` uniform-degree
route (false for non-Galois type III/IV, issue 1019).

The sole sorried-cite is the caseA **refuter** (the (9.11.2) pair-adjoining non-coherence, lane-b's
active `S11_NineElevenCoherence` work); everything else — the caseB coherence, the (11.7) `H₀C′ ≤ H₀C`
transfer, the Clifford dispatch, and the reducible-μ-column witness — is landed.
-/

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), unconditional: `𝒮(H₀C)` is coherent on `A₀(M)`** — the Clifford dichotomy
`clifford_dichotomy` dispatches to caseB (landed `caseB_coherent_sOf_H0C`, issue 9075 via the (11.7)
transfer) and caseA (`caseA_coherent_sOf_H0Cprime_of_refuter` + the same transfer).  The caseA
**refuter** — the (9.11.2) pair-adjoining non-coherence supplied by lane-b's `S11_NineElevenCoherence`
induction — is the sole sorried-cite.  The `𝒮(H₀C)`-restriction witness (shared by the transfer) is
the conjugate difference `μ̄ − μ` of a reducible μ-column (`columnSum_muColumnChar_mem_sOf_H0C`,
`w₂ ≥ 2`), `A₀`-supported and nonzero (odd-order no-real-characters).

This is the unconditional `hY` (𝒮(H₀C)-coherence) input of the honest (11.8.6) world-bridge union
glue `coherent_SOf_H0C_of_glued`; contradicting (11.3) `S_H0C_not_coherent` closes (11.8) without the
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
    refine ⟨coherent_sOf_H0C_of_coherent_sOf_H0Cprime hyp
      (OddOrder.Peterfalvi.S13.caseA_coherent_sOf_H0Cprime_of_refuter hG hyp caseA
        (by sorry)).some ⟨μ.conj - μ, ⟨?_, ?_⟩, ?_⟩⟩
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
the `ν`/`hagreeX`/`hagreeY` input of the narrow union-glue `coherent_SOf_H0C_of_glued`. -/
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
/-- **Peterfalvi (11.8.6) narrow union-coherence capstone** — the world-bridge analogue of
`S12.Hypothesis.coherent_Sset_of_column_identities`, targeting the *narrow* family `S(H₀C)` via the
`𝒮(H₀C)` coherence (contradicting (11.3)), NOT the deprecated wide `Sset \ SHCSet` uniform-degree
route (false for non-Galois type III/IV, issue 1019).

From the `S(HC)`-coherence `coh` (Peterfalvi's `τ₁`), the **unconditional** `𝒮(H₀C)`-coherence `hY`
(`coherent_sOf_H0C`, the `τ₂`), and the column identities
`(∑ᵢ μ_{ij} − dζ)^τ = ∑ᵢ ω_{ij}^σ − dζ^{τ₁}` (`hcol`, `0 < j`), the glued `τ₃` map
(`exists_glue_nu_H0C`) assembles a coherent extension of `S(H₀C) = S(HC) ∪ 𝒮(H₀C)`
(`coherent_SOf_H0C_of_glued`, `SOf_H0C_eq_SOf_HC_union_sOf`).

Three inputs of the union-glue engine remain as the genuine §14/§9 character content, mirroring the
S12 wide-route sorries (`coherent_Sset_of_column_identities` at S12:4888/4896/4917):
- `hmixed` — the (6.7) image-side orthogonality (`⟨coh.extension x, hY.extension y⟩ = 0`, the `b ≡ 0`
  congruence, §14/Sibley-gated);
- `hDτ` — the (5.8) column identity on the cross-diagonals `∑ᵢ μ_{ij} − dζ ∈ D` (fed by `hcol`,
  §14-gated after the `τ`-rewrite);
- `hgen` — the (6.8.1) generation with the single degree-`qu` diagonal `D = {∑ᵢ μ_{ij} − dζ}`.
  ⚠ **This `hgen` is TRUE only in Clifford caseB** (uniform degree `q·u`,
  `forall_mem_sOf_H0C_apply_one_eq_qu`, caseB-gated).  In **caseA it is FALSE**: `𝒮(H₀C)` then
  contains degree-`qa` irreducibles (`a>1`, `qa = a·w₁ ≠ qu`; Coq `Ptype_core_coherence` non-Galois
  branch, `PFsection9.v:1537`), and `χ_qa − a·ζ` is A₀-supported (`inducedKernelFamily_scaledDiff_support`)
  but *not* in `span ℤ (… ∪ D)` (the invariant `π = Σ Y-degree/q (mod u)` is `0` on every RHS
  generator but `a ≢ 0 (mod u)` on `χ_qa − a·ζ`, since `0 < a < u`).  The capstone *statement* is
  nonetheless TRUE (Coq proves the same coherence via `bridge_coherent`, `PFsection11.v:954`, which
  needs **no** generation hypothesis — the mixed `qa` content lives inside `hY` and the single
  `qu`-bridge suffices via norm-based `Zisometry_of_cfnorm`).  **The generation-based S07 engine is the
  wrong tool for this mixed-degree family**; the honest fix is a Coq-faithful `bridge_coherent` S07
  engine (no `hgen`), or a caseA/caseB split (caseB genuine, caseA on the enriched/bridge route).
  See issue 1019 update¹³. -/
theorem coherent_SOf_H0C_of_column_identities [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M) {d : ℕ}
    (hcol : ∀ j : Fin hyp.base.w2, j ≠ 0 →
      hyp.base.tau ((∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j) - (d : ℂ) • ζ)
        = (∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i j)
          - (d : ℂ) • coh.extension ζ) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := by
  haveI := hyp.base.finiteG
  classical
  -- `hY` = the unconditional `𝒮(H₀C)`-coherence (this file's `coherent_sOf_H0C`); the `τ₃` glue `ν`
  -- from the two coherences (issue-9016-style non-orthonormal glue).
  obtain ⟨hY⟩ := coherent_sOf_H0C hG hyp
  obtain ⟨ν, hagreeX, hagreeY⟩ := exists_glue_nu_H0C hyp coh hY
  refine ⟨coherent_SOf_H0C_of_glued hyp coh hY ν hagreeX hagreeY ?_
    {φ | ∃ j : Fin hyp.base.w2, j ≠ 0 ∧
      φ = (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j) - (d : ℂ) • ζ} ?_ ?_⟩
  · -- **hmixed** → the (6.7) image-side orthogonality (§14/Sibley-gated; mirrors S12:4888).  After
    -- `hagreeX`/`hagreeY` and the source orthogonality `⟨x,y⟩ = 0`, the residual is
    -- `⟨coh.extension x, hY.extension y⟩ = 0` (the `b ≡ 0` congruence of the two extensions).
    intro x hx y hy
    rw [hagreeX x hx, hagreeY y hy, SOf_HC_inner_sOf_H0C_eq_zero hyp hx hy]
    sorry
  · -- **hDτ** → the (5.8) column identity (§14-gated; mirrors S12:4896).  On the cross-diagonal
    -- `∑ᵢ μ_{ij} − dζ`, `hcol` rewrites the base map `τ`, leaving
    -- `ν (∑ᵢ μ_{ij} − dζ) = ∑ᵢ ω^σ_{ij} − d·coh.extension ζ` (the (5.8) identity for `ν`).
    intro d' hd'
    obtain ⟨j, hj, rfl⟩ := hd'
    rw [hcol j hj]
    sorry
  · -- **hgen** → the (6.8.1) generation.  §9 narrow uniform-degree generation (TRUE, cf.
    -- `forall_mem_sOf_H0C_apply_one_eq_qu` — the narrow `𝒮(H₀C)` degree `q·u`, NOT the false wide
    -- `Sset_diff_SHCSet_apply_one_eq_qu`); genuine version deferred.
    sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8), the genuine non-orthogonality — narrow `𝒮(H₀C)` route** (the honest
replacement of `S12.exists_zeta_residual_not_orthogonal`, which routed through the deprecated wide
`Sset \ SHCSet` uniform-degree lemma, false for non-Galois type III/IV, issue 1019).

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
theorem exists_zeta_residual_not_orthogonal_H0C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1) :
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
  -- (11.8.6) the narrow τ₃ union makes `S(H₀C)` coherent, contradicting (11.3) `S_H0C_not_coherent`.
  -- `coh` = the `ν` (h_orth-derived `S(HC)` coherence) restricted to `S(HC) ⊆ SHCSet`
  -- (`isCoherent_of_subset`, keeping `coh.extension = ν.extension`); the narrow capstone consumes
  -- `hcol` and the unconditional `𝒮(H₀C)`-coherence (`coherent_sOf_H0C`, threaded inside).
  haveI : NeZero (Nat.card (s13hyp.base.toHypothesis46 hG hG.odd).W1) :=
    ⟨by have := (s13hyp.base.toHypothesis46 hG hG.odd).one_lt_card_W1; omega⟩
  exact S_H0C_not_coherent hG s13hyp (coherent_SOf_H0C_of_column_identities hG s13hyp
    (isCoherent_of_subset ν (SOf_HC_subset_SHCSet hG s13hyp)
      (coherent_SOf_HC hG s13hyp).some.nonzero) hzS hcol)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9.b), narrow `𝒮(H₀C)` route** — `w₂ < w₁` (`q > p`) for the §10 hypothesis on a
type-III/IV/V maximal subgroup, via the honest narrow (11.8) `exists_zeta_residual_not_orthogonal_H0C`
(replacing `S12.w2_lt_w1_of_hypothesis`, which routed through the false wide uniform-degree lemma,
issue 1019) composed with the coherence-free reduction `w2_lt_w1_of_residual_not_orthogonal`.  This is
the `feitThompson`-spine consumer (`card_kappaHall_lt_of_isTypeIIIorIV`). -/
theorem w2_lt_w1_of_hypothesis_H0C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1) :
    hyp.w2 < hyp.w1 := by
  obtain ⟨ζ, hζS, hζirr, hζ1, h118⟩ :=
    exists_zeta_residual_not_orthogonal_H0C hG hyp htype hM2 hHcard
  exact OddOrder.Peterfalvi.S12.w2_lt_w1_of_residual_not_orthogonal hG hyp hζS hζirr hζ1 h118

end OddOrder.Peterfalvi.S13
