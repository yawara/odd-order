import OddOrder.Peterfalvi.S16_NonExistenceG.TSideTypeP

/-!
# Peterfalvi (14.9): the T-side Type-II theorem

The T-side type-III character estimate and the deduction that `T` is of Type II.
Topic-split from `OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupL`.
-/
namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]



open scoped Classical in
/-- **Peterfalvi (14.9): assembling the T-side `S07.Hypothesis` (`hyp07`)** (issue 9072, steps 2--4)
— the coherence-carrier constructor feeding `T_typeIII_calT1_coherent`.

Given the `calT1` family `𝒯 =` non-principal conjugate-closed `Irr(QV/Q)`-inflated sources (matching
`T_typeIII_calT1_card`/`calT1_image_induce_card_eq`), with:
* `hinertia : I_T(θ) = QV` for each `θ ∈ 𝒯` (⟹ `Ind_{QV}^T θ` irreducible), the same inertia fact
  feeding the count;
* `hne : θ ≠ 1` for each `θ ∈ 𝒯` (non-principal sources);
* `hconj𝒯 : θ ∈ 𝒯 ⟹ ⟨θ̄, θ.isIrreducible.conj⟩ ∈ 𝒯` (`𝒯` conjugate-closed, since `Irr` is);

this constructs the T-side `S07.Hypothesis calT1_set (supportInSubgroup (sigmaSharp T) T)` via the
in-repo assembler `S07.irrSubcoherent`, threading:
* `τ = tSideDadeMap hyp hG` (the genuine §10 Dade integral character map);
* the family predicates `S03.ClosedUnderConjugate`/`HasNoRealCharacters`/`PairwiseOrthogonal`, all
  derived from the induced-irreducible structure alone (Frobenius-analogous to the type-I
  `S14.Sset_*` witnesses): closure via `induce_conj`, no-real via `not_isReal_of_ne_trivial_of_odd_card'`
  (odd `|T|`, `Ind θ ≠ 1`), orthogonality via `irreducibleCharacter_inner_eq_ite`;
* the per-member `CharacterDifferenceImage` via `S07.dadeCharacterDifferenceImageOfDiff` (fed the
  conjugate-difference support `(χ̄ − χ).support ⊆ supportInSubgroup (sigmaSharp T) T`, from the
  member vanishing off `QV = T'` and `sigmaSharp T = (T')^#` = `T_typeIII_sigmaSharp_eq`);
* the isometry `tSideDadeMap_isometry_diff` (fed the family-supportedness `hSsupp`).

Everything here is **ungated**: it needs only the intrinsic type-III support identity
`T_typeIII_sigmaSharp_eq` and the induced-character bricks, no S-side βₛ / (13.12) input.  Its output
is exactly the `hyp07` argument that `T_typeIII_calT1_coherent` consumes to produce coherence. -/
noncomputable def T_typeIII_hyp07 [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (hconj𝒯 : ∀ θ ∈ 𝒯,
      (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
        θ.isIrreducible.conj⟩ :
        IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) := by
  classical
  haveI := hyp.base.finiteG
  -- `T` has odd order (subgroup of the odd `G`).
  have hodd : Odd (Nat.card ↥hyp.base.T) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.T)
  -- `K = QV.subgroupOf T` is normal in `T` (`QV = T' = derivedInG T ⊴ T`).
  haveI hKnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  -- The support identity `sigmaSharp T = (derivedInG T)^#`.
  have hAK : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  -- Membership form: `x ∈ A ↔ x ∈ K ∧ x ≠ 1`.
  have hmemA : ∀ x : ↥hyp.base.T,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ↔
        (x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T ∧ x ≠ 1) := fun x =>
    OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hAK x
  -- Each member of `calT1_set` is `Ind_K θ` for a non-principal `θ ∈ 𝒯`.
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  -- `Ind_K θ ≠ 1` (else `⟨Ind θ, 1⟩ = 1 ≠ 0 = ⟨Ind θ, 1⟩`), for non-principal `θ`.
  have hInd_ne_triv : ∀ θ (hθ : θ ∈ 𝒯),
      (⟨ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction,
        isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)⟩ :
        IrreducibleCharacter ↥hyp.base.T) ≠ trivialIrreducibleCharacter _ := by
    intro θ hθ hcontra
    -- `Res_K 1 = 1`, so `⟨Ind_K θ, 1⟩ = ⟨θ, Res 1⟩ = ⟨θ, 1⟩ = 0` (`θ ≠ 1`), contradicting `= 1`.
    have hrestrict : ClassFunction.restrict ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ)
        = (trivialIrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) :
            ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ) := by
      ext x
      simp [ClassFunction.restrict_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply]
    have hzero : ClassFunction.inner
        (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ))
        (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ) = 0 := by
      rw [ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
        irreducibleCharacter_inner_eq_ite, if_neg (hne θ hθ)]
    have hcf : ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)
        = (trivialIrreducibleCharacter ↥hyp.base.T : ClassFunction ↥hyp.base.T ℂ) :=
      congrArg (fun c : IrreducibleCharacter ↥hyp.base.T => (c : ClassFunction ↥hyp.base.T ℂ))
        hcontra
    rw [hcf, irreducibleCharacter_inner_eq_ite, if_pos rfl] at hzero
    exact one_ne_zero hzero
  -- (a) `S03.HasNoRealCharacters calT1_set`: each member is a nontrivial irreducible of the odd `T`.
  have hreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters calT1_set := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact not_isReal_of_ne_trivial_of_odd_card' (G := ↥hyp.base.T) hodd
      (χ := ⟨ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction,
        isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)⟩)
      (hInd_ne_triv θ hθ)
  -- (b) `S03.PairwiseOrthogonal calT1_set`: distinct irreducible members are orthogonal.
  have hortho : OddOrder.Peterfalvi.S03.PairwiseOrthogonal calT1_set := by
    intro χ ψ hχ hψ hne'
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    obtain ⟨θ', hθ', rfl⟩ := hmem_form ψ hψ
    have hχirr := isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
    have hψirr := isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ' (hinertia θ' hθ')
    rw [show ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction
          = ((⟨_, hχirr⟩ : IrreducibleCharacter ↥hyp.base.T) : ClassFunction ↥hyp.base.T ℂ) from rfl,
      show ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ'.toClassFunction
          = ((⟨_, hψirr⟩ : IrreducibleCharacter ↥hyp.base.T) : ClassFunction ↥hyp.base.T ℂ) from rfl,
      irreducibleCharacter_inner_eq_ite, if_neg]
    intro h
    exact hne' (congrArg
      (fun c : IrreducibleCharacter ↥hyp.base.T => (c : ClassFunction ↥hyp.base.T ℂ)) h)
  -- (c) `S03.ClosedUnderConjugate calT1_set`: `(Ind_K θ)^ = Ind_K θ̄` and `θ̄ ∈ 𝒯`.
  have hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate calT1_set := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    rw [hcalT1, Finset.mem_coe, Finset.mem_image]
    refine ⟨⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
      θ.isIrreducible.conj⟩, hconj𝒯 θ hθ, ?_⟩
    -- `Ind_K (θ̄) = (Ind_K θ)^`.
    exact (ClassFunction.induce_conj ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
      (θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ)).symm
  -- Support of the conjugate difference `χ̄ − χ` for a member `χ = Ind_K θ`: `⊆ A = (T')^#`.
  have hconjDiff_supp : ∀ χ ∈ calT1_set,
      ((χ : ClassFunction ↥hyp.base.T ℂ).conj - χ).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    intro x hx
    have hx0 : ((ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θ.toClassFunction).conj
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply] at hx0
    -- Off `K`, `Ind θ` vanishes (normal `K`), so the difference vanishes.
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θ.toClassFunction h]
      simp
    -- At `1`, `Ind θ (1)` is a real (natural) degree, so the conjugate difference vanishes.
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      obtain ⟨n, -, hn1, -⟩ :=
        (isIrreducibleCharacter_induce_of_inertia_eq
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
          (hinertia θ hθ)).exists_natDegree_charValue_one_dvd_card
      rw [hn1, star_natCast, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Support of a member *difference* `a − b`: `⊆ A` (both vanish off `K`, and `a(1) = b(1) = p`).
  have hdiff_supp : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro a ha b hb
    obtain ⟨θa, hθa, rfl⟩ := hmem_form a ha
    obtain ⟨θb, hθb, rfl⟩ := hmem_form b hb
    intro x hx
    have hx0 : (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θa.toClassFunction
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θb.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply] at hx0
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θa.toClassFunction h,
        ClassFunction.induce_eq_zero_of_not_mem_normal θb.toClassFunction h, sub_zero]
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      -- Both degrees are `[T:K]·θ(1) = [T:K]·1` (linear sources), so the difference vanishes at 1.
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one,
        hlinear θa hθa, hlinear θb hθb, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Each member is irreducible (packaged from its `Ind_K θ` form).
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- Per-member `CharacterDifferenceImage` from the Dade map (difference-support form).
  have Rdatum : ∀ χ ∈ calT1_set, OddOrder.Peterfalvi.S07.CharacterDifferenceImage
      (L := ↥hyp.base.T) (G := G) (tSideDadeMap hyp hG) χ := fun χ hχ =>
    -- Package `χ` (an irreducible member) as an `IrreducibleCharacter ↥T`; `(ζ : CF) = χ` by `rfl`.
    OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
      (tSideDadeSupport_nonempty hG hyp).some.dade (tSideDadeSupport_nonempty hG hyp).some.hconj
      ⟨χ, hirr χ hχ⟩ (hreal hχ) (hconjDiff_supp _ hχ)
  -- Assemble via the (5.3)(a) `irrSubcoherent` (0099 form: `hconjsupp` + `zSupportedSpan` isometry,
  -- the latter unconditional from the Dade pair brick).
  exact OddOrder.Peterfalvi.S07.irrSubcoherent (S := calT1_set) (tSideDadeMap hyp hG) _ Rdatum
    hconj hreal hortho
    (fun χ hχ => hdiff_supp χ hχ χ.conj (hconj hχ))
    (fun φ ψ hφ hψ => by
      simp only [tSideDadeMap]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (tSideDadeSupport_nonempty hG hyp).some.dade (tSideDadeSupport_nonempty hG hyp).some.hconj
        hφ.2 hψ.2)

open scoped Classical in
/-- **Peterfalvi (14.9): `calT1` is coherent** (Coq `PFsection14.v:750--751`
`have [tau1T cohT1]: coherent calT1 T^# tauT`, via
`apply/(uniform_degree_coherence scohT1)/(@all_pred1_constant _ p%:R)`) — the **coherence skeleton**
isolating the T-side type-`P` Dade setup as the single deep residual.

`calT1 = {Ind_{QV}^T θ | θ ∈ 𝒯}` (`QV = T' = derivedInG T`, `Q = M_F`, `𝒯 =` non-principal inflated
`Irr(QV/Q)`), realized here as the `Set`-coercion of the `Finset` image (matching
`T_typeIII_calT1_card`/`calT1_image_induce_card_eq`).  Given the **Dade setup** as the input
`hyp07 : S07.Hypothesis calT1_set A` (the Coq `subcoherent calT1 tauT rmR_T` = `FTtypeP_coh_base`,
carrying `tauT` and the seven §5.2 fields), this produces coherence via the proven engine
`S07.coherent_of_constant_degree` (Coq `uniform_degree_coherence`), **proving everything else** from
`calT1`'s structure + the proven count:

* `hirr` — each `ζ = Ind_{QV}^T θ (θ ∈ 𝒯)` is irreducible (`isIrreducibleCharacter_induce_of_inertia_eq`
  fed the inertia fact `hinertia : I_T(θ) = QV`, the same input feeding the count), so `⟨ζ,ζ⟩ = 1`
  (`IsIrreducibleCharacter.inner_self_eq_one`);
* `hconst`/`hdeg0` — each `ζ` has degree `ζ(1) = [T:QV]·θ(1) = p·1 = p ≠ 0`
  (`ClassFunction.induce_apply_one` + `T_derived_index_eq_p` `[T:QV] = p` + linearity
  `hlinear : θ(1) = 1`, since `θ` inflates from the abelian `QV/Q ≅ V`), i.e. Coq's `all_pred1_constant p`;
* `hSfin` — `calT1_set` is the image of a `Finset`, hence finite.

The residual — **the T-side type-`P` Dade isometry construction** (Coq `FTtypeP_coh_base`, a from-scratch
§4/§5 build with **no** existing type-`P` Dade base in the repo) — is precisely the input `hyp07`
together with the three genuinely Dade/support-dependent facts, kept as explicit hypotheses (each
cited from `hyp07`'s concrete Dade map at the call site, exactly as the §14 type-I assembly discharges
them via `dadeIntegralCharacterMap_mem_ZIrr_of_supported` etc.):

* `hZIrr : ∀ a b ∈ calT1_set, hyp07.tau (a − b) ∈ ZIrr G` — the Dade-map integrality on member
  differences (Coq `Ztau1T` from the `subcoherent` datum);
* `h1A : (1 : ↥T) ∉ A` and `hsuppdiff : ∀ a b ∈ calT1_set, (a − b).support ⊆ A` — the support/`A`-facts
  (Coq `A = T^#`, so `1 ∉ A` and every member difference vanishes off `T^#`);
* `hcard2 : 2 ≤ calT1_set.ncard` — the size bound `2 ≤ (|V|−1)/p` (arithmetic on `|V|`, from the proven
  count `T_typeIII_calT1_card`; kept explicit since it needs a `|V|`-lower bound not carried by the
  intrinsic datum here).

This is the honest §16 coherence assembly point for (14.9): it consumes only the verified bricks
(`isIrreducibleCharacter_induce_of_inertia_eq`, `induce_apply_one`, `T_derived_index_eq_p`,
`coherent_of_constant_degree`) and the parameterized Dade setup, leaving the type-`P` Dade base as the
single precisely-scoped deep obligation.  Its output feeds the (14.9) Γ-Bessel bound
`T_typeIII_ratio_le` (Coq `cohT1` consumed at PFsection14.v:769 `have [[Itau1T Ztau1T] Dtau1T] := cohT1`). -/
theorem T_typeIII_calT1_coherent [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (A : Set ↥hyp.base.T)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set A)
    (hZIrr : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set, hyp07.tau (a - b) ∈ ZIrr G)
    (h1A : (1 : ↥hyp.base.T) ∉ A)
    (hsuppdiff : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set, ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆ A)
    (hcard2 : 2 ≤ calT1_set.ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp07.tau calT1_set A) := by
  haveI := hyp.base.finiteG
  -- `calT1_set` is finite (image of a `Finset`).
  have hSfin : calT1_set.Finite := by rw [hcalT1]; exact (Finset.finite_toSet _)
  -- The `[T:QV] = p` index (degree factor) and its positivity.
  have hindex : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).index = hyp.base.p :=
    T_derived_index_eq_p hyp
  have hp_ne : (hyp.base.p : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hyp.base.p_prime.pos.ne'
  -- Each member `ζ = Ind_{QV}^T θ` is irreducible; extract its source `θ ∈ 𝒯` and its degree `= p`.
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  have hirr : ∀ ζ ∈ calT1_set, IsIrreducibleCharacter ζ := by
    intro ζ hζ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form ζ hζ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  have hdeg : ∀ ζ ∈ calT1_set, (ζ : ↥hyp.base.T → ℂ) 1 = (hyp.base.p : ℂ) := by
    intro ζ hζ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form ζ hζ
    rw [ClassFunction.induce_apply_one, hindex, hlinear θ hθ, mul_one]
  -- assemble and invoke the equal-degree coherence producer.
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree hyp07 hSfin hcard2 ?_ hZIrr ?_ ?_ h1A hsuppdiff
  · exact fun ζ hζ => (hirr ζ hζ).inner_self_eq_one
  · exact fun a ha b hb => by rw [hdeg a ha, hdeg b hb]
  · exact fun a ha => by rw [hdeg a ha]; exact hp_ne

open scoped Classical in
/-- **Peterfalvi (14.9): `calT1` is coherent, end-to-end** (issue 9072, Stage-1 completion) — the
composition `T_typeIII_hyp07` ∘ `T_typeIII_calT1_coherent` that produces the coherent map `τ₁` from
the *intrinsic* family data alone (plus the gated size bound `hcard2`).  The T-side `S07.Hypothesis`
Dade package `hyp07` is now **constructed** (not posited) by `T_typeIII_hyp07`, and its three
support/integrality carriers are discharged here from the induced-character support facts:

* `hZIrr` — `τ_T(a − b) ∈ ZIrr G` via `S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported` (the
  member difference is `A₁(T)`-supported (`hdiff_supp`) and lies in `ℤ[Irr T]`);
* `h1A` — `1 ∉ A₁(T) = supportInSubgroup (sigmaSharp T) T` (`one_not_mem_supportInSubgroup_sharp`);
* `hsuppdiff` — member differences vanish off `A₁(T)` (the same `hdiff_supp`, from the members
  vanishing off `QV = T'` and `sigmaSharp T = (T')^#`).

The only *external* input is `hcard2 : 2 ≤ calT1_set.ncard` (`= (|V|−1)/p ≥ 2`, the size bound needing
a `|V|`-lower bound — kept explicit, as in `T_typeIII_calT1_coherent`).  Output: the coherent
`τ₁ = hyp07.tau = tSideDadeMap hyp hG`-extension whose orthonormal image family feeds the (14.9)
Γ-Bessel bound. -/
theorem T_typeIII_calT1_isCoherent [Finite G] (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hinertia : ∀ θ ∈ 𝒯,
      IrreducibleCharacter.inertia (G := ↥hyp.base.T)
          (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T)
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _)
    (hconj𝒯 : ∀ θ ∈ 𝒯,
      (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
        θ.isIrreducible.conj⟩ :
        IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hcard2 : 2 ≤ calT1_set.ncard) :
    ∃ hyp07 : OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.base.T) (G := G) calT1_set
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T),
      hyp07.tau = tSideDadeMap hyp hG ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp07.tau calT1_set
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)) := by
  classical
  haveI := hyp.base.finiteG
  -- Support identity `sigmaSharp T = (derivedInG T)^#` and the sharp-membership form.
  have hAK : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hmemA : ∀ x : ↥hyp.base.T,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ↔
        (x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T ∧ x ≠ 1) := fun x =>
    OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hAK x
  haveI hKnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  have hmem_form : ∀ a ∈ calT1_set, ∃ θ ∈ 𝒯,
      a = ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction := by
    intro a ha
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    exact ⟨θ, hθ, rfl⟩
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := hmem_form χ hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- Member-difference support `⊆ A₁(T)` (`= hsuppdiff`).
  have hdiff_supp : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      ((a - b : ClassFunction ↥hyp.base.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    intro a ha b hb
    obtain ⟨θa, hθa, rfl⟩ := hmem_form a ha
    obtain ⟨θb, hθb, rfl⟩ := hmem_form b hb
    intro x hx
    have hx0 : (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
          θa.toClassFunction
        - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θb.toClassFunction) x
        ≠ 0 := ClassFunction.mem_support.mp hx
    rw [ClassFunction.sub_apply] at hx0
    have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
      by_contra h
      apply hx0
      rw [ClassFunction.induce_eq_zero_of_not_mem_normal θa.toClassFunction h,
        ClassFunction.induce_eq_zero_of_not_mem_normal θb.toClassFunction h, sub_zero]
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hx0
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one,
        hlinear θa hθa, hlinear θb hθb, sub_self]
    rw [hmemA x]; exact ⟨hxK, hx1⟩
  -- Build `hyp07` via `T_typeIII_hyp07`; its `.tau = tSideDadeMap hyp hG` (by `rfl`).
  set hyp07 := T_typeIII_hyp07 hyp hG hIII 𝒯 hinertia hne hlinear hconj𝒯 calT1_set hcalT1
    with hhyp07
  have htau : hyp07.tau = tSideDadeMap hyp hG := rfl
  refine ⟨hyp07, htau, ?_⟩
  -- `h1A`: `1 ∉ A₁(T)`.
  have h1A : (1 : ↥hyp.base.T) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
    rw [hmemA 1]; rintro ⟨-, h⟩; exact h rfl
  -- `hZIrr`: `τ_T(a − b) ∈ ZIrr G` (member difference `A₁(T)`-supported + in `ℤ[Irr T]`).
  have hZIrr : ∀ a ∈ calT1_set, ∀ b ∈ calT1_set, hyp07.tau (a - b) ∈ ZIrr G := by
    intro a ha b hb
    rw [htau]
    simp only [tSideDadeMap]
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (tSideDadeSupport_nonempty hG hyp).some.dade (tSideDadeSupport_nonempty hG hyp).some.hconj
      (hdiff_supp a ha b hb) ?_
    exact Submodule.sub_mem _ (hirr a ha).mem_ZIrr (hirr b hb).mem_ZIrr
  -- Feed the coherence engine `T_typeIII_calT1_coherent`.
  exact T_typeIII_calT1_coherent hyp 𝒯 hinertia hlinear _ calT1_set hcalT1 hyp07 hZIrr h1A
    hdiff_supp hcard2

open scoped Classical in
/-- **Peterfalvi (14.9), the Γ-Bessel assembly skeleton** — the *proven* structural core of the
character body, isolating the char-cascade carriers as precisely-named hypotheses.  Coq
`FTtypeP_min_typeII` (PFsection14.v:764--853): given the coherent `τ₁`-image family `calT1`
(orthonormal degree-`p` induced characters, whose `|calT1| = (v−1)/p` count is the proven
`T_typeIII_calT1_card` after the (13.12) `d = 1` substitution `v = |V|`) and the `S`-side `βₛ`
bridge gap `Γ`, the parity fact `⟨Γ, τ₁ζ⟩ ≡ 1 (mod 2)` per `ζ` (`S09.cfdot_real_vchar_even`) makes
each integer pairing coefficient `x ζ = ⟨Γ, τ₁ζ⟩` **nonzero**; then the orthogonal-integer Bessel
bridge `S09.sum_rat_weights_le_of_orthogonal_integer_decomposition` (Coq's `orthogonal_split` +
Bessel over `‖Γ‖² ≤ (u−1)/q`) gives `∑_{ζ ∈ calT1} 1 ≤ ⟨Γ,Γ⟩ ≤ (u−1)/q`, i.e.
`|calT1| = (v−1)/p ≤ (u−1)/q`.

This is the **genuinely-available** arithmetic of (14.9): everything downstream of the carriers is
proven here (the orthonormal-family Bessel step with unit weights `m ζ = 1`, the `∑ 1 = |calT1|`
count-collapse, and the `⟨Γ,Γ⟩ ≤ (u−1)/q` chaining).  The four hypotheses package exactly the deep
carriers that the honest §16 build still owes, each cited from its own construction at the
`T_typeIII_ratio_le` call site:

* `hcount : (calT1.card : ℚ) = (v−1)/p` — the coherent count (proven `T_typeIII_calT1_card` in `|V|`
  form) **after** the (13.12) `d = 1` substitution `v = |V|` (`S15.V_inf_centralizer_Q_eq_bot`, lane-b);
* `horth` — orthonormality of the `τ₁`-images (the `calT1` **coherence** carrier, proven skeleton
  `T_typeIII_calT1_coherent` fed a T-side `S07.Hypothesis` Dade package);
* `hdecomp`/`hΓ₁`/`hx` — the `S`-side `βₛ` bridge gap `Γ = ∑ x_ζ·τ₁ζ + Γ₁` (`Γ₁ ⊥ τ₁ζ`), with the
  parity nonzeroness `x_ζ ≠ 0` (Coq `nzT1_Ga` via `cfdot_real_vchar_even`);
* `hnorm : ⟨Γ,Γ⟩.re ≤ (u−1)/q` — the `S`-side norm bound on the bridge gap.

Its output `(v−1)/p ≤ (u−1)/q` is exactly the (14.9) `≤` whose `>` counterpart (14.8)
`key_inequality` contradicts. -/
theorem T_typeIII_ratio_le_of_gamma_bridge [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis (G := G))
    (calT1 : Finset (ClassFunction G ℂ)) (Γ Γ₁ : ClassFunction G ℂ)
    (x : ClassFunction G ℂ → ℤ)
    (hcount : (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (hdecomp : Γ = (∑ a ∈ calT1, (((x a : ℝ) : ℂ) • a)) + Γ₁)
    (hΓ₁ : ∀ a ∈ calT1, ClassFunction.inner Γ₁ a = 0)
    (hx : ∀ a ∈ calT1, x a ≠ 0)
    (hnorm : (ClassFunction.inner Γ Γ).re ≤
      ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ)) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  classical
  -- Bessel over the orthonormal `calT1` (unit weights `m a = 1`, integer coeffs `x a ≠ 0`),
  -- against the norm bound `⟨Γ,Γ⟩ ≤ (u−1)/q`: yields `∑_{a ∈ calT1} 1 ≤ (u−1)/q`.
  have hbessel := OddOrder.Peterfalvi.S09.sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := ClassFunction G ℂ) calT1 (fun a => a) x (fun _ => (1 : ℚ)) Γ Γ₁
    (((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ))
    hdecomp
    (fun a ha b hb => by rw [horth a ha b hb]; split <;> simp)
    hΓ₁
    (fun _ _ => zero_le_one)
    hx
    hnorm
  -- `∑_{a ∈ calT1} 1 = |calT1|`, and `|calT1| = (v−1)/p` by the coherent count.
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcount] at hbessel
  exact hbessel

open scoped Classical in
/-- **(14.9) Γ-bridge extraction engine.**  Given the `S`-side gap `Γ`, its integral nonzero
coefficients on the orthonormal coherent family `calT1`, and the orthogonality of that family to the
η-grid, define the complementary term `Γ₁ := Γ - ∑_ζ x_ζ·ζ`.  Orthonormality makes `Γ₁`
orthogonal to every family member, hence to the projection sum.  The projection sum is η-grid
orthogonal by hypothesis, so the genuine **Peterfalvi (13.18.d)** field `BetaData.Y_norm_bound`
applies to the split `Γ = Γ₁ + ∑_ζ x_ζ·ζ`.

The resulting bound is on the projection sum—not on `Γ` itself—and feeds the proven Bessel skeleton
`T_typeIII_ratio_le_of_gamma_bridge`.  Thus this theorem exactly matches the corrected (13.18.d)
statement and assumes no overstrong full-gap norm bound. -/
theorem T_typeIII_ratio_le_of_sSide_gap [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis (G := G)) (calT1 : Finset (ClassFunction G ℂ))
    (horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (hcount : (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (Γ : ClassFunction G ℂ) (x : ClassFunction G ℂ → ℤ)
    (hxcoe : ∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ))
    (hx : ∀ a ∈ calT1, x a ≠ 0)
    (heta : ∀ a ∈ calT1, ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
      ClassFunction.inner a (hyp.base.eta i k) = 0)
    (hYnorm : ∀ (X Y : ClassFunction G ℂ), Γ = X + Y →
      ClassFunction.inner X Y = 0 →
      (∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
        ClassFunction.inner Y (hyp.base.eta i k) = 0) →
      (ClassFunction.inner Y Y).re ≤
        ((hyp.base.u : ℚ) - 1) / (hyp.base.q : ℚ)) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  classical
  set Γ₁ : ClassFunction G ℂ := Γ - ∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a with hΓ₁def
  have hdecomp : Γ = (∑ a ∈ calT1, (((x a : ℝ) : ℂ) • a)) + Γ₁ := by rw [hΓ₁def]; abel
  -- `Γ₁` is orthogonal to every member: `⟨Γ₁, b⟩ = ⟨Γ, b⟩ − ∑_a x_a·⟨a,b⟩ = x_b − x_b = 0`
  -- (inner is linear in the first argument, `inner_smul_left : ⟨c•φ,ψ⟩ = c·⟨φ,ψ⟩`).
  have hΓ₁ : ∀ a ∈ calT1, ClassFunction.inner Γ₁ a = 0 := by
    intro b hb
    have hsum_left : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner (∑ a ∈ s, ((x a : ℝ) : ℂ) • a) b
          = ∑ a ∈ s, ClassFunction.inner (((x a : ℝ) : ℂ) • a) b := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_left, ih, Finset.sum_insert hc]
    rw [hΓ₁def, ClassFunction.inner_sub_left, hsum_left calT1, hxcoe b hb,
      Finset.sum_eq_single b
        (fun a ha hab => by
          rw [ClassFunction.inner_smul_left, horth a ha b hb, if_neg hab, mul_zero])
        (fun hbni => absurd hb hbni),
      ClassFunction.inner_smul_left, horth b hb b hb, if_pos rfl, mul_one, sub_self]
  -- The projection sum is the `Y` in (13.18.d).  Its complement `Γ₁` is orthogonal to it
  -- because `Γ₁` is orthogonal to every member of `calT1`.
  have hΓ₁sum : ClassFunction.inner Γ₁
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) = 0 := by
    have hsum_right : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner Γ₁ (∑ a ∈ s, ((x a : ℝ) : ℂ) • a)
          = ∑ a ∈ s, ClassFunction.inner Γ₁ (((x a : ℝ) : ℂ) • a) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_right, ih, Finset.sum_insert hc]
    rw [hsum_right calT1]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ClassFunction.inner_smul_right, hΓ₁ a ha, mul_zero]
  have hsum_eta : ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
      ClassFunction.inner (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)
        (hyp.base.eta i k) = 0 := by
    intro i k
    have hsum_left : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner (∑ a ∈ s, ((x a : ℝ) : ℂ) • a) (hyp.base.eta i k)
          = ∑ a ∈ s,
            ClassFunction.inner (((x a : ℝ) : ℂ) • a) (hyp.base.eta i k) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_left, ih, Finset.sum_insert hc]
    rw [hsum_left calT1]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ClassFunction.inner_smul_left, heta a ha i k, mul_zero]
  have hdecomp' : Γ = Γ₁ + ∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a := by
    rw [hdecomp]
    abel
  have hnormRaw := hYnorm Γ₁
    (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) hdecomp' hΓ₁sum hsum_eta
  have hu1 : 1 ≤ hyp.base.u := by
    have huc : 0 < hyp.base.u * hyp.base.c := by
      rw [← hyp.base.card_U_eq_uc]
      exact Nat.card_pos
    exact (CanonicallyOrderedAdd.mul_pos.mp huc).1
  have hsubcast : ((hyp.base.u - 1 : ℕ) : ℚ) = (hyp.base.u : ℚ) - 1 := by
    rw [Nat.cast_sub hu1]
    norm_num
  have hnorm : (ClassFunction.inner
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)).re ≤
        ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ) := by
    rw [hsubcast]
    simpa using hnormRaw
  exact T_typeIII_ratio_le_of_gamma_bridge hyp calT1
    (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) 0 x hcount horth (by simp) (by simp) hx hnorm
/-- **Peterfalvi (13.4)/(14.4), `T`-side case (9.7.b)**: the `T`-side centralizer parameter
vanishes and `v` has its full cyclotomic value.  This is obtained directly from the (13.3)
character-degree package and the (13.4) cross-expansion, before the (14.9) type-II conclusion.

Keeping this producer upstream of `T_typeIII_ratio_le` is essential: (13.4) is an input to the
(14.9) contradiction, whereas deriving the same facts from `T_typeII` would create the cycle
`T_isTypeP2 → T_typeIII_ratio_le → T_side_caseB_facts → T_typeII → T_isTypeP2`. -/
theorem T_side_caseB_facts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.D = ⊥ ∧
      hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
  obtain ⟨chars⟩ := OddOrder.Peterfalvi.S15.character_degree_analysis hG hyp.base
  obtain ⟨hD, hv, _hQ⟩ := OddOrder.Peterfalvi.S15.lambda_forces_T_caseB hG chars
  exact ⟨hD, hv⟩

/-- **Peterfalvi (14.9), the character body** — the structural `≤` half of the ratio comparison, the
sole deep obligation of (14.9).  Coq `PFsection14` `FTtypeP_min_typeII`, lines 737--853: assuming `T`
is type III, build `calT1 = seqIndD QV T QV Q` (the degree-`p` induced characters of `T`, from
`T' = Q ⊔ V` via `T_deriv_eq_QV`), coherent by uniform-degree coherence
(`S07.coherent_of_constant_degree` / Coq `uniform_degree_coherence`).  Now **reduced to the proven
Γ-Bessel skeleton** `T_typeIII_ratio_le_of_gamma_bridge` (above), which discharges all the
orthonormal-family Bessel arithmetic; this theorem supplies the skeleton's four precisely-named
char-cascade carriers (`hcount`/`horth`/`hdecomp`+`hΓ₁`+`hx`/`hnorm`), kept jointly as its single
documented residual `sorry`.  Via the `S`-side `βₛ` bridge
gap `Γ`, `⟨Γ, τ₁ ζ⟩ ≡ 1 (mod 2)` for each `ζ ∈ calT1` (Coq `nzT1_Ga`, using
`cfdot_real_vchar_even`), so `|⟨Γ, τ₁ ζ⟩|² ≥ 1`; then `orthogonal_split` + Bessel give
`(v − 1)/p = p · |calT1| ≤ ⟨Γ, Γ⟩ ≤ (u − 1)/q`.

The `|calT1| = (v − 1)/p` step is *structural* (Coq line 836--845: `size calT1 = (v.-1) %/ p` from
`v = |V/Q|` and the degree-`p` induction), so this bound does **not** re-derive the exact `v`-value;
it is exactly the type-III Γ-bridge estimate whose `>` counterpart (14.8) `key_inequality` then
contradicts.  Kept as the single precisely-named character residual of (14.9).

**Blocker map (why this stays sorried; lane-c 2026-07-06).**  The Coq spine needs four missing
pieces, none supplied by the `S16_PairingBessel` M-side template (which inducts from the *full*
`Irr(M')` via a Frobenius `(T, M', C)` and counts fibers with `card_index_mul_sum_induced_family_
degree_sq` — *not* the quotient-restricted `Irr(QV/Q)` family with a `W₁`-orbit count):

1. **`v = |V|`** (Peterfalvi (13.12), `d = 1`, i.e. `D = V ⊓ C_G(Q) = ⊥`).  Coq's `v := |V|` is
   *definitional* (PFsection14.v:66/422) so its `(v−1)/p` bound is literally `(|V|−1)/p`; the Lean
   `Hypothesis.v` is a **free** ℕ with only `card_V_eq_vd : |V| = v·d`, so `v = |V|` iff `d = 1`.
   That is `S15.V_inf_centralizer_Q_eq_bot` — currently **sorried and gated on `IsTypeII T`**, hence
   unavailable in this type-III branch.  Without it, the honest `|calT1| = (|V|−1)/p` cannot be
   identified with the goal's `(v−1)/p`.  (`T_card_quot_Q_derived_eq_card_V` above supplies the
   `|QV/Q| = |V|` half; the `|V| = v` half is the missing (13.12).)
2. **The `calT1` family + its `|calT1| = (v−1)/p` count.**  Needs (a) inflation `Irr(QV/Q) ↪
   {χ ∈ Irr QV | Q ⊆ ker}` (available: `RepresentationTheory.InflationCharacter`), (b)
   `Ind_{QV}^T`-irreducibility for nonprincipal inflated sources via `I_T(θ) = QV` — reduced below to
   two general rep-theory bricks, **both now available as shared infra**, so no longer missing — and
   (c) the `/p` **orbit count**, landed as reusable shared infra
   `RepresentationTheory.card_image_induce_eq_div` (`OrbitOnIrr.lean`):
   `|T.image (Ind_H^G)| = |T| / [G:H]` for a conjugation-invariant `T ⊆ Irr H` with `I_G(θ) = H`
   throughout — the cardinality analogue of the M-side degree-square `sum_div_normSq_induce_image_eq`,
   built from `card_filter_induce_eq_index_inertia`.  With (a)+(c) in hand the count reduces to (b).

   The residual (b) — `I_T(inflate θ) = QV` for nonprincipal `θ ∈ Irr(QV/Q)` (Coq
   `irr_induced_Frobenius_ker` + `injm_Frobenius_ker` through the quotient, PFsection14.v:757--762) —
   is packaged as the reusable brick `inertia_inflate_eq_of_frobeniusQuotient` (this file):
   `I_G(inflate θ̄) = H` from a Frobenius quotient `G/N` with kernel `H/N`, via
   `inertia_eq_of_frobeniusGroup` (⟹ `I_{G/N}(θ̄) = H/N`) + the inertia/inflation bridge
   `mem_inertia_compHom_iff` (`ConjugationBrauer.lean`) + `comap_map_eq_self` (`N ≤ H`).  Its input,
   the quotient Frobenius `T/Q = (QV/Q) ⋊ (W₂Q/Q)`, is transported (`isFrobeniusGroup_map_equiv`)
   from the **intrinsic** `U ⋊ W₁` Frobenius `T_typeIII_UW1_frobenius` through `mk' Q` (injective on
   `U ⊔ W₁` since `Q ⊓ (U ⊔ W₁) = ⊥`) — **ungated**, replacing the earlier abstract-`V ⋊ W₂`
   (`S15.isMulCommutative_V`) route that was gated through the sorried `reconciled_typePData_T`.
   Likewise `U` abelian is the intrinsic `td.U_commutative` (ungated), not the gated abstract-`V`
   abelianness.  See the (now-`UNGATED`) escape-hatch conclusion below.
3. **A full `S07.Hypothesis` (5.2) instance for `calT1`** (the (12.1) T-side Dade `tauT` +
   `difference_image`/`no_real`/`pairwise_orthogonal`/`tau_isometry_diff`), to feed
   `coherent_of_constant_degree`.  This is the T-side coherence package, itself separately gated.
4. **The `S`-side βₛ bridge gap `Γ`** and `⟨Γ, τ₁ζ⟩ ≡ 1 (mod 2)` (Coq `nzT1_Ga`, via
   `S09.cfdot_real_vchar_even`), then `orthogonal_split` + Bessel.  `Γ` needs the full S-side
   (13.x)/(14.x) βₛ construction (cf. the `S16_NonExistenceG` βₛ-grid sorry at ~line 6377).

Escape-hatch conclusion (**revised 2026-07-06, lane-c** — the count is now known **UNGATED**; this
corrects an earlier lane-c note that wrongly called items 2/b "gated behind `IsTypeP2 T`").  The
`IsTypeP2` gate is **bypassed by working with the *intrinsic* type-III datum** `td = hIII.some :
TypeIIIData T` (NOT the abstract Hypothesis `V`/`W₂`, whose reconciliation to `td` is the sorried
`S15.reconciled_typePData_T`).  Its factors `td.typeP.U`/`td.typeP.W₁` supply, **all ungated**:

* `td.U_commutative : IsMulCommutative ↥td.typeP.U` (⟹ `QV/Q ≅ U` abelian ⟹ `|Irr(QV/Q)| = |V|`);
* `T_typeIII_UW1_frobenius` — the `U ⋊ W₁` Frobenius (`S11.typeP_uW1_frobenius td.typeP td.common.1`,
  Coq `frobVW2`), the ungated source of the quotient Frobenius `T/Q` for the inertia fact;
* `T_typeIII_card_W1 : |td.typeP.W₁| = p` and `T_typeIII_card_U : |td.typeP.U| = |V|` — canonical
  (both sides are intrinsic indices `[T:T']`, `[T':M_F]`), so **no** abstract-`V`/`W₂`
  reconciliation.

Landed ungated + green: the group-theoretic foundation (`T_derived_index_eq_p`,
`T_Q_isComplement_V_derived`, `T_card_quot_Q_derived_eq_card_V`, `T_derivedSubgroupOf_normal`), the
orbit-count engine `calT1_image_induce_card_eq` (`|{Ind_{QV}^T θ}| = |𝒯|/p` for conj-invariant
inertia-`QV` `𝒯`), the reusable inflation-quotient inertia brick
`inertia_inflate_eq_of_frobeniusQuotient` (`I_G(inflate θ̄) = H` from a Frobenius quotient `G/N`,
kernel `H/N`), the four intrinsic facts above, and the **no-`sorry` assembly skeleton**
`T_typeIII_calT1_card_eq` producing `|calT1| = (|V|−1)/p` from the count engine + `|𝒯| = |V|−1`.

The remaining `|calT1| = (|V|−1)/p` work is **pure transcription, ungated** (not a gate): discharging
the skeleton's `hcard`/`hconj`/`hinertia` by (i) building `𝒯` = non-principal inflated `Irr(QV/Q)`,
(ii) the `Q`-complement `IsComplement' (Q.subgroupOf T) ((U ⊔ W₁).subgroupOf T)` → iso
`↥T/Q ≅ U ⊔ W₁` → quotient Frobenius `T/Q` via `isFrobeniusGroup_map_equiv` (feeding
`inertia_inflate_eq_of_frobeniusQuotient`), (iii) `|𝒯| = |V|−1` via `inflate_injective` +
`T_typeIII_card_U` + `card_irreducibleCharacter_eq_card_of_commGroup`, (iv) conj-invariance via
`conjBy_compHom_eq_compHom_conjBy`.  All bricks for (i)-(iv) are landed/verified.

Then the *full* (14.9) `T_typeIII_ratio_le` bound still needs, beyond `|calT1| = (|V|−1)/p`:
item 1 (`v = |V|`, i.e. (13.12) `d = 1`, separately lane-b-gated — the `(|V|−1)/p → (v−1)/p`
substitution), item 3 (the T-side coherence package `S07.Hypothesis` feeding
`coherent_of_constant_degree`), and item 4 (the S-side `Γ` bridge + `nzT1_Ga` + `orthogonal_split`
Bessel).  Those remain the documented residual of the character body. -/
theorem T_typeIII_ratio_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  -- Coq `FTtypeP_min_typeII` body (PFsection14.v:737--853): `calT1`/coherence + Γ-Bessel.
  -- Reduced to the proven Γ-Bessel skeleton `T_typeIII_ratio_le_of_gamma_bridge`; its inputs are
  -- the precisely-named char-cascade carriers, each a genuinely-missing construction kept as a
  -- documented residual `sorry` here (NOT a gate on `T_typeIII_ratio_le`'s honest structure — the
  -- Bessel/orthonormality/count arithmetic is fully proven in the skeleton).
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI := hyp.base.finiteG
  haveI : Fintype ↥hyp.base.T := Fintype.ofFinite _
  haveI : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥hyp.base.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- **Carrier 1 (the coherent `τ₁`-image family, now DISCHARGED from the (14.9) coherence).**
  -- The intrinsic type-III datum builds the degree-`p` `Ind_{QV}^T`-family `calT1_set` with all
  -- coherence inputs (`T_typeIII_calT1_family`); the T-side Dade package + coherence engine
  -- (`T_typeIII_calT1_isCoherent`, i.e. `T_typeIII_hyp07` ∘ `T_typeIII_calT1_coherent`) then produce
  -- the coherent map `τ₁ = hτ.extension`.  Its image `calT1 := τ₁(calT1_set)` is an **orthonormal**
  -- set of `G`-class functions (`horth`), because `τ₁` is an isometry on `ℤ[calT1_set]`
  -- (`IsCoherent.extension_inner_eq`) and the source members are orthonormal irreducibles.
  obtain ⟨𝒯, hinertia, hne, hlinear, hconj𝒯, hcount_V⟩ :=
    T_typeIII_calT1_family hyp hIII.some
  set calT1_set : Set (ClassFunction ↥hyp.base.T ℂ) :=
    ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) with hcalT1
  -- Members of `calT1_set` are orthonormal irreducibles of `T` (irreducible + pairwise orthogonal
  -- via `T_typeIII_hyp07`'s family predicates), reused below for `horth`.
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at hχ
    obtain ⟨θ, hθ, rfl⟩ := hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- `hcard2 : 2 ≤ |calT1_set|` — the crude size bound `(|V|−1)/p ≥ 2`, **ungated**: from the
  -- intrinsic `2p + 1 ≤ |V|` (`T_typeIII_two_p_add_one_le_card_V`, odd-order Frobenius `U ⋊ W₁`)
  -- and the count `|calT1_set| = (|V|−1)/p` (`hcount_V`), via `2 ≤ (|V|−1)/p ⟺ 2p ≤ |V|−1`.  The
  -- lane-b `|V|`-lower-bound (`v = (q^p−1)/(q−1)`, 13.15) is only needed for the *exact* count, not
  -- this `≥ 2`.
  have hcard2 : 2 ≤ calT1_set.ncard := by
    have hV := T_typeIII_two_p_add_one_le_card_V hG hyp hIII.some
    have hncard : calT1_set.ncard = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
      rw [hcalT1, Set.ncard_coe_finset]; exact hcount_V
    rw [hncard, Nat.le_div_iff_mul_le hyp.base.p_prime.pos]
    omega
  -- The T-side coherence: `τ₁ = hτ.extension`, `IsCoherent (tSideDadeMap) calT1_set A₁(T)`.
  obtain ⟨hyp07, _htau, ⟨hτ⟩⟩ :=
    T_typeIII_calT1_isCoherent hyp hG hIII 𝒯 hinertia hlinear hne hconj𝒯 calT1_set hcalT1 hcard2
  -- `calT1 := τ₁(calT1_set)`, the coherent-image `Finset` in `CF(G)`.
  set calT1 : Finset (ClassFunction G ℂ) :=
    calT1_set.toFinset.image (⇑hτ.extension) with hcalT1img
  -- **`horth`: the coherent images are orthonormal** — the discharged coherence carrier.
  have horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 := by
    intro a ha b hb
    rw [hcalT1img, Finset.mem_image] at ha hb
    obtain ⟨ζ, hζT, rfl⟩ := ha
    obtain ⟨ζ', hζ'T, rfl⟩ := hb
    rw [Set.mem_toFinset] at hζT hζ'T
    -- `⟨τ₁ζ, τ₁ζ'⟩ = ⟨ζ, ζ'⟩` (coherent isometry on `ℤ[calT1_set]`).
    have hiso : ClassFunction.inner (hτ.extension ζ) (hτ.extension ζ')
        = ClassFunction.inner ζ ζ' :=
      hτ.extension_inner_eq ζ ζ' (Submodule.subset_span hζT) (Submodule.subset_span hζ'T)
    -- `⟨ζ, ζ'⟩ = if ζ = ζ' then 1 else 0` (orthonormal irreducibles).
    have hsrc : ClassFunction.inner ζ ζ' = if ζ = ζ' then (1 : ℂ) else 0 := by
      by_cases hζζ' : ζ = ζ'
      · subst hζζ'; rw [if_pos rfl]; exact (hirr ζ hζT).inner_self_eq_one
      · rw [if_neg hζζ']; exact hyp07.pairwise_orthogonal hζT hζ'T hζζ'
    rw [hiso, hsrc]
    -- The image equality `τ₁ζ = τ₁ζ'` iff `ζ = ζ'` (injectivity from the isometry).
    by_cases hζζ' : ζ = ζ'
    · rw [if_pos hζζ', if_pos (by rw [hζζ'])]
    · rw [if_neg hζζ', if_neg ?_]
      -- if `τ₁ζ = τ₁ζ'` then `⟨ζ,ζ'⟩ = ⟨τ₁ζ,τ₁ζ⟩ = ⟨ζ,ζ⟩ = 1 ≠ 0 = ⟨ζ,ζ'⟩`, contradiction.
      intro hab
      have h1 : ClassFunction.inner ζ ζ' = ClassFunction.inner ζ ζ := by
        rw [← hiso, ← hab,
          hτ.extension_inner_eq ζ ζ (Submodule.subset_span hζT) (Submodule.subset_span hζT)]
      rw [hsrc, if_neg hζζ', (hirr ζ hζT).inner_self_eq_one] at h1
      exact one_ne_zero h1.symm
  -- The coherent extension is injective on `calT1_set`: equality of two images would turn the
  -- source cross-inner-product `0` into the source self-inner-product `1`.
  have hinj : Set.InjOn (⇑hτ.extension) (↑calT1_set.toFinset : Set _) := by
    intro ζ hζ ζ' hζ' heq
    have hζS : ζ ∈ calT1_set := by simpa using hζ
    have hζ'S : ζ' ∈ calT1_set := by simpa using hζ'
    by_contra hne
    have hEq : ClassFunction.inner ζ ζ' = ClassFunction.inner ζ ζ := by
      rw [← hτ.extension_inner_eq ζ ζ' (Submodule.subset_span hζS)
          (Submodule.subset_span hζ'S), ← heq,
        hτ.extension_inner_eq ζ ζ (Submodule.subset_span hζS) (Submodule.subset_span hζS)]
    rw [hyp07.pairwise_orthogonal hζS hζ'S hne, (hirr ζ hζS).inner_self_eq_one] at hEq
    exact zero_ne_one hEq
  have hcalcard : calT1.card = calT1_set.toFinset.card := by
    rw [hcalT1img, Finset.card_image_of_injOn hinj]
  have hsourcecard :
      calT1_set.toFinset.card = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
    rw [← Set.ncard_eq_toFinset_card' calT1_set, hcalT1, Set.ncard_coe_finset]
    exact hcount_V
  -- (13.4) gives `D = ⊥`; hence `d = |D| = 1` and `|V| = v d = v`.
  have hDbot : hyp.base.D = ⊥ := (T_side_caseB_facts hG hyp).1
  have hd1 : hyp.base.d = 1 := by
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  have hVcard : Nat.card ↥hyp.base.V = hyp.base.v := by
    rw [hyp.base.card_V_eq_vd, hd1, mul_one]
  -- The same (13.4) value makes `v ≡ 1 (mod p)`, so the exact Nat quotient casts to the
  -- rational ratio used by the Bessel engine.
  have hvfull := (T_side_caseB_facts hG hyp).2
  have hvodd : Odd hyp.base.v := by
    rw [hvfull]
    exact hyp.tSide_cyclotomic_quotient_odd
  have hvdvd :
      hyp.base.v ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
    rw [hvfull]
  have hvmod : hyp.base.v ≡ 1 [MOD hyp.base.p] :=
    hyp.tSide_cyclotomic_quotient_divisor_modEq_one
      hyp.base.v hvodd.pos.ne' hvdvd
  have hpdiv : hyp.base.p ∣ hyp.base.v - 1 :=
    (Nat.modEq_iff_dvd' hvodd.pos).mp hvmod.symm
  have hcount : (calT1.card : ℚ) =
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) := by
    rw [hcalcard, hsourcecard, hVcard]
    exact Nat.cast_div hpdiv (Nat.cast_ne_zero.mpr hyp.base.p_prime.ne_zero)
  -- **The gated `S`-side `βₛ` bridge content** (one documented residual `sorry`), now reduced
  -- to the gap coefficients and their η-grid orthogonality:
  --   • `hxcoe`/`hx` = the `S`-side gap coefficients `⟨Γ, ζ⟩ = x_ζ ∈ ℤ` with parity nonzeroness
  --     `x_ζ ≠ 0` (Coq `nzT1_Ga`, via `S09.cfdot_real_vchar_even`);
  --   • `heta` = every coherent image is orthogonal to the η-grid.
  -- The gap itself and the genuine (13.18.d) projected norm are the concrete, correctly stated
  -- `betaData_of_grid.Gamma` and `Y_norm_bound`; they are no longer part of this residual.
  let betaData := OddOrder.Peterfalvi.S15.betaData_of_grid hG hyp.base
    ⟨1, hyp.base.p_prime.one_lt⟩ (by simp)
  obtain ⟨x, hxcoe, hx, heta⟩ :
      ∃ (x : ClassFunction G ℂ → ℤ),
        (∀ a ∈ calT1, ClassFunction.inner betaData.Gamma a = ((x a : ℝ) : ℂ)) ∧
        (∀ a ∈ calT1, x a ≠ 0) ∧
        (∀ a ∈ calT1, ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
          ClassFunction.inner a (hyp.base.eta i k) = 0) := by
    sorry
  exact T_typeIII_ratio_le_of_sSide_gap hyp calT1 horth hcount
    betaData.Gamma x hxcoe hx heta betaData.Y_norm_bound

/-- **Complement-conjugacy transfer of commutativity `V → d.U`** (`T`-side, ungated by (14.9)).
Given that the `κ`-Hall complement `V` of `Q = T_F` in `T' = [T,T]` is abelian, *any* type-`P`
witness `d` on `T` has its own derived complement `d.U` (the `H = M_F` complement in `T'`) abelian
too.  Both `V` and `d.U` complement the *same* normal Hall subgroup `Q = d.H` in `T'` (`Q ⋊ V = T' =
Q ⋊ d.U`), so Schur–Zassenhaus conjugacy inside `↥T'` (`IsComplement'.exists_conj_of_coprime`,
coprimality from `Q` being Hall in `T`) conjugates `V` onto `d.U`, transporting `IsMulCommutative`.

Structurally the mirror of `S15.isMulCommutative_V` (which runs `d.U → V`); the sole difference is
that the `(|Q|, |V|)`-coprimality is sourced from `maxNilpotentNormalHall_isHall` +
`IsHallSubgroup.coprime_index` (with `|V| = [T':Q] ∣ [T:Q]` via the tower law) rather than from a
`TypeIIData`, so it is available for a *generic* `TypePData d`. -/
theorem isMulCommutative_typePData_U_of_V [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (d : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hVcomm : IsMulCommutative ↥hyp.base.V) :
    IsMulCommutative ↥d.U := by
  have hdisj : hyp.base.Q ⊓ hyp.base.V = ⊥ := hyp.base.Q_inf_V_eq_bot
  have hQH : hyp.base.Q = d.H := by rw [hyp.base.Q_eq_TF, d.H_eq]
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have hM'_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.base.Q ≤ hyp.base.T := by
    rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.base.T
  have hT_le_NQ : hyp.base.T ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  haveI hQn_normal : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  have hVcompl : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).IsComplement'
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.base.Q ⊓ hyp.base.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hdisj, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊔
          (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.base.T_deriv_eq_QV.symm,
          Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
        (hyp.base.V.subgroupOf (derivedInG hyp.base.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hV'compl : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).IsComplement'
      (d.U.subgroupOf (derivedInG hyp.base.T)) := by
    rw [hQH]; exact d.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)))
      ((hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).index) := by
    -- `|Q|` (Hall in `T`) is coprime to `[T:Q]`; and `[T':Q] ∣ [T:Q]` by the tower law
    -- (`Q ≤ T' ≤ T`).  `(Q.subgroupOf T').index = Q.relIndex T' ∣ Q.relIndex T`.
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.base.T
    rw [← hyp.base.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    -- `h0 : Nat.Coprime (Nat.card ↥Q) (Q.relIndex T)`
    have hcard : Nat.card ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) = Nat.card ↥hyp.base.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).index ∣
        (hyp.base.Q.subgroupOf hyp.base.T).index := by
      have htower : hyp.base.Q.relIndex (derivedInG hyp.base.T) *
          (derivedInG hyp.base.T).relIndex hyp.base.T = hyp.base.Q.relIndex hyp.base.T :=
        Subgroup.relIndex_mul_relIndex hyp.base.Q (derivedInG hyp.base.T) hyp.base.T hQ_le hM'_le_T
      show hyp.base.Q.relIndex (derivedInG hyp.base.T) ∣ hyp.base.Q.relIndex hyp.base.T
      exact ⟨(derivedInG hyp.base.T).relIndex hyp.base.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.base.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.base.T_maximal).1)
  haveI hQsolv : IsSolvable ↥hyp.base.Q := hG.solvable_of_lt_top hyp.base.Q hQ_lt_top
  have hsolv : IsSolvable ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ∨
      IsSolvable (↥(derivedInG hyp.base.T) ⧸ hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hVcompl hV'compl
  -- `hn : (V.subgroupOf T').map (conj n) = d.U.subgroupOf T'`.  Push `V` commutative forward.
  have hVsub : IsMulCommutative ↥(hyp.base.V.subgroupOf (derivedInG hyp.base.T)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hV_le).symm hVcomm
  have hmapped : IsMulCommutative
      ↥((hyp.base.V.subgroupOf (derivedInG hyp.base.T)).map (MulAut.conj n).toMonoidHom) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective) hVsub
  rw [hn] at hmapped
  exact OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe d.U_le) hmapped

/-- **Peterfalvi (11.9)/(14.9), the Type-IV exclusion residual** — the genuine deep content of the
type determination.  Coq `FTtype34_structure` (Peterfalvi (11.9), `PFsection11.v:1001`, consumed at
`PFsection14.v:735`) pins a non-type-II type-`P` maximal `T` to Type III (not IV) via the
character/Galois argument `suffices galM : typeP_Galois MtypeP` (`PFsection11.v:1139`) — the
`η`-grid projection computation `a₁₁ = a₁₀ = 0`.  In this formalisation the III/IV discriminator is
`IsMulCommutative U` (`TypeIIIData` carries `U_commutative`, `TypeIVData` its negation), so the
(11.9) content is exactly: *`T`'s derived complement `U`-factor (`= V`) is abelian*.

This is genuine §11 character theory — **not** a σ-structural config fact — and is formalised
nowhere in this repo (the §11/§13 layer `S13_MaximalIII_IV` only ever *posits* `IsTypeIII M ∨
IsTypeIV M`, and there is no universal Type-IV exclusion analogous to the proven Type-V one
`no_typeV_maximal`).  Isolated here as the *single* residual of the (14.9) type determination:
everything else (Type-V exclusion, the III/IV structural wiring incl. `normalizer_le`) is proven in
`T_isTypeIII_of_isTypeP1` below. -/
theorem T_not_isTypeIV_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    ¬ OddOrder.GroupTheory.IsTypeIV hyp.base.T := by
  -- Coq (11.9) `FTtype34_structure` ⟹ `typeP_Galois T` ⟹ (in the `IsMulCommutative U` presentation)
  -- the `U = V` factor is abelian, so `T` is Type III not IV.  The deep character/projection argument
  -- is now isolated to the single residual `hVcomm` (`V` abelian); everything else is the honest
  -- complement-conjugacy transfer `isMulCommutative_typePData_U_of_V`.
  --
  -- EXACT REDUCTION of `IsMulCommutative V` (verified against Coq `PFsection{9,11}.v`, 2026-07-06):
  --   V abelian  ⟸  `cyclic V`  ⟸  `typeP_Galois T`  (the genuine (11.9) content).
  -- Coq chain (`FTtype34_structure`, `PFsection11.v:1139-1144`):
  --   `suffices galM : typeP_Galois MtypeP` (`:1139`); then
  --   `typeP_Galois_P` (`PFsection9.v:501-511`) extracts `cyclic Ubar` (`:1140`), and
  --   `cyclic V` + `nilpotent V` ⟹ `cyclic V` ⟹ `abelian V`
  --   (`cyclic_nilpotent_quo_der1_cyclic`/`cyclic_abelian`, `:1144`).
  -- `typeP_Galois := acts_irreducibly U Hbar 'Q` (`PFsection9.v:323`): `V` acts IRREDUCIBLY on
  -- `Hbar = Q/Φ(Q)`.  Proving THAT is the `η`-grid projection `a₁₁ = a₁₀ = 0` (`PFsection11.v:1041-
  -- 1126`), whose inputs are the FULL §3–§11 apparatus: `S₁`-coherence (`cohS1`), the Dade isometry
  -- (`Dade_isometry`/`Dade_reciprocity`, §4/§5), the cyclic-TI isometry (`cycTIiso`,
  -- `coherent_ortho_cycTIiso`, §3), and prime-TI reducibles (`prTIred`) — via the norm bound
  -- `⟨X,X⟩ ≤ q` and odd-order parity.  So this is genuinely (11.9)-GATED, NOT σ-theory: the §9/§13
  -- σ-engine (`card_le_cyclotomicQuotient_of_faithful_fpf`, `TypePGaloisUBound.lean`) is the (13.2.c)
  -- `u`-bound `|V| ≤ (p^q−1)/(p−1)` which CARRIES `[CommGroup V]` as a hypothesis — it consumes
  -- commutativity, never proves it.
  --
  -- WHY NOT STRUCTURALLY FREE (contrast S-side): the S-side `U` is abelian for free via BG 15.1(b)
  -- (`typeP_hall_derived_eq_and_abelian`, `⁅U,U⁆ ≤ U ⊓ M_σ = ⊥`) BECAUSE `U` is the `(κ∪σ)'`-Hall
  -- of `S`.  For type `P₁` (`IsTypeP1 T ⟺ κ(T) = σ'(T) = π(T) ∖ σ(T)`, `S14.IsTypeP1`), the
  -- `(κ∪σ)'`-Hall is TRIVIAL (`κ ∪ σ = π`) and `V` is instead the κ-Hall complement to `Q = T_F` in
  -- `T' = Q ⋊ V`; with `T_F ⊊ M_σ` (III/IV case) one gets `V ⊓ M_σ ≠ ⊥` (exactly the σ-part that,
  -- at type IV, is where non-commutativity lives), so the `⁅V,V⁆ ≤ V ⊓ M_σ = ⊥` mechanism FAILS.
  -- Structurally `V` is only known to be a nilpotent Frobenius kernel (`Hypothesis.isNilpotent_V`,
  -- `V ⋊ W₂` Frobenius with `C_V(W₂) = ⊥`) — nilpotent ⇏ abelian.  No lane-c-doable sub-part
  -- advances this: even the final `nilpotent + cyclic V/V' ⟹ abelian` step needs `cyclic V`, which
  -- is downstream of `typeP_Galois`.  Missing bridge (Lean): a `typeP_Galois`/`cyclic V` producer,
  -- itself requiring the §5–§11 coherence/Dade layer (S05/S06/S07 Dade + coherence, still sorried).
  have hVcomm : IsMulCommutative ↥hyp.base.V := sorry  -- (11.9)-gated: V (=T's U-factor) abelian ⟸ `cyclic V` ⟸ `typeP_Galois T`
  rintro ⟨d⟩
  exact d.U_not_commutative (isMulCommutative_typePData_U_of_V hG hyp d.typeP hVcomm)

/-- **Peterfalvi (14.9), the type determination** — Coq `PFsection14`
`have [_ _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2` (line 735): a type-`P` maximal
subgroup that is *not* type II is type III.  In σ-theoretic terms, `IsTypeP1 T` (equivalently
`¬ IsTypeP2 T` given `IsTypeP T`) forces `T` to be structurally Type III.

**Fully reduced to the single (11.9) residual `T_not_isTypeIV_of_isTypeP1`.**  The type dictionary
`proposition_type_classification` (BG Prop 16.1, proven) gives, from `IsTypeP1 T`, either Type III/IV
(if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).  **Type V is excluded outright** by Peterfalvi (10.10)
`no_typeV_maximal` (proven — no maximal subgroup of a minimal simple group of odd order is Type V),
so `M_F ≠ M_σ` and `T` is Type III or IV.  Excluding Type IV — the genuine (11.9) Galois/character
content — is the isolated residual `T_not_isTypeIV_of_isTypeP1`.  The Type-V exclusion and the III/IV
structural wiring (incl. the `TypeIIIData.normalizer_le` field, bundled into the clause-(c)
disjunction) are proven here. -/
theorem T_isTypeIII_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    OddOrder.GroupTheory.IsTypeIII hyp.base.T := by
  -- Type dictionary (BG Prop 16.1): `IsTypeP1 T` ⟹ III/IV (`M_F ≠ M_σ`) or V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.base.T_maximal
  -- Type V excluded universally by Peterfalvi (10.10) `no_typeV_maximal`, so `M_F ≠ M_σ`.
  have hMF : OddOrder.BG.Ch4.S15.MF hyp.base.T ≠ OddOrder.BG.Ch3.S10.Msigma hyp.base.T := fun h =>
    OddOrder.Peterfalvi.S12.no_typeV_maximal hG ⟨hyp.base.T, hyp.base.T_maximal, hdV.mpr ⟨hP1, h⟩⟩
  -- `T` is Type III or IV; exclude IV by the (11.9) residual.
  exact (hcIII_IV.mpr ⟨hP1, hMF⟩).resolve_right (T_not_isTypeIV_of_isTypeP1 hG hyp hP1)

/-- **Peterfalvi (14.9), reduced to its canonical residual** — the `T`-side dual of the `S`-side
`(13.2.a)` carrier field `S_typeP2`.  `T` is of BG type `P₂` (`κ(T) ≠ σ'(T)`; Coq `PFsection14`
`FTtypeP_min_typeII : FTtype T == 2`).  The `IsTypeP T` conjunct is discharged honestly from `T_nonI`
(`isTypeP_of_isTypeNonI`).

The residual `κ(T) ≠ σ'(T)` is proved by the (14.9) contradiction, following Coq
`FTtypeP_min_typeII` (`apply: contraLR v1p_gt_u1q => notTtype2`): were `κ(T) = σ'(T)` (i.e.
`IsTypeP1 T`), then `T` is Type III (`T_isTypeIII_of_isTypeP1`, the `FTtype34_structure`
determination), whence the character body forces `(v − 1)/p ≤ (u − 1)/q` (`T_typeIII_ratio_le`) —
contradicting (14.8) `key_inequality`'s `(v − 1)/p > (u − 1)/q`.

The two deep pieces are isolated as `T_typeIII_ratio_le` (character body) and
`T_isTypeIII_of_isTypeP1` (type determination), both consumed below.  The `>` half is (14.8);
because the file's `T_typeII` feeds `T_side_caseB_facts` (whose case-(9.7.b) `v`-value is what
`key_inequality`'s `>` rests on), `T_isTypeP2` is strictly upstream of `key_inequality` in this
file's linearization and cannot cite it — so the `>` fact is left as this theorem's single residual,
a documented forward reference to `key_inequality` (proved later in this same file). -/
theorem T_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP2 hyp.base.T := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.base.T_maximal hyp.base.T_nonI
  refine ⟨hP, ?_⟩
  -- (14.9), by contradiction (Coq `contraLR v1p_gt_u1q => notTtype2`): assume `κ(T) = σ'(T)`.
  intro hκeq
  -- Then `T` is type `P₁`, hence (Coq `FTtype34_structure`) structurally Type III.
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := ⟨hP, hκeq⟩
  have hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T := T_isTypeIII_of_isTypeP1 hG hyp hP1
  -- The character body then gives the type-III Γ-bridge estimate `(v − 1)/p ≤ (u − 1)/q`.
  have hle : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := T_typeIII_ratio_le hG hyp hIII
  -- (14.8) `key_inequality` gives the strict `>`, contradicting `hle`.  `key_inequality` is proved
  -- below in this file but is unreachable here (its `>` rests on the case-(9.7.b) `v`-value, which
  -- flows through `T_side_caseB_facts ← T_typeII ← T_isTypeP2`), so the `>` is this theorem's
  -- single documented forward residual.
  have hgt : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
    -- (14.8) = `(key_inequality hG hyp).2`; forward-referenced.
    sorry
  exact absurd hle (not_le.mpr hgt)

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II.  Dual to the `S`-side `(13.2.a)` line
`isTypeII_of_isTypeP2 … S_maximal S_typeP2`: `T` is of type `P₂` (`T_isTypeP2`), and *every* type-`P₂`
maximal subgroup is type II by the proven BG bridge `isTypeII_of_isTypeP2`.  That bridge discharges
the deep `M'`-type-`F` structure — `IsTypeF (derivedInG T)` and `(T')_F = T_F` — internally
(`isTypeF_derivedInG_of_isTypeP2`), so the sole residual of (14.9) is the type-`P₂` fact `T_isTypeP2`.
(Placed ahead of `exists_LHypothesis` so the §14 `T`-side chain — `typeII_overNormalizer_frobenius`
etc. — can cite `IsTypeII T` locally.) -/
theorem T_typeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.T_maximal (T_isTypeP2 hG hyp)

end OddOrder.Peterfalvi.S16
