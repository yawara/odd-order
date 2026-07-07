/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.Peterfalvi.S07_Subcoherent
import OddOrder.Peterfalvi.S08_CoherenceWeighted

/-!
# Peterfalvi (9.11): coherence of `𝒮(H₀C′)` — the maximality induction

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§9, pp. 55–57 (mmd `04.11`); Coq mirror `Ptype_core_coherence`
(`PFsection9.v:1484-2227`).

## What this file provides

The §9-family instantiation of the (9.11) maximality induction, assembled on

* the maximal-coherent-subfamily skeleton
  (`S07.exists_maximal_coherent_between` / `S07.coherent_of_maximal_coherent_pair_refuted`,
  `S07_Subcoherent.lean`),
* the `Snorm`/`sumnS` squeeze lemmas (`S07_Subcoherent.lean`: `lb0_le_lb1_of_degreeRatio_le`,
  `two_mul_le_of_dvd_of_odd` (lb12), `relIndex_le_relIndex_of_le` (lb23),
  `sumnS_of_norm_one_constant_degree` (lb3S1′), `sumnS_le_of_subset` (lbS1′2),
  `two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS` (the `extend_coherent` firing bridge)),
* the weighted (5.6) adjoin engines (`S08.xAdjoinStepW` for irreducible breaks,
  `S08.xAdjoinStepW_k` for reducible `μ_j`-column breaks, `S08_CoherenceWeighted.lean`).

The (9.11) proof splits on the Clifford dichotomy (9.7):

* **case (9.7.b)**: every member of `𝒮(H₀C′)` has degree `qu` (`caseB_degree_qu`, proven), and
  the uniform-degree producer (5.7) applies — the reducible members `μ_j` (norm `q`) need the
  weighted adjoining, seeded from the irreducible uniform cut;
* **case (9.7.a)**: the maximality induction proper — `𝒮₁` = degree-`qa` members (coherent by
  (5.7)), `𝒮₂ ⊇ 𝒮₁` maximal coherent conjugation-closed, and if `𝒮₃ = 𝒮(H₀C′) − 𝒮₂ ≠ ∅` the
  squeeze (9.11.1) either fires the adjoin engine on some `χ ∈ 𝒮₃` (contradicting maximality)
  or forces the equality configuration `a = (p−1)/2`, `C = U′`, `𝒮₂ = 𝒮₁`, … refuted by
  (9.11.2)–(9.11.8).

Consumers: lane b's (13.3) `coherent_H0Cprime_S` re-grounding (`S`-instance, issue 1017 G1),
lane a's gate-2 `hY` (`coherent_Sset_diff_SHCSet`, issue 9016) and (10.7)
`typeII_derived_frobenius`.

Reference note: `issues/1017-pf-s5-uniform-degree-coherence.md` (G1),
`issues/9016-gate2-nine-eleven-difference-report.md` (hY contract).
-/

namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### (9.11.1) preamble: the source-degree bound `χ(1) ≤ u` on `𝒳(H₀C′)`

Book (9.11.1), first paragraph: *"Let `χ ∈ 𝒳(H₀C′)`.  There is thus a character `θ ∈ Irr(HC)`
such that `H₀C′ ⊂ Ker θ` and such that `χ` is an irreducible component of `Ind_{HC}^{HU} θ`.
Thus, `χ(1) ≤ |U : C|·θ(1) = u`."*  (Coq `lb01`'s inner bound, `PFsection9.v:1560-1571`.)

The constituent `θ = ψ` is any `Irr(HC)`-character `χ` lies over (`exists_liesOver`); it is
linear because `⁅HC,HC⁆ ⊆ H₀C′ ⊆ Ker χ` (`commutator_hcInHu_le_realized`, the (9.9.a) kernel
containment) makes it factor through the abelian quotient; and the constituent degree bound
`χ(1) ≤ (Ind_{HC}^{HU} ψ)(1) = [HU:HC]·ψ(1)` (`apply_one_le_induce_apply_one_of_liesOver`)
finishes with `[HU:HC] = [U:C] = u` (the (9.9.a) index steps). -/

section DegreeBound

variable [Finite G] {M : Subgroup G}

open scoped Classical ComplexOrder in
/-- **Peterfalvi (9.11.1), the source-degree bound: every `χ ∈ 𝒳(H₀C′)` has `χ(1) ≤ u`.**

The degree of a source character with `H₀C′` in its kernel is at most `u = [U:C]`: `χ` lies over
a linear character `ψ` of `HC` (linear by the (9.9.a) commutator containment
`⁅HC,HC⁆ ≤ H₀C′ ⊆ Ker χ`), so `χ(1) ≤ (Ind_{HC}^{HU} ψ)(1) = [HU:HC] = u`.  This is the *upper*
half of the (9.9.a) degree computation, valid in **both** Clifford cases (case (b) upgrades it
to equality via the inertia argument, `caseB_degree_qu`); the (9.11.1) squeeze `lb0 ≤ lb1`
consumes it for the `𝒮₃`-member `χ` (member degree `q·χ(1) ≤ q·u`). -/
theorem xiOf_H0Cprime_source_apply_one_le_u {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχ : χ ∈ xiOf data (chief.H0 ⊔ chars.Cprime)) :
    ((χ : ClassFunction ↥(huSub data) ℂ) : ↥(huSub data) → ℂ) 1 ≤ (chars.u : ℂ) := by
  classical
  haveI : Fintype ↥M := Fintype.ofFinite _
  haveI : Fintype ↥(huSub data) := Fintype.ofFinite _
  haveI : Fintype ↥(hInHu data ⊔ cInHu data chief) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥(hInHu data ⊔ cInHu data chief) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter ↥(huSub data)) :=
    Fintype.ofFinite _
  -- A constituent `ψ ∈ Irr(HC)` that `χ` lies over.
  obtain ⟨ψ, hψover⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
      (H := hInHu data ⊔ cInHu data chief) χ
  -- `ψ` is linear: `⁅HC,HC⁆ ⊆ Ker χ` (via `H₀C′ ⊆ Ker χ`), so `ψ` factors through the
  -- abelianization (the (9.9.a) obligation-3 block of `caseB_degree_qu`, verbatim).
  have hψdeg : (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ)
      (1 : ↥(hInHu data ⊔ cInHu data chief)) = 1 := by
    haveI : IsMulCommutative (↥(hInHu data ⊔ cInHu data chief) ⧸
        commutator ↥(hInHu data ⊔ cInHu data chief)) :=
      inferInstanceAs (IsMulCommutative (Abelianization ↥(hInHu data ⊔ cInHu data chief)))
    refine OddOrder.RepresentationTheory.apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥(hInHu data ⊔ cInHu data chief)) ψ ?_
    intro g hg
    refine liesOver_mem_characterKernel hψover ?_
    refine hχ.2 ?_
    have hgmem : (g : ↥(huSub data))
        ∈ ⁅hInHu data ⊔ cInHu data chief, hInHu data ⊔ cInHu data chief⁆ := by
      rw [← derivedInG_eq_commutator]
      exact Subgroup.mem_map_of_mem _ hg
    exact commutator_hcInHu_le_realized data chief hgmem
  -- Constituent degree bound: `χ(1) ≤ (Ind_{HC}^{HU} ψ)(1)`.
  have hle := OddOrder.RepresentationTheory.apply_one_le_induce_apply_one_of_liesOver
    (I := hInHu data ⊔ cInHu data chief) χ ψ hψover
  -- `(Ind_{HC}^{HU} ψ)(1) = [HU:HC]·ψ(1) = [HU:HC] = u`.
  have hind : ClassFunction.induce (hInHu data ⊔ cInHu data chief)
      (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ) (1 : ↥(huSub data))
      = (chars.u : ℂ) := by
    rw [ClassFunction.induce_apply_one, hψdeg, mul_one]
    have hidx : (hInHu data ⊔ cInHu data chief).index = chars.u :=
      (index_hcInHu_eq_relindex_cInHu data chief).trans
        (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) hidx
  rw [hind] at hle
  exact hle

open scoped ComplexOrder in
/-- **Peterfalvi (9.11.1), member form: every `φ ∈ 𝒮(H₀C′)` has `φ(1) ≤ q·u`.**

The `M`-induced form of `xiOf_H0Cprime_source_apply_one_le_u`: `φ = Ind_{HU}^M χ` has degree
`q·χ(1) ≤ q·u` (`induceHU_apply_one_eq_q_mul`).  This bounds the `𝒮₃`-member degree in the
(9.11.1) squeeze `lb0 = 2qa·χ(1) ≤ 2qa·qu ~ lb1` (after the anchor rescaling). -/
theorem sOf_H0Cprime_apply_one_le_qu {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data (chief.H0 ⊔ chars.Cprime)) :
    (φ : ↥M → ℂ) 1 ≤ ((data.q * chars.u : ℕ) : ℂ) := by
  classical
  obtain ⟨χ, hχ, rfl⟩ := hφ
  rw [induceHU_apply_one_eq_q_mul]
  have hle := xiOf_H0Cprime_source_apply_one_le_u chars hχ
  push_cast
  refine mul_le_mul_of_nonneg_left hle ?_
  exact_mod_cast Nat.zero_le data.q

end DegreeBound

/-! ### (9.11.1) preamble: the case-(a) divisibility `a ∣ χ(1)` on `𝒳(H₀)` (Coq `a_dv_XH0`)

Coq `typeP_nonGalois_characters` part (a) (`PFsection9.v:884-916`): *for `s ∈ 𝒳(H₀)`,
`a ∣ χ_s(1)`*.  The (9.11.1) squeeze consumes it for the anchor ratio: every strict-branch
adjoining `χ − (χ(1)/qa)·χ₁` needs `qa ∣ χ(1)`, i.e. `a ∣ (source degree)`.

The Coq proof: a constituent `θ` of `Res_H χ` descends to a linear `θ̄ ≠ 1` of `H̄`; `θ̄` is
nontrivial on some Clifford summand `Hpart w`; the inertia `T = I_{HU}(θ)` then satisfies
`T ∩ U ≤ C_U(Hpart w)`, so `a = [HU : H·C_U(Hpart w)] ∣ [HU : T]`; and the Clifford degree
formula `χ(1) = e·[HU:T]·θ(1)` gives `[HU:T] ∣ χ(1)`.

This subsection lands the **`S₀`-witness form** (the summand is the orbit generator `S₀`): the
inertia containment `I(θ₀) ≤ H·C_U(S₀)` (`inertia_le_hcuInHu`, the modular assembly over the
landed hard direction `inertia_inf_uInHu_le_cuInHu`) and the divisibility
(`caseA_source_degree_dvd_a_of_S0_witness`).  The general-summand case reduces to this one by a
`W₁`-conjugation transport of `χ` (the summands are the `W₁`-orbit of `S₀`,
`CliffordCaseAData.Hpart_orbit`) — the next brick. -/

section CaseADivisibility

variable [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
  {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}

/-- **The inertia of an `S₀`-nontrivial chief-factor character lies in `H·C_U(S₀)`**
(Peterfalvi (9.8.d)/(9.11.2) inertia containment, one-sided form).

The modular assembly over the landed hard direction `inertia_inf_uInHu_le_cuInHu`: decompose
`g ∈ I(θ₀)` as `g = h·u` (`H ⊔ U = ⊤` in `HU`, `H ◁ HU`); `h ∈ H ≤ I(θ₀)` always, so
`u = h⁻¹g ∈ I(θ₀) ⊓ U ≤ C_U(S₀)` by the single-factor stabilizer analysis.  This is the
containment half of the (9.8.d) inertia lift `I = H·C_U(S₀)` — sufficient for the (9.11.1)
divisibility, which only needs `[HU : H·C_U(S₀)] ∣ [HU : I(θ₀)]`. -/
theorem inertia_le_hcuInHu [Fintype ↥(hInHu data)] (caseA : CliffordCaseAData chars)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      ≤ hInHu data ⊔ cuInHu caseA := by
  set θ₀ := ClassFunction.compHom (hInHuEquivH data).toMonoidHom
    (ClassFunction.compHom (QuotientGroup.mk' chief.N)
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) with hθ₀
  intro g hg
  have hgtop : g ∈ hInHu data ⊔ uInHu data := hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
  rw [Subgroup.mem_sup_of_normal_left] at hgtop
  obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
  have hh_in : h ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
    ClassFunction.subgroup_le_inertia θ₀ hh
  have hu_in : u ∈ ClassFunction.inertia (H := hInHu data) θ₀ := by
    have hmem : h⁻¹ * (h * u) ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
      mul_mem (inv_mem hh_in) hg
    rwa [inv_mul_cancel_left] at hmem
  exact mul_mem (Subgroup.mem_sup_left hh)
    (Subgroup.mem_sup_right (inertia_inf_uInHu_le_cuInHu caseA hreg ⟨hu_in, hu⟩))

open scoped Classical in
/-- **Peterfalvi (9.11.1)/(9.8.a) case-(a) divisibility, `S₀`-witness form: `a ∣ χ(1)`.**

For `χ ∈ Irr(HU)` lying over the inflation of a linear `θ̄ : H̄ →* ℂˣ` that is **nontrivial on
the orbit generator `S₀`**, the Clifford integer `a = |U : C_U(S₀)|` divides the degree of `χ`:
the inertia `I(θ₀)` is contained in `H·C_U(S₀)` (`inertia_le_hcuInHu`), so
`a = [HU : H·C_U(S₀)]` (`index_hcuInHu_eq_caseA_a`) divides `[HU : I(θ₀)]`
(`Subgroup.index_dvd_of_le`), which divides `χ(1) = e·[HU:I(θ₀)]·θ₀(1)`
(`apply_one_eq_restrictionMultiplicity_mul_index_inertia`, `θ₀(1) = 1`).

This is Coq `a_dv_XH0` (`PFsection9.v:884-916`) with the summand pinned to `S₀`; the general
`𝒳(H₀)`-member reduces to this by `W₁`-transport (the summands are the `W₁`-orbit of `S₀`). -/
theorem caseA_source_degree_dvd_a_of_S0_witness
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (caseA : CliffordCaseAData chars)
    {χ : IrreducibleCharacter ↥(huSub data)}
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ}
    (hover : IrreducibleCharacter.LiesOver (hInHu data) χ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hS0 : ∃ x ∈ caseA.S0, θbar x ≠ 1)
    {d : ℕ} (hd : (χ : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (d : ℂ)) :
    caseA.a ∣ d := by
  classical
  haveI : Fintype ↥M := Fintype.ofFinite _
  haveI : Fintype ↥(huSub data) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (IrreducibleCharacter ↥(hInHu data)) := Fintype.ofFinite _
  -- The realized constituent `θ₀ = linear(θ̄ ∘ mk'N ∘ equiv)` and its inflated `compHom` form.
  set θ₀ : IrreducibleCharacter ↥(hInHu data) :=
    linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
      (hInHuEquivH data).toMonoidHom)) with hθ₀def
  have hform : (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            ((linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
    rw [ClassFunction.compHom_linearIrreducibleCharacter,
      ClassFunction.compHom_linearIrreducibleCharacter, MonoidHom.comp_assoc]
  -- The regularity witness in irreducible-character form.
  have hreg : ∃ x ∈ caseA.S0,
      ((linearIrreducibleCharacter θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)) :
        ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ ((linearIrreducibleCharacter θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)) :
          ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    obtain ⟨x, hx, hne⟩ := hS0
    refine ⟨x, hx, ?_⟩
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      Units.val_one]
    exact fun h => hne (Units.val_eq_one.mp h)
  -- Inertia containment `I(θ₀) ≤ H·C_U(S₀)`, hence `a ∣ [HU : I(θ₀)]`.
  have hcont : IrreducibleCharacter.inertia (G := ↥(huSub data)) (H := hInHu data) θ₀
      ≤ hInHu data ⊔ cuInHu caseA := by
    show ClassFunction.inertia (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      ≤ hInHu data ⊔ cuInHu caseA
    rw [hform]
    exact inertia_le_hcuInHu caseA hreg
  have hdvd_idx : caseA.a
      ∣ (IrreducibleCharacter.inertia (G := ↥(huSub data)) (H := hInHu data) θ₀).index := by
    rw [← index_hcuInHu_eq_caseA_a caseA]
    exact Subgroup.index_dvd_of_le hcont
  -- Clifford degree formula `χ(1) = e·[HU:I(θ₀)]·θ₀(1)` with `θ₀(1) = 1`.
  have key := OddOrder.RepresentationTheory.apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (H := hInHu data) χ θ₀ hover
  obtain ⟨e, he⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.restrictionMultiplicity_natCast
      (H := hInHu data) χ θ₀
  have hθ₀1 : (θ₀ : ClassFunction ↥(hInHu data) ℂ) (1 : ↥(hInHu data)) = 1 := by
    rw [hθ₀def, linearIrreducibleCharacter_apply, map_one, Units.val_one]
  rw [he, hθ₀1, hd, mul_one] at key
  -- `(d : ℂ) = e·[HU:I]`, so `d = e·[HU:I]` in `ℕ` and `a ∣ [HU:I] ∣ d`.
  have hdeq : d = e * (IrreducibleCharacter.inertia (G := ↥(huSub data))
      (H := hInHu data) θ₀).index := by
    exact_mod_cast key
  rw [hdeq]
  exact Dvd.dvd.mul_left hdvd_idx e

/-- **A nontrivial `H̄`-hom is nontrivial on some Clifford summand.**  The summands span
(`Hpart_iSup : ⨆ i, Hpart i = ⊤`), so a hom `θ̄` trivial on every `Hpart i` is trivial on all of
`H̄` (`Subgroup.iSup_induction`).  Selects the summand `w` of Coq `a_dv_XH0`'s
`/exists_inP[w W1w nt_t_w]` step. -/
theorem exists_summand_witness_of_ne_one (caseA : CliffordCaseAData chars)
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ} (hne : θbar ≠ 1) :
    ∃ w : Fin data.q, ∃ x ∈ caseA.Hpart w, θbar x ≠ 1 := by
  by_contra hall
  push_neg at hall
  apply hne
  refine MonoidHom.ext fun y => ?_
  rw [MonoidHom.one_apply]
  have hy : y ∈ ⨆ i, caseA.Hpart i := caseA.Hpart_iSup ▸ Subgroup.mem_top y
  refine Subgroup.iSup_induction (C := fun z => θbar z = 1) caseA.Hpart hy
    (fun i z hz => hall i z hz) (map_one θbar) ?_
  intro a b ha hb
  rw [map_mul, ha, hb, mul_one]

open scoped Classical in
/-- **Peterfalvi (9.8.a)/(9.11.1) case-(a) divisibility: `a ∣ χ(1)` on `𝒳(H₀)`** (Coq
`a_dv_XH0`, `typeP_nonGalois_characters` part (a), `PFsection9.v:884-916`).

Every `χ ∈ 𝒳` with `H₀ ⊆ Ker χ` has degree divisible by the Clifford integer
`a = |U : C_U(S₀)|`.  Extraction (`exists_hom_constituent_of_mem_xiSet_H0`) yields a nontrivial
linear seed `θ̄` with `χ` lying over its inflation; `θ̄` is nontrivial on some summand
`Hpart w = φ(rep_w)•S₀` (`exists_summand_witness_of_ne_one`); conjugating `χ` by the
`M`-realization `m` of `rep_w` twists the seed to `θ̄∘φ(rep_w)` — nontrivial on `S₀` — while
preserving irreducibility and degree, so the `S₀`-witness form
(`caseA_source_degree_dvd_a_of_S0_witness`) applies to `χ^m` and `a ∣ χ^m(1) = χ(1)`.

This is the anchor-ratio divisibility of the (9.11.1) squeeze: every strict-branch adjoining
`χ − (χ(1)/qa)·χ₁` needs `a ∣ (source degree of χ)`. -/
theorem caseA_source_degree_dvd_a (caseA : CliffordCaseAData chars)
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχX : χ ∈ xiSet data)
    (hχH0 : ((chief.H0.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ))
    {d : ℕ} (hd : (χ : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (d : ℂ)) :
    caseA.a ∣ d := by
  classical
  haveI : Fintype ↥M := Fintype.ofFinite _
  haveI : Fintype ↥(huSub data) := Fintype.ofFinite _
  haveI : Fintype ↥(hInHu data) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- Extraction: a nontrivial linear seed `θ̄` with `χ` over its inflation.
  obtain ⟨θbar, hθbarne, hover⟩ := exists_hom_constituent_of_mem_xiSet_H0 hχX hχH0
  -- `θ̄` is nontrivial on some summand `Hpart w = φ(rep_w) • S₀`.
  obtain ⟨w, y, hyHw, hyne⟩ := exists_summand_witness_of_ne_one caseA hθbarne
  -- The twisted seed `θ̄ ∘ φ(rep_w)` is nontrivial on `S₀`.
  set φw := quotientMulAutHom chief.N_aInvariant (caseA.orbitRep w) with hφw
  set θbarw : (↥data.H ⧸ chief.N) →* ℂˣ := θbar.comp φw.toMonoidHom with hθbarw
  have hS0 : ∃ x ∈ caseA.S0, θbarw x ≠ 1 := by
    refine ⟨φw⁻¹ • y, ?_, ?_⟩
    · rw [caseA.Hpart_orbit w, ← hφw] at hyHw
      exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hyHw
    · rw [hθbarw, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      show θbar (φw (φw⁻¹ • y)) ≠ 1
      simpa [MulAut.smul_def] using hyne
  -- The `M`-realization `m` of `rep_w` and the conjugated character `χ' = χ^m`.
  have hUW1M : data.typeP.U ⊔ data.typeP.W1 ≤ M := sup_le (U_le_M data) data.typeP.W1_le
  set m : ↥M := ⟨(caseA.orbitRep w : G), hUW1M (caseA.orbitRep w).2⟩ with hm
  have hmb : ((m : ↥M) : G) = ((caseA.orbitRep w : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  haveI := huSub_normal data
  set χ' : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.conjBy (G := ↥M) (H := huSub data) m (χ : ClassFunction ↥(huSub data) ℂ),
      ClassFunction.IsIrreducibleCharacter.conjBy (H := huSub data) χ.isIrreducible m⟩
    with hχ'
  -- `χ'` lies over the inflation of the twisted seed.
  have hover' : IrreducibleCharacter.LiesOver (hInHu data) χ'
      (linearIrreducibleCharacter (θbarw.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))) := by
    -- `Res χ' = compHom (hInHuConj m) (Res χ)` and the twisted target is the
    -- `compHom (hInHuConj m)`-image of the original target; inner products transport.
    have htarget : (linearIrreducibleCharacter (θbarw.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)
        = ClassFunction.compHom (hInHuConj data m)
            (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
              (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ) := by
      rw [show (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
            (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)
          = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                ((linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) by
        rw [ClassFunction.compHom_linearIrreducibleCharacter,
          ClassFunction.compHom_linearIrreducibleCharacter, MonoidHom.comp_assoc]]
      rw [compHom_hInHuConj_hInHuEquivH data (caseA.orbitRep w) m hmb,
        compHom_typeP_conjAction_inflation,
        ClassFunction.compHom_linearIrreducibleCharacter,
        ClassFunction.compHom_linearIrreducibleCharacter,
        ClassFunction.compHom_linearIrreducibleCharacter, ← hφw, ← hθbarw]
      rfl
    show OddOrder.RepresentationTheory.ClassFunction.restrictionMultiplicity _
      (χ' : ClassFunction ↥(huSub data) ℂ) _ ≠ 0
    rw [OddOrder.RepresentationTheory.ClassFunction.restrictionMultiplicity_def, htarget, hχ']
    show ClassFunction.inner (ClassFunction.restrict (hInHu data)
        (ClassFunction.conjBy (G := ↥M) (H := huSub data) m
          (χ : ClassFunction ↥(huSub data) ℂ)))
      (ClassFunction.compHom (hInHuConj data m) _) ≠ 0
    rw [hInHuConj_restrict_conjBy data m (χ : ClassFunction ↥(huSub data) ℂ),
      inner_compHom_of_bijective (hInHuConj data m) (hInHuConj_bijective data m)]
    exact hover
  -- `χ'(1) = χ(1) = d` (conjugation fixes the identity).
  have hd' : (χ' : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (d : ℂ) := by
    rw [hχ']
    show (ClassFunction.conjBy (G := ↥M) (H := huSub data) m
      (χ : ClassFunction ↥(huSub data) ℂ)) 1 = (d : ℂ)
    rw [ClassFunction.conjBy_apply, ← hd]
    exact congrArg _ (by simp)
  -- Conclude by the `S₀`-witness form applied to `χ'`.
  exact caseA_source_degree_dvd_a_of_S0_witness caseA hover' hS0 hd'

/-- **The Clifford integer `a` is odd** (Coq `odd_a`, `PFsection9.v:1536`): `a = [HU : H·C_U(S₀)]`
divides `|HU| ∣ |M| ∣ |G|`, and `|G|` is odd.  The parity input of the (9.11.1) `lb12` squeeze
step `2a ≤ p − 1` (`two_mul_le_of_dvd_of_odd`: `a ∣ p−1` odd + `p−1` even ⟹ `2a ∣ p−1`). -/
theorem caseA_a_odd (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    Odd caseA.a := by
  have hdvd : caseA.a ∣ Nat.card G := by
    rw [← index_hcuInHu_eq_caseA_a caseA]
    exact ((hInHu data ⊔ cuInHu caseA).index_dvd_card).trans
      ((Subgroup.card_subgroup_dvd_card (huSub data)).trans
        (Subgroup.card_subgroup_dvd_card M))
  rcases Nat.even_or_odd caseA.a with heven | hodd
  · exfalso
    obtain ⟨k, hk⟩ := hG.odd
    have h2 : (2 : ℕ) ∣ Nat.card G := (even_iff_two_dvd.mp heven).trans hdvd
    omega
  · exact hodd

/-- **`a·|U′| ∣ |U|`** (the (9.11) `szS1′` exactness, half 1).  `a = [U : C_U(S₀)]` (realized:
`(cuInHu.subgroupOf uInHu).index`), so `|U| = |C_U(S₀)|·a` (Lagrange), and `|U′| ∣ |C_U(S₀)|`
(`U′ ≤ C_U(S₀)`, `uprimeSub_le_cuSub`).  Makes the ℕ-division in the landed (9.8.d) count
(`caseA_character_counts` part (d): `((p−1)/a)·(|U|/(a·|U′|))`) **exact**, aligning it with the
Coq `szS1′ = (p−1)·[U:U′]/a²` of the (9.11.1) squeeze (Coq `dv_lb`, `PFsection9.v:1596`). -/
theorem caseA_a_mul_card_uprime_dvd_card_U [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    caseA.a * Nat.card ↥(uprimeSub data) ∣ Nat.card ↥data.U := by
  classical
  -- Lagrange in `uInHu`: `|C_U(S₀)-realized| · a = |uInHu| = |U|`.
  have hmul : Nat.card ↥((cuInHu caseA).subgroupOf (uInHu data)) * caseA.a
      = Nat.card ↥(uInHu data) := by
    have h := Subgroup.card_mul_index ((cuInHu caseA).subgroupOf (uInHu data))
    rwa [index_cuInHu_subgroupOf_uInHu_eq_a caseA, ← caseA.a_eq_card_restrictAut_range] at h
  -- `|U′|` equals the card of its double realization inside `uInHu`.
  have hle1 : ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) ≤ uInHu data :=
    Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (uprimeSub_le_U data))
  have hcardU' : Nat.card ↥((((uprimeSub data).subgroupOf M).subgroupOf
        (huSub data)).subgroupOf (uInHu data))
      = Nat.card ↥(uprimeSub data) := by
    have hle2 : (uprimeSub data).subgroupOf M ≤ huSub data :=
      Subgroup.subgroupOf_mono _ ((uprimeSub_le_U data).trans le_sup_right)
    have hle3 : uprimeSub data ≤ M := (uprimeSub_le_U data).trans (U_le_M data)
    calc Nat.card ↥((((uprimeSub data).subgroupOf M).subgroupOf
          (huSub data)).subgroupOf (uInHu data))
        = Nat.card ↥(((uprimeSub data).subgroupOf M).subgroupOf (huSub data)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv
      _ = Nat.card ↥((uprimeSub data).subgroupOf M) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle2).toEquiv
      _ = Nat.card ↥(uprimeSub data) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle3).toEquiv
  -- `U′-realized ≤ C_U(S₀)-realized` inside `uInHu`, so `|U′| ∣ |C_U(S₀)-realized|`.
  have hdvdC : Nat.card ↥(uprimeSub data)
      ∣ Nat.card ↥((cuInHu caseA).subgroupOf (uInHu data)) := by
    rw [← hcardU']
    exact Subgroup.card_dvd_of_le (Subgroup.subgroupOf_mono _
      (Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (uprimeSub_le_cuSub caseA))))
  -- Assemble: `a·|U′| ∣ a·|C_U(S₀)| = |uInHu| = |U|`.
  rw [← card_uInHu_eq data, ← hmul]
  obtain ⟨k, hk⟩ := hdvdC
  exact ⟨k, by rw [hk]; ring⟩

/-- **`a²·|U′| ∣ (p−1)·|U|`** (Coq `dv_lb`/`lb_d ∣ lb_n`, the (9.8.d)/(9.11.5) count-denominator
exactness): from `a ∣ p−1` (`a_dvd_p_sub_one`) and `a·|U′| ∣ |U|`
(`caseA_a_mul_card_uprime_dvd_card_U`).  This is what turns the landed count's iterated
ℕ-division `((p−1)/a)·(|U|/(a·|U′|))` into the exact `(p−1)·|U| / (a²·|U′|)` of the (9.11.1)
squeeze's `lb3 ≤ sumnS S₁′` step. -/
theorem caseA_sq_mul_card_uprime_dvd [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    caseA.a * caseA.a * Nat.card ↥(uprimeSub data)
      ∣ (chief.p - 1) * Nat.card ↥data.U := by
  have h1 : caseA.a ∣ chief.p - 1 := caseA.a_dvd_p_sub_one
  have h2 := caseA_a_mul_card_uprime_dvd_card_U caseA
  calc caseA.a * caseA.a * Nat.card ↥(uprimeSub data)
      = caseA.a * (caseA.a * Nat.card ↥(uprimeSub data)) := by ring
    _ ∣ (chief.p - 1) * Nat.card ↥data.U := mul_dvd_mul h1 h2

end CaseADivisibility

/-! ### The (9.11.1) squeeze: arithmetic core

Book (9.11.1): with `𝒮₂` maximal and `χ ∈ 𝒮₃`, *"By Theorem (5.6) and by (9.8.a, d),
`(p−1)|U:U′|q² ≤ ∑_{ψ∈𝒮₁∩𝒮(H₀U′)∩Irr M} ψ(1)²/‖ψ‖² ≤ ∑_{ψ∈𝒮₂} ψ(1)²/‖ψ‖² ≤ 2q²aχ(1) ≤ 2q²au`.
Thus `((p−1)/2)|C:U′| ≤ a`.  As `a` divides `p−1` and is odd, `a ≤ (p−1)/2`.  It follows that
`C = U′` and `a = (p−1)/2`.  Furthermore, the inequalities above are equalities."*

This subsection isolates the **closed-circle arithmetic**: six real quantities linked by the
squeeze inequalities whose composition returns to the start, forcing every step to be an
equality; the cancellations then extract the (9.11.1) conclusions.  The quantities are abstract
naturals here (`p−1`, `q`, `a`, `u`, `[U:U′]`, the `𝒮₃`-member source degree, `|𝒮₁′|`) plus the
real `sumnS 𝒮₂`; the §9 identifications and the (5.6)-contrapositive input
`sumnS 𝒮₂ ≤ 2q²a·χdeg` (the pair-refuted clause through the weighted adjoin engine) are supplied
by the caller. -/

section SqueezeArithmetic

/-- **Peterfalvi (9.11.1), the closed squeeze circle** (arithmetic core).

Inputs: the divisibility/parity facts making `2a ≤ p−1` (`two_mul_le_of_dvd_of_odd`), the degree
bound `χdeg ≤ u` (9.11.1 preamble), the index bound `u ≤ [U:U′]` (Lagrange), the (9.8.d) count
`(p−1)·[U:U′] ≤ n₁·a²` (exact form), the `sumnS` lower bound `n₁·(qa)² ≤ s₂` ((9.11.5)-(9.11.6):
uniform `Snorm` on `𝒮₁′` + subset monotonicity), and the pair-refuted upper bound
`s₂ ≤ 2q²a·χdeg` (the (5.6) contrapositive).  The chain
`(p−1)[U:U′]q² ≤ n₁(qa)² ≤ s₂ ≤ 2q²a·χdeg ≤ 2q²au ≤ (p−1)q²u ≤ (p−1)q²[U:U′]`
closes into a circle, so every inequality is an equality; cancellation extracts the (9.11.1)
conclusions `χdeg = u`, `2a = p−1`, `u = [U:U′]`, `n₁·a² = (p−1)·[U:U′]`, `s₂ = n₁(qa)²`. -/
theorem nineElevenOne_squeeze_arithmetic
    {p1 q a u iUU' χdeg n₁ : ℕ} {s₂ : ℝ}
    (hq : 0 < q) (ha : 0 < a) (hu : 0 < u) (hp1 : 0 < p1)
    (hadvd : a ∣ p1) (haodd : Odd a) (hpeven : Even p1)
    (hχu : χdeg ≤ u)
    (hule : u ≤ iUU')
    (hcount : p1 * iUU' ≤ n₁ * (a * a))
    (hs1' : (n₁ : ℝ) * ((q * a : ℕ) : ℝ) ^ 2 ≤ s₂)
    (hpair : s₂ ≤ 2 * (q : ℝ) ^ 2 * a * χdeg) :
    χdeg = u ∧ 2 * a = p1 ∧ u = iUU' ∧ n₁ * (a * a) = p1 * iUU' ∧
      s₂ = (n₁ : ℝ) * ((q * a : ℕ) : ℝ) ^ 2 := by
  -- `2a ≤ p−1` (Gauss: `a` odd divides the even `p1`).
  have h2a : 2 * a ≤ p1 :=
    OddOrder.Peterfalvi.S07.two_mul_le_of_dvd_of_odd hadvd haodd hpeven hp1
  -- The six nodes of the circle, as reals.
  set r₀ : ℝ := (p1 : ℝ) * iUU' * q ^ 2 with hr₀
  set r₁ : ℝ := (n₁ : ℝ) * ((q * a : ℕ) : ℝ) ^ 2 with hr₁
  set r₂ : ℝ := 2 * (q : ℝ) ^ 2 * a * χdeg with hr₂
  set r₃ : ℝ := 2 * (q : ℝ) ^ 2 * a * u with hr₃
  set r₄ : ℝ := (p1 : ℝ) * q ^ 2 * u with hr₄
  -- The circle: `r₀ ≤ r₁ ≤ s₂ ≤ r₂ ≤ r₃ ≤ r₄ ≤ r₀`.
  have h01 : r₀ ≤ r₁ := by
    have hc : ((p1 : ℝ) * iUU') ≤ (n₁ : ℝ) * (a * a) := by exact_mod_cast hcount
    calc r₀ = ((p1 : ℝ) * iUU') * (q : ℝ) ^ 2 := by rw [hr₀]; try ring
      _ ≤ ((n₁ : ℝ) * (a * a)) * (q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = r₁ := by rw [hr₁]; push_cast; try ring
  have h23 : r₂ ≤ r₃ := by
    have hχu' : (χdeg : ℝ) ≤ (u : ℝ) := by exact_mod_cast hχu
    rw [hr₂, hr₃]
    exact mul_le_mul_of_nonneg_left hχu' (by positivity)
  have h34 : r₃ ≤ r₄ := by
    have h2a' : ((2 * a : ℕ) : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast h2a
    calc r₃ = ((2 * a : ℕ) : ℝ) * ((q : ℝ) ^ 2 * u) := by rw [hr₃]; push_cast; try ring
      _ ≤ (p1 : ℝ) * ((q : ℝ) ^ 2 * u) :=
          mul_le_mul_of_nonneg_right h2a' (by positivity)
      _ = r₄ := by rw [hr₄]; try ring
  have h40 : r₄ ≤ r₀ := by
    have hule' : (u : ℝ) ≤ (iUU' : ℝ) := by exact_mod_cast hule
    calc r₄ = ((p1 : ℝ) * (q : ℝ) ^ 2) * u := by rw [hr₄]; try ring
      _ ≤ ((p1 : ℝ) * (q : ℝ) ^ 2) * iUU' :=
          mul_le_mul_of_nonneg_left hule' (by positivity)
      _ = r₀ := by rw [hr₀]; try ring
  -- Close the circle: each adjacent pair is an equality.
  have e1s : r₁ = s₂ := le_antisymm hs1'
    (hpair.trans (h23.trans (h34.trans (h40.trans h01))))
  have es2 : s₂ = r₂ := le_antisymm hpair
    (h23.trans (h34.trans (h40.trans (h01.trans hs1'))))
  have e23 : r₂ = r₃ := le_antisymm h23
    (h34.trans (h40.trans (h01.trans (hs1'.trans hpair))))
  have e34 : r₃ = r₄ := le_antisymm h34
    (h40.trans (h01.trans (hs1'.trans (hpair.trans h23))))
  have e40 : r₄ = r₀ := le_antisymm h40
    (h01.trans (hs1'.trans (hpair.trans (h23.trans h34))))
  have e01 : r₀ = r₁ := le_antisymm h01
    (hs1'.trans (hpair.trans (h23.trans (h34.trans h40))))
  -- Cancellation constants.
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hp1R : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast hp1
  -- (E1) `χdeg = u` from `r₂ = r₃`.
  have hE1 : χdeg = u := by
    have h : (χdeg : ℝ) = (u : ℝ) := by
      have h2q2a : (0 : ℝ) < 2 * (q : ℝ) ^ 2 * a := by positivity
      have := e23
      rw [hr₂, hr₃] at this
      exact mul_left_cancel₀ h2q2a.ne' this
    exact_mod_cast h
  -- (E2) `2a = p1` from `r₃ = r₄`.
  have hE2 : 2 * a = p1 := by
    have h : (2 * a : ℝ) = (p1 : ℝ) := by
      have hq2u : (0 : ℝ) < (q : ℝ) ^ 2 * u := by positivity
      have := e34
      rw [hr₃, hr₄] at this
      -- `2q²au = p1·q²u` ⟹ `2a = p1` (cancel `q²u`).
      have h' : (2 * (a : ℝ)) * ((q : ℝ) ^ 2 * u) = (p1 : ℝ) * ((q : ℝ) ^ 2 * u) := by
        linear_combination this
      exact mul_right_cancel₀ hq2u.ne' h'
    exact_mod_cast h
  -- (E3) `u = iUU'` from `r₄ = r₀`.
  have hE3 : u = iUU' := by
    have h : (u : ℝ) = (iUU' : ℝ) := by
      have hpq : (0 : ℝ) < (p1 : ℝ) * (q : ℝ) ^ 2 := by positivity
      have := e40
      rw [hr₄, hr₀] at this
      have h' : ((p1 : ℝ) * (q : ℝ) ^ 2) * (u : ℝ)
          = ((p1 : ℝ) * (q : ℝ) ^ 2) * (iUU' : ℝ) := by linear_combination this
      exact mul_left_cancel₀ hpq.ne' h'
    exact_mod_cast h
  -- (E4) `n₁·a² = p1·iUU'` from `r₀ = r₁`.
  have hE4 : n₁ * (a * a) = p1 * iUU' := by
    have h : ((n₁ * (a * a) : ℕ) : ℝ) = ((p1 * iUU' : ℕ) : ℝ) := by
      have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
      have := e01
      rw [hr₀, hr₁] at this
      have h' : ((p1 : ℝ) * iUU') * (q : ℝ) ^ 2 = ((n₁ : ℝ) * (a * a)) * (q : ℝ) ^ 2 := by
        push_cast at this ⊢
        linear_combination this
      have := mul_right_cancel₀ hq2.ne' h'
      push_cast
      linear_combination this.symm
    exact_mod_cast h
  exact ⟨hE1, hE2, hE3, hE4, e1s.symm⟩

end SqueezeArithmetic

end OddOrder.Peterfalvi.S11
