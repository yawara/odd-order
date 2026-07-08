/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S11_MaximalII_III_IV
import OddOrder.Peterfalvi.S07_Subcoherent
import OddOrder.Peterfalvi.S08_CoherenceWeighted
import OddOrder.GroupTheory.RepresentationTheory.NonInflatedDegreeSqInterval

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

/-! ### The (9.11.1) squeeze: §9 identification of the circle nodes

The arithmetic core below abstracts the squeeze quantities as bare naturals; this subsection
supplies the §9 identifications tying them to the group world (Coq `PFsection9.v:1560-1607`):
the ambient relative-index realizations `[U:C_U(S₀)] = a` / `[U:C] = u` (Lagrange transports of
the `uInHu`-realized indices), the factorization `[U:U'] = a·[C_U(S₀):U']` behind Coq's
`szS1' = (p−1)·[U:U']/a²`, the `lb23` bound `u ≤ [U:U']`, and the **exact** (9.8.d) count
`(p−1)·[U:U'] ≤ n₁·a²` (the landed `caseA_character_counts` (d) with its iterated ℕ-division
resolved by the `dv_lb` divisibilities above). -/

section SqueezeIdentifications

variable [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
  {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}

/-- **`[U : C_U(S₀)] = a`** (ambient-`G` relative-index form of
`index_cuInHu_subgroupOf_uInHu_eq_a`): Lagrange `[U:C_U(S₀)]·|C_U(S₀)| = |U| = a·|C_U(S₀)|`
(`card_U_eq_a_mul_card_cuSub`), cancelling `|C_U(S₀)| > 0`. -/
theorem relIndex_cuSub_U_eq_a (caseA : CliffordCaseAData chars) :
    (cuSub caseA).relIndex data.U = caseA.a := by
  have h1 : (cuSub caseA).relIndex data.U * Nat.card ↥(cuSub caseA) = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cuSub caseA).subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cuSub_le_U caseA)).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
    (h1.trans (card_U_eq_a_mul_card_cuSub caseA))

/-- **`[U:U'] = a·[C_U(S₀):U']`** (the Coq `szS1'` denominator factorization): relative-index
multiplicativity along `U' ≤ C_U(S₀) ≤ U` with `[U:C_U(S₀)] = a`. -/
theorem relIndex_uprimeSub_U_eq (caseA : CliffordCaseAData chars) :
    (uprimeSub data).relIndex data.U
      = caseA.a * (uprimeSub data).relIndex (cuSub caseA) := by
  rw [← Subgroup.relIndex_mul_relIndex (uprimeSub data) (cuSub caseA) data.U
      (uprimeSub_le_cuSub caseA) (cuSub_le_U caseA),
    relIndex_cuSub_U_eq_a caseA, mul_comm]

/-- **`[U : C] = u`** (ambient-`G` relative-index form of `index_cInHu_subgroupOf_uInHu_eq_u`):
both sides multiply by `|C|` to `|U|` (Lagrange in `U` and in the `uInHu` realization). -/
theorem relIndex_cSub_U_eq_u (chars : Section11CharacterData data chief) :
    (cSub data chief).relIndex data.U = chars.u := by
  have h1 : (cSub data chief).relIndex data.U * Nat.card ↥(cSub data chief)
      = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cSub data chief).subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cSub_le_U data chief)).toEquiv] at h
  have h2 : chars.u * Nat.card ↥(cSub data chief) = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cInHu data chief).subgroupOf (uInHu data))
    rwa [index_cInHu_subgroupOf_uInHu_eq_u data chief chars,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cInHu_le_uInHu data chief)).toEquiv,
      card_cInHu_eq data chief, card_uInHu_eq data] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

/-- **The `lb23` bound `u ≤ [U:U']`** — `u = [U:C]` and Lagrange monotonicity `[U:C] ≤ [U:U']`
along `U' ≤ C ≤ U` (`relIndex_le_relIndex_of_le`).  The `hule` input of the (9.11.1) squeeze. -/
theorem u_le_relIndex_uprimeSub_U (chars : Section11CharacterData data chief) :
    chars.u ≤ (uprimeSub data).relIndex data.U := by
  rw [← relIndex_cSub_U_eq_u chars]
  exact OddOrder.Peterfalvi.S07.relIndex_le_relIndex_of_le
    (uprimeSub_le_cSub data chief) (cSub_le_U data chief)

/-- **The exact (9.8.d) count `(p−1)·[U:U'] ≤ n₁·a²`** (Coq `lb_Sqa` with the `dv_lb`
exactness), `n₁` the number of degree-`qa` irreducibles in `𝒮(H₀U')`.  The landed count
(`caseA_character_counts` (d)) bounds `n₁` below by the iterated ℕ-division
`((p−1)/a)·(|U|/(a·|U'|))`; the divisibilities `a ∣ p−1` and `a·|U'| ∣ |U|` make both divisions
exact, and multiplying through by `a²` gives the multiplicative form consumed by the (9.11.1)
squeeze (`nineElevenOne_squeeze_arithmetic`'s `hcount`). -/
theorem caseA_character_count_exact (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (caseA : CliffordCaseAData chars) :
    (chief.p - 1) * ((uprimeSub data).relIndex data.U)
      ≤ {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a) := by
  have hcount := (caseA_character_counts hG chars caseA).2.2.2
  rw [show chars.Uprime = uprimeSub data from rfl,
    Section11CharacterData.SOf_eq,
    card_U_div_a_mul_card_Uprime_eq_relIndex caseA] at hcount
  rw [relIndex_uprimeSub_U_eq caseA, ← Nat.mul_div_cancel' caseA.a_dvd_p_sub_one]
  calc caseA.a * ((chief.p - 1) / caseA.a)
        * (caseA.a * (uprimeSub data).relIndex (cuSub caseA))
      = (chief.p - 1) / caseA.a * ((uprimeSub data).relIndex (cuSub caseA))
          * (caseA.a * caseA.a) := by ring
    _ ≤ {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a) := Nat.mul_le_mul_right _ hcount

end SqueezeIdentifications

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

/-! ### The (9.11.1) squeeze: the group-world equality configuration

Book (9.11.1) reads its numeric squeeze conclusions back into the group world: *"It follows that
`C = U′` and `a = (p−1)/2`. … `𝒮₂ = 𝒮₁ ⊂ 𝒮(H₀C) ∩ Irr(M)`, `|𝒮₁| = (p−1)u/a² = 2u/a` and
`χ(1) = u`."*  This subsection performs the translation of `nineElevenOne_squeeze_arithmetic`'s
numeric equalities `u = [U:U']`, `2a = p−1`, `χdeg = u` into the group facts `C = U'`, `a = (p−1)/2`
and the `𝒮₃`-member source degree `= u`.

The load-bearing translation is `[U:C] = [U:U'] ⟹ C = U'`: with `U' ≤ C ≤ U`, the relative index is
*strictly* monotone off equality (`relIndex_lt_relIndex_of_le_of_ne`, landed), so equal indices
force `C = U'`.  The remaining inputs `hs1'`/`hpair` are the world-specific member bundle: `hs1'` is
the uniform sub-family value `|𝒮₁'|·(qa)² ≤ sumnS 𝒮₂` ((9.11.5)-(9.11.6)) and `hpair` is the (5.6)
contrapositive `sumnS 𝒮₂ ≤ 2q²a·χ(1)` (the pair-refuted clause through the weighted adjoin engine
`coherentDegreeSqNormBound_of_not_coherentW`); both are supplied by the refuter assembly. -/

section Configuration

variable [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
  {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}

/-- **`Even (p − 1)`** for the chief-factor prime `p` of a minimal simple group of odd order.  `p`
divides `|H̄| = p^q ∣ |H| ∣ |G|` (odd), so `p` is odd (`≠ 2`) and `p − 1` is even.  The `lb12`
parity input `2a ∣ (p−1)`. -/
theorem chiefFactor_p_sub_one_even (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Even (chief.p - 1) := by
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  have hpq : chief.p ^ data.q ∣ Nat.card ↥data.H :=
    ⟨Nat.card ↥chief.H0, chief.quotient_order⟩
  have hp_dvd : chief.p ∣ Nat.card G :=
    (dvd_pow_self chief.p hq.ne').trans (hpq.trans (Subgroup.card_subgroup_dvd_card data.H))
  have hp_ne2 : chief.p ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.mpr hG.odd) (even_iff_two_dvd.mpr (h ▸ hp_dvd))
  obtain ⟨k, hk⟩ := chief.p_prime.odd_of_ne_two hp_ne2
  exact ⟨k, by omega⟩

/-- **Peterfalvi (9.11.1), the group-world equality configuration.**

The translation of `nineElevenOne_squeeze_arithmetic`'s numeric equalities into the group facts of
(9.11.1): given the squeeze inputs — the landed §9 identifications (`hχu`,
`u_le_relIndex_uprimeSub_U`, `caseA_character_count_exact`) plus the world bundle (`hs1'` uniform
sub-family value, `hpair` (5.6) contrapositive) — the squeeze circle closes to force

* `2·a = p − 1` (hence `a = (p−1)/2`);
* `C = U'` (from `[U:C] = [U:U']`, strict-index monotonicity off equality);
* the `𝒮₃`-member source degree `χdeg = u`;
* the count equality `n₁·a² = (p−1)·[U:U']` (`|𝒮₁| = (p−1)u/a²`).

Here `χdeg` is the abstract source degree of the chosen `𝒮₃`-member (`χ(1) ≤ u`) and `n₁` the number
of degree-`qa` irreducibles in `𝒮(H₀U')` (the landed count `caseA_character_counts` (d)); `s₂` is
the real `sumnS 𝒮₂`.  This is what the (9.11.2)–(9.11.8) refutation consumes. -/
theorem nineElevenOne_configuration (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (caseA : CliffordCaseAData chars) {χdeg : ℕ} {s₂ : ℝ}
    (hq : 0 < data.q) (hu : 0 < chars.u)
    (hp1 : 0 < chief.p - 1) (hχu : χdeg ≤ chars.u)
    (hs1' : ({χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard : ℝ)
        * ((data.q * caseA.a : ℕ) : ℝ) ^ 2 ≤ s₂)
    (hpair : s₂ ≤ 2 * (data.q : ℝ) ^ 2 * caseA.a * χdeg) :
    2 * caseA.a = chief.p - 1 ∧ chars.C = chars.Uprime ∧ χdeg = chars.u ∧
      {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a) = (chief.p - 1) * ((uprimeSub data).relIndex data.U) := by
  obtain ⟨hE1, hE2, _hE3, hE4, _⟩ :=
    nineElevenOne_squeeze_arithmetic (p1 := chief.p - 1) (q := data.q) (a := caseA.a)
      (u := chars.u) (iUU' := (uprimeSub data).relIndex data.U) (χdeg := χdeg)
      (n₁ := {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard)
      (s₂ := s₂) hq caseA.a_pos hu hp1 caseA.a_dvd_p_sub_one (caseA_a_odd hG caseA)
      (chiefFactor_p_sub_one_even hG) hχu (u_le_relIndex_uprimeSub_U chars)
      (caseA_character_count_exact hG caseA) hs1' hpair
  -- `hE3 : u = [U:U']` translates to `C = U'` via strict index monotonicity off equality.
  refine ⟨hE2, ?_, hE1, hE4⟩
  -- `[U:C] = u = [U:U']`, and `U' ≤ C ≤ U`, so `C = U'`.
  have hCU' : (cSub data chief).relIndex data.U = (uprimeSub data).relIndex data.U := by
    rw [relIndex_cSub_U_eq_u chars]; exact _hE3
  by_contra hne
  have hne' : cSub data chief ≠ uprimeSub data := fun h => hne (by
    show chars.C = chars.Uprime
    simp only [Section11CharacterData.C, Section11CharacterData.Uprime]; exact h)
  exact absurd hCU' (ne_of_lt (OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
    (uprimeSub_le_cSub data chief) (cSub_le_U data chief) hne'))

end Configuration

/-- **`[U : K₁ ⊓ K₂] ≤ [U:K₁]·[U:K₂]`** (relative-index form of `Subgroup.index_inf_le`): the
relative index `H.relIndex U = (H.subgroupOf U).index`, and `subgroupOf = comap` distributes over
`⊓` (`Subgroup.comap_inf`), so the ambient `index_inf_le` in `↥U` applies.  The (9.11.2) injectivity
`Ū ↪ (U/U₁)×(U/U₁ʷ)` in relative-index form. -/
theorem relIndex_inf_le {G : Type*} [Group G] {K₁ K₂ U : Subgroup G} :
    (K₁ ⊓ K₂).relIndex U ≤ K₁.relIndex U * K₂.relIndex U := by
  simp only [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_inf]
  exact Subgroup.index_inf_le

/-- **Peterfalvi (9.11.2), the bound `u ≤ a²`.**  Book (9.11.2): *"The canonical mapping from `Ū` to
`(U/U₁)×(U/U₁ʷ)` is injective, and so `u ≤ a²`."*  Given the inertia identity `C = U₁ ⊓ U₁ʷ` (the
*first* assertion of (9.11.2), the deep character-theoretic input: `U₁ = C_U(H₁)`, `U₁ʷ = C_U(H₂)`,
their intersection is `C = C_U(H̄)`) and the per-summand index `[U:U₁] = [U:U₁ʷ] = a`, the relative
index `u = [U:C]` is bounded by `[U:U₁]·[U:U₁ʷ] = a²` (`relIndex_inf_le`).  Consumed by the (9.11.5)
polynomial bound (`nineElevenFive_refutation`'s `hua2`). -/
theorem nineElevenTwo_u_le_a_sq [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁.relIndex data.U = caseA.a) (hK₂ : K₂.relIndex data.U = caseA.a)
    (hCinf : chars.C = K₁ ⊓ K₂) : chars.u ≤ caseA.a * caseA.a := by
  have hu : (K₁ ⊓ K₂).relIndex data.U = chars.u := by
    rw [← hCinf]; exact relIndex_cSub_U_eq_u chars
  rw [← hu]
  calc (K₁ ⊓ K₂).relIndex data.U ≤ K₁.relIndex data.U * K₂.relIndex data.U := relIndex_inf_le
    _ = caseA.a * caseA.a := by rw [hK₁, hK₂]

/-! ### (9.11.5) preamble: the uniform sub-family `sumnS` value

Book (9.11.5) / Coq `lb3S1'` left endpoint: on `𝒮₁'` (the degree-`qa` irreducibles) every member is
norm-one of degree `qa`, so `Snorm ≡ (qa)²` and `sumnS 𝒮₁' = |𝒮₁'|·(qa)²`.  This is the `hs1'`
supplier of `nineElevenOne_configuration` combined with `sumnS_le_of_subset` (`𝒮₁' ⊆ 𝒮₂`). -/

section UniformSubfamily

variable [Finite G] {M : Subgroup G}

/-- **The uniform sub-family `sumnS` value.**  For a finite family `Si` of irreducible characters of
common degree `d`, `sumnS Si = |Si|·d²`: each member is norm-one (`inner_self_eq_one`, so `Snorm =
degree²`) of degree `d`.  The (9.11.5) left endpoint (`sumnS_of_norm_one_constant_degree` fed the
two pointwise facts from irreducibility + the degree). -/
theorem sumnS_irreducible_constant_degree [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)]
    (Si : Finset (ClassFunction ↥M ℂ)) {d : ℕ}
    (hirr : ∀ ψ ∈ Si, IsIrreducibleCharacter ψ) (hdeg : ∀ ψ ∈ Si, ψ 1 = (d : ℂ)) :
    OddOrder.Peterfalvi.S07.sumnS Si = (Si.card : ℝ) * (d : ℝ) ^ 2 := by
  refine OddOrder.Peterfalvi.S07.sumnS_of_norm_one_constant_degree
    (fun ψ hψ => ?_) (fun ψ hψ => ?_)
  · have h : ClassFunction.inner ψ ψ = 1 := by
      simpa using OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
        (⟨ψ, hirr ψ hψ⟩ : IrreducibleCharacter ↥M) ⟨ψ, hirr ψ hψ⟩
    rw [h, Complex.one_re]
  · rw [hdeg ψ hψ, Complex.natCast_re]

end UniformSubfamily

/-! ### (9.11.5): the exponential-beats-polynomial arithmetic contradiction

Book (9.11.5), final step: assuming `|𝒮₄| ≤ ‖α‖²`, the (9.11.3)/(9.11.4) norm identities and
(9.11.2) give `p^q − 1 ≤ (q+2)a³ + q²a² + 2qa`; with `p = 2a+1` this forces `2^q ≤ q+2`,
contradicting the induction `2^x > x+2` for `x ≥ 3`.  This subsection isolates the pure
`ℕ`-arithmetic core: the binomial lower bound `(2a+1)^q ≥ 2^q a^q + 2q(q−1)a² + 2qa + 1`
(extracting the `k ∈ {0,1,2,q}` terms) composed with the polynomial upper bound is impossible for
`q ≥ 3`, `a ≥ 1`. -/

section FiveArithmetic

/-- **`q + 2 < 2^q` for `q ≥ 3`** (the (9.11.5) endgame `2^x > x+2`, `x ≥ 3`), by induction:
base `3 + 2 = 5 < 8`, step `2·2^q ≥ 2(q+3) ≥ (q+1)+3`. -/
theorem add_two_lt_two_pow {q : ℕ} (hq : 3 ≤ q) : q + 2 < 2 ^ q := by
  induction q with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp_all <;> omega
    · have := ih hn
      rw [pow_succ]
      omega

/-- **`2·(q.choose 2) = q·(q−1)`** (the `k = 2` binomial coefficient in exact form): `q.choose 2 =
q(q−1)/2` and `q(q−1)` is even (consecutive product). -/
theorem two_mul_choose_two (q : ℕ) : 2 * q.choose 2 = q * (q - 1) := by
  rw [Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · simp [hq]
  · have heven : 2 ∣ q * (q - 1) := by
      rcases Nat.even_or_odd q with h | h
      · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
      · exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd h odd_one)) _
    exact Nat.mul_div_cancel' heven

/-- **The (9.11.5) binomial lower bound** `2^q·a^q + 2q(q−1)·a² + 2q·a + 1 ≤ (2a+1)^q` (`q ≥ 3`):
the sum of the `k ∈ {0,1,2,q}` terms of `(2a+1)^q = ∑ (2a)^k·C(q,k)`, all others being
nonnegative. -/
theorem binomial_lower_bound {q a : ℕ} (hq : 3 ≤ q) :
    2 ^ q * a ^ q + 2 * q * (q - 1) * a ^ 2 + 2 * q * a + 1 ≤ (2 * a + 1) ^ q := by
  have hexp : (2 * a + 1) ^ q = ∑ k ∈ Finset.range (q + 1), (2 * a) ^ k * q.choose k := by
    rw [add_pow]
    exact Finset.sum_congr rfl fun k _ => by rw [one_pow, mul_one, Nat.cast_id]
  rw [hexp]
  have hsub : ({0, 1, 2, q} : Finset ℕ) ⊆ Finset.range (q + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
  -- The subset sum over `{0,1,2,q}` equals the four extracted terms.
  have h01 : (0 : ℕ) ∉ ({1, 2, q} : Finset ℕ) := by simp; omega
  have h12 : (1 : ℕ) ∉ ({2, q} : Finset ℕ) := by simp; omega
  have h2q : (2 : ℕ) ∉ ({q} : Finset ℕ) := by simp; omega
  rw [show ({0, 1, 2, q} : Finset ℕ) = insert 0 (insert 1 (insert 2 {q})) from rfl,
    Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_insert h2q, Finset.sum_singleton]
  -- Evaluate each term.
  have e0 : (2 * a) ^ 0 * q.choose 0 = 1 := by simp
  have e1 : (2 * a) ^ 1 * q.choose 1 = 2 * q * a := by
    rw [pow_one, Nat.choose_one_right]; ring
  have e2 : (2 * a) ^ 2 * q.choose 2 = 2 * q * (q - 1) * a ^ 2 := by
    rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from rfl, mul_comm ((4 : ℕ) * a ^ 2) (q.choose 2),
      ← mul_assoc, show (q.choose 2) * 4 = 2 * (2 * q.choose 2) by ring, two_mul_choose_two]
    ring
  have eq : (2 * a) ^ q * q.choose q = 2 ^ q * a ^ q := by
    rw [Nat.choose_self, mul_one, mul_pow]
  rw [e0, e1, e2, eq]; omega

/-- **Peterfalvi (9.11.5), the arithmetic contradiction.**  For `q ≥ 3` and `a ≥ 1`, the polynomial
bound `(2a+1)^q − 1 ≤ (q+2)a³ + q²a² + 2qa` (from `|𝒮₄| ≤ ‖α‖²` via (9.11.2)-(9.11.4), with
`p = 2a+1`) is impossible: the binomial lower bound forces `2^q·a^q ≤ (q+2)·a³` (the `a²` terms
cancel since `2q(q−1) ≥ q²` for `q ≥ 2`), hence `2^q ≤ q+2` (as `a^q ≥ a³`), contradicting
`add_two_lt_two_pow`. -/
theorem nineElevenFive_arithmetic_contradiction {q a : ℕ} (hq : 3 ≤ q) (ha : 1 ≤ a)
    (hbound : (2 * a + 1) ^ q - 1 ≤ (q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a) : False := by
  have hlb := binomial_lower_bound (a := a) hq
  -- `2^q a^q + 2q(q−1)a² + 2qa ≤ (2a+1)^q − 1 ≤ (q+2)a³ + q²a² + 2qa`, cancel `2qa`.
  have hchain : 2 ^ q * a ^ q + 2 * q * (q - 1) * a ^ 2
      ≤ (q + 2) * a ^ 3 + q ^ 2 * a ^ 2 := by
    have h1 : 2 ^ q * a ^ q + 2 * q * (q - 1) * a ^ 2 + 2 * q * a
        ≤ (2 * a + 1) ^ q - 1 := by omega
    omega
  -- `q²a² ≤ 2q(q−1)a²` (since `2q(q−1) ≥ q²` for `q ≥ 2`), so `2^q a^q ≤ (q+2)a³`.
  have hq2 : q ^ 2 ≤ 2 * q * (q - 1) := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ q)]
  have hqaq : 2 ^ q * a ^ q ≤ (q + 2) * a ^ 3 := by nlinarith [Nat.mul_le_mul_right (a ^ 2) hq2]
  -- `a^q ≥ a^3` (as `q ≥ 3`, `a ≥ 1`), so `2^q a³ ≤ (q+2)a³`, giving `2^q ≤ q+2`.
  have haq : a ^ 3 ≤ a ^ q := Nat.pow_le_pow_right ha hq
  have hfinal : 2 ^ q ≤ q + 2 := by
    have ha3 : 0 < a ^ 3 := pow_pos (by omega : (0 : ℕ) < a) 3
    have : 2 ^ q * a ^ 3 ≤ (q + 2) * a ^ 3 :=
      le_trans (Nat.mul_le_mul_left (2 ^ q) haq) hqaq
    exact Nat.le_of_mul_le_mul_right this ha3
  exact absurd hfinal (Nat.not_le.mpr (add_two_lt_two_pow hq))

/-- **Peterfalvi (9.11.3), the `|𝒮₄|` count** (arithmetic core, denominator-cleared).

Book (9.11.3): the sum-of-squares class equation on the quotient `HŪ/(H₀C)` — `n` characters of
degree `u` and `q(p−1)u/a²` of degree `a`, plus the `u` linear characters of `Ū` — gives
`p^q·u = u + n·u² + q(p−1)·u` (`hclass`).  Cancelling one `u` yields `n·u + q(p−1) + 1 = p^q`; with
the conjugate/reducible split `n = q·|𝒮₄| + (p−1)` (`hn`: `(9.8.b)` gives `p−1` of the `n` inducing
reducibly, the rest falling into `W₁`-orbits of size `q`), this rearranges to the cleared count
`|𝒮₄|·qu + (p−1)u + (p−1)q + 1 = p^q` — the `hcount` input of `nineElevenFive_refutation` (with
`p = 2a+1`).  The two group inputs `hclass` (character sum-of-squares) and `hn` (W₁-orbit count) are
the deep (9.11.3) content, supplied separately. -/
theorem nineElevenThree_count {p q u n S4 : ℕ} (hu : 1 ≤ u)
    (hclass : u + n * u ^ 2 + q * (p - 1) * u = p ^ q * u)
    (hn : n = S4 * q + (p - 1)) :
    S4 * (q * u) + (p - 1) * u + (p - 1) * q + 1 = p ^ q := by
  -- Cancel one `u` from the class equation: `n·u + q(p−1) + 1 = p^q`.
  have key : (n * u + q * (p - 1) + 1) * u = p ^ q * u := by
    have hexp : (n * u + q * (p - 1) + 1) * u = u + n * u ^ 2 + q * (p - 1) * u := by ring
    rw [hexp]; exact hclass
  have hnu : n * u + q * (p - 1) + 1 = p ^ q :=
    Nat.eq_of_mul_eq_mul_right (by omega) key
  -- Substitute the `W₁`-orbit split and reassociate.
  rw [hn] at hnu
  have hre : (S4 * q + (p - 1)) * u + q * (p - 1) + 1
      = S4 * (q * u) + (p - 1) * u + (p - 1) * q + 1 := by ring
  rw [← hre]; exact hnu

/-- **Peterfalvi (9.11.5), the full refutation** (`|𝒮₄| ≤ ‖α‖²` is impossible).

The (9.11.5) argument in denominator-cleared `ℕ` form.  Inputs (all `ℕ`, integrality already used):

* `hcount` — (9.11.3) cleared: `|𝒮₄|·qu + (p−1)q + (p−1)u + 1 = p^q`, i.e. with `p = 2a+1`,
  `S₄·qu + 2aq + 2au + 1 = (2a+1)^q`.  (Book: `|𝒮₄| = (p^q−1)/(qu) − (p−1)/u − (p−1)/q`.)
* `hnorm` — (9.11.4) cleared: `‖α‖²·u = (a+1)u + (q−1)a²`.  (Book: `‖α‖² = a+1+(q−1)a²/u`;
  `‖α‖² ∈ ℤ` as a virtual-character norm.)
* `hua2` — (9.11.2): `u ≤ a²`.
* `hle` — the contradiction hypothesis `|𝒮₄| ≤ ‖α‖²`.

From `hle`: `S₄·qu ≤ q·(‖α‖²·u) = (a+1)qu + q(q−1)a²`; substituting into `hcount` and using `u ≤ a²`
to bound the `u`-linear part `(aq+q+2a)u ≤ (aq+q+2a)a²` gives `(2a+1)^q − 1 ≤ (q+2)a³ + q²a² + 2qa`,
refuted by `nineElevenFive_arithmetic_contradiction`.  This is what the (9.11.6)–(9.11.8) coherence
contradiction (or directly the maximality refutation) feeds. -/
theorem nineElevenFive_refutation {q a u S4 N : ℕ} (hq : 3 ≤ q) (ha : 1 ≤ a) (hu : 1 ≤ u)
    (hua2 : u ≤ a * a)
    (hcount : S4 * (q * u) + 2 * a * q + 2 * a * u + 1 = (2 * a + 1) ^ q)
    (hnorm : N * u = (a + 1) * u + (q - 1) * a ^ 2)
    (hle : S4 ≤ N) : False := by
  refine nineElevenFive_arithmetic_contradiction hq ha ?_
  rw [← hcount, Nat.add_sub_cancel]
  -- `S₄·(q·u) ≤ (a+1)·q·u + q·(q−1)·a²`.
  have key1 : S4 * (q * u) ≤ (a + 1) * (q * u) + q * ((q - 1) * a ^ 2) := by
    calc S4 * (q * u) ≤ N * (q * u) := Nat.mul_le_mul_right _ hle
      _ = q * (N * u) := by ring
      _ = q * ((a + 1) * u + (q - 1) * a ^ 2) := by rw [hnorm]
      _ = (a + 1) * (q * u) + q * ((q - 1) * a ^ 2) := by ring
  -- `(a·q + q + 2·a)·u ≤ (a·q + q + 2·a)·a²` from `u ≤ a²`.
  have key2 : (a * q + q + 2 * a) * u ≤ (a * q + q + 2 * a) * (a * a) :=
    Nat.mul_le_mul_left _ hua2
  -- Clear the `q − 1` subtraction (`q ≥ 3`), then combine as a polynomial inequality.
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at key1 ⊢
  nlinarith [key1, key2, ha, hu, sq_nonneg a, Nat.zero_le q']

end FiveArithmetic

/-! ### (9.11.3) preamble: the `𝒳(H₀C)` character sum-of-squares

Book (9.11.3): the class equation `p^q·u = |Ū| + ∑_{χ ∈ 𝒳(H₀C)} χ(1)²` on the quotient `HŪ/(H₀C)`.
Its character-theoretic core — the sum `∑_{χ ∈ 𝒳(H₀C)} χ(1)²` — is the kernel-interval
degree-square sum (`sumDegreeSq_kernelInterval`, `NonInflatedDegreeSqInterval.lean`) at `N = H₀C`,
`K = H`: `𝒳(H₀C)` is exactly `{χ ∈ Irr(HU) | H₀C ⊆ ker χ, H ⊄ ker χ}` (the `xiOf` conditions), so
the sum equals `|HU/(H₀C)| − |HU/(H ⊔ H₀C)| = |HU/(H₀C)| − |HU/HC|`.  The second term
`|HU/HC| = [HU:HC] = u` is resolved here (`index_hcInHu`); the first term `|HU/(H₀C)| = p^q·u` is
the remaining index arithmetic (`|H|/|H₀| = p^q` × `[U:C] = u`), threaded by the (9.11.3)
`nineElevenThree_count`'s `hclass`. -/

section CharacterSumOfSquares

variable [Finite G] {M : Subgroup G}

/-- **Peterfalvi (9.11.3) quotient order**: the realized `H₀C` in `HU` has index `p^q·u`.

`[HU : H₀C] = [HU : HC]·[HC : H₀C] = u·p^q`, where `HC = H·C = hInHu ⊔ cInHu`:
* `[HU : HC] = u` (`index_hcInHu_eq_relindex_cInHu` ∘ `index_cInHu_subgroupOf_uInHu_eq_u`);
* `[HC : H₀C] = p^q` by the second isomorphism `HC/H₀C ≅ H/(H ⊓ H₀C) = H/H₀ = H̄`
  (`relIndex_sup_right` with `HC = H ⊔ H₀C`, and `H ⊓ H₀C = H₀` via
  `hInHu_inf_realizedH0supC_eq_realizedH0`), so `[HC : H₀C] = [H : H₀] = |H|/|H₀| = p^q`
  (`chief.quotient_order`).
This is the first term of the (9.11.3) class equation, folded into `sum_xiOf_H0C_degreeSq`. -/
theorem index_realizedH0supC_eq (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    (chars : Section11CharacterData data chief) :
    Nat.card (↥(huSub data) ⧸
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      = chief.p ^ data.q * chars.u := by
  haveI : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal :=
    (chiefFactor_H0supC_subgroupOf_normal chief).subgroupOf (huSub data)
  rw [← Subgroup.index_eq_card]
  have hHC : hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      = hInHu data ⊔ cInHu data chief := hInHu_sup_realizedH0supC chief
  have hle : ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data ⊔ cInHu data chief := by rw [← hHC]; exact le_sup_right
  have hu : (hInHu data ⊔ cInHu data chief).index = chars.u :=
    (index_hcInHu_eq_relindex_cInHu data chief).trans
      (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
  -- `[HC : H₀C] = [H : H₀] = p^q` via the second isomorphism theorem.
  have hrel : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).relIndex
      (hInHu data ⊔ cInHu data chief) = chief.p ^ data.q := by
    rw [← hHC, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_left,
      hInHu_inf_realizedH0supC_eq_realizedH0 chief]
    -- `[H : H₀] = |H|/|H₀| = p^q`.
    have hH0le : (chief.H0.subgroupOf M).subgroupOf (huSub data) ≤ hInHu data :=
      Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M chief.H0_lt_H.le)
    have hcard_H0r : Nat.card ↥((chief.H0.subgroupOf M).subgroupOf (huSub data))
        = Nat.card ↥chief.H0 := by
      have hH0M : chief.H0 ≤ M := chief.H0_lt_H.le.trans (H_le_M data)
      have hH0subM : chief.H0.subgroupOf M ≤ huSub data :=
        Subgroup.subgroupOf_mono M (chief.H0_lt_H.le.trans le_sup_left)
      calc Nat.card ↥((chief.H0.subgroupOf M).subgroupOf (huSub data))
          = Nat.card ↥(chief.H0.subgroupOf M) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH0subM).toEquiv
        _ = Nat.card ↥chief.H0 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH0M).toEquiv
    have hlag := Subgroup.index_mul_card
      (((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf (hInHu data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH0le).toEquiv, hcard_H0r,
      Nat.card_congr (hInHuEquivH data).toEquiv, chief.quotient_order] at hlag
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hlag
  rw [← Subgroup.relIndex_mul_index hle, hrel, hu]

open scoped Classical in
/-- **Peterfalvi (9.11.3), the `𝒳(H₀C)` character sum-of-squares (fully resolved: `p^q·u − u`).**

The kernel-interval degree-square sum (`sumDegreeSq_kernelInterval`) instantiated at the realized
`N = H₀C`, `K = H` inside `HU`: over `𝒳(H₀C) = {χ ∈ Irr(HU) | H₀C ⊆ ker, H ⊄ ker}`,
`∑ χ(1)² = |HU/(H₀C)| − |HU/(H ⊔ H₀C)|`, and `H ⊔ H₀C = HC` (`hInHu_sup_realizedH0supC`) with
`|HU/HC| = [HU:HC] = u` (`index_hcInHu`) and `|HU/(H₀C)| = p^q·u` (`index_realizedH0supC_eq`).
So `∑ χ(1)² = p^q·u − u`, the (9.11.3) class equation `|Ū| = |HU/H₀C| − ∑ χ(1)²` value fed to
`nineElevenThree_count`'s `hclass`. -/
theorem sum_xiOf_H0C_degreeSq (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    (chars : Section11CharacterData data chief) :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter ↥(huSub data) =>
        (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :
            Set ↥(huSub data)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) ∧
        ¬ ((hInHu data : Set ↥(huSub data)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ))),
        ((χ : ClassFunction ↥(huSub data) ℂ) 1) ^ 2
      = (chief.p ^ data.q * chars.u : ℂ) - (chars.u : ℂ) := by
  haveI : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal :=
    (chiefFactor_H0supC_subgroupOf_normal chief).subgroupOf (huSub data)
  haveI : (hInHu data).Normal := hInHu_normal data
  rw [OddOrder.RepresentationTheory.sumDegreeSq_kernelInterval
    (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) (hInHu data)]
  have hHC : hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      = hInHu data ⊔ cInHu data chief := hInHu_sup_realizedH0supC chief
  have hu : (hInHu data ⊔ cInHu data chief).index = chars.u :=
    (index_hcInHu_eq_relindex_cInHu data chief).trans
      (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
  -- First term `|HU/(H₀C)| = p^q·u` (`index_realizedH0supC_eq`); second `|HU/HC| = u`.
  congr 1
  · exact_mod_cast index_realizedH0supC_eq data chief chars
  · rw [hHC]; exact_mod_cast hu

end CharacterSumOfSquares

/-! ### (9.11.4): the norm reduction `‖α‖² = ‖γ‖² + 1`

Book (9.11.4): `α = γ − ψ₁` with `γ = Ind_{HU₁}^M 1` and `ψ₁ ∈ 𝒮₁` a norm-one irreducible.  Since
every constituent of the trivial-induced `γ` has `H ⊆ ker` while `ψ₁` does not, `⟨γ, ψ₁⟩ = 0`, and
the virtual-character norm splits `‖α‖² = ‖γ‖² + 1` (Coq `'[alpha] = '[gamma] + 1`,
`PFsection9.v:1905`).  The remaining `‖γ‖²` is the Mackey double-coset count
`(1/q)·Σ_{w∈W₁} |U₁ ∩ U₁ʷ| / |C| = a + (q−1)a²/u`, resolved through the (9.11.2) inertia identity
`U₁ ∩ U₁ʷ = C`; **this subsection isolates the character-side reduction, which is independent of
(9.11.2)**. -/

section NineElevenFour

/-- **Peterfalvi (9.11.4), the norm reduction `‖γ − ψ‖² = ‖γ‖² + 1`** (`cfnormBd`).

For a norm-one irreducible character `ψ` orthogonal to a class function `γ` (`⟨γ, ψ⟩ = 0`), the
difference `α = γ − ψ` has `⟨α, α⟩ = ⟨γ, γ⟩ + 1`: sesquilinearity expands
`⟨γ−ψ, γ−ψ⟩ = ⟨γ,γ⟩ − ⟨γ,ψ⟩ − ⟨ψ,γ⟩ + ⟨ψ,ψ⟩`, with `⟨γ,ψ⟩ = 0` (hypothesis),
`⟨ψ,γ⟩ = conj⟨γ,ψ⟩ = 0` (`inner_conj_symm`), and `⟨ψ,ψ⟩ = 1`
(`IsIrreducibleCharacter.inner_self_eq_one`).  This is the character-side step of (9.11.4): with
`γ = Ind_{HU₁}^M 1` and `ψ = ψ₁ ∈ 𝒮₁` (orthogonal because `H ⊆ ker` of every constituent of `γ`
but not of `ψ₁`), it gives `‖α‖² = ‖γ‖² + 1`; the remaining `‖γ‖²` is the (9.11.2)-gated Mackey
count.  Stated for an arbitrary character `γ` (no coherence/induction hypothesis), so it is reusable
wherever a norm-one irreducible is subtracted off orthogonally. -/
theorem cfnorm_sub_irreducible_orthogonal {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {γ ψ : ClassFunction Γ ℂ}
    (hψ : IsIrreducibleCharacter ψ) (hortho : ClassFunction.inner γ ψ = 0) :
    ClassFunction.inner (γ - ψ) (γ - ψ) = ClassFunction.inner γ γ + 1 := by
  have hψγ : ClassFunction.inner ψ γ = 0 := by
    rw [inner_conj_symm γ ψ, hortho, star_zero]
  have hψψ : ClassFunction.inner ψ ψ = 1 := by
    simpa using irreducibleCharacter_inner_eq_ite
      (⟨ψ, hψ⟩ : IrreducibleCharacter Γ) ⟨ψ, hψ⟩
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hortho, hψγ, hψψ]
  ring

end NineElevenFour

/-! ### (9.11.2)–(9.11.5): the equality-branch refutation (assembly)

Book (9.11.2)–(9.11.8): under the (9.11.1) equality configuration (`p = 2a+1`, forced by
`nineElevenOne_configuration`'s `2a = p−1`), the coherence bound `|𝒮₄| ≤ ‖α‖²` — the negation of
"some conjugate pair from `𝒮₃` can be adjoined" — is impossible.  This subsection assembles the four
landed steps into one refutation, isolating the three remaining deep group/character inputs as named
hypotheses:

* **(9.11.2)** the inertia identity `C = K₁ ⊓ K₂` with `[U:K₁] = [U:K₂] = a` (`K₁ = C_U(S₀)`,
  `K₂ = C_U(S₀ʷ)`), giving `u ≤ a²` (`nineElevenTwo_u_le_a_sq`).  Gated on the two-summand `θ`-character
  inertia computation (generalising `hcPsi_inertia_index_eq_u` from all summands to two).
* **(9.11.3)** the `HŪ/(H₀C)` class equation `hclass` (`|Ū| + Σχ(1)² = p^q·u`, its character side
  `sum_xiOf_H0C_degreeSq` landed) and the `W₁`-orbit split `hn` (`n = q·|𝒮₄| + (p−1)`), giving the
  cleared count (`nineElevenThree_count`).
* **(9.11.4)** the Mackey norm `hnorm` (`‖α‖²·u = (a+1)u + (q−1)a²`), whose `‖α‖² = ‖γ‖²+1` reduction
  is `cfnorm_sub_irreducible_orthogonal` and whose `‖γ‖²` is the non-normal-`HU₁` double-coset count.

The (9.11.5) exponential-beats-polynomial contradiction (`nineElevenFive_refutation`) closes it. -/

/-- **Peterfalvi (9.11.2)–(9.11.5), the equality-branch refutation.**

In the (9.11.1) equality configuration `p = 2a+1` (`hpeq`), the three deep inputs — the (9.11.2)
inertia identity (`hK₁`/`hK₂`/`hCinf`), the (9.11.3) class equation and `W₁`-orbit split
(`hclass`/`hn`), and the (9.11.4) Mackey norm (`hnorm`) — combine with the coherence bound
`|𝒮₄| ≤ ‖α‖²` (`hle`) to a contradiction.  This is the equality branch of the (9.11) caseA refuter:
`nineElevenOne_configuration` produces `hpeq` (and `C = U′`, `χdeg = u`) from the (9.11.1) squeeze,
and here (9.11.2)/(9.11.3)/(9.11.4) are chained through to `nineElevenFive_refutation`.  Only the
three named group/character inputs remain honest content; the arithmetic is fully discharged. -/
theorem nineElevenCaseA_equality_refutation [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hq3 : 3 ≤ data.q) (hu : 1 ≤ chars.u) (hpeq : chief.p = 2 * caseA.a + 1)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁.relIndex data.U = caseA.a)
    (hK₂ : K₂.relIndex data.U = caseA.a) (hCinf : chars.C = K₁ ⊓ K₂)
    {n S4 : ℕ}
    (hclass : chars.u + n * chars.u ^ 2 + data.q * (chief.p - 1) * chars.u
      = chief.p ^ data.q * chars.u)
    (hn : n = S4 * data.q + (chief.p - 1))
    {N : ℕ} (hnorm : N * chars.u = (caseA.a + 1) * chars.u + (data.q - 1) * caseA.a ^ 2)
    (hle : S4 ≤ N) : False := by
  have ha : 1 ≤ caseA.a := caseA.a_pos
  -- (9.11.2): `u ≤ a²` from the inertia identity `C = K₁ ⊓ K₂`.
  have hua2 : chars.u ≤ caseA.a * caseA.a := nineElevenTwo_u_le_a_sq caseA hK₁ hK₂ hCinf
  -- (9.11.3): the cleared count `|𝒮₄|·qu + (p−1)u + (p−1)q + 1 = p^q`.
  have hcount0 : S4 * (data.q * chars.u) + (chief.p - 1) * chars.u
      + (chief.p - 1) * data.q + 1 = chief.p ^ data.q := nineElevenThree_count hu hclass hn
  -- Substitute `p = 2a+1` to match `nineElevenFive_refutation`'s `(2a+1)^q` form.
  have hp1 : chief.p - 1 = 2 * caseA.a := by omega
  have hcount : S4 * (data.q * chars.u) + 2 * caseA.a * data.q + 2 * caseA.a * chars.u + 1
      = (2 * caseA.a + 1) ^ data.q := by
    rw [hp1, hpeq] at hcount0; omega
  -- (9.11.5): the exponential-beats-polynomial contradiction.
  exact nineElevenFive_refutation hq3 ha hu hua2 hcount hnorm hle

end OddOrder.Peterfalvi.S11
