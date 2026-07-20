/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S10_SubcoherentTypeP
import OddOrder.Peterfalvi.S11_MaximalII_III_IV.ThetaCountAssembly

/-!
# The §9 family sits inside the (8.15.3) family — the subcoherence bridge

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8 (8.15.3) and §9 (9.5), pp. 47-51 (issue 1045).

Peterfalvi gets the base coherence used by (9.11) from **(8.15.3)**: the family `𝒮` of §9 is a
conjugation-closed set of induced characters to which Hypothesis (5.2) applies, and (5.7)
(`S07.coherent_subset_of_constant_degree`) then makes any constant-degree subfamily coherent.
The repo instead routed that through the §10 μ-grid engine
(`S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent`), which is what tied the (9.11) chain to
the §10/§11 packaging and hence to types III/IV.

This file supplies the missing link — that §9's family is a subfamily of the (8.15.3) one:

* §9 (9.5) family: `𝒮(Y) = {Ind_{HU}^M χ | χ ∈ Irr(HU), H ⊄ Ker χ, Y ⊆ Ker χ}` (`S11.sOf`);
* (8.15.3) family: `{Ind_{M'}^M θ | θ ∈ Irr M', M_σ ⊄ Ker θ}` (`S10.inducedNonKernelFamily`).

They induce from the *same* subgroup, since `HU = M'` (`huSub_eq_derivedInG_subgroupOf`,
Peterfalvi (9.2)); and §9's filter is the *stronger* one, since `M_F ≤ M_σ`
(`BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma`) makes `M_F ⊄ Ker χ` imply `M_σ ⊄ Ker χ`.

⚠ In types III/IV, `M_s = M'`, so (8.15.3)'s filter degenerates to `θ ≠ 1` and §9's family is
strictly narrower; the containment still runs the direction we need.

⚠ **Why a separate leaf**: `S10_SubcoherentTypeP` (where `inducedNonKernelFamily` lives) and
`S11_MaximalII_III_IV.*` (where `sOf` lives) are *sibling* modules — neither imports the other.
Putting the bridge in the §8 file would make an §8 module import §9, reintroducing exactly the
layering inversion that issues 1045/1046 removed.
-/

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **`H` sits inside `M_σ`, realised in `HU`**: `hInHu data ≤ (M_σ.subgroupOf M).subgroupOf (HU)`.

Two applications of `Subgroup.subgroupOf` monotonicity to `M_F ≤ M_σ`
(`BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma`, rewritten through `data.typeP.H_eq`). -/
theorem hInHu_le_Msigma_subgroupOf [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) :
    hInHu data ≤ ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).subgroupOf (huSub data) := by
  have hMF : data.H ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    rw [show data.H = data.typeP.H from rfl, data.typeP.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM
  exact Subgroup.comap_mono (Subgroup.comap_mono hMF)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The §9 family is contained in the (8.15.3) family** (issue 1045): `𝒮(Y) ⊆ 𝒮_{(8.15.3)}`.

This is what lets Peterfalvi's own route to the (9.11) base coherence — (8.15.3) followed by (5.7)
— replace the repo's §10 μ-grid engine, and with it the type-III/IV restriction: the (8.15.3)
producer `S10.typePACore_subcoherent` carries no type hypothesis beyond `IsTypeP`.

The proof establishes membership over `huSub data` and then transports along
`huSub_eq_derivedInG_subgroupOf`; the two subgroups are only *propositionally* equal, so
`↥(huSub data)` and `↥((derivedInG M).subgroupOf M)` are distinct types and the characters do not
transfer definitionally.  This is the same `▸`-transport idiom the repo already uses for
`S08.inducedKernelFamily` (`S15_SSetMemberRFamily`). -/
theorem sOf_subset_inducedNonKernelFamily [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    sOf data Y ⊆ OddOrder.Peterfalvi.S10.inducedNonKernelFamily
      ((derivedInG M).subgroupOf M) ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) := by
  have hKeq : huSub data = (derivedInG M).subgroupOf M :=
    huSub_eq_derivedInG_subgroupOf data
  have hle := hInHu_le_Msigma_subgroupOf hG hM data
  -- first over `huSub data`, then transport
  have hbase : sOf data Y ⊆ OddOrder.Peterfalvi.S10.inducedNonKernelFamily
      (huSub data) ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) := by
    rintro φ ⟨χ, hχ, rfl⟩
    refine ⟨χ, ?_, induceHU_eq_induce data _⟩
    -- `M_σ ⊄ Ker χ`: else `H ⊆ Ker χ` too, contradicting `χ ∈ 𝒳`
    intro hsub
    exact hχ.1 fun x hx => hsub (SetLike.mem_coe.mpr (hle (SetLike.mem_coe.mp hx)))
  exact hKeq ▸ hbase

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(9.11) base coherence at §9 level**: the degree-`d` irreducible cut of `𝒮(Y)` is coherent.

This is the step that takes the (9.11) base case off the §10 μ-grid engine.  The repo obtained it
from `S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent`, which needs a `S13.Hypothesis` and
hence types III/IV; Peterfalvi instead routes it through **(8.15.3) then (5.7)**, neither of which
carries a type hypothesis.  Here that route is assembled:

* the cut sits inside the (8.15.3) family — `sOf_subset_inducedNonKernelFamily`;
* it is conjugation-closed — `irrCut_conjClosed` (§9-level since issue 1045);
* it is finite — `sOf_finite` (§9-level since issue 1045);
* (5.3.b) + (5.7) — `S10.inducedNonKernelFamily_degreeSubfamily_coherent`.

⚠ `h2 : 2 ≤ ncard` stays exposed, as in the §8 companion and in
`S15.Hypothesis.sSetIrrDeg_coherent`: the (9.8.d) count gives `∃ ζ`, not two members.

`hKeq`/`hHeq` pin Hypothesis (4.6)'s `K` and `H` to `M'` and `M_σ` — the book's choice, supplied by
`S10.typePACore_toHypothesis46_core`.  They are taken as hypotheses rather than assumed
definitionally so that no `Hypothesis46Core` has to be rebuilt here (rebuilding it is what makes
the two copies fail to be definitionally equal). -/
theorem sOf_degreeSubfamily_coherent [Finite G] {M : Subgroup G} {A : Set G}
    (hodd : Odd (Nat.card ↥M))
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46Core A M)
    (dd : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M A)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) (d : ℕ)
    (hKeq : h46.K = (derivedInG M).subgroupOf M)
    (hHeq : h46.subH = (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    (hd0 : ((d : ℂ)) ≠ 0)
    (h2 : 2 ≤ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}.ncard)
    (h1A : (1 : ↥M) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S10.inducedNonKernelFamily_subcoherent hodd h46 dd
        (hKeq ▸ hHeq ▸ (fun _ hx => sOf_subset_inducedNonKernelFamily hG hM data Y hx.1))
        (fun _ hx => hx.2.1)
        (fun _ hx => irrCut_conjClosed data Y d hx)).tau
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}
      (OddOrder.Peterfalvi.S04.supportInSubgroup A M)) :=
  OddOrder.Peterfalvi.S10.inducedNonKernelFamily_degreeSubfamily_coherent hodd h46 dd _ _ _
    ((sOf_finite data Y).subset fun _ hx => hx.1) h2 (d : ℂ) (fun _ hx => hx.2.2) hd0 h1A

end OddOrder.Peterfalvi.S11
