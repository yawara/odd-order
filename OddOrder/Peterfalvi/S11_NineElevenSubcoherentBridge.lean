/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S10_SubcoherentTypeP
import OddOrder.Peterfalvi.S11_MaximalII_III_IV.ThetaCountAssembly
import OddOrder.Peterfalvi.S11_SingleFactorCentralizer

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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), case (9.7.a), at §9 level**: reduction to the maximality refuter.

The §9-level form of `S13.caseA_coherent_sOf_H0Cprime_of_refuter`.  Everything is stated over
Hypotheses (9.2)/(9.4)/(9.5) — `data`, `chief`, `chars` — with the Dade map `tau` and support `A0`
as explicit parameters, so **no type hypothesis appears anywhere**.

The §11 version reaches the same conclusion through `S13.Hypothesis`, whose `type_alt` pins types
III/IV.  Tracing its proof shows that packaging is inessential: `hyp.C` is `cSub data chief`,
`hyp.H0Cprime` is `chief.H0 ⊔ cprimeSub data chief`, `hyp.base.tau`/`.A0` are parameters, the
finiteness bridge is `sOf_finite`, and the degree-`qa` base coherence — the one genuinely §10-bound
input, via `S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent` — becomes the parameter
`hbase`, which `sOf_degreeSubfamily_coherent` supplies along the book's (8.15.3) → (5.7) route.

Book argument (unchanged): the (9.8.d) count `caseA_character_count_exact` has positive lower
bound `(p−1)·[U:U′]`, so a degree-`qa` irreducible exists in `𝒮(H₀U′)`; it transports to
`𝒮(H₀C′)` along `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′`), and the maximality skeleton
`S07.coherent_of_maximal_coherent_pair_refuted` closes it against `hrefute`. -/
theorem caseA_coherent_sOf_cprime_of_refuter [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M)
    (caseA : CliffordCaseAData chars)
    (hbase : OddOrder.Peterfalvi.S07.IsCoherent tau
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} A0)
    (hrefute : ∀ S₂ : Set (ClassFunction ↥M ℂ),
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
          IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
        S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) →
        OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
        Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau S₂ A0) →
        (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty →
        (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
          ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {χ, χ.conj}) A0)) → False) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau
      (sOf data (chief.H0 ⊔ cprimeSub data chief)) A0) := by
  classical
  -- positivity of the (9.8.d) count lower bound `(p−1)·[U:U′]`
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  have hrel : 0 < (uprimeSub data).relIndex data.U :=
    lt_of_lt_of_le (u_odd hG chars).pos (u_le_relIndex_uprimeSub_U chars)
  have hNpos := lt_of_lt_of_le (mul_pos hp1 hrel) (caseA_character_count_exact hG caseA)
  -- the (9.8.d) count set is nonempty: a degree-`qa` irreducible in `𝒮(H₀U′)`
  have hne : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
      IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    intro h0
    rw [h0, Nat.zero_mul] at hNpos
    exact absurd hNpos (lt_irrefl 0)
  -- `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′` by derived-subgroup monotonicity)
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  -- assemble the reduction via the maximality skeleton
  exact OddOrder.Peterfalvi.S07.coherent_of_maximal_coherent_pair_refuted
    (S₁ := {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))})
    (sOf_finite data _)
    (sOf_closedUnderConjugate data _)
    (fun _ hφ => hφ.1)
    (fun _ hχ => irrCut_conjClosed data _ (data.q * caseA.a) hχ)
    ⟨hbase⟩
    hrefute


open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The §9 family sits inside the `⊥`-kernel induced family**: `𝒮(Y) ⊆ S(⊥)`.

Composite of `sOf_subset_inducedNonKernelFamily` with
`S10.inducedNonKernelFamily_subset_inducedKernelFamily_bot`.

This is the §9-level replacement for the "world-bridge" step that the §11 chain performs with
`hyp.SOf_eq`/`hyp.sOf_subset_SOf` — the route through the `S13.Hypothesis` packaging.  The §11
pivot lemmas (`caseB_sOf_memberRFamily`, `sOf_anchor_diff_support`, …) use that bridge only to
borrow the `S08.inducedKernelFamily_*` suite (support, no-real-characters, pairwise orthogonality,
`ZIrr` membership); with this lemma they can borrow the same suite without a `S13.Hypothesis`. -/
theorem sOf_subset_inducedKernelFamily_bot [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    sOf data Y ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun _ hx =>
  OddOrder.Peterfalvi.S10.inducedNonKernelFamily_subset_inducedKernelFamily_bot
    (sOf_subset_inducedNonKernelFamily hG hM data Y hx)


open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Uniform-degree member differences are `A₀`-supported, at §9 level** (the `hsuppdiff` input of
the (9.11) caseB engine).

The §9 form of `S13.sOf_anchor_diff_support`.  That version reaches the `⊥`-kernel induced family
through `hyp.SOf_eq`/`hyp.sOf_subset_SOf`, i.e. through `S13.Hypothesis`; here the same step is
`sOf_subset_inducedKernelFamily_bot`, and the (8.10) containment `(M')^# ⊆ A₀` — which the §13
version reads off `hyp.base.mderivSharp_subset_A0` — becomes the explicit parameter `hKsupp`.

Neither version needs a type hypothesis; the §13 binding was purely the packaging. -/
theorem sOf_anchor_diff_support [Finite G] {M : Subgroup G} {A0 : Set ↥M}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 → x ∈ A0)
    (d : ℕ) (hunif : ∀ φ ∈ sOf data Y, ((φ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ))
    {χ₁ x : ClassFunction ↥M ℂ}
    (hχ₁mem : χ₁ ∈ sOf data Y) (hx : x ∈ sOf data Y) :
    ((x - χ₁ : ClassFunction ↥M ℂ)).support ⊆ A0 := by
  -- `M' ⊴ M` (the comap of a `map` along the injective `M.subtype`); in the §13 version this
  -- instance arrived transitively through the packaging's import closure.
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp
    (sOf_subset_inducedKernelFamily_bot hG hM data Y hx)
    (sOf_subset_inducedKernelFamily_bot hG hM data Y hχ₁mem) (d := 1)
    (by rw [Nat.cast_one, one_mul, hunif x hx, hunif χ₁ hχ₁mem])
  rwa [one_smul] at h


/-- **Peterfalvi (9.9.b), member form** (§6 level, no transport): a reducible induced character
from `h46.K` is a certain-type column sum.

This is the content the §9 caseB `R`-family dispatch needs, isolated so that **no coercion between
`↥h46.K` and `↥(huSub data)` appears** — everything stays inside `h46.K`.  An earlier attempt stated
it over `sOf data Y` directly and tried to move the source character across
`h46.K = huSub data`; that rewrite is not type-correct (the motive mentions
`IrreducibleCharacter ↥_a` *and* `chiRestrict χ₂ = χ`, both dependent on the subgroup).  Splitting
it this way keeps the dependent step transport-free and leaves the §9 identification to the
Set-valued level, where the `▸` idiom does work (cf. `sOf_subset_inducedNonKernelFamily`).

The §13 analogue is `S13.caseB_sOf_member_dichotomy`, whose conclusion is phrased in the §10 μ-grid;
the book builds these members from (4.7) and Theorem (4.5), both §6, so the `columnSum` form here is
the faithful one. -/
theorem induce_columnSum_of_not_irreducible {M : Subgroup G} {A : Set G} [Finite G] [Fintype G]
    [Fintype ↥M]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)] [Invertible (Nat.card ↥h46.K : ℂ)]
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥h46.K)
    (hχne : χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥h46.K)
    (hred : ¬ IsIrreducibleCharacter
      (ClassFunction.induce h46.K (χ : ClassFunction ↥h46.K ℂ))) :
    ∃ χ₂ ≠ 1, ClassFunction.induce h46.K (χ : ClassFunction ↥h46.K ℂ)
      = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ := by
  obtain ⟨χ₂, hχ₂⟩ := (h46.induce_not_isIrreducible_iff χ).mp hred
  refine ⟨χ₂, ?_, ?_⟩
  · -- `χ₂ = 1` would make the source trivial (`chiRestrict_one_eq_trivial`)
    rintro rfl
    rw [h46.chiRestrict_one_eq_trivial] at hχ₂
    exact hχne hχ₂.symm
  · rw [← hχ₂, OddOrder.Peterfalvi.S06.columnSum_def]
    exact h46.induce_restrict_certainType_eq χ₂

/-- **Transporting an induction source across an equality of induction subgroups.**  For `K = K'`
an irreducible `K'`-character has an irreducible `K`-counterpart with the *same* induction, and the
two are trivial together.

The equality is discharged by `subst` (both subgroups are variables here), which is exactly why the
lemma is stated in this generality rather than at `h46.K = huSub data`: there `h46.K` is a
projection, so `subst` does not apply and a direct `▸` on the dependent character type breaks the
motive (cf. the docstring of `induce_columnSum_of_not_irreducible`).  The residual `Invertible`
mismatch after `subst` is propositional (`Subsingleton`), the same wrinkle
`induceHU_eq_induce` handles. -/
theorem exists_induce_eq_of_subgroup_eq {L : Type*} [Group L] [Fintype L] {K K' : Subgroup L}
    (hKK' : K = K') [Invertible (Nat.card ↥K : ℂ)] [Invertible (Nat.card ↥K' : ℂ)]
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K') :
    ∃ χ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.induce K (χ' : ClassFunction ↥K ℂ)
          = ClassFunction.induce K' (χ : ClassFunction ↥K' ℂ) ∧
        (χ' = OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K ↔
          χ = OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K') := by
  subst hKK'
  refine ⟨χ, ?_, Iff.rfl⟩
  convert rfl using 2
  exact Subsingleton.elim (α := Invertible (Nat.card ↥K : ℂ)) _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.9.b) at §9 level**: a *reducible* member of `𝒮(Y)` is a nontrivial certain-type
column sum `μ_{χ₂}` of Hypothesis (4.6).

This is the §9 replacement for `S13.caseB_sOf_member_dichotomy`, whose conclusion is stated in the
§10 μ-grid (`hyp.base.muColumnChar`) and therefore drags the whole §10/§11 packaging — and with it
the type III/IV restriction — into the caseB `R`-family dispatch.  The book has no such detour: it
builds the reducible members from (4.7) and Theorem (4.5), both §6 results, which is exactly the
`S06.columnSum` form produced here.  (§10 converts §6-columns to μ-grid columns and `certainTypeR`
converts them back, so the packaging route is a round trip; issue 1045.)

The `𝒮`-side source is nontrivial because `𝒳` demands `H ⊄ Ker χ` while the trivial character has
kernel everything, and `hKeq` moves it into the (4.6) world where
`induce_columnSum_of_not_irreducible` applies.  Callers get `hKeq` from
`huSub_eq_derivedInG_subgroupOf` together with the `K`-field of the (4.6) producer
(`S10.typePACore_toHypothesis46_core`). -/
theorem sOf_columnSum_of_not_irreducible [Finite G] {M : Subgroup G} {A : Set G}
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) {Y : Subgroup G} {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data Y) (hred : ¬ IsIrreducibleCharacter φ) :
    ∃ χ₂ ≠ 1, φ = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ := by
  obtain ⟨χ, hχ, rfl⟩ := hφ
  -- `χ ≠ 1`: the trivial character's kernel is everything, contradicting `H ⊄ Ker χ` (`𝒳`).
  have hχne : χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥(huSub data) := by
    intro htriv
    apply hχ.1
    rw [htriv]
    simp only [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  obtain ⟨χ', hind, htriviff⟩ := exists_induce_eq_of_subgroup_eq hKeq χ
  have hred' : ¬ IsIrreducibleCharacter
      (ClassFunction.induce h46.K (χ' : ClassFunction ↥h46.K ℂ)) := by
    rw [hind, ← induceHU_eq_induce data (χ : ClassFunction ↥(huSub data) ℂ)]
    exact hred
  obtain ⟨χ₂, hχ₂ne, heq⟩ :=
    induce_columnSum_of_not_irreducible h46 χ' (fun h => hχne (htriviff.mp h)) hred'
  exact ⟨χ₂, hχ₂ne,
    (induceHU_eq_induce data (χ : ClassFunction ↥(huSub data) ℂ)).trans (hind.symm.trans heq)⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The certain-type `R`-family transported to a member equal to its column.**  For `η = μ_{χ₂}`
with `χ₂ ≠ 1`, this is `S06.certainTypeR` restated at `η`.

Only the `image_eq` field mentions the member, so `imageSet`/`mem_ZIrr`/`orthonormal` are reused
verbatim and `.imageSet` is *definitionally* `certainTypeR`'s — the form the (5.2.e)
cross-orthogonality lemmas consume.  Keeping `χ₂` and `hηeq` as parameters (rather than choosing
them inside) is what makes the `η`-rewrite in `image_eq` type-correct: were `χ₂` obtained by
`Classical.choose` from an existential over `η`, the `imageSet` in the motive would itself depend on
`η`. -/
noncomputable def columnRFamily {M : Subgroup G} {A : Set G} [Finite G]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {η : ClassFunction ↥M ℂ} (hηeq : η = OddOrder.Peterfalvi.S06.columnSum h46 χ₂) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) η where
  imageSet := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
    (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).imageSet
  mem_ZIrr := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
    (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).mem_ZIrr
  orthonormal := (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
    (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).orthonormal
  image_eq := by
    rw [hηeq]
    exact (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).image_eq

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Per-member orthonormal `R`-family over `𝒮(Y)`, at §9 level** — the raw (5.2.d) datum feeding
the norm-general (5.7) engine `S07.uniform_degree_coherence_of_families` in case (9.7.b) of (9.11).

Every member of `𝒮(Y)` is either irreducible or, by (9.9.b)
(`sOf_columnSum_of_not_irreducible`), a nontrivial certain-type column `μ_{χ₂}`; the `R`-family is
dispatched accordingly:

* **irreducible `η`** — the 2-element signed Dade family
  `S07.dadeOrthonormalCharacterImageFamilyOfDiff` (`τ(η − η̄) = ε·(μ − ν)`), whose no-realness and
  `A₀`-supported difference come from the `⊥`-kernel world-bridge
  (`sOf_subset_inducedKernelFamily_bot`) rather than from a `S13.Hypothesis`;
* **column `η = μ_{χ₂}`** — the `2q`-element certain-type family `S06.certainTypeR`.

This is the §9 replacement for `S13.caseB_sOf_memberRFamily`.  The two differ only in where the
reducible branch gets its column: the §13 version reads a μ-grid index `k : Fin hyp.base.w2` off the
§10 packaging (which is what confined it to types III/IV), while here it is the §6 column `χ₂` that
`certainTypeR` consumes anyway.  **No type hypothesis appears on this route.**

⚠ `τ` is *not* a free parameter here (unlike case (9.7.a)'s `caseA_coherent_sOf_cprime_of_refuter`):
`certainTypeR` produces its family over `dadeIntegralCharacterMap h46.dade0 h46.tau`, so the
conclusion is pinned to it, and the irreducible branch — which lands on
`h46.dade0.fullDadeIsometryData hconj` — is matched to it by `htau`.  For the intended producer
`S10.typePACore_toHypothesis46_core`, which stores `tau := dade0.fullDadeIsometryData hconj`
verbatim, `htau` is `rfl`.

⚠ The family is assembled field-by-field rather than by transporting along `htau` / `η = μ_{χ₂}`,
so that `.imageSet` is *definitionally* the underlying constructor's — the form in which the (5.2.e)
cross-orthogonality lemmas consume it (same reason as in the §13 version). -/
noncomputable def sOf_memberRFamily [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) η := by
  classical
  -- `M' ⊴ M`; in the §13 version this instance arrived through the packaging's import closure.
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hηIKF0 := sOf_subset_inducedKernelFamily_bot hG hM data Y hη
  by_cases hirr : IsIrreducibleCharacter η
  · -- irreducible member: the signed Dade image family, matched to `h46.tau` by `htau`
    have hreal : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)) (⊥ : Subgroup ↥M) hηIKF0
    have hdiffsupp := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp hηIKF0
    exact
      { imageSet := (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          h46.dade0 hconj ⟨η, hirr⟩ hreal hdiffsupp).imageSet
        mem_ZIrr := (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          h46.dade0 hconj ⟨η, hirr⟩ hreal hdiffsupp).mem_ZIrr
        orthonormal := (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          h46.dade0 hconj ⟨η, hirr⟩ hreal hdiffsupp).orthonormal
        image_eq := by
          rw [htau]
          exact (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
            h46.dade0 hconj ⟨η, hirr⟩ hreal hdiffsupp).image_eq }
  · -- reducible member: (9.9.b) gives the column `χ₂ ≠ 1`, and `certainTypeR` its `2q`-family
    exact columnRFamily h46 (sOf_columnSum_of_not_irreducible data h46 hKeq hη hirr).choose_spec.1
      (sOf_columnSum_of_not_irreducible data h46 hKeq hη hirr).choose_spec.2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`sOf_memberRFamily` reduction, irreducible case**: for an irreducible member the dispatched
family *is* `S07.dadeOrthonormalCharacterImageFamilyOfDiff` (imageSet form).  The realness and
support proofs are existential — they are proof-irrelevant inputs to a proof-independent
`imageSet` — so the (5.2.e) lemmas apply after rewriting. -/
theorem sOf_memberRFamily_imageSet_of_irr [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y)
    (hirr : IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ))
      (hs : ((η : ClassFunction ↥M ℂ).conj - (η : ClassFunction ↥M ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M),
      (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          h46.dade0 hconj ⟨η, hirr⟩ hr hs).imageSet := by
  classical
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hηIKF0 := sOf_subset_inducedKernelFamily_bot hG hM data Y hη
  refine ⟨OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)) (⊥ : Subgroup ↥M) hηIKF0,
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp hηIKF0, ?_⟩
  unfold sOf_memberRFamily
  rw [dif_pos hirr]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`sOf_memberRFamily` reduction, column case**: for a reducible member the dispatched family
*is* `S06.certainTypeR` at the (9.9.b) column `χ₂` (imageSet form), exposed together with the
membership equation `η = μ_{χ₂}` — which is what supplies the `≠`-side conditions of the μ×μ and
μ×irr cross-orthogonality. -/
theorem sOf_memberRFamily_imageSet_of_col [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ sOf data Y)
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (hχ₂ : χ₂ ≠ 1),
      η = OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∧
      (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).imageSet := by
  classical
  have hex := sOf_columnSum_of_not_irreducible data h46 hKeq hη hcol
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold sOf_memberRFamily
  rw [dif_neg hcol]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Dade image of an `A₁`-supported function vanishes on the exceptional set `V`**, at
Hypothesis (4.6) generality.

`V ⊆ A₀` — the exceptional elements *are* Dade base points — so the explicit (2.5) evaluation
(`dadeValue_eq` at `a = v`, `h = 1`) reduces `α^τ(v)` to `α(v)`, which vanishes as soon as `α` is
supported on some set `A₁` that `V` avoids.

This is the (4.6)-level form of `S13.tau_apply_eq_zero_of_mem_typePV`, which fixes
`A₁ = A(M) = (M')^#` and reads the avoidance off `typePData_typePV_not_mem_derived`.  Keeping `A₁`
separate from the (4.6) ambient `A` matters: the members of `𝒮(Y)` have `(M')^#`-supported
differences, and for a type-uniform `A(M)` (i.e. `typePACore`) that is *strictly larger* than `A`,
so the §13 phrasing would not transfer. -/
theorem dadeICM_apply_eq_zero_of_avoidV [Finite G] {M : Subgroup G} {A : Set G}
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    (tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) h46.dade0)
    {α : ClassFunction ↥M ℂ}
    (hαA0 : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {A₁ : Set G} (hαA₁ : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ M)
    {v : G} (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V) (hvA₁ : v ∉ A₁) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 tau α v = 0 := by
  classical
  have hvV : v ∈ h46.tic.V := by rw [h46.tic_V]; exact hv
  have hvA0 : v ∈ A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V :=
    Or.inr ⟨v, hvV, 1, M.one_mem, by group⟩
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support h46.dade0 _ hαA0,
    OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_apply,
    h46.dade0.dadeValue_eq _ (a := ⟨v, hvA0⟩) (Subgroup.one_mem _) (by rw [mul_one])]
  by_contra hne
  exact hvA₁ (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp
    (hαA₁ (ClassFunction.mem_support.mpr hne)))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the dispatched `R`-families over `𝒮(Y)`, at §9 level** — the
`hRorth` input of the norm-general (5.7) engine.

For members `φ, ξ` with `⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the families `R(φ) ⊥ R(ξ)`: a `2×2` case split on
the member dichotomy.

* **irr × irr** — `S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`; the two extra scalars
  `⟨φ̄, ξ⟩`, `⟨φ̄, ξ̄⟩` are `star`-conjugates of `⟨φ, ξ̄⟩`, `⟨φ, ξ⟩`;
* **irr × column** / **column × irr** —
  `S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV` (irr-on-left via an
  `inner_conj_symm` swap), whose anchor is `dadeICM_apply_eq_zero_of_avoidV` at `A₁ = M'`;
* **column × column** — `S06.certainTypeR_imageSet_orthogonal_certainTypeR`, whose `χ₂ ≠ χ₂'` and
  `χ₂ ≠ χ₂'⁻¹` side conditions come from `⟨φ, ξ⟩ = 0` and `⟨φ, ξ̄⟩ = 0`: equality would force
  `φ = ξ` (resp. `φ = ξ̄` by `columnSum_conj_eq`) and the self-norm `w₁ ≠ 0`.

The §13 analogue is `S13.caseB_sOf_memberRFamily_orthogonal`.  The only genuinely ambient input
here is `hVsub`: the exceptional set `V` avoids `M'` (at the intended instantiation, exactly
`S10.typePData_typePV_not_mem_derived`).  **No type hypothesis appears.** -/
theorem sOf_memberRFamily_orthogonal [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data) (hconj : h46.dade0.HConjInvariant)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData hconj)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    {Y : Subgroup G} {φ ξ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data Y) (hξ : ξ ∈ sOf data Y)
    (h1 : ClassFunction.inner φ ξ = 0) (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hφ).Orthogonal
      (sOf_memberRFamily hG hM data h46 hKeq hconj htau hKsupp hξ) := by
  classical
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  -- member differences are `M'`-supported (the `A₁` of the anchor), on top of being `A₀`-supported
  have hMderiv : ∀ {ζ : ClassFunction ↥M ℂ}, ζ ∈ sOf data Y →
      ((ζ.conj - ζ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        ((derivedInG M : Set G)) M) := fun {ζ} hζ =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      (fun _ hx _ => Subgroup.mem_subgroupOf.mp hx)
      (sOf_subset_inducedKernelFamily_bot hG hM data Y hζ)
  -- the anchor of the mixed stratum: `(ζ − ζ̄)^τ` vanishes on the exceptional `V`
  have hanchor : ∀ {ζ : ClassFunction ↥M ℂ}, ζ ∈ sOf data Y →
      ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0
        (h46.dade0.fullDadeIsometryData hconj) (ζ - ζ.conj) v = 0 := by
    intro ζ hζ v hv
    have hflip : (ζ - ζ.conj : ClassFunction ↥M ℂ) = -(ζ.conj - ζ) := by abel
    refine dadeICM_apply_eq_zero_of_avoidV h46 _ ?_ ?_ hv (hVsub v hv)
    · rw [hflip, ClassFunction.support_neg]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp
        (sOf_subset_inducedKernelFamily_bot hG hM data Y hζ)
    · rw [hflip, ClassFunction.support_neg]
      exact hMderiv hζ
  have hw1ne : (Nat.card h46.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  intro α hα β hβ
  by_cases hφirr : IsIrreducibleCharacter φ <;> by_cases hξirr : IsIrreducibleCharacter ξ
  · -- irr × irr
    obtain ⟨hrφ, hsφ, hφeq⟩ :=
      sOf_memberRFamily_imageSet_of_irr hG hM data h46 hKeq hconj htau hKsupp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ :=
      sOf_memberRFamily_imageSet_of_irr hG hM data h46 hKeq hconj htau hKsupp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hbarχ : ClassFunction.inner φ.conj ξ = 0 := by
      rw [← ClassFunction.conj_conj ξ, inner_conj_conj, h2, star_zero]
    have hbarχbar : ClassFunction.inner φ.conj ξ.conj = 0 := by
      rw [inner_conj_conj, h1, star_zero]
    exact OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
      h46.dade0 hconj (x := ⟨φ, hφirr⟩) (χ := ⟨ξ, hξirr⟩) hrφ hsφ hrξ hsξ h1 h2 hbarχ hbarχbar
      α hα β hβ
  · -- irr × column
    obtain ⟨hrφ, hsφ, hφeq⟩ :=
      sOf_memberRFamily_imageSet_of_irr hG hM data h46 hKeq hconj htau hKsupp hφ hφirr
    obtain ⟨χ₂, hχ₂, -, hξeq⟩ :=
      sOf_memberRFamily_imageSet_of_col hG hM data h46 hKeq hconj htau hKsupp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    rw [inner_conj_symm β α]
    rw [OddOrder.Peterfalvi.S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV
      h46 hχ₂ (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
      h46.dade0 hconj ⟨φ, hφirr⟩ hrφ hsφ (hanchor hφ) β hβ α hα, star_zero]
  · -- column × irr
    obtain ⟨χ₂, hχ₂, -, hφeq⟩ :=
      sOf_memberRFamily_imageSet_of_col hG hM data h46 hKeq hconj htau hKsupp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ :=
      sOf_memberRFamily_imageSet_of_irr hG hM data h46 hKeq hconj htau hKsupp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact OddOrder.Peterfalvi.S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV
      h46 hχ₂ (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
      h46.dade0 hconj ⟨ξ, hξirr⟩ hrξ hsξ (hanchor hξ) α hα β hβ
  · -- column × column
    obtain ⟨χ₂, hχ₂, hφcol, hφeq⟩ :=
      sOf_memberRFamily_imageSet_of_col hG hM data h46 hKeq hconj htau hKsupp hφ hφirr
    obtain ⟨χ₂', hχ₂', hξcol, hξeq⟩ :=
      sOf_memberRFamily_imageSet_of_col hG hM data h46 hKeq hconj htau hKsupp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    -- `χ₂ ≠ χ₂'`: else `φ = ξ` and `⟨φ, φ⟩ = w₁ ≠ 0` contradicts `h1`
    have hne1 : χ₂ ≠ χ₂' := by
      intro heq
      rw [hφcol, hξcol, heq, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h1
      exact hw1ne h1
    -- `χ₂ ≠ χ₂'⁻¹`: else `φ = ξ̄` and `⟨φ, ξ̄⟩ = w₁ ≠ 0` contradicts `h2`
    have hne2 : χ₂ ≠ χ₂'⁻¹ := by
      intro heq
      rw [hφcol, hξcol, OddOrder.Peterfalvi.S06.columnSum_conj_eq, heq,
        OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h2
      exact hw1ne h2
    exact OddOrder.Peterfalvi.S06.certainTypeR_imageSet_orthogonal_certainTypeR h46 hχ₂ hχ₂'
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂').symm hne1 hne2 α hα β hβ


end OddOrder.Peterfalvi.S11
