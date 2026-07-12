import OddOrder.Peterfalvi.S15_SAndT_Setup.SubcoherenceInputs
import OddOrder.Peterfalvi.S11_ImprimitiveUBound
import OddOrder.Peterfalvi.S11_SingleFactorCentralizer

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT_Setup.HypothesisBasics` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ### Dade-independent subcoherence inputs for the §9 induced family `𝒮`

The (5.3.a) subcoherence assembler `S07.irrSubcoherent` needs, besides the Dade isometry, the family
properties `hconj`/`hreal`/`hortho` of `𝒮 = Ind_{HU}^M 𝒳`.  These are **Dade-independent** — provable
directly from the induced-character conjugation identity and the orthogonality of distinct-orbit
inductions — so they can be discharged ahead of the (13.2.e) Dade-isometry foundation.  Here we land
`hconj` (conjugate-closure); it feeds the honest §9 subcoherence assembly that re-grounds
`coherent_H0Cprime_S` off the unsound `sibleyTarget_H0C`. -/

open OddOrder.Peterfalvi.S11 in
/-- **`𝒳` is closed under complex conjugation** (Peterfalvi (9.5)): for `χ ∈ 𝒳` (irreducible,
`H ⊄ Ker χ`), the conjugate `χ̄` is again irreducible (`IsIrreducibleCharacter.conj`) with the same
kernel (`characterKernel_conj`), so `H ⊄ Ker χ̄`, i.e. `χ̄ ∈ 𝒳`. -/
theorem conj_mem_xiSet {M : Subgroup G} [Finite G] {data : TypesIIIIIIVSetup M}
    {χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub data)}
    (hχ : χ ∈ xiSet data) :
    (⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩ :
      OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  -- Membership unfolds (rfl) to a `characterKernel`-containment on the conjugate coe, which is
  -- defeq `(↑χ).conj`; `characterKernel_conj` rewrites it back to `characterKernel ↑χ` = `hχ`.
  show ¬ (↑(hInHu data) ⊆ OddOrder.Peterfalvi.S03.characterKernel
    ((χ : ClassFunction ↥(huSub data) ℂ).conj))
  rw [OddOrder.Peterfalvi.S03.characterKernel_conj]
  exact hχ

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮` is closed under complex conjugation** (Peterfalvi (9.5), subcoherence input (5.2.a)).
For `φ = Ind_{HU}^M χ ∈ 𝒮` with `χ ∈ 𝒳`, the conjugate is `φ̄ = Ind_{HU}^M χ̄` (`conj_induce`), and
`χ̄ ∈ 𝒳` (`conj_mem_xiSet`), so `φ̄ ∈ 𝒮`.  This is the `hconj` input the (5.3.a) subcoherence
assembler `S07.irrSubcoherent` consumes for the §9 induced family — a Dade-independent family
property, provable directly from the induced-character conjugation identity `conj_induce`. -/
theorem sSet_closedUnderConjugate {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (sSet data) := by
  rintro _ ⟨χ, hχ, rfl⟩
  refine ⟨⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩,
    conj_mem_xiSet hχ, ?_⟩
  -- `(Ind_{HU}^M χ)̄ = Ind_{HU}^M χ̄` (`conj_induce`); `induceHU` bakes in its own `Invertible`
  -- instance, so `convert` absorbs the (subsingleton) instance mismatch.
  show (induceHU data (χ : ClassFunction ↥(huSub data) ℂ)).conj
    = induceHU data ((χ : ClassFunction ↥(huSub data) ℂ).conj)
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  simp only [induceHU]
  convert OddOrder.RepresentationTheory.conj_induce (χ : ClassFunction ↥(huSub data) ℂ) using 2

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`𝒮` is pairwise orthogonal** (Peterfalvi (9.5), subcoherence input (5.2)).  Distinct members
`Ind_{HU}^M χ ≠ Ind_{HU}^M χ'` arise from non-`M`-conjugate irreducible sources `χ ≁ χ'`
(`induce_eq_induce_iff_conj`), so the cross-Mackey orthogonality `inner_induce_eq_zero_of_not_conj`
gives `⟨Ind χ, Ind χ'⟩ = 0` — a Dade-independent family property (the `𝒮`-instance of the general
`inducedKernelFamily_pairwise_orthogonal`).  The `FiniteInduce`-scoped `Fintype`/`Invertible`
instances are the ones `induceHU` bakes in, so `induceHU = Ind` reduces definitionally.  This is the
`pairwise_orthogonal` input the (5.3.a) assembler `S07.irrSubcoherent` consumes for the honest §9
induced family. -/
theorem sSet_pairwiseOrthogonal {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal (sSet data) := by
  rintro _ _ ⟨χ, hχ, rfl⟩ ⟨χ', hχ', rfl⟩ hne
  -- non-conjugate sources: else the inductions—hence the members—coincide, contradicting `hne`.
  have hnc : ∀ g : ↥M, IrreducibleCharacter.conjBy g χ ≠ χ' := fun g hg => hne (by
    show ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (χ' : ClassFunction ↥(huSub data) ℂ)
    exact (induce_eq_induce_iff_conj χ χ').mpr ⟨g, hg⟩)
  show ClassFunction.inner (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ))
      (ClassFunction.induce (huSub data) (χ' : ClassFunction ↥(huSub data) ℂ)) = 0
  exact inner_induce_eq_zero_of_not_conj χ χ' hnc

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`𝒮` has no real members** (Peterfalvi (9.5)/(1.1), subcoherence input (5.2)), for `M` of odd
order.  A real `Ind_{HU}^M χ` would force `χ̄ = χ^g` for some `g ∈ M` (`induce_conj` +
`induce_eq_induce_iff_conj`), impossible in odd order (`conjBy_ne_conj_of_odd`: a nontrivial
irreducible of an odd-order group is never `M`-conjugate to its dual).  `𝒳`-membership `H ⊄ Ker χ`
supplies the nontriviality (`Ker 1 = univ ⊇ hInHu`).  The `𝒮`-instance of the general
`inducedKernelFamily_hasNoRealCharacters`; the `no_real_characters` input for `S07.irrSubcoherent`. -/
theorem sSet_hasNoRealCharacters {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M)
    (hodd : Odd (Nat.card ↥M)) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (sSet data) := by
  rintro _ ⟨χ, hχ, rfl⟩ hreal
  -- `χ` nontrivial: else `Ker χ = univ ⊇ hInHu`, contradicting `χ ∈ 𝒳`.
  have hχne : (χ : ClassFunction ↥(huSub data) ℂ) ≠ trivialClassFunction ↥(huSub data) := by
    intro h
    apply hχ
    rw [h, OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  let χc : IrreducibleCharacter ↥(huSub data) :=
    ⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩
  -- realness of `Ind χ` transfers to the sources: `Ind χ = (Ind χ)̄ = Ind χ̄`.
  have hind : ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (χc : ClassFunction ↥(huSub data) ℂ) := by
    have h1 : (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)).conj
        = ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ) := hreal
    calc ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
        = (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)).conj := h1.symm
      _ = ClassFunction.induce (huSub data) (χc : ClassFunction ↥(huSub data) ℂ) :=
          ClassFunction.induce_conj (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj χ χc).mp hind
  refine conjBy_ne_conj_of_odd hodd χ.isIrreducible hχne g ?_
  have hcoe := congrArg
    (fun η : IrreducibleCharacter ↥(huSub data) => (η : ClassFunction ↥(huSub data) ℂ)) hg
  simpa [IrreducibleCharacter.coe_conjBy, χc] using hcoe

/-- **`Odd |S|`** for the maximal subgroup `S` of the minimal simple group `G` of odd order
(issue 1017, subcoherence input for the §9 induced family).  `|S| ∣ |G|` (subgroup) and `|G|` is odd
(`hG.odd`), so `|S|` is odd — the hypothesis `sSet_hasNoRealCharacters` (the (5.2.a) realness input)
needs. -/
theorem Hypothesis.oddCardS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Odd (Nat.card ↥hyp.S) := by
  rcases hG.odd with ⟨k, hk⟩
  -- From `|S| ∣ |G|` and `|G|` odd, deduce `|S|` odd (a divisor of an odd number is odd).
  have hdvd : Nat.card ↥hyp.S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.S
  rcases Nat.even_or_odd (Nat.card ↥hyp.S) with heven | hodd
  · exfalso
    have h2 : (2 : ℕ) ∣ Nat.card G := (even_iff_two_dvd.mp heven).trans hdvd
    rw [hk] at h2
    omega
  · exact hodd

open OddOrder.Peterfalvi.S11 in
/-- **The per-irreducible-member Dade `CharacterDifferenceImage` for a `𝒮 = sSet`-member**
(Peterfalvi (5.3.a) R-datum, issue 1017 Part B).  Given an irreducible source `ξ ∈ 𝒳` whose induced
`Ind_{HU}^S ξ` is **itself irreducible** (the irreducible sub-family of the mixed §9 family — the
reducible residues `μ_j` are handled separately, as a `CharacterPsiDecomposition.imageFamily` of
variable length, *not* through this 2-element `CharacterDifferenceImage`), this packages the signed
difference image `(Ind ξ − (Ind ξ)̄)^τ = ±(μ − ν)` under the honest (13.2.e) Dade map
`τ = dadeIntegralCharacterMap (dadeHypS hG) …`.

Assembled entirely from landed inputs:
* the Dade hypothesis `dadeHypS hG` and its `HConjInvariant` `dadeHypS_hconj hG`;
* the member's non-realness `sSet_hasNoRealCharacters` (needs `oddCardS`);
* the difference support `sSet_member_diffsupp` (`((Ind ξ)̄ − Ind ξ).support ⊆ A(S)`),
  fed through `dadeCharacterDifferenceImageOfDiff`.

This is the exact `S`-instance analogue of the §14 `R1cdi` (`S14_MaximalI.lean:744`), which builds
the same per-member R-datum for the (12.2) family via `dadeCharacterDifferenceImageOfDiff`.  It is
the per-member piece that `S07.irrSubcoherent` consumes on the irreducible sub-family (the (9.11)
base + Galois glue), and the (9.11) pair-adjoining induction consumes (as `Da`/`Dmem` decomposition
data) for the whole family. -/
noncomputable def Hypothesis.sSet_member_differenceImage [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥hyp.S) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      (induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)) := by
  -- Bundle the (irreducible) member as an `IrreducibleCharacter ↥S`.
  set φ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S :=
    ⟨induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ), hirr⟩ with hφ_def
  -- Non-realness of the member (the `¬IsReal` input), from the family property + `Odd |S|`.
  have hreal : ¬ ClassFunction.IsReal (φ : ClassFunction ↥hyp.S ℂ) :=
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) ⟨ξ, hξ, rfl⟩
  -- The difference support `((φ)̄ − φ).support ⊆ supportInSubgroup A(S) S` (the `hdiffsupp` input).
  have hdiffsupp :
      ((φ : ClassFunction ↥hyp.S ℂ).conj - (φ : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hyp.sSet_member_diffsupp hG hξ
  -- Package via the general (5.3.a) Dade R-datum constructor.
  exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
    (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) φ hreal hdiffsupp

open OddOrder.Peterfalvi.S11 in
/-- **The uniform-degree irreducible sub-family `S₁(d) = {φ ∈ 𝒮 | φ irreducible, φ(1) = d}`**
(issue 1017, the (9.11) base / Galois glue per update #17).  The honest §9 family `𝒮 = sSet` is
*mixed*-degree — both across the `p−1` reducible residues `μ_j` and across the irreducible members
`Ind ξ` of source degree `ξ(1)` (degree `q·ξ(1)`).  Since the (0099) weakening, the
(5.2)-subcoherence `S07.Hypothesis` *is* instantiable on mixed-degree families (its
`tau_isometry_diff` field only demands the isometry on the `A(S)`-supported sublattice `ℤ[S, A]`);
what still needs equal degrees is the **(5.7) equal-degree coherence producer**
(`coherent_of_constant_degree`'s `hconst`/`hsuppdiff` inputs — member differences must vanish at
`1`).  Fixing a single degree value `d` carves out the uniform-degree conjugate-closed irreducible
sub-family on which that producer fires; the (9.11) base case (`d = q·a`) and the whole Galois case
(`d = q·u`) are the two instances the coherence route consumes. -/
noncomputable def Hypothesis.sSetIrrDeg [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (d : ℂ) : Set (ClassFunction ↥hyp.S ℂ) :=
  { φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) |
      OddOrder.RepresentationTheory.IsIrreducibleCharacter φ ∧ (φ : ↥hyp.S → ℂ) 1 = d }

open OddOrder.Peterfalvi.S11 in
theorem Hypothesis.sSetIrrDeg_subset_sSet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (d : ℂ) :
    hyp.sSetIrrDeg hG d ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := fun _ h => h.1

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)` is closed under complex conjugation** (issue 1017, extracted from
`sSetIrrDeg_subcoherent`'s `hconj` input).  For `φ ∈ S₁(d)`: `φ̄ ∈ 𝒮` (`sSet_closedUnderConjugate`),
`φ̄` is irreducible (`IsIrreducibleCharacter.conj`), and `φ̄(1) = star (φ(1)) = star d = d`
(uses `hd : star d = d`).  This is the (A)-engine / (5.3.a) `hconj` input for the uniform
sub-family, and (via `sSetIrrDeg_member_diff_supported`) the `χ̄ ∈ S₁(d)` witness of the
`hconjsupp` / `hsupp` inputs. -/
theorem Hypothesis.sSetIrrDeg_closedUnderConjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ) (hd : star d = d) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.sSetIrrDeg hG d) := by
  intro φ hφ
  refine ⟨sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hφ.1, hφ.2.1.conj, ?_⟩
  rw [ClassFunction.conj_apply, hφ.2.2, hd]

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)` has no real members** (issue 1017, extracted from `sSetIrrDeg_subcoherent`'s `hreal`
input): the §9 no-real fact `sSet_hasNoRealCharacters` (via `oddCardS`), restricted to `S₁(d) ⊆ 𝒮`.
The (A)-engine / (5.3.a) `hnoReal` input for the uniform sub-family. -/
theorem Hypothesis.sSetIrrDeg_hasNoRealCharacters [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.sSetIrrDeg hG d) :=
  (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG)).mono
    (hyp.sSetIrrDeg_subset_sSet hG d)

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-members are supported in `A(S) ∪ {1}`** (issue 1017, extracted from the `hmem_supp`
local of `sSetIrrDeg_subcoherent`/`sSetIrrDeg_coherent`).  A member `φ = Ind_{HU}^S ξ` has
`φ.support ⊆ A(S) ∪ {1}` by the honest (4.7) support fact `sSet_member_support_subset_A`. -/
theorem Hypothesis.sSetIrrDeg_member_support_subset [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ)
    {φ : ClassFunction ↥hyp.S ℂ} (hφ : φ ∈ hyp.sSetIrrDeg hG d) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S ∪ {1} := by
  obtain ⟨hφsSet, _⟩ := hφ
  obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
  rw [hφeq]
  exact hyp.sSet_member_support_subset_A hG hξ

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-member differences are `A(S)`-supported** (issue 1017, extracted from the
`hdiff_of_mem` local of `sSetIrrDeg_subcoherent` / the `hsuppdiff` local of `sSetIrrDeg_coherent`).
For `x, y ∈ S₁(d)` (hence `x(1) = d = y(1)`), the difference `x − y` vanishes at `1`, so its support
avoids `{1}` and lands in `A(S)` (`sSetIrrDeg_member_support_subset` minus the identity).  This is
the (A)-engine `hsupp` (with `y = x̄`) and the (5.3.a) `hconjsupp` / (5.7) `hsuppdiff` input. -/
theorem Hypothesis.sSetIrrDeg_member_diff_supported [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ)
    {x : ClassFunction ↥hyp.S ℂ} (hx : x ∈ hyp.sSetIrrDeg hG d)
    {y : ClassFunction ↥hyp.S ℂ} (hy : y ∈ hyp.sSetIrrDeg hG d) :
    (x - y).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
  intro z hz
  have hz0 : (x - y) z ≠ 0 := hz
  have hdeg : (x : ↥hyp.S → ℂ) 1 = (y : ↥hyp.S → ℂ) 1 := by rw [hx.2.2, hy.2.2]
  rcases (ClassFunction.support_sub_subset x y hz) with h | h
  · rcases hyp.sSetIrrDeg_member_support_subset hG d hx h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSetIrrDeg_member_support_subset hG d hy h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)` is finite** (issue 1017, extracted from `sSetIrrDeg_coherent`'s `hSfin`): the family
injects into `IrreducibleCharacter ↥S` (a `Finite` type) via its irreducibility field. -/
theorem Hypothesis.sSetIrrDeg_finite [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ) :
    (hyp.sSetIrrDeg hG d).Finite := by
  apply Set.Finite.subset (Set.finite_range
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
      (χ : ClassFunction ↥hyp.S ℂ)))
  rintro φ ⟨_, hirr, _⟩
  exact ⟨⟨φ, hirr⟩, rfl⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The `S07.Hypothesis` (5.2)-subcoherence structure for the uniform-degree irreducible
sub-family `S₁(d)`** (issue 1017, update #17 — the first honest stage of the (9.11) coherence route).
Assembled from the honest (13.2.e) Dade isometry `τ = Ind_S^G` (`dadeHypS`) and the landed
Dade-independent family inputs:
* `Rdatum` = `sSet_member_differenceImage` per irreducible member;
* `hconj` = `sSet_closedUnderConjugate` (conj of an irreducible degree-`d` member is again one — the
  conjugate `φ̄` is irreducible with `φ̄(1) = conj(φ(1)) = d` as `d = q·s` is a positive real);
* `hreal` = `sSet_hasNoRealCharacters` (via `oddCardS`), restricted to `S₁(d) ⊆ 𝒮`;
* `hortho` = `sSet_pairwiseOrthogonal`, restricted to `S₁(d) ⊆ 𝒮`;
* `hconjsupp` = conjugate differences `χ − χ̄` are `A(S)`-supported: `χ̄ ∈ S₁(d)` (conj-closedness,
  `star d = d`) and equal degrees make the difference vanish at `1`
  (`sSet_member_support_subset_A` minus the identity);
* `hiso` = the (0099) `zSupportedSpan`-form lattice isometry, unconditional from the Dade pair
  brick `dadeIntegralCharacterMap_inner_eq_of_supported` (only the supportedness halves are used).

The `hconj` field requires `d` to be real (`star d = d`); this holds for the genuine degree values
`d = q·s` (positive natural), supplied by the caller.  This is the (5.3.a) subcoherence hypothesis on
a uniform-degree family, ready for `coherent_subset_of_constant_degree` (the (9.11) base + Galois). -/
noncomputable def Hypothesis.sSetIrrDeg_subcoherent [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    (d : ℂ) (hd : star d = d) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.S) (G := G)
      (hyp.sSetIrrDeg hG d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) := by
  classical
  -- The honest (13.2.e) Dade isometry `τ = Ind_S^G`.
  set τ := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
    ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) with hτ
  -- Conjugation stability of `S₁(d)` (uses `star d = d`), extracted as
  -- `sSetIrrDeg_closedUnderConjugate`.
  have hconjmem := hyp.sSetIrrDeg_closedUnderConjugate hG d hd
  refine OddOrder.Peterfalvi.S07.irrSubcoherent τ
    (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)
    (fun φ hφ => ?_) ?_ ?_ ?_ ?_ ?_
  · -- `Rdatum`: `φ ∈ S₁(d) ⇒ ∃ ξ ∈ 𝒳, φ = Ind ξ` (irreducible).  The `∃` witness is extracted via
    -- `choose` (not `obtain`) so it may be eliminated into the data goal `CharacterDifferenceImage`.
    have hφsSet : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) := hφ.1
    have hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ := hφ.2.1
    obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
    rw [hφeq] at hirr ⊢
    exact hyp.sSet_member_differenceImage hG hξ hirr
  · -- `hconj`: conjugate of a degree-`d` irreducible member of `𝒮` is again one (uses `star d = d`).
    exact hconjmem
  · -- `hreal`: no real members, restricted to `S₁(d) ⊆ 𝒮` (`sSetIrrDeg_hasNoRealCharacters`).
    exact hyp.sSetIrrDeg_hasNoRealCharacters hG d
  · -- `hortho`: pairwise orthogonal, restricted to `S₁(d) ⊆ 𝒮`.  The `FiniteInduce`-scoped instances
    -- baked into `sSet_pairwiseOrthogonal`'s `inner` are (subsingleton-)equal to the section ones.
    intro φ ψ hφ hψ hne
    convert sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hφ.1 hψ.1 hne using 2 <;>
      exact Subsingleton.elim _ _
  · -- `hconjsupp`: the conjugate difference `χ − χ̄` is `A(S)`-supported (`χ̄ ∈ S₁(d)` + equal degree),
    -- extracted as `sSetIrrDeg_member_diff_supported` (with `y = χ̄`).
    intro χ hχ
    exact hyp.sSetIrrDeg_member_diff_supported hG d hχ (hconjmem hχ)
  · -- `hiso`: the (0099) `zSupportedSpan`-form lattice isometry — unconditional from the Dade
    -- pair brick (only the supportedness halves of the `ℤ[S₁(d), A(S)]` memberships are used).
    intro φ ψ hφ hψ
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hφ.2 hψ.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) base / Galois coherence of the uniform-degree irreducible sub-family `S₁(d)`**
(issue 1017, update #18 — the honest (9.11) base coherence).  Feeds the landed subcoherence
`sSetIrrDeg_subcoherent` into `coherent_subset_of_constant_degree` (Peterfalvi (5.7)∘(5.3.a),
`S07_Subcoherent.lean:246`) with `S' = S = sSetIrrDeg d` (the uniform subset of itself), producing
`Nonempty (IsCoherent τ (S₁ d) A)` for the honest Dade map `τ = Ind_S^G` (`dadeHypS`) and support
`A(S)`.  This is the whole **Galois case** (`d = q·u`) and the **base case `S₁`** (`d = q·a`) of the
(9.11) `Ptype_core_coherence` derived-series induction (Coq `PFsection9.v:1484`).

The `coherent_subset_of_constant_degree` hypotheses discharge as follows, all *internally* from the
landed §9 family lemmas — **except `hcard` (≥ 2 membership)**, which is *exposed as a parameter*
`h2`: no `2 ≤ (S₁ d).ncard` fact exists yet in the repo (the degree-`d` count is the §9 (9.8.d)
counting content — `caseA_exists_irreducible_source_degree_qa`, `S11:6437`, and its `M`-induction
strengthening at `S11:12250`, give an *existence* `∃ ζ`, not two distinct members).  Exposing it
keeps this def sorry-free and defers the genuine upstream count to the caller — the honest pattern.

Internal discharges:
* `hconj'` = `sSetIrrDeg_subcoherent`'s own `.conjugate_closed` field (conj of a degree-`d`
  irreducible member is again one, uses `star d = d`);
* `hSfin` = `S₁ d ⊆ range (IrreducibleCharacter.toClassFunction)` (finite range of a `Finite` type);
* `hirr` = `IsIrreducibleCharacter.inner_self_eq_one` (each member is irreducible by definition);
* `hZIrr` = `dadeIntegralCharacterMap_mem_ZIrr_of_supported` — the member difference `a − b` is
  `A(S)`-supported (equal degree, vanishes at `1`) and a virtual character (difference of two
  irreducibles), so the honest Dade map sends it into `ℤ[Irr G]`;
* `hconst` = definitional uniform degree `φ(1) = d`;
* `hdeg0` = exposed `d ≠ 0`;
* `h1A` = `honestTypeP2ASet_one_not_mem` (`1 ∉ A(S)`);
* `hsuppdiff` = the equal-degree two-member support fact (member differences `A(S)`-supported),
  the same argument `sSetIrrDeg_subcoherent`'s `hiso` uses internally. -/
noncomputable def Hypothesis.sSetIrrDeg_coherent [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    (d : ℂ) (hd : star d = d) (hd0 : d ≠ 0)
    (h2 : 2 ≤ (hyp.sSetIrrDeg hG d).ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      (hyp.sSetIrrDeg hG d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  classical
  set A := OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S with hA
  -- The landed (5.3.a) subcoherence structure on `S₁(d)`; its `.tau` is the honest Dade map.
  set hyp' := hyp.sSetIrrDeg_subcoherent hG d hd with hhyp'
  -- `hSfin`: `S₁(d)` injects into `IrreducibleCharacter ↥S` (a `Finite` type) — `sSetIrrDeg_finite`.
  have hSfin : (hyp.sSetIrrDeg hG d).Finite := hyp.sSetIrrDeg_finite hG d
  -- `hirr`: each member is an irreducible character, so has self-inner `1`.
  have hirr : ∀ ζ ∈ hyp.sSetIrrDeg hG d, ClassFunction.inner ζ ζ = 1 :=
    fun ζ hζ => hζ.2.1.inner_self_eq_one
  -- `hconst`: uniform degree `φ(1) = d` (definitional membership).
  have hconst : ∀ a ∈ hyp.sSetIrrDeg hG d, ∀ b ∈ hyp.sSetIrrDeg hG d,
      ((a : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 = ((b : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 :=
    fun a ha b hb => by rw [ha.2.2, hb.2.2]
  -- `hdeg0`: nonzero degree (exposed `d ≠ 0`).
  have hdeg0 : ∀ a ∈ hyp.sSetIrrDeg hG d, ((a : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 ≠ 0 :=
    fun a ha => by rw [ha.2.2]; exact hd0
  -- `h1A`: `1 ∉ A(S)`.
  have h1A : (1 : ↥hyp.S) ∉ A := by
    rw [hA, OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    simpa using honestTypeP2ASet_one_not_mem (M := hyp.S)
  -- `hsuppdiff`: for `x, y ∈ S₁(d)`, `(x − y).support ⊆ A(S)` (equal degree ⇒ vanish at `1`);
  -- extracted as `sSetIrrDeg_member_diff_supported` (also the (5.3.a) `hconjsupp` input).
  have hsuppdiff : ∀ x ∈ hyp.sSetIrrDeg hG d, ∀ y ∈ hyp.sSetIrrDeg hG d,
      ((x - y : ClassFunction ↥hyp.S ℂ)).support ⊆ A := by
    intro x hx y hy
    exact hyp.sSetIrrDeg_member_diff_supported hG d hx hy
  -- `hZIrr`: the honest Dade map sends `A(S)`-supported virtual-character differences into `ℤ[Irr G]`.
  have hZIrr : ∀ a ∈ hyp.sSetIrrDeg hG d, ∀ b ∈ hyp.sSetIrrDeg hG d,
      hyp'.tau (a - b) ∈ OddOrder.RepresentationTheory.ZIrr G := by
    intro a ha b hb
    have hab_supp : (a - b : ClassFunction ↥hyp.S ℂ).support ⊆ A := hsuppdiff a ha b hb
    have hab_Z : (a - b : ClassFunction ↥hyp.S ℂ) ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
      Submodule.sub_mem _ ha.2.1.mem_ZIrr hb.2.1.mem_ZIrr
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hab_supp hab_Z
  -- Fire the (5.7)∘(5.3.a) uniform-degree coherence producer on `S' = S = S₁(d)`.
  exact OddOrder.Peterfalvi.S07.coherent_subset_of_constant_degree hyp'
    (subset_refl _) hyp'.conjugate_closed hSfin h2 hirr hZIrr hconst hdeg0 h1A hsuppdiff

open scoped FiniteInduce in
/-- **(9.11) base / Galois coherence of `S₁(d)`, re-grounded onto the induction map `τ = Ind_S^G`**
(issue 1017, update #19 — the honest-`indS` re-grounding of `sSetIrrDeg_coherent`).  The landed
uniform-degree coherence `sSetIrrDeg_coherent` produces `IsCoherent τ (S₁ d) A(S)` for the honest
Dade map `τ = dadeIntegralCharacterMap (dadeHypS hG) …`; but the (13.3) consumers — the (A) engine
`S15.coherentIndS_image_inner_eta_eq_zero` and (ultimately) `coherent_H0Cprime_S` — want the
coherence phrased with the plain induction map `hyp.indS = Ind_S^G` (Peterfalvi (13.2.e)).

The two maps **agree on every `A(S)`-supported class function**
(`sInstance_dade_eq_induce`, the honest (13.2.e) `normedTI` isometry half, Rungs B+C), and
`S07.IsCoherent` depends on its map *only* through `extends_on_supported` (whose domain is
`zSupportedSpan (S₁ d) A(S)`, every member of which is `A(S)`-supported by definition), so the
general `S07.IsCoherent.congrMap` re-targets the coherence onto `indS` with no further analytic
input.  This is the `indS`-form the honest (9.11) route delivers to the (A) engine; once the
(9.11.1)–(9.11.8) pair-adjoining induction lifts it from the uniform sub-family to the full `sSet`,
the same `congrMap` step re-grounds `coherent_H0Cprime_S` off the unsound `sibleyTarget_H0C`.

All finiteness instances are taken from the `FiniteInduce` scope (from `[Finite G]`), so the
`Ind_S^G` produced here (via `indS`) and the one `sInstance_dade_eq_induce` names share the *same*
`Fintype ↥S` instance — no subsingleton-instance juggling is needed. -/
theorem Hypothesis.sSetIrrDeg_coherent_indS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (d : ℂ) (hd : star d = d) (hd0 : d ≠ 0)
    (h2 : 2 ≤ (hyp.sSetIrrDeg hG d).ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (hyp.sSetIrrDeg hG d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) :=
  (hyp.sSetIrrDeg_coherent hG d hd hd0 h2).map fun c =>
    c.congrMap fun φ hφ => by
      rw [hyp.indS_apply]
      exact hyp.sInstance_dade_eq_induce hG hφ.2

open OddOrder.Peterfalvi.S11 in
/-- **(9.11) base cardinality `2 ≤ (S₁(q·a)).ncard`** in the non-Galois case (issue 1017, Step 2 —
the honest discharge of `sSetIrrDeg_coherent`/`sSetIrrDeg_coherent_indS`'s exposed `h2` at the base
degree `d = q·a`).

Coq `PFsection9.v:1537-1551` needs only `0 < size S1` for the uniform base `S1 = {ζ ∈ 𝒮 | ζ(1) =
q·a}`: since `𝒮` is conjugate-closed and has no real members, a single member `χ` and its distinct
conjugate `χ̄` give `size S1 ≥ 2`.  The single member comes from the **positive** (9.8.d) count
`caseA_exists_irreducible_qa` — `(p−1)/a ≥ 1` since `a ∣ p−1` (`CliffordCaseAData.a_dvd_p_sub_one`)
and `[C_U(S₀):U′] ≥ 1` — whose witness lies in `𝒮(H₀U′) ⊆ 𝒮` (`sOf_subset_sSet`); conjugate-closure
(`sSetIrrDeg_closedUnderConjugate`, `q·a` a positive real so `star d = d`) and non-realness
(`sSetIrrDeg_hasNoRealCharacters`) then double it.

Given a `CliffordCaseAData` for the `S`-instance §9 data (the non-Galois case assumption), this
discharges the `h2` parameter of `sSetIrrDeg_coherent_indS` at the base degree `d = q·a`, un-gating
the uniform base coherence (whose downstream is the (A)-engine orthogonality
`S15.sSetIrrDeg_coherentIndS_image_inner_eta_eq_zero`).  In the Galois case (caseB) the whole
family is uniform of degree `q·u`, so no such base-count is needed. -/
theorem Hypothesis.sSetIrrDeg_qa_two_le_ncard [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) :
    2 ≤ (hyp.sSetIrrDeg hG
        (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)).ncard := by
  classical
  -- (9.8.d) existence of one degree-`q·a` irreducible member of `𝒮(H₀U′) ⊆ 𝒮`.
  obtain ⟨χ, hχSOf, hχirr, hχdeg⟩ := caseA_exists_irreducible_qa hG chars caseA
  set d : ℂ := (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) with hd_def
  have hd : star d = d := by rw [hd_def]; exact star_natCast _
  rw [chars.SOf_eq] at hχSOf
  have hχ : χ ∈ hyp.sSetIrrDeg hG d :=
    ⟨sOf_subset_sSet _ _ hχSOf, hχirr, hχdeg⟩
  -- `χ̄ ∈ S₁(d)` (conj-closed) and `χ ≠ χ̄` (no real members).
  have hχc : χ.conj ∈ hyp.sSetIrrDeg hG d := hyp.sSetIrrDeg_closedUnderConjugate hG d hd hχ
  have hne : χ ≠ χ.conj := fun heq =>
    hyp.sSetIrrDeg_hasNoRealCharacters hG d hχ heq.symm
  -- `{χ, χ̄} ⊆ S₁(d)` has two distinct members.
  calc 2 = ({χ, χ.conj} : Set (ClassFunction ↥hyp.S ℂ)).ncard := (Set.ncard_pair hne).symm
    _ ≤ (hyp.sSetIrrDeg hG d).ncard :=
        Set.ncard_le_ncard (Set.insert_subset hχ (Set.singleton_subset_iff.mpr hχc))
          (hyp.sSetIrrDeg_finite hG d)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) non-Galois base coherence of `S₁(q·a)` on `Ind_S^G`, fully un-gated** (issue 1017,
Step 2 — the `h0` entry point of the pair-adjoining lift).  Combines the uniform base coherence
`sSetIrrDeg_coherent_indS` with the base-count discharge `sSetIrrDeg_qa_two_le_ncard`, so the
exposed `hd`/`hd0`/`h2` parameters are all discharged from the `S`-instance §9 caseA data:
`star (q·a) = q·a` (positive real, `star_natCast`), `q·a ≠ 0` (`data.q > 0` = `Nat.card_pos`,
`caseA.a_pos`), and `2 ≤ ncard` (the (9.8.d) count + conjugacy doubling).

This is the base coherence `h0` that Peterfalvi's (9.11) pair-adjoining induction (Coq
`Ptype_core_coherence`, `coherentPairChain`/`coherentOfPairChainCover`) starts from, for the honest
type-`P₂` `S`.  The remaining lift steps to the full `𝒮 = sSet` are the degree-monotone
decomposition (`hpairs`/`hcover`, the reducible `μ_j` via `CharacterPsiDecomposition` and the
irreducible conjugate pairs via `CharacterDifferenceImage`) and the per-pair (5.6)/(9.11.5) retarget
(`Snorm`/`sumnS` squeeze + `xAdjoinStepW`), all keeping `S₀ = S₁(q·a)` as the anchor prefix.  In the
Galois case (caseB) the whole family is uniform of degree `q·u`, coherent directly by
`sSetIrrDeg_coherent_indS` (no lift). -/
theorem Hypothesis.sSetIrrDeg_qa_coherent_indS_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  have hqpos : 0 < (hyp.toTypesIIIIIIVSetupS hG).q := Nat.card_pos
  exact hyp.sSetIrrDeg_coherent_indS hG _ (star_natCast _)
    (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hqpos.ne' caseA.a_pos.ne'))
    (hyp.sSetIrrDeg_qa_two_le_ncard hG chars caseA)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) non-Galois-branch coherence of the full family `𝒮 = sSet` on `Ind_S^G`** (issue 1017,
caseA of Peterfalvi (9.11) `Ptype_core_coherence`, Coq `PFsection9.v:1484`).  In the non-Galois case
(`CliffordCaseAData`) the honest §9 family `𝒮 = sSet` is **genuinely mixed-degree**: the degree-`q·a`
irreducibles fill `𝒮(H₀U′)` (at least `((p−1)/a)·(|U|/(a|U′|))` of them, `caseA_character_counts` /
`caseA_exists_irreducible_qa`) alongside the degree-`q·u` members of `𝒮(H₀C)` (the `p−1` reducible
μ_j residues plus an irreducible).

Honest route (the pieces landed so far):
* **base `h0`** = the degree-`q·a` irreducible cut `S₁(q·a)` is coherent on `Ind_S^G`
  (`sSetIrrDeg_qa_coherent_indS_caseA`, **landed sorry-free** modulo the accepted `dadeHypS` Dade
  foundation) — the anchor prefix of the (9.11) induction;
* **lift** = adjoin the higher-degree irreducible conjugate pairs `{χ, χ̄}` (per-member R-datum
  `sSet_member_differenceImage`, landed) and the `p−1` reducible μ_j columns (as
  `CharacterPsiDecomposition`/`OrthonormalCharacterImageFamily`) one at a time, retargeting each step
  by the `Snorm`/`sumnS` squeeze (`S07_Subcoherent.lean`, landed) + `xAdjoinStepW`, and folding by
  `coherentOfPairChainCover` (`S07_Coherence`, CoherenceUnion) — the (9.11.1)–(9.11.8) maximality
  induction (arithmetic bricks in `S11_NineElevenCoherence.lean`, landed).

The residual is the `S`-instance degree-monotone member enumeration (`hpairs`/`hcover`) and the
per-adjoin retarget data (`hstep`) for the honest Dade world (`indS`, `A(S)`) — the multi-step
family-specific assembly mirroring lane-a's M-instance `caseB_coherent_sOf_H0Cprime_of_mixed`
(`S13_MaximalIII_IV.lean:1033`).  Sorried-cite here as the honest (9.11) non-Galois statement pending
that assembly; the base and all arithmetic are landed. -/
theorem Hypothesis.sSet_coherent_indS_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  -- Base coherence `h0 = sSetIrrDeg_qa_coherent_indS_caseA` (landed) anchors the pair-adjoining
  -- induction; the lift to the full mixed family `𝒮 = sSet` (`coherentOfPairChainCover` over the
  -- reducible μ_j columns + higher-degree conjugate pairs) is the remaining (9.11.1)–(9.11.8) work.
  sorry

/-- **Peterfalvi (13.2.b), order part**: the Fitting kernel `P = S_F` has order `p^q`.

This is the order half of (13.2.b) ("`P` is elementary abelian of order `p^q`").  `S` is of Type II
from the κ-Hall carrier `S_typeP2` (`isTypeII_of_isTypeP2`), so §11's Wielandt fixed-point order
relation `typeII_III_IV_order_relations` (Peterfalvi (9.3)) applies to the type-II setup on `S` with
`typeP := Sdata`, giving `|S_F| = |W₂|^q`.

The one input not derivable from the bare `Hypothesis` fields is the reconciliation `Sdata.W2 = W2`
between the *intrinsic* type-`P` `W₂` of `S` (`Sdata.W2 = C_{S'}(W₁#)`) and the abstract `W₂`
(complement of `W₁` in the cyclic `W = S ∩ T`) — the `W₂`-analogue of the carried
`Sdata_U_eq` / `Sdata_W1_eq`.  It is honest §16-carrier content (`Section16TypePStructure`, which
builds `Sdata`); taken here as an explicit hypothesis so the order computation is unconditional on
its proof.  See issue 3001 for threading it through the carrier (then `basic_structure_gated`'s
`P_order` field discharges). -/
theorem Hypothesis.card_P_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hSdataW2 : hyp.Sdata.W2 = hyp.W2) :
    Nat.card ↥hyp.P = hyp.p ^ hyp.q := by
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  -- (9.3) Wielandt order relation for the type-II setup on `S` (`toTypesIIIIIIVSetupS`).
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    (hyp.toTypesIIIIIIVSetupS hG)).1 hSII
  have hord2 : Nat.card ↥hyp.Sdata.H
      = Nat.card ↥hyp.Sdata.W2 ^ Nat.card ↥hyp.Sdata.W1 := hord.2
  have hW2card : Nat.card ↥hyp.Sdata.W2 = hyp.p := by
    rw [hSdataW2, ← hyp.p_eq_card_W2]
  rw [hyp.Sdata.H_eq, ← hyp.P_eq_SF, hW2card, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at hord2
  exact hord2

/-- **The `S`-instance chief kernel `N` is trivial**: `P = S_F` has order `p^q`
(`card_P_eq`), and the chief factor `H̄ = P/H₀ ≅ ↥P ⧸ N` already has order `(chief.p)^q`
(`chiefFactor_quotient_card`), so `chief.p = p` and `|N| = 1`, i.e. `N = ⊥`.  Thus `↥P ⧸ N ≅ ↥P`
— `P` itself is the chief factor.  The source of both `H₀ = ⊥` (below) and `cSub = C_U(P) = C`
(the `C_U(H̄) = C_U(P)` identification once `H̄ = P`). -/
theorem Hypothesis.toTypesIIIIIIVSetupS_chief_N_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.N = ⊥ := by
  haveI := chief.N_normal
  have hHeq : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    show hyp.Sdata.H = hyp.P
    rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    show Nat.card ↥hyp.Sdata.W1 = hyp.q
    rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [show ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P from hHeq]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hq] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  -- `p^q = chief.p^q · |N|` forces `chief.p = p` and `|N| = 1`
  have hdvd : chief.p ∣ hyp.p ^ hyp.q := by
    refine dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.p :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  rw [hpp] at hsplit
  have hN1 : Nat.card ↥chief.N = 1 := by
    have := hsplit.symm
    nlinarith [Nat.card_pos (α := ↥chief.N), pow_pos hyp.p_prime.pos hyp.q]
  exact Subgroup.card_eq_one.mp hN1

/-- **The `S`-instance chief `H₀` is trivial** (`toTypesIIIIIIVSetupS_chief_N_eq_bot`, mapped):
`H₀ = N.map subtype = ⊥`.  Collapses the §9 families of the `S`-instance (`𝒳(H₀) = 𝒳(⊥)`), making
the (13.3.a) kernel condition `H₀ ⊆ Ker χ_j` automatic. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_chief_H0_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.H0 = ⊥ := by
  rw [chief.H0_eq, hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief]
  exact Subgroup.map_bot _

/-- **A subgroup of coprime `p`-order lies in a normal subgroup of `p`-coprime index.**  If
`W ≤ S`, `P.subgroupOf S ⊴ S`, `p` is coprime to `[S : P]`, and every `w ∈ W` has order dividing
`p`, then `W ≤ P`: each `w`'s image in `S/P` has order dividing both `p` and `[S : P]`, hence `1`.
This is the substantive core of `pgroup_le_of_normal_coprime_index`, taking the prime-vs-index
coprimality **directly** (so it applies when `p ∣ |P|` is unknown/false but `p ∤ [S : P]`, e.g. to
place `W₁` — of order `q ≠ p` — inside `T'` whose index is `p`). -/
theorem subgroup_le_of_normal_coprime_index_prime [Finite G]
    {S P W : Subgroup G} {p : ℕ}
    (hWS : W ≤ S) (hPnorm : (P.subgroupOf S).Normal)
    (hcop : Nat.Coprime p (P.subgroupOf S).index)
    (hWp : ∀ w ∈ W, orderOf w ∣ p) : W ≤ P := by
  haveI := hPnorm
  intro w hw
  have hwS : w ∈ S := hWS hw
  have horder : orderOf w ∣ p := hWp w hw
  have hmk : QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩ = 1 := by
    rw [← orderOf_eq_one_iff]
    have hd1 : orderOf (QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩) ∣ p := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [show orderOf (⟨w, hwS⟩ : ↥S) = orderOf w from
        (orderOf_injective S.subtype Subtype.coe_injective ⟨w, hwS⟩).symm]
      exact horder
    have hd2 : orderOf (QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩) ∣
        (P.subgroupOf S).index := orderOf_dvd_natCard _
    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
  have hmem : (⟨w, hwS⟩ : ↥S) ∈ P.subgroupOf S := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact hmk
  rwa [Subgroup.mem_subgroupOf] at hmem

/-- **A `p`-subgroup lies in a normal subgroup of coprime-to-`p` index.**  If `W ≤ S`,
`P.subgroupOf S ⊴ S`, `[S : P]` is coprime to `|P|`, and `p ∣ |P|`, then every element of `W` of
order dividing `p` lies in `P`: its image in `S/P` has order dividing both `p` and `[S : P]`, hence
`1`.  Generic group theory (used to place the prime-order factors `W₁`, `W₂` inside the Fitting
kernels `Q`, `P`).  Reduces to `subgroup_le_of_normal_coprime_index_prime` via `Coprime |P| [S:P]`
and `p ∣ |P|` ⟹ `p ∤ [S:P]` ⟹ `Coprime p [S:P]`. -/
theorem pgroup_le_of_normal_coprime_index [Finite G]
    {S P W : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hWS : W ≤ S) (hPnorm : (P.subgroupOf S).Normal)
    (hcop : Nat.Coprime (Nat.card ↥P) (P.subgroupOf S).index)
    (hpP : p ∣ Nat.card ↥P) (hWp : ∀ w ∈ W, orderOf w ∣ p) : W ≤ P := by
  have hcop2 : Nat.Coprime p (P.subgroupOf S).index :=
    (hp.coprime_iff_not_dvd).mpr fun hdvd =>
      Nat.Prime.not_dvd_one hp (hcop ▸ Nat.dvd_gcd hpP hdvd)
  exact subgroup_le_of_normal_coprime_index_prime hWS hPnorm hcop2 hWp

/-- **Peterfalvi (13.2.b)/(14.2.a): `W₂ ≤ P`.**  `W₂` is a `p`-group (`|W₂| = p`) inside `S`
(`W₂ ≤ W = S ⊓ T ≤ S`), while `P = S_F` is the normal Hall `p`-subgroup of `S` of order `p^q`
(`basic_structure`); hence `W₂ ≤ P` — the `F_p ⊆ F` identification of (14.2.a). -/
theorem W2_le_P [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W2 ≤ hyp.P := by
  have hP_card : Nat.card ↥hyp.P = hyp.p ^ hyp.q := hyp.card_P_eq _hG hyp.Sdata_W2_eq
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  refine pgroup_le_of_normal_coprime_index (S := hyp.S) hyp.p_prime ?_ ?_ ?_ ?_ ?_
  · have h1 : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have h2 : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
    exact h1.trans h2
  · rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.S
  · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
    rw [← hyp.P_eq_SF] at hHall
    have hcard_eq : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
    exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
  · rw [hP_card]; exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
  · intro w hw
    have heq : orderOf (⟨w, hw⟩ : ↥hyp.W2) = orderOf w :=
      (orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨w, hw⟩).symm
    have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W2) ∣ Nat.card ↥hyp.W2 := orderOf_dvd_natCard _
    rw [heq, ← hyp.p_eq_card_W2] at h1
    exact h1

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **`μ_j ∈ 𝒮(H₀)` for the `S`-instance** ((13.3.a) membership): the nonzero `μ`-column sum
lies in the §9 family `𝒮(H₀)` of `toTypesIIIIIIVSetupS`.  The (4.5.a) witness `ψ`
(`mu_colSum_eq_induce`) transports along `huSub = S'` (`huSub_eq_derivedInG_subgroupOf`,
`induce_compHom_subgroupCongr`); the `𝒳`-conditions are `H₀ = ⊥ ⊆ Ker`
(`toTypesIIIIIIVSetupS_chief_H0_eq_bot`) and `H = P ⊄ Ker` from the (4.7) `W₂`-nonkernel
conjunct with `W₂ ≤ P` (`W2_le_P`). -/
theorem Hypothesis.mu_colSum_mem_sOf_H0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    (∑ i : Fin hyp.q, hyp.mu i j)
      ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG) chief.H0 := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) :=
    Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨ψ, hψirr, hψeq, hψker⟩ := hyp.mu_colSum_eq_induce j
  have hKeq : OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)
      = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf _
  set χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ :=
    ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom ψ with hχdef
  have hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hKeq).surjective hψirr
  rw [OddOrder.Peterfalvi.S11.mem_sOf]
  refine ⟨⟨χ, hχirr⟩, ?_, ?_⟩
  · rw [OddOrder.Peterfalvi.S11.mem_xiOf]
    constructor
    · -- `H ⊄ Ker χ` (`xiSet`): a kernel containment would violate the `W₂`-nonkernel conjunct
      intro hsub
      apply hψker hj
      intro c hc
      have hcW2 : ((c : ↥hyp.S) : G) ∈ hyp.W2 :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hc))
      set x : ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) :=
        (MulEquiv.subgroupCongr hKeq).symm c with hxdef
      have hxval : ((x : ↥hyp.S) : G) = ((c : ↥hyp.S) : G) := by
        rw [hxdef]
        exact congrArg Subtype.val (MulEquiv.subgroupCongr_symm_apply hKeq c)
      have hxhInHu : x ∈ OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupS hG) := by
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
        show ((x : ↥hyp.S) : G) ∈ hyp.Sdata.H
        rw [hxval, hyp.Sdata.H_eq, ← hyp.P_eq_SF]
        exact W2_le_P hG hyp hcW2
      have hxker := hsub (SetLike.mem_coe.mpr hxhInHu)
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hxker
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
      have hxker' : χ x = χ 1 := hxker
      rw [hχdef, ClassFunction.compHom_apply, ClassFunction.compHom_apply, hxdef,
        MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] at hxker'
      exact hxker'
    · -- `H₀ = ⊥ ⊆ Ker χ`
      rw [hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief]
      intro x hx
      have hx1 : x = 1 := by
        have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp
          (SetLike.mem_coe.mp hx))
        rw [Subgroup.mem_bot] at h2
        exact Subtype.ext (Subtype.ext h2)
      rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
  · -- `∑ μ_{ij} = Ind_{HU}^S χ`
    rw [hψeq]
    have h1 : OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG) χ
        = ClassFunction.induce
            (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) χ := by
      unfold OddOrder.Peterfalvi.S11.induceHU
      congr! <;> exact Subsingleton.elim _ _
    have h2 : ClassFunction.induce ((derivedInG hyp.S).subgroupOf hyp.S) ψ
        = OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG) χ := by
      rw [h1, hχdef]
      exact (OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq ψ).symm
    exact h2

open OddOrder.Peterfalvi.S11 in
/-- **(9.9.a) uniform degree `q·u` of the full honest §9 family `𝒮 = sSet` in the Galois case**
(issue 1017, the `hdeg` input of the caseB (5.7) uniform-degree coherence engine).  In Clifford
case (b) every member of `𝒮(H₀C′)` has degree `q·u` (`caseB_degree_qu`); for the honest type-`P₂`
`S`-instance the kernel data degenerates — `chief.H₀ = ⊥` (`toTypesIIIIIIVSetupS_chief_H0_eq_bot`)
and `C′ = [C,C] = ⊥` (the chief `cprimeSub = derivedInG (cSub)`, `cSub ≤ U` abelian by
`S_U_commutative`, so its derived subgroup is `⊥` — the same argument as `Cprime_eq_bot`), so
`𝒮(H₀C′) = 𝒮(⊥) = 𝒮 = sSet` — whence **every** member of the *full* family has degree `q·u`.  This
is the uniform-degree fact that lets the (5.7) engine `uniform_degree_coherence_of_families` fire on
the whole mixed family (irreducibles + the `p−1` reducible μ_j columns, all degree `q·u`). -/
theorem Hypothesis.sSet_caseB_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {φ : ClassFunction ↥hyp.S ℂ} (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) := by
  classical
  -- `chief.H₀ = ⊥` and `C′ = ⊥`, so `chief.H₀ ⊔ chars.Cprime = ⊥` and `sSet = 𝒮(⊥) = 𝒮(H₀C′)`.
  have hH0 : chief.H0 = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief
  have hCp : chars.Cprime = ⊥ := by
    -- `C′ = cprimeSub = derivedInG (cSub)`, and `cSub ≤ U` abelian, so its derived subgroup is `⊥`.
    show OddOrder.Peterfalvi.S11.cprimeSub (hyp.toTypesIIIIIIVSetupS hG) chief = ⊥
    have hCU : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief ≤ hyp.U :=
      (OddOrder.Peterfalvi.S11.cSub_le_U _ _).trans (le_of_eq hyp.Sdata_U_eq)
    have hCab : IsMulCommutative
        ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) :=
      ⟨⟨fun a b => Subtype.ext (by
        have h := hyp.S_U_commutative.is_comm.comm
          (⟨(a : G), hCU a.2⟩ : ↥hyp.U) ⟨(b : G), hCU b.2⟩
        simpa using congrArg Subtype.val h)⟩⟩
    have hcomm : commutator
        ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := ⊥)).mpr (fun a _ b _ => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hCab.is_comm.comm a b
    show derivedInG (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) = ⊥
    rw [derivedInG, hcomm, Subgroup.map_bot]
  -- membership in the smaller `𝒮(H₀C′)` (equal to `sSet` once the kernel demand degenerates)
  have hmem : φ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime) := by
    rw [Section11CharacterData.SOf_eq, hH0, hCp, sup_bot_eq]
    obtain ⟨χ, hχ, rfl⟩ := hφ
    refine ⟨χ, ?_, rfl⟩
    rw [mem_xiOf]
    refine ⟨hχ, ?_⟩
    -- the realized `⊥` kernel demand is vacuous
    intro x hx
    have hx1 : x = 1 := by
      have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hx))
      rw [Subgroup.mem_bot] at h2
      exact Subtype.ext (Subtype.ext h2)
    rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def]
  exact caseB_degree_qu hG chars caseB φ hmem

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮 = sSet` is finite** (issue 1017, the `hSfin` input of the caseB (5.7) coherence engine):
the family injects into `IrreducibleCharacter ↥(huSub data)` (a `Finite` type) via the induction map,
so it is a subset of a finite range. -/
theorem sSet_finite {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    (sSet data).Finite := by
  apply Set.Finite.subset (Set.finite_range
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub data) =>
      induceHU data (χ : ClassFunction ↥(huSub data) ℂ)))
  rintro φ ⟨χ, -, rfl⟩
  exact ⟨χ, rfl⟩

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮`-members are supported in `A(S) ∪ {1}`** (issue 1017, the full-family analogue of
`sSetIrrDeg_member_support_subset`).  Every `φ = Ind_{HU}^S ξ ∈ 𝒮` has `φ.support ⊆ A(S) ∪ {1}` by
the honest (4.7) support fact `sSet_member_support_subset_A`. -/
theorem Hypothesis.sSet_member_support_subset [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {φ : ClassFunction ↥hyp.S ℂ} (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S ∪ {1} := by
  obtain ⟨ξ, hξ, rfl⟩ := hφ
  exact hyp.sSet_member_support_subset_A hG hξ

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮`-member differences are `A(S)`-supported in the Galois case** (issue 1017, the `hsuppdiff`
input of the caseB (5.7) coherence engine).  For `x, y ∈ 𝒮` both of the uniform degree `q·u`
(`sSet_caseB_apply_one_eq_qu`), the difference `x − y` vanishes at `1`, so its support avoids `{1}`
and lands in `A(S)` (`sSet_member_support_subset` minus the identity). -/
theorem Hypothesis.sSet_caseB_member_diff_supported [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {x : ClassFunction ↥hyp.S ℂ} (hx : x ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    {y : ClassFunction ↥hyp.S ℂ} (hy : y ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    (x - y).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
  intro z hz
  have hz0 : (x - y) z ≠ 0 := hz
  have hdeg : (x : ↥hyp.S → ℂ) 1 = (y : ↥hyp.S → ℂ) 1 := by
    rw [hyp.sSet_caseB_apply_one_eq_qu hG chars caseB hx,
      hyp.sSet_caseB_apply_one_eq_qu hG chars caseB hy]
  rcases ClassFunction.support_sub_subset x y hz with h | h
  · rcases hyp.sSet_member_support_subset hG hx h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSet_member_support_subset hG hy h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member orthonormal Dade `R`-family over `𝒮 = sSet` in the Galois case** (issue 1017, the
`R` input of the caseB (5.7) engine `uniform_degree_coherence_of_families`, the honest `S`-instance
analogue of the M-instance `caseB_sOf_memberRFamily`, `S13_MaximalIII_IV.lean:546`).  Every member
of the uniform-degree-`q·u` family `𝒮` is dispatched to its (5.2.d) `R`-datum:

* **irreducible member `η`** — the 2-element signed Dade image family
  `dadeOrthonormalCharacterImageFamilyOfDiff` (`η^τ − η̄^τ = ε·(μ − ν)`), assembled sorry-free from
  the landed inputs: non-realness (`sSet_hasNoRealCharacters` via `oddCardS`) and the conjugate
  difference support `(η̄ − η).support ⊆ A(S)` (`sSet_caseB_member_diff_supported`, both `η, η̄ ∈ 𝒮`);
* **reducible member `η = μ_j` (a nonzero μ-column sum)** — the `2q`-element certain-type image
  family `∑_i δ_j η_{ij}`.  This branch is the **residual**: it is the honest `S`-instance port of the
  §6 `certainTypeR` construction (the Dade image of the column difference `μ_j − μ̄_j` as the η-grid
  columns `j, j⁻¹`, orthonormal by `mu_orthonormal`/`eta`-orthonormality), the reducible-column
  machinery whose landed pieces are `mu_colSum_mem_sOf_H0` / `mu_j_isIndPC` (membership + linearity);
  the image-family assembly from the η-grid is the remaining (multi-step) work. -/
noncomputable def Hypothesis.sSet_caseB_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG))) η := by
  classical
  by_cases hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter η
  · -- irreducible member: the 2-element signed Dade image family (assembled sorry-free)
    refine OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) ⟨η, hirr⟩ ?_ ?_
    · exact sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hη
    · exact hyp.sSet_caseB_member_diff_supported hG chars caseB
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη) hη
  · -- reducible member (`η = μ_j`): the certain-type image family — RESIDUAL (S-instance §6 port)
    exact sorry

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the caseB per-member `R`-families** (issue 1017, the `hRorth`
input of `uniform_degree_coherence_of_families`, the honest `S`-instance analogue of the M-instance
`caseB_sOf_memberRFamily_orthogonal`).  For members `φ, ξ ∈ 𝒮` with `⟨φ, ξ⟩ = 0` and `⟨φ, ξ̄⟩ = 0`
(distinct non-conjugate members), the Dade image families `R(φ)`, `R(ξ)` are orthogonal.

**RESIDUAL** (pending the reducible branch of `sSet_caseB_memberRFamily`): the irreducible–irreducible
case is the landed (5.2.e) `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`; the cases where a
member is a reducible μ-column reference the certain-type image family whose S-instance construction
is the remaining reducible-column work. -/
theorem Hypothesis.sSet_caseB_memberRFamily_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {φ ξ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (h1 : ClassFunction.inner φ ξ = 0)
    (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (hyp.sSet_caseB_memberRFamily hG chars caseB hφ).Orthogonal
      (hyp.sSet_caseB_memberRFamily hG chars caseB hξ) := by
  sorry

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) Galois-branch coherence of `𝒮 = sSet` on the honest Dade map** (issue 1017, caseB — the
`uniform_degree_coherence_of_families` assembly, the honest `S`-instance mirror of the M-instance
`caseB_coherent_sOf_H0Cprime`, `S13_CoreStructure.lean:1544`).  In the Galois case the whole family
`𝒮` is uniform degree `q·u` (`sSet_caseB_apply_one_eq_qu`), so the (5.7) *norm-general* coherence
producer fires directly (no reducible-column *fold* needed): the pivot is a reducible μ-column
`μ₁ = ∑ᵢ μ_{i1}` (of self-norm `q`, from `mu_orthonormal`), and every member carries its (5.2.d)
`R`-datum via `sSet_caseB_memberRFamily`.  All the family inputs — finiteness (`sSet_finite`),
pairwise orthogonality (`sSet_pairwiseOrthogonal`), conjugate-closure (`sSet_closedUnderConjugate`),
no-real (`sSet_hasNoRealCharacters`), the Dade isometry / ZIrr-image / support facts
(`dadeIntegralCharacterMap_*_of_supported`, `sSet_caseB_member_diff_supported`), and the uniform
degree — are landed sorry-free; the sole residual is the reducible branch of
`sSet_caseB_memberRFamily` (+ `_orthogonal`), the `S`-instance §6 certain-type port. -/
noncomputable def Hypothesis.sSet_coherent_dade_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  classical
  -- Pivot: a nonzero reducible μ-column `μ₁ = ∑ᵢ μ_{i1} ∈ 𝒮` (self-norm `q`).
  have hj0 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  have hη₁ : (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
      ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief ⟨1, hyp.p_prime.one_lt⟩ hj0)
  have hN : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
      (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩) = (hyp.q : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ i : Fin hyp.q, ClassFunction.inner (hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
            (∑ i' : Fin hyp.q, hyp.mu i' ⟨1, hyp.p_prime.one_lt⟩)
        = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q,
            ClassFunction.inner (hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
              (hyp.mu i' ⟨1, hyp.p_prime.one_lt⟩) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q, if i = i' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
          rw [hyp.mu_orthonormal i i' ⟨1, hyp.p_prime.one_lt⟩ ⟨1, hyp.p_prime.one_lt⟩]
          simp
      _ = ∑ _i : Fin hyp.q, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp
      _ = (hyp.q : ℂ) := by simp
  refine OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    (sSet_finite _) hη₁
    (fun η hη => hyp.sSet_caseB_memberRFamily hG chars caseB hη)
    (fun a ha b hb hab => by
      have h := sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) ha hb hab
      convert h using 2 <;> exact Subsingleton.elim _ _)
    (fun a ha => sSet_closedUnderConjugate _ ha)
    (fun a ha heq => sSet_hasNoRealCharacters _ (hyp.oddCardS hG) ha heq.symm)
    ⟨hyp.q, hN⟩
    (fun {φ ψ} hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hφ.2 hψ.2)
    (fun a ha b hb => by
      have hab_Z : (a - b : ClassFunction ↥hyp.S ℂ) ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
        Submodule.sub_mem _ (sSet_subset_ZIrr _ ha) (sSet_subset_ZIrr _ hb)
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG)
        (hyp.sSet_caseB_member_diff_supported hG chars caseB ha hb) hab_Z)
    (fun a ha b hb => hyp.sSet_caseB_member_diff_supported hG chars caseB ha hb)
    (fun {φ ξ} hφ hξ h1 h2 =>
      hyp.sSet_caseB_memberRFamily_orthogonal hG chars caseB hφ hξ h1 h2)
    (fun a ha => (hyp.sSet_caseB_apply_one_eq_qu hG chars caseB ha).trans
      (hyp.sSet_caseB_apply_one_eq_qu hG chars caseB hη₁).symm)
    (by
      rw [hyp.sSet_caseB_apply_one_eq_qu hG chars caseB hη₁]
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero Nat.card_pos.ne'
        (OddOrder.Peterfalvi.S11.u_odd hG chars).pos.ne'))
    (by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
      simpa using honestTypeP2ASet_one_not_mem (M := hyp.S))
    (sSet_closedUnderConjugate _ hη₁)
    (sSet_hasNoRealCharacters _ (hyp.oddCardS hG) hη₁)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) Galois-branch coherence of the full family `𝒮 = sSet` on `Ind_S^G`** (issue 1017, caseB
of Peterfalvi (9.11) `Ptype_core_coherence`).  In the Galois case (`CliffordCaseBData`) **every**
member of `𝒮 = sSet` has degree `q·u` (`caseB_degree_qu`/`caseB_character_counts`), but `𝒮` is still
**mixed**: it contains exactly `p−1` reducible members (the μ_j residues, each `Ind` of a linear
character of `HC`, `reducible_count_sOf_H0`) alongside the degree-`q·u` irreducibles.

Honest route (mirroring the *landed* M-instance `caseB_coherent_sOf_H0Cprime`,
`S13_CoreStructure.lean:1544`, which likewise routes through the norm-general (5.7) engine rather
than the mixed *fold*): since the whole family is **uniform** degree `q·u`
(`sSet_caseB_apply_one_eq_qu`), coherence on the honest Dade map `τ` follows directly from
`uniform_degree_coherence_of_families` (`sSet_coherent_dade_caseB`, this file) with a reducible μ-column
pivot; then `congrMap` re-grounds `τ` onto `Ind_S^G` on the `A(S)`-supported span
(`sInstance_dade_eq_induce`).  All the (5.7)-engine wiring, the uniform-degree fact, the pivot norm,
the Dade isometry/ZIrr/support inputs, and the *irreducible* per-member `R`-datum are landed
sorry-free here; the sole residual is the **reducible** branch of `sSet_caseB_memberRFamily`
(+ `_orthogonal`) — the `S`-instance §6 certain-type image-family port. -/
theorem Hypothesis.sSet_coherent_indS_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) :=
  -- Coherence on the honest Dade map `τ` (`sSet_coherent_dade_caseB`, the (5.7) `uniform_degree`
  -- assembly) re-grounded onto `Ind_S^G` by `congrMap`: `τ` and `indS` agree on every
  -- `A(S)`-supported class function (`sInstance_dade_eq_induce`, the (13.2.e) `normedTI` isometry
  -- half), and `IsCoherent` depends on its map only through the `A(S)`-supported span — exactly the
  -- `indS`-re-grounding `sSetIrrDeg_coherent_indS` performs for the uniform sub-family.
  (hyp.sSet_coherent_dade_caseB hG chars caseB).map fun c =>
    c.congrMap fun φ hφ => by
      rw [hyp.indS_apply]
      exact hyp.sInstance_dade_eq_induce hG hφ.2

open OddOrder.Peterfalvi.S11 in
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Honest §9 character data on `S`** (issue 2035 step 3; support corrected to `A(S)`, issue 1017):
the `mkSection11CharacterDataS` mirror with the *genuine* coherence inputs — `tau := Ind_S^G` (`indS`,
Peterfalvi (13.2.e)) and `H0CprimeSupport := A(S)` (`supportInSubgroup (honestTypeP2ASet S) S`, the
honest Dade support `⋃_{x∈S_σ#} C_{S′}(x)#`).

**Support choice (issue 1017 verify-first).**  For the type-`P₂` maximal `S` the coherence support
`(H₀ ⊔ C′)^#` degenerates to the empty set — `H₀ = ⊥` (chief kernel trivial) and `C′ = [C,C] = ⊥`
(`Cprime_eq_bot`, `C ≤ U` abelian), so `(C′)^# = cprimeSharpS = ∅` (`cprimeSharpS_eq_empty`).  With
support `∅`, `zSupportedSpan 𝒮 ∅ = {0}`, which makes `IsCoherent`'s `nonzero` field (a nonzero
supported witness) **unsatisfiable** — the target `IsCoherent Ind_S^G 𝒮 ∅` is uninhabited, which is
exactly why the old `sibleyTarget_H0C` route was unsound.  The honest support is the (13.2.e) Dade
support `A(S)`, on which the family differences genuinely live (`sSet_member_diffsupp`) and
`extends_on_supported` carries real content (`τ₁ = Ind_S^G` on `A(S)`-supported combinations); the
degenerate `(C′)^# ⊆ A(S)` (`cprimeSharpS_subset_supportA`) restriction would only re-vacuate it.

Fed to `coherent_H0Cprime_S` (re-grounded off the unsound `sibleyTarget_H0C` onto the honest
`sSet_coherent_indS_A`) to extract the coherent extension `τ₁` (the (13.2.d)⇐(9.11) route to the
(13.3) `τ₁`-fields).  `u` and `u_eq_card_quotient` are unchanged (rfl-pinned to the `U`-action
image, as in the placeholder). -/
noncomputable def Hypothesis.mkSection11CharacterDataS_honest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      ((hyp.toTypesIIIIIIVSetupS hG).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)).subtype).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S
  tau := hyp.indS
  quotientSemidirectFrobenius := True

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) coherence of the full honest §9 family `𝒮 = sSet` on `Ind_S^G`, unconditional** (issue
1017 — the honest S-instance Peterfalvi (9.11) `Ptype_core_coherence`, replacing the unsound
`sibleyTarget_H0C`).  Case-splits the Clifford dichotomy (9.7) (`clifford_dichotomy` on the honest
character data) and dispatches to the Galois branch (`sSet_coherent_indS_caseB`) or the non-Galois
branch (`sSet_coherent_indS_caseA`).  The map is the genuine induction `τ = Ind_S^G` (`indS`,
(13.2.e)) and the support is the honest Dade support `A(S)` (nonempty — unlike the degenerate
`(C′)^# = ∅`, which makes `IsCoherent`'s `nonzero` field unsatisfiable). -/
theorem Hypothesis.sSet_coherent_indS_A [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataS_honest hG chief) with hA | hB
  · exact hyp.sSet_coherent_indS_caseA hG (hyp.mkSection11CharacterDataS_honest hG chief) hA.some
  · exact hyp.sSet_coherent_indS_caseB hG (hyp.mkSection11CharacterDataS_honest hG chief) hB.some

open scoped FiniteInduce in
/-- **(9.11)-coherence of the honest `S`-instance §9 data** (issue 2035 step 4; re-grounded off the
unsound `sibleyTarget_H0C`, issue 1017).  The `.some` of the honest unconditional
`sSet_coherent_indS_A`, yielding `IsCoherent Ind_S^G 𝒮 A(S)` — the Peterfalvi (13.2.d)⇐(9.11)
coherence for `𝒮(H₀C′) = 𝒮` (in the type-`P₂` `S`-instance, `H₀C′ = ⊥`) with the genuine Dade map
`τ = Ind_S^G` and the honest Dade support `A(S)`.

**This no longer routes through `coherent_H0C_commutator`/`sibleyTarget_H0C`** (the unsound (6.8)
shortcut whose target `IsCoherent Ind_S^G 𝒮 (C′)^# = IsCoherent Ind_S^G 𝒮 ∅` is uninhabited).  The
remaining gap is the honest (9.11) pair-adjoining assembly inside `sSet_coherent_indS_{caseA,caseB}`
(base coherences landed, the mixed-family lift sorried-cite), not a soundness defect. -/
noncomputable def Hypothesis.coherent_H0Cprime_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IsCoherent (hyp.mkSection11CharacterDataS_honest hG chief).tau
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport :=
  (hyp.sSet_coherent_indS_A hG chief).some

open scoped FiniteInduce in
/-- **The coherent extension `τ₁` for the honest `S`-instance** (issue 2035 step 4): the
`.extension` of the (9.11)-coherence `coherent_H0Cprime_S`.  This is the (13.2.d) `τ₁ :
IntegralCharacterMap ↥S G` that the (13.3) degree analysis threads (the `μ_j^{τ₁}` machinery).
Now grounded on the honest `sSet_coherent_indS_A` (base coherences landed, mixed-family lift
sorried-cite), no longer on the unsound `sibleyTarget_H0C`. -/
noncomputable def Hypothesis.tau1S_ofHonest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G :=
  (hyp.coherent_H0Cprime_S hG chief).extension

open scoped FiniteInduce in
/-- **Type-alignment probe for the (13.3) `τ₁` route** (issue 2035 step 4 verification): confirms
`coherent_H0Cprime_S` obtains and its `.extension` is definitionally `tau1S_ofHonest`, of the
expected `IntegralCharacterMap ↥S G` type; and that `extends_on_supported` gives
`τ₁ φ = Ind_S^G φ` on the supported span (`tau1S_apply_induce` on the family) — the input to the
(13.3) `tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` fields. -/
theorem Hypothesis.tau1S_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (φ : ClassFunction ↥hyp.S ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport) :
    hyp.tau1S_ofHonest hG chief φ = ClassFunction.induce hyp.S φ := by
  have h := (hyp.coherent_H0Cprime_S hG chief).extends_on_supported φ hφ
  -- `.extension φ = chars.tau φ = indS φ = Ind_S^G φ`
  simpa [Hypothesis.tau1S_ofHonest, Hypothesis.mkSection11CharacterDataS_honest,
    Hypothesis.indS_apply] using h

set_option linter.unusedFintypeInType false in
/-- **Constituent kernel step for (1.5.a)** (Coq `S1cases` inner kernel argument), stated
generically.  For subgroups `P0, K'` of a finite group `Γ`, an irreducible `s ∈ Irr(Γ)`, and an
irreducible `θ'` of `K'` with `P0.subgroupOf K' ⊄ ker θ'`: if `θ'` is a constituent of
`Res_{K'} s` (`⟨θ', Res_{K'} s⟩ ≠ 0`), then `P0 ⊄ ker s`.

**Contrapositive.**  `P0 ⊆ ker s` makes `Res_{K'} s` trivial on `P0.subgroupOf K'`
(`characterKernel_restrict_subgroupOf`); `θ'`, a constituent of the genuine character `Res_{K'} s`
(`isCharacter_restrict`), inherits the containment
(`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), so `P0.subgroupOf K' ⊆ ker θ'`,
contradicting the hypothesis.  This is the `S`-instance analogue of the leaf
`PrimeTIResidue.constituent_P_not_subset_ker`, grounded on the honest `S'`-family — no
`PrimeTIResidueData` and no prime-TI dichotomy is used. -/
private theorem constituent_P_not_subset_characterKernel {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] (P0 K' : Subgroup Γ) [Fintype ↥K']
    [Invertible (Nat.card ↥K' : ℂ)]
    (θ' : ClassFunction ↥K' ℂ)
    (hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθ'P : ¬ ((P0.subgroupOf K' : Set ↥K') ⊆ OddOrder.Peterfalvi.S03.characterKernel θ'))
    (s : OddOrder.RepresentationTheory.IrreducibleCharacter Γ)
    (hs : ClassFunction.inner θ' (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) ≠ 0) :
    ¬ ((P0 : Set Γ) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction Γ ℂ)) := by
  intro hker
  have hResChar : IsCharacter (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter K'
  have hinner' : ClassFunction.inner
      (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) θ' ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    exact star_ne_zero.mpr hs
  have hResker : ((P0.subgroupOf K') : Set ↥K') ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf K' hker
  exact hθ'P fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hθ'irr hinner' (hResker hx)

open scoped FiniteInduce in
/-- **Peterfalvi (13.5) preamble / (1.5.a) — the family membership `Ind_{PC}^S θ ∈ ℤ[𝒮]`**
(issue 2035 step 5a).

For an irreducible character `θ` of `H = PC` **whose kernel does not contain `P`**, the induced
character `Ind_{PC}^S θ` lies in `ℤ[𝒮]` (`zSpan` of the honest §9 family `𝒮 = sSet`).  In
Coq's `PFsection13` this is `sS1S : {subset calS1 <= 'Z[calS]}` (with `calS1 = seqIndD H S P 1`,
`calS = seqIndD PU S P 1`), used implicitly throughout (13.5)–(13.8).

**Honest proof, grounded on the S06 §4 residue theory** (issue 9014 session 8).  The family
`𝒮 = sSet = {Ind_{S'}^S χ | χ ∈ Irr(S'), P ⊄ ker χ}` is *exactly* the set of inductions
from the derived subgroup `S' = huSub` of `P`-nonlinear irreducibles (`P = data.H`), so **membership
is by witness** — no dichotomy on the induced character is needed.  Writing the single-stage
`Ind_{PC}^S θ` as the two-stage `Ind_{S'}^S (Ind_{PC'}^{S'} θ')` (`induce_induce_subgroupOf`, with
`PC' = (PC).subgroupOf S'` and `θ'` the transport of `θ`) and expanding the inner induction into
`S'`-constituents `Ind_{PC'}^{S'} θ' = ∑_{s ∈ Irr(S')} ⟨θ', Res s⟩ • s`
(`induce_eq_sum_inner_restrict_smul`), each constituent `s` with nonzero (necessarily `ℕ`)
coefficient has `P ⊄ ker s` (`constituent_P_not_subset_characterKernel`), so `Ind_{S'}^S s`
lies in `sSet` by witness `s`; the coefficient-weighted `ℤ`-sum lands in `zSpan sSet`.  This
grounds the family
membership on the proven S06 setup (`typePData_toS06Hypothesis` for `S` supplies the certain-type
Hypothesis, though only its `S'`-family shape is needed here); no prime-TI residue dichotomy is used. -/
theorem Hypothesis.induce_H_mem_zSpan_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∈
      OddOrder.Peterfalvi.S07.zSpan (hyp.mkSection11CharacterDataS_honest hG chief).S := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- Target family is `sSet data` with `data = toTypesIIIIIIVSetupS hG`.
  rw [OddOrder.Peterfalvi.S11.Section11CharacterData.S_eq]
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  -- Work with the §9 induction carrier `HU = huSub data`, equal to `S' = derivedInG S` in `↥S`.
  set HU : Subgroup ↥hyp.S := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  letI : Fintype ↥HU := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `PC = H.subgroupOf S ≤ S' = HU`.
  have hHderiv : hyp.H ≤ derivedInG hyp.S := by
    show hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.H.subgroupOf hyp.S ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.S hHderiv
  letI : Fintype ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The transport `θ' = θ ∘ e` of `θ` onto `PC' = (PC).subgroupOf HU ≤ HU`.
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  -- Two-stage induction: `Ind_{PC}^S θ = Ind_{HU}^S (Ind_{PC'}^{HU} θ')`.
  rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ]
  -- Expand the inner induction into `HU`-constituents and push `Ind_{HU}^S` inside.
  rw [OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
    ClassFunction.induce_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [ClassFunction.induce_smul]
  -- The coefficient `⟨θ', Res s⟩` is a non-negative integer `(k : ℂ)`.
  have hResChar : IsCharacter (ClassFunction.restrict
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
  obtain ⟨k, hk⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
  have hc : ClassFunction.inner
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
      (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
        (s : ClassFunction ↥HU ℂ)) = (k : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hk, star_natCast]
  rw [hc, Nat.cast_smul_eq_nsmul ℂ k (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · refine nsmul_mem ?_ k
    -- `P (in HU) ⊄ ker s`: kernel step from `P ⊄ ker θ'` (from `hθP`) and constituent `θ'`.
    have hθ'P : ¬ ((((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
          ((hyp.H.subgroupOf hyp.S).subgroupOf HU) :
        Set ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
      rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
      -- The image of `((P.subgroupOf S).subgroupOf HU).subgroupOf (PC.subgroupOf HU)` under `e`
      -- is `(P.subgroupOf S).subgroupOf (PC.subgroupOf S)`, which `hθP` does not kill.
      have himg : (((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
            ((hyp.H.subgroupOf hyp.S).subgroupOf HU)).map
            (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          = (hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) := by
        ext y
        rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        rfl
      rw [himg]; exact hθP
    refine Submodule.subset_span ?_
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    -- `s ∈ xiSet data`: `hInHu data ⊄ ker s`, with `hInHu = (P.subgroupOf S).subgroupOf HU`.
    show ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.P.subgroupOf hyp.S).subgroupOf HU : Set ↥HU) := by
      congr 1
      show (data.H.subgroupOf hyp.S).subgroupOf HU = (hyp.P.subgroupOf hyp.S).subgroupOf HU
      have hPeq : data.H = hyp.P := by
        show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
      rw [hPeq]
    rw [hHInHu]
    -- The generic kernel step: `θ'` is a constituent of `Res s` (coefficient `k > 0`), and
    -- `P (in HU) ⊄ ker θ'` (`hθ'P`), so `P (in HU) ⊄ ker s`.
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hc]; exact_mod_cast hk0.ne'
    exact constituent_P_not_subset_characterKernel ((hyp.P.subgroupOf hyp.S).subgroupOf HU)
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'P s hs

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ isometry on the `H`-induced family** (issue 2035 step 5a): `τ₁ = tau1S_ofHonest`
preserves inner products of `Ind_{PC}^S θ` for irreducible `θ` of `H = PC` with `P ⊄ Ker θ`.  From
the coherence field `extension_inner_eq` (isometric on all of `ℤ[𝒮]`) together with the family
membership `induce_H_mem_zSpan_S`.  This is the honest engine for the `CharacterDegreeData`
`tau1S_inner_induce` field (with the `P ⊄ Ker` hypothesis the (13.3) consumers actually satisfy —
`μ_j`, `λ` all have `P ⊄ Ker`). -/
theorem Hypothesis.tau1S_ofHonest_inner_induce [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    ClassFunction.inner
        (hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
        (hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
      = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  exact (hyp.coherent_H0Cprime_S hG chief).extension_inner_eq _ _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)
    (hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P)

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ sends the `H`-induced family into `ℤ[Irr G]`** (issue 2035 step 5a): for
irreducible `θ` of `H = PC` with `P ⊄ Ker θ`, `τ₁ (Ind_{PC}^S θ) ∈ ℤ[Irr G]`.  From the coherence
field `extension_mem_ZIrr` (virtual-character codomain on all of `ℤ[𝒮]`) and the family membership
`induce_H_mem_zSpan_S`.  Honest engine for the `CharacterDegreeData` `tau1S_induce_mem_ZIrr` field. -/
theorem Hypothesis.tau1S_ofHonest_induce_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G :=
  (hyp.coherent_H0Cprime_S hG chief).extension_mem_ZIrr _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)

/-- **Peterfalvi (13.2.b)/(11.7) for the `S`-instance**: `P = S_F` is elementary abelian of
exponent `p`.  Assembled from the §11 chief-factor data of `S` (`exists_chiefFactorData` on
`toTypesIIIIIIVSetupS`): the chief kernel `N = ⊥` (`toTypesIIIIIIVSetupS_chief_N_eq_bot`), so
`P/⊥ ≅ P` *is* the chief factor and carries `ChiefFactorData.quotient_elementaryAbelian` at the
chief prime `chief.p = p` (forced by `|P| = p^q`).  **Ungated** — the `S`-instance `H₀ = ⊥` is
proven (`P` itself is the chief factor), unlike the generic sorried `chief_H0_eq_bot`.  Discharges
`basic_structure_gated.P_elementaryAbelian`. -/
theorem Hypothesis.P_elementaryAbelian [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.p ↥hyp.P := by
  classical
  obtain ⟨chief, _⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
    show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hN : chief.N = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief
  -- `chief.p = p` from `|P| = p^q = chief.p^q · |N|` with `|N| = 1`.
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    show Nat.card ↥hyp.Sdata.W1 = hyp.q; rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hq] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  have hdvd : chief.p ∣ hyp.p ^ hyp.q := by
    refine dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.p :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  -- Transport `quotient_elementaryAbelian` along `↥H ⧸ ⊥ ≃* ↥H`, then rewrite `H = P`.
  have hEA : IsElementaryAbelian hyp.p ↥(hyp.toTypesIIIIIIVSetupS hG).H := by
    have h := chief.quotient_elementaryAbelian
    rw [hpp] at h
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
  rwa [hHeq] at hEA

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **`C_U(H̄) = C`** for the `S`-instance: the §9 kernel `cSub` (`= C_U(H̄)`) equals Peterfalvi's
`C = C_U(P) = U ⊓ C_G(P)`.  The reverse `C ≤ cSub` is general (an element of `U` centralizing
`H = P` acts trivially on any quotient of `H`, so lies in the action kernel); the forward
`cSub ≤ C` uses `H₀ = ⊥` (`toTypesIIIIIIVSetupS_chief_H0_eq_bot`): with `H̄ = P/H₀ = P` the kernel
`cSub` centralizes `H = P` (`⁅cSub, H⁆ ≤ H₀ = ⊥`, `commutator_cSub_H_le_H0`).  This is the
last spelling piece of the (13.3.a) `μ_j = Ind_{PC}(linear)`: `HC = P·C = P·cSub`. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_cSub_eq_C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief = hyp.C := by
  haveI := hyp.finiteG
  haveI := chief.N_normal
  have hUeq : (hyp.toTypesIIIIIIVSetupS hG).U = hyp.U := hyp.Sdata_U_eq
  have hHeq : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  apply le_antisymm
  · -- forward: `cSub ≤ U ⊓ C_G(P)`
    rw [hyp.C_eq]
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨hUeq ▸ OddOrder.Peterfalvi.S11.cSub_le_U _ chief hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    -- `⁅cSub, H⁆ ≤ H₀ = ⊥`, so `g` centralizes `H = P`
    have hcomm : ⁅OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief,
        (hyp.toTypesIIIIIIVSetupS hG).H⁆ ≤ ⊥ := by
      rw [← hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief]
      exact OddOrder.Peterfalvi.S11.commutator_cSub_H_le_H0 _ chief
    have hpH : p ∈ (hyp.toTypesIIIIIIVSetupS hG).H := hHeq ▸ hp
    have hcm := hcomm (Subgroup.commutator_mem_commutator hg hpH)
    rw [Subgroup.mem_bot, commutatorElement_def] at hcm
    -- `g p g⁻¹ p⁻¹ = 1 ⟹ p g = g p`
    have hpg : g * p * g⁻¹ = p := by
      have h1 : g * p * g⁻¹ * p⁻¹ * p = p := by rw [hcm, one_mul]
      rwa [inv_mul_cancel_right] at h1
    have hgp : g * p = p * g := by
      have h2 : g * p * g⁻¹ * g = p * g := by rw [hpg]
      rwa [inv_mul_cancel_right] at h2
    exact hgp.symm
  · -- reverse: `U ⊓ C_G(P) ≤ cSub`
    rw [hyp.C_eq]
    intro g hg
    obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgUdata : g ∈ (hyp.toTypesIIIIIIVSetupS hG).U := hUeq ▸ hgU
    have hgUW1 : g ∈ (hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔
        (hyp.toTypesIIIIIIVSetupS hG).typeP.W1 :=
      (le_sup_left : (hyp.toTypesIIIIIIVSetupS hG).typeP.U ≤ _) hgUdata
    set bUW1 : ↥((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔
        (hyp.toTypesIIIIIIVSetupS hG).typeP.W1) := ⟨g, hgUW1⟩ with hbUW1def
    have hbUW1mem : bUW1 ∈ ((hyp.toTypesIIIIIIVSetupS hG).typeP.U).subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1) :=
      Subgroup.mem_subgroupOf.mpr hgUdata
    -- `bUW1` acts trivially on `H̄`: `g` centralizes `H = P`
    have haut : quotientMulAutHom chief.N_aInvariant bUW1 = 1 := by
      ext q
      refine QuotientGroup.induction_on q ?_
      intro x
      rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply
        chief.N_aInvariant bUW1 x, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [OddOrder.Peterfalvi.S11.typeP_conjAction_apply]
      have hxP : ((x : G)) ∈ hyp.P := hHeq ▸ x.2
      have hcx : g * (x : G) = (x : G) * g :=
        (Subgroup.mem_centralizer_iff.mp hgC (x : G) hxP).symm
      show (bUW1 : G) * (x : G) * (bUW1 : G)⁻¹ = (x : G)
      rw [hbUW1def]
      show g * (x : G) * g⁻¹ = (x : G)
      rw [hcx]; group
    have hbker : (⟨bUW1, hbUW1mem⟩ : ↥(((hyp.toTypesIIIIIIVSetupS hG).typeP.U).subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)))
        ∈ (OddOrder.Peterfalvi.S11.uActionHom (hyp.toTypesIIIIIIVSetupS hG) chief).ker := by
      rw [MonoidHom.mem_ker, OddOrder.Peterfalvi.S11.uActionHom, MonoidHom.comp_apply]
      exact haut
    -- assemble `g ∈ cSub`
    simp only [OddOrder.Peterfalvi.S11.cSub, Subgroup.mem_map]
    exact ⟨bUW1, ⟨⟨bUW1, hbUW1mem⟩, hbker, rfl⟩, rfl⟩



/-- **Peterfalvi (13.2.c)/(9.7): the `u`-bound `u ≤ (p^q − 1)/(p − 1)` for the type-`P₂`
member `S`**, unconditionally.  This is the honest discharge of `basic_structure_gated.u_bound`
(Pf (13.2.c), issue 9000 lane-b cite / 2038 HUB ruling): lane a proved the unconditional §9/§11
bound `S11.u_le_cyclotomicQuotient` (`chars.u ≤ (chief.p^data.q − 1)/(chief.p − 1)` for *any*
`Section11CharacterData` on a `TypesIIIIIIVSetup`), and we cite it on the `S`-instance
`toTypesIIIIIIVSetupS` after discharging the three identifications:
* `data.q = q` (`|W₁| = q`, `q_eq_card_W1`);
* `chief.p = p` (the chief prime, forced by `|P| = p^q = chief.p^q · |N|`);
* `chars.u = u` (the `U`-action image `|Ū| = [U : C_U(P)] = |U|/|C| = uc/c = u`, via the proven
  `relIndex_cSub_U_eq_u` `[U : C] = chars.u` and `cSub = C`, `card_U_eq_uc`).
**Ungated** — depends only on `S11.u_le_cyclotomicQuotient` (proven, Clifford dichotomy) and the
`S`-instance identities, not on the (11.9) `typeP_Galois` character body. -/
theorem Hypothesis.u_le_cyclotomicQuotient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := by
  classical
  haveI := hyp.finiteG
  obtain ⟨chief, _⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  haveI := chief.N_normal
  -- (i) the `S`-instance chief factor `q` equals `q = |W₁|`.
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    change Nat.card ↥hyp.Sdata.W1 = hyp.q
    rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  -- (ii) the chief prime `chief.p = p`, from `|P| = p^q = chief.p^q · |N|`.
  have hpp : chief.p = hyp.p := by
    have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
      change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
      rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
    have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
    rw [hq] at hquot
    have hsplitP := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
    rw [hquot, hcardH] at hsplitP
    have hdvd : chief.p ∣ hyp.p ^ hyp.q :=
      dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') (hsplitP ▸ Dvd.intro _ rfl)
    exact (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  -- (iii) the `U`-action image order `chars.u = |Ū| = [U : C] = u`.
  have hu_eq : (hyp.mkSection11CharacterDataS hG chief).u = hyp.u := by
    have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hc0 ?_
    have key : (hyp.mkSection11CharacterDataS hG chief).u
        * Nat.card ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
        = Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).U := by
      rw [← OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u (hyp.mkSection11CharacterDataS hG chief)]
      have h := Subgroup.index_mul_card
        ((OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief).subgroupOf
          (hyp.toTypesIIIIIIVSetupS hG).U)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)).toEquiv] at h
    rw [hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief, ← hyp.c_eq_card_C,
      show (hyp.toTypesIIIIIIVSetupS hG).U = hyp.U from hyp.Sdata_U_eq, hyp.card_U_eq_uc] at key
    exact key
  -- cite lane a's unconditional bound and rewrite through the three identifications.
  have hbound :=
    OddOrder.Peterfalvi.S11.u_le_cyclotomicQuotient (hyp.mkSection11CharacterDataS hG chief)
  rw [hu_eq, hpp, hq] at hbound
  exact hbound

/-- **Peterfalvi (13.2.b,c,e)** structural producer: the `M_F`-structure of the type-`P₂` member
`S`.  Faithful obligation on the §16 σ-structure (`BasicStructureGated` docstring).

`U_commutative` (13.2.a U-side) and `P_order` (13.2.b order part) are now **genuine**:
* `U_commutative` from the carried `S_U_commutative` (BG Lemma 15.1(b) `typeP_hall_derived_eq_and_abelian`, `U` the `(κ∪σ)'`-Hall, supplied at construction);
* `P_order` = `|P| = p^q` from `card_P_eq` fed by the carried `Sdata_W2_eq` (the intrinsic dual factor `Sdata.W2 = C_{S'}(W₁#)` equals the abstract `W₂ = K*`, via `typePData_of_kappaHall_hallComplement_W2`).

The `A_0(S)`/`τ_S` clauses are the opaque scaffold Props (`True`).  The two former concrete
residuals are now **genuine** (both discharged ungated on the `S`-instance `toTypesIIIIIIVSetupS`):
* `P_elementaryAbelian` — Pf (11.7), from the §11 chief factor `P = S_F` (`H₀ = ⊥`), via
  `Hypothesis.P_elementaryAbelian`;
* `u_bound` — Pf (9.7) `u ≤ (p^q−1)/(p−1)`, via `Hypothesis.u_le_cyclotomicQuotient`
  (cites the proven unconditional `S11.u_le_cyclotomicQuotient`; issue 9000 lane-b cite). -/
noncomputable def basic_structure_gated [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : BasicStructureGated hyp where
  U_commutative := hyp.S_U_commutative
  P_elementaryAbelian := hyp.P_elementaryAbelian hG
  P_order := hyp.card_P_eq hG hyp.Sdata_W2_eq
  u_bound := hyp.u_le_cyclotomicQuotient hG
  A0S_TI := True
  A0S_TI_holds := trivial
  tauS_eq_induction := True
  tauS_eq_induction_holds := trivial

/-- **Peterfalvi (13.2.a--c,e)**: `S` is type II or III, `P` is elementary
abelian of order `p^q`, `u` is bounded, and `A_0(S)` is a TI-subset.

The **type determination** (13.2.a) is discharged `sorry`-free from the §16 carrier `S_typeP2`
(`isTypeII_of_isTypeP2`): `S` is type II, hence the `IsTypeII ∨ IsTypeIII` and `q < p → IsTypeII`
fields hold with the type-II side.  The remaining `M_F`-structure data (13.2.b,c,e) is read off the
faithful §16-gated producer `basic_structure_gated`. -/
theorem basic_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : BasicStructureData hyp,
      (IsTypeII hyp.S ∨ IsTypeIII hyp.S) ∧ IsElementaryAbelian hyp.p ↥hyp.P ∧
        Nat.card ↥hyp.P = hyp.p ^ hyp.q ∧
        hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ∧ data.A0S_TI := by
  -- (13.2.a) type determination: `S` is type II, sorry-free from the carrier `S_typeP2`.
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 _hG hyp.S_maximal hyp.S_typeP2
  -- `U ≠ ⊥`: the carrier `Sdata.U` has the same order as the type-II witness's `typeP.U`
  -- (`card_U_eq_index = [M' : M_F]`), and the latter is `≠ ⊥` (`TypePNontrivialCore`).
  have tdata : TypeIIData hyp.S := hSII.some
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  -- (13.2.a) `U W₁` Frobenius: sorry-free from the carrier `Sdata` (`typeP_uW1_frobenius`,
  -- reconciled `Sdata.U = U`, `Sdata.W1 = W1`).
  have hUW1frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.U ⊔ hyp.W1) (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
        (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    rwa [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at h
  -- (13.2.b,c,e) `M_F`-structure: the localized faithful §16 producer.
  let core := basic_structure_gated _hG hyp
  refine ⟨{ S_typeII_or_typeIII := Or.inl hSII
            q_lt_p_forces_typeII := fun _ => hSII
            U_commutative := core.U_commutative
            UW1_frobenius := hUW1frob
            P_elementaryAbelian := core.P_elementaryAbelian
            P_order := core.P_order
            u_bound := core.u_bound
            A0S_TI := core.A0S_TI
            A0S_TI_holds := core.A0S_TI_holds
            tauS_eq_induction := core.tauS_eq_induction
            tauS_eq_induction_holds := core.tauS_eq_induction_holds }, ?_⟩
  exact ⟨Or.inl hSII, core.P_elementaryAbelian, core.P_order, core.u_bound, core.A0S_TI_holds⟩

/-- **Structural input for Peterfalvi (13.2.d) — ⚠ VESTIGIAL, do not complete as stated**
(hub ruling 2026-07-02; provenance: closed issues 1004/4014).

The S-side maximal-coherent Dade route (`tauS`/`Sset`/`A0S`) is **off the FT path**: the §13/§16
contradiction is routed through the W-side grid `eta = tau3 ∘ omega` and the carrier supplies
`tauS = 0` as a placeholder, so nothing on the spine consumes this witness.  Building it as
stated would prove an unconsumed S-side statement.  Anyone touching the (13.5)–(13.9) cascade
must first restate it W-side or retire it — see the 2026-07-02 hub section of
`notes/peterfalvi/s16_w4_char_cascade.md` (and note (6.8) `S08.sibleySetup_is_coherent` itself
is already proven; the old "once lane B supplies (6.8)" framing is obsolete). -/
noncomputable def sibleyTarget_S [Fintype G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) [Fintype ↥hyp.S]
    [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)] :
    CoherenceWiring.SibleyTarget hyp.tauS hyp.Sset hyp.A0S := sorry

/-- **Peterfalvi (13.2.d)**: the family `S` is coherent — ⚠ VESTIGIAL endpoint (0 spine cites).

Wired to the proven (6.8) capstone `S08.sibleySetup_is_coherent` through the coherence-wiring
bridge; the only gap is `sibleyTarget_S`, which is ruled **do-not-complete-as-stated** (see its
docstring — the spine routes through the W-side `eta` grid, `tauS = 0` placeholder).  Kept for
statement fidelity to Pf (13.2.d); do not invest proof effort here. -/
theorem S_coherent [Finite G] [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) [Fintype ↥hyp.S]
    [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tauS hyp.Sset hyp.A0S) :=
  CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_S hG hyp)

end OddOrder.Peterfalvi.S15

