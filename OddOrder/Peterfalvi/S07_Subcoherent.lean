/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_Coherence
import OddOrder.Peterfalvi.S07_CoherenceConstantDegree

/-!
# Peterfalvi §5 (5.3)(a): the subcoherent `R`-datum producer (`irr_subcoherent`)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§5, pp. 21-24.

## What this file provides

The subcoherence **structure** of Peterfalvi (5.2) is already ported as
`OddOrder.Peterfalvi.S07.Hypothesis` (`S07_Coherence.lean`), a field-for-field
transcription of Coq `PFsection5.subcoherent S tau R`:

| Coq `subcoherent S tau R` field  | `S07.Hypothesis` field                    |
|----------------------------------|-------------------------------------------|
| (a) `~~ has cfReal`, `ccClosed`  | `no_real_characters`, `conjugate_closed`  |
| (b) `isometry tau` to ZIrr       | `tau_isometry_diff` (+ ZIrr codomain)     |
| (c) `pairwise_orthogonal S`      | `pairwise_orthogonal`                     |
| (d) `R xi`: orthonormal ZIrr img | `difference_image` (`CharacterDifferenceImage`) |
| (e) cross-orthogonality of `R`   | `difference_images_orthogonal`            |

The per-member `R(χ)` datum (Coq's `R xi`, a `2.-tuple` of orthonormal
irreducibles) is the `CharacterDifferenceImage` record; its generic *producer*
from the §3 (1.4) keystone is `characterDifferenceImageOfIsometry`
(`S07_Coherence.lean`).

What was **missing** is a top-level *assembler*: given an orthonormal, conjugate-
closed, non-real family `S ⊆ Irr L` with a lattice-relative isometry `τ` (the
setting of Coq `irr_subcoherent`, `PFsection5.v:636`), package the six
`S07.Hypothesis` fields in one shot.  Every existing consumer (e.g.
`S14_MaximalI` at `Sset_differenceImage` / `Sset_differenceImages_orthogonal`)
hand-assembles this record inline.  This file factors that out into
`irr_subcoherent`, building **strictly on** the existing per-member producer
`characterDifferenceImageOfIsometry` and the (5.2.e) cross-orthogonality bridge
`orthogonal_of_signedDifference_inner_eq_zero`.  Nothing here is posited: each
`R(χ)` is extracted from the keystone, and the (5.2.e) cross-orthogonality is
derived from the difference-isometry.

## Coq map

* Coq `subcoherent` (`PFsection5.v:486`)  ↦  `S07.Hypothesis` (already ported).
* Coq `irr_subcoherent` (`PFsection5.v:636`)  ↦  `irr_subcoherent` (this file).
* Coq `prDade_subcoherent` (`PFsection5.v:683`) / `FTtypeP_subcoherent`
  (`PFsection8.v:819`)  ↦  **NOT here, and not needed**: the prime-TI machinery
  is already in the repo under `certainType`/`columnFamily` names (S06), and
  `prDade`'s content is already assembled as `sixTwoDecompositionData` (S13).  A
  `prDade`-shaped `S07.Hypothesis` is impossible anyway (variable-length `R`) and
  has zero consumers.  See the corrected module note at the end of this file.

Reference note: `notes/peterfalvi/s07_coherence.md`, issue `1017`.
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-! ### The (5.2.e) source-side inner-product expansion

The heart of Coq's `irr_subcoherent` (5.2.e) step is: if `χ` is orthogonal to the
conjugate pair `{ψ, ψ̄}`, then the source differences `χ − χ̄` and `ψ − ψ̄` are
orthogonal.  Via the isometry this transports to `⟨(χ−χ̄)^τ, (ψ−ψ̄)^τ⟩ = 0`, i.e.
`⟨signedDiff χ, signedDiff ψ⟩ = 0`, feeding
`orthogonal_of_signedDifference_inner_eq_zero`.
-/

/-- **Source-side (5.2.e) orthogonality of conjugate differences.**

If `⟨χ, ψ⟩ = 0` and `⟨χ, ψ̄⟩ = 0`, then the conjugate differences are orthogonal:
`⟨χ − χ̄, ψ − ψ̄⟩ = 0`.

Expanding `⟨χ−χ̄, ψ−ψ̄⟩ = ⟨χ,ψ⟩ − ⟨χ,ψ̄⟩ − ⟨χ̄,ψ⟩ + ⟨χ̄,ψ̄⟩`.  The two remaining
cross terms are the conjugates of the given zeros
(`OddOrder.RepresentationTheory.inner_conj_conj`, `⟨φ̄, ψ̄⟩ = conj⟨φ, ψ⟩`):
`⟨χ̄, ψ̄⟩ = conj⟨χ, ψ⟩ = 0`, and `⟨χ̄, ψ⟩ = ⟨χ̄, (ψ̄)̄⟩ = conj⟨χ, ψ̄⟩ = 0`. -/
theorem inner_conjugateDifference_eq_zero
    {χ ψ : ClassFunction L ℂ}
    (hχψ : ClassFunction.inner χ ψ = 0)
    (hχψbar : ClassFunction.inner χ ψ.conj = 0) :
    ClassFunction.inner (χ - χ.conj) (ψ - ψ.conj) = 0 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hχψ, hχψbar]
  -- Remaining: `- (0 - 0) - (⟨χ̄, ψ⟩ - ⟨χ̄, ψ̄⟩) = 0`, i.e. `⟨χ̄,ψ⟩ = ⟨χ̄,ψ̄⟩ = 0`.
  have hbar1 : ClassFunction.inner χ.conj ψ = 0 := by
    have h := inner_conj_conj χ ψ.conj
    rw [ClassFunction.conj_conj, hχψbar, star_zero] at h
    exact h
  have hbar2 : ClassFunction.inner χ.conj ψ.conj = 0 := by
    have h := inner_conj_conj χ ψ
    rw [hχψ, star_zero] at h
    exact h
  rw [hbar1, hbar2]; ring

/-! ### `irr_subcoherent`: the (5.3)(a) assembler

Coq `PFsection5.v:636`:
```
Lemma irr_subcoherent (L G : {group gT}) S tau :
    cfConjC_subset S (irr L) -> ~~ has cfReal S ->
    {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]} ->
  {R | subcoherent S tau R}.
```
We package the same conclusion as the six-field `S07.Hypothesis` record.  The
generic per-member producer `characterDifferenceImageOfIsometry` supplies field
(d), and `inner_conjugateDifference_eq_zero` + `tau_isometry_diff` + `image_eq`
supply field (e).

The per-member (1.4) inputs (`virtual`, `vanishAtOne`, `isom`) are taken as
family-indexed hypotheses rather than re-derived from the raw
`{in 'Z[S,L#], isometry tau, to ZIrr}` predicate: in every repo application they
are discharged directly from the ambient Dade isometry (cf. the
`dadeCharacterDifferenceImageOfDiff` witnesses), and threading them explicitly
keeps this assembler independent of the particular `IntegralCharacterMap`
packaging.  See `dadeCharacterDifferenceImageOfDiff` (`S07_Coherence.lean`) for
the canonical way these three are produced. -/

variable {S : Set (ClassFunction L ℂ)}

/-- **Peterfalvi (5.3)(a), assembler form (`irr_subcoherent`).**

Given
* `τ` a base integral character map,
* a family `S` that is conjugate-closed (`hconj`), has no real members (`hreal`),
  and is pairwise orthogonal (`hortho`),
* `A`-supportedness of the conjugate differences `χ − χ̄` (`hconjsupp` — Coq's
  `'Z[S, L^#]` membership of the (5.2.d) differences),
* `τ` a lattice-relative isometry on `ℤ[S, A]` (`hiso`, the (0099) `zSupportedSpan`
  form of Coq's `{in 'Z[S, L^#], isometry tau}`), and
* per-member difference images `Rdatum χ : CharacterDifferenceImage τ χ` whose
  underlying map is `τ` and whose image obeys `τ(χ − χ̄) = ε·(μ − ν)`,

this constructs the subcoherent `S07.Hypothesis` record on `S` with base `τ`.
This is the top-level producer that every §7/§14 consumer hand-assembled before.

Field (e) `difference_images_orthogonal` is derived: from `⟨φ, χ⟩ = 0` and
`⟨φ, χ̄⟩ = 0`, `inner_conjugateDifference_eq_zero` gives `⟨φ − φ̄, χ − χ̄⟩ = 0`;
the lattice isometry `hiso` (fed the `ℤ[S, A]`-membership of the conjugate
differences, via `hconjsupp`) transports this to `⟨(φ−φ̄)^τ, (χ−χ̄)^τ⟩ = 0`, i.e.
`⟨signedDiff φ, signedDiff χ⟩ = 0` (via `image_eq`), feeding
`orthogonal_of_signedDifference_inner_eq_zero`. -/
noncomputable def irrSubcoherent (τ : IntegralCharacterMap L G) (A : Set L)
    (Rdatum : ∀ χ ∈ S, CharacterDifferenceImage (L := L) (G := G) τ χ)
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hortho : OddOrder.Peterfalvi.S03.PairwiseOrthogonal S)
    (hconjsupp : ∀ χ ∈ S, ((χ - χ.conj : ClassFunction L ℂ)).support ⊆ A)
    (hiso : ∀ ⦃φ ψ : ClassFunction L ℂ⦄, φ ∈ zSupportedSpan (L := L) S A →
      ψ ∈ zSupportedSpan (L := L) S A →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ) :
    Hypothesis (L := L) (G := G) S A where
  tau := τ
  tau_isometry_diff := hiso
  conjugate_closed := hconj
  no_real_characters := hreal
  pairwise_orthogonal := hortho
  difference_image := fun χ hχ => Rdatum χ hχ
  difference_images_orthogonal := fun {φ χ} hφ hχ h1 h2 => by
    -- (5.2.e): reduce to `⟨signedDiff φ, signedDiff χ⟩ = 0`.
    refine (Rdatum φ hφ).orthogonal_of_signedDifference_inner_eq_zero (Rdatum χ hχ) ?_
    -- Rewrite both signed differences as `τ` applied to the conjugate differences.
    rw [← (Rdatum φ hφ).image_eq_signedDifference, ← (Rdatum χ hχ).image_eq_signedDifference]
    -- Conjugate differences lie in `ℤ[S, A]` (members + `hconjsupp`).
    have hmem : ∀ ⦃ψ : ClassFunction L ℂ⦄, ψ ∈ S →
        ψ - ψ.conj ∈ zSupportedSpan (L := L) S A := fun ψ hψ =>
      ⟨Submodule.sub_mem _ (Submodule.subset_span hψ) (Submodule.subset_span (hconj hψ)),
        hconjsupp _ hψ⟩
    -- Isometry: `⟨τ(φ−φ̄), τ(χ−χ̄)⟩ = ⟨φ−φ̄, χ−χ̄⟩`, then source orthogonality.
    rw [hiso (hmem hφ) (hmem hχ)]
    exact inner_conjugateDifference_eq_zero h1 h2

/-! ### `subset_subcoherent`: restricting a subcoherent family (Coq `PFsection5.v:845`)

Coq `PFsection5.v:845`:
```
Lemma subset_subcoherent S1 : cfConjC_subset S1 S -> subcoherent S1 tau R.
```
Given a subcoherent `subcoherent S tau R` and a `cfConjC_subset S1 S` (`S1 ⊆ S`, conjugate-closed),
every field of `subcoherent` restricts: `sub_in1`/`sub_in2` restrict the per-member `R`-datum and the
cross-orthogonality; `sub_iso_to`/`zchar_subset` restrict the isometry; the family predicates restrict
along the inclusion.  This is the first glue step of the (9.11) `Ptype_core_coherence` derived-series
induction (`PFsection9.v:1484`), where the full type-P subcoherent family is cut down to
`S_ H0C'` (and again to the uniform-degree sub-family `S1`) before `uniform_degree_coherence` fires.

The `S07.Hypothesis` transcription restricts identically: `tau` is unchanged, and each of the five
data/orthogonality fields is precomposed with the inclusion `hsub : S' ⊆ S`.  The
`conjugate_closed`ness of `S'` is *not* inherited automatically (a subset of a conjugate-closed set
need not itself be conjugate-closed), so it is taken as a hypothesis `hconj'` — exactly Coq's
`cfConjC_subset` carrying `ccS1`. -/

/-- **Peterfalvi (5.3)(a) restriction (`subset_subcoherent`).**

Restrict a subcoherent `S07.Hypothesis` on `S` to a subset `S' ⊆ S` that is itself conjugate-closed.
All fields restrict directly along the inclusion `hsub`; the base map `τ`, the difference isometry,
the no-real / pairwise-orthogonal predicates, the per-member `R`-datum, and the cross-orthogonality
all hold a fortiori on the smaller family.  Conjugate-closedness of `S'` (`hconj'`) is supplied
separately, matching Coq's `cfConjC_subset S' S` premise. -/
noncomputable def Hypothesis.restrict (hyp : Hypothesis (L := L) (G := G) S A)
    {S' : Set (ClassFunction L ℂ)} (hsub : S' ⊆ S)
    (hconj' : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S') :
    Hypothesis (L := L) (G := G) S' A where
  tau := hyp.tau
  tau_isometry_diff := fun {_φ _ψ} hφ hψ =>
    hyp.tau_isometry_diff (zSupportedSpan_mono_left hsub hφ) (zSupportedSpan_mono_left hsub hψ)
  conjugate_closed := hconj'
  no_real_characters := fun {_χ} hχ => hyp.no_real_characters (hsub hχ)
  pairwise_orthogonal := fun {_χ _ψ} hχ hψ hne => hyp.pairwise_orthogonal (hsub hχ) (hsub hψ) hne
  difference_image := fun {_χ} hχ => hyp.difference_image (hsub hχ)
  difference_images_orthogonal := fun {_φ _χ} hφ hχ h1 h2 =>
    hyp.difference_images_orthogonal (hsub hφ) (hsub hχ) h1 h2

/-- Alias of `Hypothesis.restrict` following the Coq lemma name `subset_subcoherent`
(`PFsection5.v:845`). -/
noncomputable def subset_subcoherent (hyp : Hypothesis (L := L) (G := G) S A)
    {S' : Set (ClassFunction L ℂ)} (hsub : S' ⊆ S)
    (hconj' : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S') :
    Hypothesis (L := L) (G := G) S' A :=
  hyp.restrict hsub hconj'

/-! ### `coherent_subset_of_constant_degree`: the (9.11) base-case / Galois glue

This is the reusable composition that Coq's `Ptype_core_coherence` (`PFsection9.v:1484`) invokes
twice:

* the Galois case `apply: uniform_degree_coherence scohS0` (the whole family `S_ H0C'` is uniform,
  degree `|M:HU|·u`), and
* the non-Galois base case `apply: uniform_degree_coherence (subset_subcoherent scohS0 sS10)` (the
  uniform sub-family `S1`, degree `q·a`, seeds the (9.11.1)-(9.11.8) pair-adjoining induction).

Both are `coherent_of_constant_degree ∘ subset_subcoherent`: restrict the subcoherent family to a
uniform-degree conjugate-closed subset, then fire the (5.7) equal-degree coherence producer.  Lane
a's (10.7) `typeII_derived_frobenius` (Coq `Frob_der1_type2`) consumes the same base-case glue on
the 4-element uniform T2 family. -/

/-- **Peterfalvi (5.7)∘(5.3)(a): coherence of a uniform-degree conjugate-closed subfamily.**

Given a subcoherent `S07.Hypothesis` on `S` and a *uniform-degree* conjugate-closed subset
`S' ⊆ S` (finite, `≥ 2` members, all irreducible with equal, nonzero degree, whose member
differences the base map `τ` sends into `ℤ[Irr G]` and which are `A`-supported), the subfamily
`(S', A, τ)` is coherent.

This factors the `uniform_degree_coherence (subset_subcoherent …)` idiom of the (9.11) proof: it
`subset_subcoherent`-restricts to `S'`, then applies `coherent_of_constant_degree`.  It is the base
case of the (9.11) derived-series induction and the whole Galois case; it is *not* the full (9.11)
coherence for a mixed-degree family (which needs the (9.11.1)-(9.11.8) pair-adjoining induction on
top of this base). -/
theorem coherent_subset_of_constant_degree
    (hyp : Hypothesis (L := L) (G := G) S A)
    {S' : Set (ClassFunction L ℂ)} (hsub : S' ⊆ S)
    (hconj' : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S')
    (hSfin : S'.Finite) (hcard : 2 ≤ S'.ncard)
    (hirr : ∀ ζ ∈ S', ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S', ∀ b ∈ S', hyp.tau (a - b) ∈ ZIrr G)
    (hconst : ∀ a ∈ S', ∀ b ∈ S',
      ((a : ClassFunction L ℂ) : L → ℂ) 1 = ((b : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ∀ a ∈ S', ((a : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0) (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ a ∈ S', ∀ b ∈ S', ((a - b : ClassFunction L ℂ)).support ⊆ A) :
    Nonempty (IsCoherent hyp.tau S' A) := by
  -- `(hyp.restrict hsub hconj').tau = hyp.tau` definitionally; rewrite `hZIrr` through it so the
  -- `coherent_of_constant_degree` application's `tau`-typed argument aligns syntactically.
  have htau : (hyp.restrict hsub hconj').tau = hyp.tau := rfl
  refine coherent_of_constant_degree (hyp.restrict hsub hconj') hSfin hcard hirr ?_ hconst hdeg0
    h1A hsuppdiff
  rw [htau]; exact hZIrr

/-! ### Multi-session build outline for `FTtypeP_subcoherent` and the (9.11) cascade

`irrSubcoherent` above is the (5.3)(a) *abstract* producer.  The full
`FTtypeP_subcoherent` (Coq `PFsection8.v:819`) and its consumption in
(9.11)/(10.7)/(13.3) require the following, in dependency order.  None is
attempted in this session; each item names the Coq mirror and the existing repo
pieces it would compose from.

**⚠ CORRECTED 2026-07-06** (prior draft of this note falsely claimed the prime-TI
machinery is "absent, grep 0 refs" and listed `prDade_subcoherent` as the gate —
both wrong, a Coq-name-grep false-negative, disproven by verify-first):

1. **`prDade_subcoherent`** (Coq `PFsection5.v:683`) does **NOT** need building.
   Its content is **already in the repo, sorry-free**: the prime-TI machinery is
   present under `certainType`/`columnFamily` names — the reducible-column `Rmu`
   R-datum is `S06.certainTypeR` (`S06_CertainTypeCoherence.lean:639`), and its
   coherence-free form `columnImageFamilyCohFree` (`S12_…_Core.lean:5619`).  The
   full (5.2.d)+(5.2.e) per-member R-datum + cross-orthogonality is **already
   assembled as `sixTwoDecompositionData`** (`S13_SixTwoBridge.lean:814`,
   sorry-free, from the issue-2022 lane-a loops).  Moreover a `prDade`-shaped
   `S07.Hypothesis` is **impossible** (Coq `subcoherent`'s `R` is variable-length
   — `2` for irreducibles, `2w₁` for reducible `μ_j` — while `S07.Hypothesis`'s
   `difference_image` hardcodes a 2-element `CharacterDifferenceImage`) **and has
   zero consumers** (every `S07.Hypothesis`/`IsCoherent` consumer takes an
   irreducible-only family; the reducible-column coherence is consumed directly
   as `S07.IsCoherent` via `certainType_isCoherent`, `S06:505`, in the §8 (6.8)
   case-B capstone).  So `irrSubcoherent` (irreducible producer) is the only
   `S07.Hypothesis`-form piece needed.

2. **The real gate is the (13.3) coherence route**, not `prDade`.  `coherent_H0Cprime_S`
   (`S15_SAndT_Setup.lean:572`) → `coherent_H0C_commutator` (S11) currently routes
   through `sibleyTarget_H0C` (S11:7775, sorried, **likely-UNSOUND** — `PU ≠ C'`
   kernel contradiction, same defect class as the reverted issue 2032).  Honest
   fix = re-ground it on the **(9.11) `Ptype_core_coherence`** 8-step derived-series
   induction (Coq `PFsection9.v:1484`), which composes `subset_subcoherent`
   (restrict a subcoherent family to a `cfConjC_subset`, Coq `PFsection5.v:845`) +
   `coherent_of_constant_degree` (= `uniform_degree_coherence`, **already proven**,
   `S07_CoherenceConstantDegree.lean:551`), with `sixTwoDecompositionData` as the
   subcoherent supply.  Lane a's (10.7) `typeII_derived_frobenius` consumes the
   same (9.11) coherence.

**LANDED 2026-07-06 (this file, sorry-free — `#print axioms` shows only
`propext`/`Classical.choice`/`Quot.sound`)**:
* `Hypothesis.restrict` / `subset_subcoherent` (Coq `PFsection5.v:845`): restrict a subcoherent
  `S07.Hypothesis` to a `cfConjC_subset` (conjugate-closed subset).
* `coherent_subset_of_constant_degree`: the `uniform_degree_coherence (subset_subcoherent …)`
  idiom — restrict to a *uniform-degree* conjugate-closed subset, then fire
  `coherent_of_constant_degree`.  This is the whole **Galois case** and the **base case `S1`** of
  the (9.11) derived-series induction.

**NOT re-grounded this session — genuine multi-step induction (honest verdict, verify-first
2026-07-06)**: `coherent_H0Cprime_S` cannot yet drop `sibleyTarget_H0C`.  The honest `S`-instance
family `chars.S = sSet` is **mixed-degree** (`(Ind_{HU}^M χ)(1) = q·χ(1)` for varying `χ(1)`;
`S11.induceHU_apply_one_eq_q_mul`), so `coherent_of_constant_degree` alone does **not** apply — it
is exactly Coq's **non-Galois case**, needing the (9.11.1)-(9.11.8) pair-adjoining induction on top
of the uniform base.  Precise remaining steps to fully replace `sibleyTarget_H0C`:

1. Assemble a subcoherent `S07.Hypothesis` for `sSet` on the honest Dade map `indS` (via
   `irrSubcoherent`, feeding per-member `R`-data from the §9 induced-family Dade witnesses).
2. `coherent_subset_of_constant_degree` on the uniform sub-family `S1 = {χ ∈ sSet | χ(1)=q·a}` —
   this base case is now reachable from (1) + the landed glue (Coq `cohS1`).
3. The **(9.11.1)-(9.11.8) induction proper** (Coq `PFsection9.v:1519-1660`): run
   `coherentPairChain` (`S07_Coherence.lean:4907`) from the `S1` base, adjoining conjugate pairs
   `{χ,χ̄}` up to `sSet` via `retarget_isCoherent_of_decompositions_and_memberFamily`
   (`S07_Coherence.lean:4083`).  The engine and the per-step (5.6) adjoining are **present and
   sorry-free**; the **missing analytic content** is each step's `hstep` data — the (5.6.2)
   integer-forcing `hY : Da.Y = a•Da.tau1 χ₁`, discharged in (9.11) by the norm chain
   `lb0 ≤ … ≤ sumnS S2 ≤ lb0` (Peterfalvi's `extend_coherent` + the `Snorm`/`sumnS` degree-sum
   bounds).  **UPDATE 2026-07-06: this norm chain is now landed sorry-free in the `Snorm`/`sumnS`
   section below** (`Snorm`/`sumnS`/`sumnS_image_eq_anchorSq_mul`/
   `two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS`/`lb0_le_lb1_of_degreeRatio_le`), with the
   `extend_coherent` positive engine identified as the pre-existing sorry-free `xAdjoinStepW`
   (`S08_CoherenceWeighted.lean:287`).  What remains is the (9.11.1)-(9.11.8) *assembly* — see the
   section's closing outline.

This norm chain was the single genuine analytic gap for both (13.3) [lane b] and (10.7)
`typeII_derived_frobenius` [lane a], which consumes the same (9.11) coherence on its 4-element T2
family.  **If that T2 family is uniform-degree, base case (2) may close (10.7) directly, without the
full induction — worth checking lane-a-side.**  Tracking = issue 1017. -/

/-! ### The `Snorm`/`sumnS` degree-square-over-norm quantity and the (9.11) `extend_coherent` core

**Peterfalvi (9.11) norm chain (Coq `Ptype_core_coherence`, `PFsection9.v:1484-1560`).**  The
non-Galois case of (9.11) runs the pair-adjoining induction (`coherentPairChain`,
`S07_Coherence.lean:4907`); each step's (5.6.2) integer-forcing `hY : Da.Y = a • Da.tau1 χ₁`
(the hypothesis of `retarget_isCoherent_of_decompositions_and_memberFamily`, `S07_Coherence.lean:4083`)
is discharged in Coq by the **squeeze**

`lb0 ≤ lb1 ≤ lb2 ≤ lb3 ≤ sumnS S1' ≤ sumnS S2 ≤ lb0`  (Coq `lb01`/`lb12`/`lb23`/`lb3S1'`/`lbS1'2`),

where `Snorm ψ = ψ(1)²/'[ψ]` and `sumnS Si = ∑_{ψ ∈ Si} Snorm ψ`, and the adjoining fires via
`extend_coherent` (Coq `PFsection5.v:1124`) the moment `lb0 < sumnS S2`.

**Verify-first (2026-07-06 lane-b):**
* The **`Snorm`/`sumnS` name** is genuinely absent from the repo (grep of the Coq names returns
  nothing); this section introduces it.
* The underlying **quantity** `∑ᵢ ψᵢ(1).re²/'[ψᵢ].re` and the `extend_coherent` **positive engine**
  are *not* absent.  The Peterfalvi (5.6) extension `extend_coherent`/`extend_coherent_with` is the
  landed, sorry-free `xAdjoinStepW` (`S08_CoherenceWeighted.lean:287`): given the anchor-normalized
  bound `hDeg : 2·a < ∑ᵢ deg(i)²/mc(i)` it produces coherence of `S₁ ∪ {χ, χ̄}`.  Its contrapositive
  is `coherentDegreeSqNormBound_of_not_coherentW` (`:635`), and the raw-degree `sumnS` bound
  `∑ᵢ χᵢ(1).re²/‖χᵢ‖² ≤ 2·ψ(1).re·η(1).re` is already assembled for the §8 case-B family as
  `sMember_degreeSqNormReBound_of_not_coherent` (`S08_CaseBEnumeration.lean:1080`).

So the (9.11) content still missing is **(i)** the named `Snorm`/`sumnS` quantity, **(ii)** the
*raw↔normalized* rescaling bridge `sumnS = anchorDeg²·(∑ deg²/mc)` (the `calc` currently duplicated
inline at `S08_CaseBEnumeration.lean:1118-1125`/`1170-1177`), and **(iii)** the (9.11) squeeze base
step `lb0 ≤ lb1` and the `extend_coherent`-firing precondition `lb0 < sumnS ⟹ 2·a < ∑ deg²/mc`.
This section lands (i)-(iii) sorry-free; the (9.11.2)-(9.11.8) family-specific squeeze steps
(`lb12`/`lb23`/`lb3S1'`, which pin down `C = U'` and the exact `|S1|`) remain, and are outlined at
the end of the section. -/

/-- **Peterfalvi (9.11): the degree-square-over-norm weight `Snorm ψ = ψ(1)²/'[ψ]` (real form).**

Coq `PFsection9.v:1534` `pose Snorm (psi : 'CF(M)) := psi 1%g ^+ 2 / '[psi]`.  The real-part form
`(ψ 1).re² / (⟨ψ,ψ⟩).re` used throughout §8 (`S08_CaseBEnumeration.lean:829`,
`S08_Theorem63.lean:46`): for an actual character `ψ`, `ψ(1)` is a real degree and `⟨ψ,ψ⟩` a positive
real, so this real form agrees with the complex `ψ(1)²/⟨ψ,ψ⟩`. -/
noncomputable def Snorm (ψ : ClassFunction L ℂ) : ℝ :=
  (ψ (1 : L)).re ^ 2 / (ClassFunction.inner ψ ψ).re

/-- **Peterfalvi (9.11): the summed degree-square-over-norm `sumnS Si = ∑_{ψ ∈ Si} Snorm ψ`.**

Coq `PFsection9.v:1535` `pose sumnS Si := \sum_(psi <- Si) Snorm psi`.  Taken over a `Finset` of
class functions (the finite subfamilies `S1'`, `S2` of the (9.11) induction). -/
noncomputable def sumnS (Si : Finset (ClassFunction L ℂ)) : ℝ :=
  ∑ ψ ∈ Si, Snorm ψ

@[simp] theorem sumnS_empty : sumnS (L := L) (∅ : Finset (ClassFunction L ℂ)) = 0 := by
  simp [sumnS]

/-- Each `Snorm` weight is nonnegative (`ψ(1).re²` is a square, `⟨ψ,ψ⟩.re ≥ 0`). -/
theorem Snorm_nonneg (ψ : ClassFunction L ℂ) : 0 ≤ Snorm (L := L) ψ :=
  div_nonneg (sq_nonneg _) (inner_self_re_nonneg ψ)

/-- `sumnS` of a finite family is nonnegative (sum of nonnegative `Snorm` weights). -/
theorem sumnS_nonneg (Si : Finset (ClassFunction L ℂ)) : 0 ≤ sumnS (L := L) Si :=
  Finset.sum_nonneg fun ψ _ => Snorm_nonneg ψ

/-- `sumnS` is monotone under `⊆` (adding nonnegative-`Snorm` members can only increase it). -/
theorem sumnS_le_of_subset {S₁ S₂ : Finset (ClassFunction L ℂ)} (h : S₁ ⊆ S₂) :
    sumnS (L := L) S₁ ≤ sumnS (L := L) S₂ :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ψ _ _ => Snorm_nonneg ψ

open scoped Classical in
/-- **Peterfalvi (9.11): the raw↔normalized rescaling bridge for `sumnS`.**

If every member `χmem i` has real degree a natural multiple of a common anchor degree `η` —
`χmem i (1) .re = deg(i)·η` (`hdeg`) — and squared norm `⟨χmem i, χmem i⟩.re = mc(i)` (`hmc`), then
the raw `sumnS` factors through the anchor degree:

`sumnS (image χmem s) = η² · ∑ᵢ deg(i)²/mc(i)`.

This is the `calc` block that §8 duplicates inline (`S08_CaseBEnumeration.lean:1118-1125`); factoring
it out is what lets the (9.11) squeeze `lb0 ≤ sumnS S2` (raw form) feed `xAdjoinStepW`'s
`hDeg : 2·a < ∑ᵢ deg(i)²/mc(i)` (anchor-normalized form). `hinj` makes the sum over the image agree
with the sum over the index set. -/
theorem sumnS_image_eq_anchorSq_mul {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction L ℂ)
    (deg : ι → ℕ) (mc : ι → ℝ) (η : ℝ) (hinj : Set.InjOn χmem s)
    (hdeg : ∀ i ∈ s, (χmem i (1 : L)).re = (deg i : ℝ) * η)
    (hmc : ∀ i ∈ s, (ClassFunction.inner (χmem i) (χmem i)).re = mc i) :
    sumnS (L := L) (s.image χmem) = η ^ 2 * ∑ i ∈ s, (deg i : ℝ) ^ 2 / mc i := by
  classical
  rw [sumnS, Finset.sum_image (fun a ha b hb => hinj ha hb), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Snorm, hdeg i hi, hmc i hi]
  ring

open scoped Classical in
/-- **Peterfalvi (9.11): the `extend_coherent`-firing precondition (raw `sumnS` ⟹ normalized bound).**

The bridge from the (9.11) squeeze `lb0 < sumnS S₁` (raw degree-sum form) to the anchor-normalized
degree bound `2·a < ∑ᵢ deg(i)²/mc(i)` that `xAdjoinStepW`/`retarget_isCoherent_of_decompositions`
consume (their `hDeg`/(5.6.2)-forcing input).  Here `lb0 = 2·a·η²` in the Coq chain
(`lb0 = 2·q·a·χ(1)` after rescaling by the anchor `η = χ₁(1)`), and `sumnS` factors as `η²·∑` by
`sumnS_image_eq_anchorSq_mul`; cancelling the positive `η² > 0` gives the normalized bound.

This is the load-bearing step: once the family-specific (9.11.1)-(9.11.8) arithmetic establishes
`lb0 < sumnS S₂` (Coq's `boolP (lb0 < sumnS S2)` branch, `PFsection9.v:1611`), *this* lemma converts
it to the `hDeg` that fires the adjoining engine on the running family. -/
theorem two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS {ι : Type*} (s : Finset ι)
    (χmem : ι → ClassFunction L ℂ) (deg : ι → ℕ) (mc : ι → ℝ) (η : ℝ) (a : ℝ)
    (hηpos : 0 < η) (hinj : Set.InjOn χmem s)
    (hdeg : ∀ i ∈ s, (χmem i (1 : L)).re = (deg i : ℝ) * η)
    (hmc : ∀ i ∈ s, (ClassFunction.inner (χmem i) (χmem i)).re = mc i)
    (hlb0 : 2 * a * η ^ 2 < sumnS (L := L) (s.image χmem)) :
    2 * a < ∑ i ∈ s, (deg i : ℝ) ^ 2 / mc i := by
  rw [sumnS_image_eq_anchorSq_mul s χmem deg mc η hinj hdeg hmc] at hlb0
  -- `2·a·η² < η²·∑`; cancel `η² > 0`.
  have hη2 : 0 < η ^ 2 := by positivity
  have h : η ^ 2 * (2 * a) < η ^ 2 * ∑ i ∈ s, (deg i : ℝ) ^ 2 / mc i := by
    rw [show η ^ 2 * (2 * a) = 2 * a * η ^ 2 by ring]; exact hlb0
  exact lt_of_mul_lt_mul_left h (le_of_lt hη2)

/-- **Peterfalvi (9.11): the base squeeze step `lb0 ≤ lb1` (Coq `lb01`).**

Coq `PFsection9.v:1560` `have lb01: lb0 <= lb1 ?= iff (chi 1%g == (q * u)%:R)`, with
`lb0 = 2·q·a·χ(1)` and `lb1 = 2·a·q²·u`.  In normalized form (dividing the Coq inequality by the
anchor degree `η = χ₁(1)` and writing `χ(1) = c·η`, i.e. `c = q·χ(1)/η` the degree ratio): the map
`c ↦ 2·a·c·η` is monotone in `c ≥ 0`, so the base bound `lb0` is at most `lb1 = 2·a·b·η` whenever the
degree ratio `c ≤ b` (Coq's `chi 1%g ≤ q*u`, the ordering that (9.11.1) forces to equality).  We
isolate the pure-arithmetic monotonicity (over `ℝ`, `η ≥ 0`, `a ≥ 0`); the identification of `c`, `b`
with the group-theoretic `q·χ(1)`, `q²·u` is supplied by the family. -/
theorem lb0_le_lb1_of_degreeRatio_le {a c b η : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η) (hcb : c ≤ b) :
    2 * a * c * η ≤ 2 * a * b * η := by
  have h2a : 0 ≤ 2 * a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hcb h2a, mul_nonneg h2a hη]

/-- **`Snorm` of a norm-one class function is its squared real degree** (`⟨ψ,ψ⟩.re = 1 ⟹
Snorm ψ = ψ(1).re²`).  For an irreducible character `ψ`, `IsIrreducibleCharacter.inner_self_eq_one`
gives `⟨ψ,ψ⟩ = 1`, hence `⟨ψ,ψ⟩.re = 1`; this is the `Snorm ψ = ψ(1)²` specialization used on the
uniform sub-family `S1'` of Peterfalvi (9.11), whose members are irreducible of degree `q·a`. -/
theorem Snorm_of_inner_self_re_one {ψ : ClassFunction L ℂ}
    (hψ : (ClassFunction.inner ψ ψ).re = 1) : Snorm (L := L) ψ = (ψ (1 : L)).re ^ 2 := by
  rw [Snorm, hψ, div_one]

/-- **`sumnS` of a family with constant `Snorm` weight** (`Snorm ψ = v` on `Si ⟹
sumnS Si = |Si|·v`).  The `Finset.sum_const` specialization of `sumnS`. -/
theorem sumnS_constant {Si : Finset (ClassFunction L ℂ)} {v : ℝ}
    (h : ∀ ψ ∈ Si, Snorm ψ = v) : sumnS (L := L) Si = (Si.card : ℝ) * v := by
  rw [sumnS, Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

/-- **Peterfalvi (9.11): the uniform sub-family `sumnS` value (Coq `lb3S1'` left endpoint).**

If every member of `Si` is norm-one (`⟨ψ,ψ⟩.re = 1`, e.g. irreducible) of common real degree `d`,
then `sumnS Si = |Si|·d²`.  This is the value Coq computes for `sumnS S1'` (`PFsection9.v:1607`,
`rewrite (eq_bigr (fun _ => ((q * a) ^ 2)%:R))`): on `S1'` every member is irreducible of degree
`q·a`, so `Snorm ≡ (q·a)²` and `sumnS S1' = |S1'|·(q·a)²` — the left endpoint of the `lb3 ≤ sumnS S1'`
squeeze step, combined with the `lb_Sqa` lower bound `|S1'| ≥ (p−1)·|U:U'| / a²`. -/
theorem sumnS_of_norm_one_constant_degree {Si : Finset (ClassFunction L ℂ)} {d : ℝ}
    (hnorm : ∀ ψ ∈ Si, (ClassFunction.inner ψ ψ).re = 1)
    (hdeg : ∀ ψ ∈ Si, (ψ (1 : L)).re = d) :
    sumnS (L := L) Si = (Si.card : ℝ) * d ^ 2 :=
  sumnS_constant fun ψ hψ => by rw [Snorm_of_inner_self_re_one (hnorm ψ hψ), hdeg ψ hψ]

/-- **Peterfalvi (9.11): the `lb12` divisibility monotonicity `2a ≤ p−1` (`≤` form).**

Coq `PFsection9.v:1571` `have lb12: lb1 <= lb2 ?= iff (a == p.-1./2)`, with `lb1 = 2·a·q²·u` and
`lb2 = (p−1)·q²·u`.  After cancelling the positive `q²·u` the content is purely `ℕ`: with
`a ∣ (p−1)` (Coq `a_dvd_pm1`), `a` odd (odd order), and `p` odd — so `p−1` even (Coq
`Dp: p = 2·(p.-1./2)+1`) —
Gauss's lemma (`Nat.Coprime 2 a`, `a` odd) upgrades `a ∣ m` and `2 ∣ m` to `2·a ∣ m`, hence
`2·a ≤ m` by `Nat.le_of_dvd`.  Stated as a pure `ℕ` lemma; the caller identifies `m = p−1` and
multiplies through by `q²·u`. -/
theorem two_mul_le_of_dvd_of_odd {a m : ℕ} (hdvd : a ∣ m) (ha : Odd a) (hm : Even m)
    (hm0 : 0 < m) : 2 * a ≤ m :=
  Nat.le_of_dvd hm0 (ha.coprime_two_left.mul_dvd_of_dvd_of_dvd hm.two_dvd hdvd)

/-- **Peterfalvi (9.11): the `2·a ∣ (p−1)` fact underlying `lb12`'s equality clause.**

The divisibility that `two_mul_le_of_dvd_of_odd` bounds with.  Exposed separately so the caller can
extract the `lb12` `?= iff (a == p.-1./2)` equality: `2·a ∣ m` gives `2·a = m ↔ …`, and the equality
`2·a = m` (i.e. `a = m/2 = (p−1)/2`) is exactly the (9.11.1) `without loss` normalization forcing
`a = (p−1)/2`.  Pure `ℕ`; identification of `m = p−1` deferred to the caller. -/
theorem two_mul_dvd_of_dvd_of_odd {a m : ℕ} (hdvd : a ∣ m) (ha : Odd a) (hm : Even m) :
    2 * a ∣ m :=
  ha.coprime_two_left.mul_dvd_of_dvd_of_dvd hm.two_dvd hdvd

/-- **Peterfalvi (9.11): the strict `lb12` bound `2·a < p−1` off the equality (`<` form).**

The strict companion of `two_mul_le_of_dvd_of_odd`: when the `lb12` equality clause fails
(`2·a ≠ p−1`, i.e. `a ≠ (p−1)/2`) the squeeze `lb1 ≤ lb2` is strict.  Pure `ℕ`; `m = p−1`
deferred. -/
theorem two_mul_lt_of_dvd_of_odd_of_ne {a m : ℕ} (hdvd : a ∣ m) (ha : Odd a) (hm : Even m)
    (hm0 : 0 < m) (hne : 2 * a ≠ m) : 2 * a < m :=
  lt_of_le_of_ne (two_mul_le_of_dvd_of_odd hdvd ha hm hm0) hne

/-- **Peterfalvi (9.11): the `lb23` subgroup-index monotonicity `[U:C] ≤ [U:U']` (`≤` form).**

Coq `PFsection9.v:1590` `have lb23: lb2 <= lb3 ?= iff (C :==: U')`, with `lb2 = (p−1)·q²·u`,
`lb3 = (p−1)·q²·[U:U']` and `u = [U:C]`.  After cancelling `(p−1)·q²` the content is Lagrange
monotonicity of relative index: for nested subgroups `U' ≤ C ≤ U`, the relative index `[U:C]`
(`= C.relIndex U`) divides `[U:U']` (`Subgroup.relIndex_dvd_of_le_left`, the `U' ≤ C` half), so
`[U:C] ≤ [U:U']` (`Nat.le_of_dvd`, `[U:U'] > 0` from finiteness).  Stated group-theoretically over
an abstract finite group `Γ`; the caller identifies `u = [U:C]`, `[U:U']`, `p−1`, `q²` and the
ambient group.  (`_hCU : C ≤ U` records the full `U' ≤ C ≤ U` nesting of the `lb23` datum; the `≤`
bound itself needs only `U' ≤ C`, the strict/equality companion below uses both.) -/
theorem relIndex_le_relIndex_of_le {Γ : Type*} [Group Γ] [Finite Γ] {U' C U : Subgroup Γ}
    (hU'C : U' ≤ C) (_hCU : C ≤ U) : C.relIndex U ≤ U'.relIndex U :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.relIndex_dvd_of_le_left U hU'C)

/-- **Peterfalvi (9.11): the strict `lb23` bound off the equality (`C ≠ U' ⟹ [U:C]<[U:U']`).**

The strict companion of `relIndex_le_relIndex_of_le` supplying the `lb23` `?= iff (C:==:U')` clause.
From `[U:U'] = [C:U']·[U:C]` (`Subgroup.relIndex_mul_relIndex`, `U' ≤ C ≤ U`), equality
`[U:C] = [U:U']` forces `[C:U'] = 1` (cancel the positive `[U:U']`), i.e. `C ≤ U'`
(`Subgroup.relIndex_eq_one`); with `U' ≤ C` this is `C = U'`.  Contrapositive: `C ≠ U'` makes the
`lb23` squeeze strict.  Group-theoretic over a finite `Γ`; identification deferred to the caller. -/
theorem relIndex_lt_relIndex_of_le_of_ne {Γ : Type*} [Group Γ] [Finite Γ] {U' C U : Subgroup Γ}
    (hU'C : U' ≤ C) (hCU : C ≤ U) (hne : C ≠ U') : C.relIndex U < U'.relIndex U := by
  refine lt_of_le_of_ne (relIndex_le_relIndex_of_le hU'C hCU) ?_
  intro heq
  have hcomp : U'.relIndex C * C.relIndex U = U'.relIndex U :=
    Subgroup.relIndex_mul_relIndex U' C U hU'C hCU
  rw [heq] at hcomp
  have hpos : 0 < U'.relIndex U := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hone : U'.relIndex C = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hcomp)
  exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp hone) hU'C)

/-! ### Remaining (9.11.1)-(9.11.8) induction steps (outline, honest verdict 2026-07-06)

With the `Snorm`/`sumnS` quantity (above), the `extend_coherent` positive engine
(`xAdjoinStepW`, sorry-free), the raw↔normalized bridge (`sumnS_image_eq_anchorSq_mul`), the
firing precondition (`two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS`), and the base squeeze step
(`lb0_le_lb1_of_degreeRatio_le`) landed, the residual for the full (9.11) non-Galois coherence is:

* **(9.11.2)-(9.11.4)** — the *middle* squeeze steps `lb1 ≤ lb2 ≤ lb3` (Coq `lb12`/`lb23`,
  `PFsection9.v:1571-1596`).  **Landed** as pure lemmas above: `lb12` = `two_mul_le_of_dvd_of_odd`
  (+ `two_mul_dvd_of_dvd_of_odd`/`two_mul_lt_of_dvd_of_odd_of_ne` for the `?= iff (a==p.-1./2)`
  equality clause; `a ∣ (p−1)` + `a` odd + `p−1` even ⟹ `2·a ∣ (p−1)` by Gauss), and `lb23` =
  `relIndex_le_relIndex_of_le` (+ `relIndex_lt_relIndex_of_le_of_ne` for the `?= iff (C:==:U')`
  clause; Lagrange `[U:U'] = [C:U']·[U:C]` for `U' ≤ C ≤ U`).  The caller multiplies `lb12` by
  `q²·u` and `lb23` by `(p−1)·q²` and identifies `u = [U:C]`.  No new analytic content.
* **(9.11.5)** — `lb3 ≤ sumnS S1'` (Coq `lb3S1'`, `PFsection9.v:1596`): the uniform sub-family `S1'`
  has every member of degree `q·a`, so `Snorm ≡ (q·a)²` on it and `sumnS S1' = |S1'|·(q·a)²`; combine
  with the base-case lower bound `|S1| ≥ (p−1)·u/a²` (Coq `lb_Sqa`, the type-P `lb_Sqa` datum).  The
  uniform-`Snorm` computation is `sumnS_image_eq_anchorSq_mul` specialized to constant `deg`.
* **(9.11.6)** — `sumnS S1' ≤ sumnS S2` (Coq `lbS1'2`, `PFsection9.v:1601`): `sumnS_le_of_subset`
  above (`S1' ⊆ S2`, all `Snorm ≥ 0`).  **Landed** as a reusable lemma.
* **(9.11.1)/(9.11.7)/(9.11.8)** — the `without loss` normalization + the maximality contradiction
  (Coq `PFsection9.v:1519-1540`, `1640-1660`): the induction skeleton, driven by `coherentPairChain`
  from the `S1` base (`coherent_subset_of_constant_degree`, landed) adjoining pairs to `S2` via
  `retarget_isCoherent_of_decompositions_and_memberFamily`, whose `hY` per step is discharged by the
  `lb0 < sumnS S2` branch (`extend_coherent`) using the firing precondition above.

**Verdict + effort.**  The single *analytic* gap named in the issue — the `Snorm`/`sumnS` degree-sum
quantity and the `extend_coherent` integer-forcing bridge — is now landed sorry-free.  What remains
is the **assembly** of the (9.11) induction: the middle squeeze steps (9.11.2-9.11.5) are ℕ-index
arithmetic (medium, mechanical), and (9.11.1)/(9.11.7)/(9.11.8) are the `coherentPairChain` fold
against the honest §9 induced-family Dade witnesses (the per-step `Dmem`/`hmemOrtho`/`hgen` data, as
in `S08_CaseBEnumeration.sMember_degreeSqNormBound_of_not_coherent`, but for the §9 `S_ H0C'` family
rather than §8 case-B).  This is **one focused multi-step session** for lane b's (13.3)
`coherent_H0Cprime_S` re-grounding (drop `sibleyTarget_H0C`) once the §9 induced-family witnesses
are threaded, and the same (9.11) coherence closes lane a's (10.7) `typeII_derived_frobenius`.
Tracking = issue 1017. -/

/-! ### Peterfalvi (9.11): the maximal-coherent-subfamily skeleton

The (9.11) non-Galois induction opens (mmd 04.11, (9.11) proof): *"Let `𝒮₂` be maximal such that
`𝒮₁ ⊂ 𝒮₂ ⊂ 𝒮(H₀C′)`, `𝒮₂` is coherent and `𝒮₂` is closed under complex conjugation.  Let
`𝒮₃ = 𝒮(H₀C′) − 𝒮₂`.  Suppose that `𝒮₃ ≠ ∅`."* — and the eight steps (9.11.1)–(9.11.8) refute
that supposition, so `𝒮₂ = 𝒮(H₀C′)` and the family is coherent.  (Coq `Ptype_core_coherence`
runs the same argument as an induction on `|𝒮₃|`, `PFsection9.v:1516-1540`; the maximal-subfamily
form is the book's, and is what we formalize.)

This subsection provides the **family-agnostic skeleton** of that argument:

* `exists_maximal_coherent_between` — a maximal coherent conjugation-closed intermediate `𝒮₂`
  exists (finiteness of the ambient family; the analogue for coherent subfamilies of
  `exists_maximal_normal_between`);
* `coherent_of_maximal_coherent_refuted` — if every maximal *proper* `𝒮₂` is absurd, the full
  family is coherent;
* `coherent_of_maximal_coherent_pair_refuted` — the conjugate-pair specialization: the refuter
  receives exactly the (9.11) situation — a proper coherent conj-closed `𝒮₂ ⊇ 𝒮₁` with `𝒮₃ ≠ ∅`
  such that **no conjugate pair `{χ, χ̄}`, `χ ∈ 𝒮₃`, can be adjoined coherently** — and must
  derive `False`.

The (9.11.1) squeeze discharges the refuter: either the degree bound `lb0 < sumnS 𝒮₂` fires the
(5.6) adjoining engine (`xAdjoinStepW`/`xAdjoinStepW_k`) on some `χ ∈ 𝒮₃` — contradicting the
pair clause — or all squeeze inequalities are equalities, a configuration refuted by
(9.11.2)–(9.11.8).  Consumers: lane b's (13.3) `coherent_H0Cprime_S` re-grounding (S-instance),
lane a's gate-2 `hY` (`coherent_Sset_diff_SHCSet`, issue 9016) and (10.7)
`typeII_derived_frobenius`. -/

/-- **Peterfalvi (9.11): a maximal coherent conjugation-closed subfamily exists.**

*"Let `𝒮₂` be maximal such that `𝒮₁ ⊂ 𝒮₂ ⊂ 𝒮(H₀C′)`, `𝒮₂` is coherent and `𝒮₂` is closed
under complex conjugation."*  For a finite ambient family `S`, the collection of coherent
conjugation-closed intermediates `S₁ ⊆ S₂ ⊆ S` is finite and contains `S₁`, so a maximal one
exists (`Set.Finite.exists_maximalFor` on subset order).  The maximality clause is stated in the
"any bigger candidate collapses" form consumed by the refutation skeleton. -/
theorem exists_maximal_coherent_between
    {τ : IntegralCharacterMap L G} {A : Set L}
    {S S₁ : Set (ClassFunction L ℂ)} (hSfin : S.Finite) (hS₁S : S₁ ⊆ S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (h0 : Nonempty (IsCoherent τ S₁ A)) :
    ∃ S₂ : Set (ClassFunction L ℂ), S₁ ⊆ S₂ ∧ S₂ ⊆ S ∧
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ ∧ Nonempty (IsCoherent τ S₂ A) ∧
      ∀ S' : Set (ClassFunction L ℂ), S' ⊆ S →
        OddOrder.Peterfalvi.S03.ClosedUnderConjugate S' → Nonempty (IsCoherent τ S' A) →
        S₂ ⊆ S' → S' = S₂ := by
  classical
  obtain ⟨S₂, hmem, hmax⟩ :=
    Set.Finite.exists_maximalFor (id : Set (ClassFunction L ℂ) → Set (ClassFunction L ℂ))
      {T | S₁ ⊆ T ∧ T ⊆ S ∧ OddOrder.Peterfalvi.S03.ClosedUnderConjugate T ∧
        Nonempty (IsCoherent τ T A)}
      (hSfin.finite_subsets.subset fun _ hT => hT.2.1)
      ⟨S₁, subset_rfl, hS₁S, hS₁conj, h0⟩
  obtain ⟨hS₁S₂, hS₂S, hS₂conj, hS₂coh⟩ := hmem
  refine ⟨S₂, hS₁S₂, hS₂S, hS₂conj, hS₂coh, fun S' hS'S hS'conj hS'coh hS₂S' => ?_⟩
  exact le_antisymm (hmax ⟨hS₁S₂.trans hS₂S', hS'S, hS'conj, hS'coh⟩ hS₂S') hS₂S'

/-- **Peterfalvi (9.11): the refute-the-maximal-subfamily skeleton.**

If every *proper* maximal coherent conjugation-closed intermediate `S₁ ⊆ S₂ ⊊ S` is absurd
(`hrefute` receives its maximality clause and must produce `False`), then the full family `S` is
coherent.  This is the outermost reduction of the (9.11) proof: the maximal `S₂` of
`exists_maximal_coherent_between` either equals `S` (done) or is handed to the refuter. -/
theorem coherent_of_maximal_coherent_refuted
    {τ : IntegralCharacterMap L G} {A : Set L}
    {S S₁ : Set (ClassFunction L ℂ)} (hSfin : S.Finite) (hS₁S : S₁ ⊆ S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (h0 : Nonempty (IsCoherent τ S₁ A))
    (hrefute : ∀ S₂ : Set (ClassFunction L ℂ), S₁ ⊆ S₂ → S₂ ⊆ S →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ → Nonempty (IsCoherent τ S₂ A) →
      S₂ ≠ S →
      (∀ S' : Set (ClassFunction L ℂ), S' ⊆ S →
        OddOrder.Peterfalvi.S03.ClosedUnderConjugate S' → Nonempty (IsCoherent τ S' A) →
        S₂ ⊆ S' → S' = S₂) → False) :
    Nonempty (IsCoherent τ S A) := by
  obtain ⟨S₂, hS₁S₂, hS₂S, hS₂conj, hS₂coh, hS₂max⟩ :=
    exists_maximal_coherent_between hSfin hS₁S hS₁conj h0
  by_cases hS₂eq : S₂ = S
  · exact hS₂eq ▸ hS₂coh
  · exact (hrefute S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₂eq hS₂max).elim

/-- **Peterfalvi (9.11): the conjugate-pair form of the maximal-subfamily refutation.**

The specialization the (9.11) argument actually runs: the refuter receives a proper coherent
conjugation-closed `S₁ ⊆ S₂ ⊊ S` together with `𝒮₃ = S \ S₂ ≠ ∅` and the fact that **no
conjugate pair `{χ, χ̄}` with `χ ∈ 𝒮₃` can be coherently adjoined** — the negation of what the
(5.6) adjoining engine would produce.  Maximality converts a successful adjoining
`IsCoherent τ (S₂ ∪ {χ, χ̄}) A` into `S₂ ∪ {χ, χ̄} = S₂`, contradicting `χ ∉ S₂`; so the pair
clause holds for the maximal `S₂` and the refuter applies.  Requires the ambient family to be
conjugation-closed (so the adjoined pair stays inside `S`). -/
theorem coherent_of_maximal_coherent_pair_refuted
    {τ : IntegralCharacterMap L G} {A : Set L}
    {S S₁ : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (hSconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S) (hS₁S : S₁ ⊆ S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (h0 : Nonempty (IsCoherent τ S₁ A))
    (hrefute : ∀ S₂ : Set (ClassFunction L ℂ), S₁ ⊆ S₂ → S₂ ⊆ S →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ → Nonempty (IsCoherent τ S₂ A) →
      (S \ S₂).Nonempty →
      (∀ χ ∈ S \ S₂, ¬ Nonempty (IsCoherent τ (S₂ ∪ {χ, χ.conj}) A)) → False) :
    Nonempty (IsCoherent τ S A) := by
  refine coherent_of_maximal_coherent_refuted hSfin hS₁S hS₁conj h0 ?_
  intro S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₂ne hS₂max
  have hS₃ne : (S \ S₂).Nonempty := by
    rcases Set.eq_empty_or_nonempty (S \ S₂) with he | hne
    · exact absurd (Set.Subset.antisymm hS₂S (fun ψ hψ => by
        by_contra hψ₂
        exact Set.notMem_empty ψ (he ▸ Set.mem_diff_of_mem hψ hψ₂))) hS₂ne
    · exact hne
  refine hrefute S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne ?_
  rintro χ ⟨hχS, hχS₂⟩ ⟨hcoh'⟩
  have hS'S : S₂ ∪ {χ, χ.conj} ⊆ S := by
    rintro ψ (hψ | hψ)
    · exact hS₂S hψ
    · rcases hψ with rfl | hψ
      · exact hχS
      · rw [Set.mem_singleton_iff] at hψ
        exact hψ ▸ hSconj hχS
  have hS'conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (S₂ ∪ {χ, χ.conj}) := by
    rintro ψ (hψ | hψ)
    · exact Or.inl (hS₂conj hψ)
    · rcases hψ with rfl | hψ
      · exact Or.inr (Set.mem_insert_of_mem _ rfl)
      · rw [Set.mem_singleton_iff] at hψ
        subst hψ
        exact Or.inr (Set.mem_insert_iff.mpr (Or.inl (ClassFunction.conj_conj χ)))
  have heq := hS₂max _ hS'S hS'conj ⟨hcoh'⟩ Set.subset_union_left
  exact hχS₂ (heq ▸ Set.mem_union_right _ (Set.mem_insert _ _))

end OddOrder.Peterfalvi.S07
