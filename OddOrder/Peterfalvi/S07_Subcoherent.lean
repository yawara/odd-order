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
* `τ` a lattice-relative difference isometry on `S` (`hiso`), and
* per-member difference images `Rdatum χ : CharacterDifferenceImage τ χ` whose
  underlying map is `τ` and whose image obeys `τ(χ − χ̄) = ε·(μ − ν)`,

this constructs the subcoherent `S07.Hypothesis` record on `S` with base `τ` and
`A = L^#` (here any `A`; the isometry field is `A`-agnostic).  This is the missing
top-level producer that every §7/§14 consumer currently hand-assembles.

Field (e) `difference_images_orthogonal` is derived: from `⟨φ, χ⟩ = 0` and
`⟨φ, χ̄⟩ = 0`, `inner_conjugateDifference_eq_zero` gives `⟨φ − φ̄, χ − χ̄⟩ = 0`;
the difference isometry `hiso` transports this to `⟨(φ−φ̄)^τ, (χ−χ̄)^τ⟩ = 0`, i.e.
`⟨signedDiff φ, signedDiff χ⟩ = 0` (via `image_eq`), feeding
`orthogonal_of_signedDifference_inner_eq_zero`. -/
noncomputable def irrSubcoherent (τ : IntegralCharacterMap L G) (A : Set L)
    (Rdatum : ∀ χ ∈ S, CharacterDifferenceImage (L := L) (G := G) τ χ)
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hortho : OddOrder.Peterfalvi.S03.PairwiseOrthogonal S)
    (hiso : ∀ ⦃a b c d : ClassFunction L ℂ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      ClassFunction.inner (τ (a - b)) (τ (c - d)) = ClassFunction.inner (a - b) (c - d)) :
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
    -- Isometry: `⟨τ(φ−φ̄), τ(χ−χ̄)⟩ = ⟨φ−φ̄, χ−χ̄⟩`, then source orthogonality.
    rw [hiso hφ (hconj hφ) hχ (hconj hχ)]
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
  tau_isometry_diff := fun {_a _b _c _d} ha hb hc hd =>
    hyp.tau_isometry_diff (hsub ha) (hsub hb) (hsub hc) (hsub hd)
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
   bounds).  This norm chain is **not yet in the repo** (the (6.6) chain uses the simpler
   `two_mul_lt_sq_of_primePow_gap` gap, not the (9.11) `sumnS` arithmetic).

This norm chain is the single genuine gap for both (13.3) [lane b] and (10.7)
`typeII_derived_frobenius` [lane a], which consumes the same (9.11) coherence on its 4-element T2
family.  **If that T2 family is uniform-degree, base case (2) may close (10.7) directly, without the
full induction — worth checking lane-a-side.**  Tracking = issue 1017. -/

end OddOrder.Peterfalvi.S07
