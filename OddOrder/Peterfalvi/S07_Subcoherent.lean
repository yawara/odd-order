/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_Coherence

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
  (`PFsection8.v:819`)  ↦  **NOT here**: those instantiate the prime-Dade
  hypothesis and depend on the §3/§4 prime-TI machinery (`primeTIred`,
  `cyclicTIiso`) not yet in the repo.  See the module note at the end of this
  file for the multi-session outline.

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

/-! ### Multi-session build outline for `FTtypeP_subcoherent` and the (9.11) cascade

`irrSubcoherent` above is the (5.3)(a) *abstract* producer.  The full
`FTtypeP_subcoherent` (Coq `PFsection8.v:819`) and its consumption in
(9.11)/(10.7)/(13.3) require the following, in dependency order.  None is
attempted in this session; each item names the Coq mirror and the existing repo
pieces it would compose from.

1. **`prDade_subcoherent`** (Coq `PFsection5.v:683`, "(5.3)(b)").  Specializes
   `irr_subcoherent` to the **prime-Dade** setting: `S ⊆ seqIndD K L H 1`, the
   Dade map `τ = Dade ddA`, and — crucially — pins the `R`-datum on the
   *reducible* members `μ_j = primeTIred` to the explicit cyclic-TI value
   `Rmu j = dsw j j ++ map -%R (dsw j (conjC_Iirr j))`.
   *Blocked on*: the §3/§4 **prime-TI machinery** (`primeTIred`, `cyclicTIiso`,
   `primeTIsign`, `cyclicTIirr`) — **absent in the repo** (grep 0 refs, confirmed
   in issue 1017 RE-DIAGNOSIS).  This is the single largest missing block and is
   an ungated, unowned shared-infra leaf (claim under a 9000-series issue before
   building).  The irreducible-member part reuses `irrSubcoherent`; only the
   reducible-column `Rmu` needs the new prime-TI values.

2. **`FTtypeP_subcoherent`** (Coq `PFsection8.v:819`).  A thin instantiation of
   item 1 at the Feit–Thompson type-P data: `K = M`_s`, `A = 'A(M)`,
   `A0 = 'A0(M)`, via `FT_prDade_hyp` (`PFsection8.v:800`).  Reuses the repo's
   `FTtypeP`/`Hypothesis M` type-P infrastructure (S08/S12).  Once item 1 lands
   this is mechanical.

3. **(9.11) `Ptype_core_coherence`** (Coq `PFsection9.v:1484`,
   `coherent (S_ H0C') M^#`).  The honest route (issue 1017, lane-b update):
   an 8-step induction over the derived-series filtration that at each step
   invokes `coherent_of_constant_degree` (already proven `= uniform_degree_coherence`,
   `S07_CoherenceConstantDegree.lean`) on a uniform-degree sub-family cut out by
   `subset_subcoherent` from `FTtypeP_subcoherent` (item 2).  Composes from:
   `coherent_of_constant_degree` (have), item 2 (missing), and a
   `subset_subcoherent`-analog — i.e. **restrict `S07.Hypothesis` to a
   `cfConjC_subset` sub-family** (Coq `subset_subcoherent`, `PFsection5.v:845`),
   a small, ungated lemma reachable *now* on top of `irrSubcoherent`
   (next-session candidate: `Hypothesis.restrict`).

4. **(10.7) `typeII_derived_frobenius`** (`S12_MaximalIII_IV_V_Core.lean:47`;
   Coq `Frob_der1_type2`, `PFsection10.v:549`).  Consumes item 3's coherence on
   the 4-element uniform family `T2` (lane a's (10.8) `typeII_coherence_..._estimate`
   hB side).  Also needs `IsTypeF (derivedInG S)` upgrade (issue 1017 item 3).

5. **(13.3) `character_degree_analysis` τ₁-coherence** (lane b).  Currently routed
   through `sibleyTarget_H0C` (S11), flagged **likely-unsound** (issue 1017
   2026-07-06 update: `PU ≠ C'` kernel contradiction, same defect class as issue
   2032).  Honest fix = re-ground `coherent_H0Cprime_S` on the item 3 route
   (subcoherent + `coherent_of_constant_degree`), a signature-preserving internal
   re-proof, *after* items 1–3 land.

**Reachable now (next session, no prime-TI needed)**: `Hypothesis.restrict`
(item 3's `subset_subcoherent`) and further `irrSubcoherent`-based API.  Item 1
(prime-TI) is the true gate for everything downstream and should be claimed as
shared infra first. -/

end OddOrder.Peterfalvi.S07
