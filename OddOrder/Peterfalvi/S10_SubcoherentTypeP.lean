/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S10_MinimalSimpleBasic
import OddOrder.Peterfalvi.S07_Subcoherent
import OddOrder.Peterfalvi.S08_SixTwoGeneral

/-!
# Peterfalvi (8.15), claim 3: Hypothesis (5.2) for the type-`P` induced family

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, (8.15) claim 3, pp. 47-48 (issue 1042).

**(8.15), claim 3**: if `M` is of type `P` and `𝒮 ⊆ {Ind_{M'}^M θ | θ ∈ Irr M', M_s ⊄ Ker θ}`
is non-empty and stable under complex conjugation, then Hypothesis (5.2) holds with `L = M`
(proof from (1.5.e) + (5.3.b)).  Coq mirror: `FTtypeP_subcoherent` (`PFsection8.v:819`),
instantiating `prDade_subcoherent` (= (5.3.b), `PFsection5.v:683`) at
`calS = seqIndD M^`(1) M M`_\s 1`.

## What this file provides

The two producers `inducedKernelFamily_subcoherent` (support parameter `A₀(M)`, the repo
consumer shape) and `inducedKernelFamily_subcoherent_sharp` (support parameter `M^#`, the
book-literal (5.2.b) shape), assembling `S07.Hypothesis` — the ported (5.2) structure — for any
conjugation-closed family `S` of **irreducible** members of the type-`P` induced family
`S(⊥) = {Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1}` (`S08.inducedKernelFamily`), over the honest Dade
map of the (8.15) claim-1 datum `DadeSupportHypothesisData M (A₀(M))`
(`dadeSupportHypothesisData_typePA0_of_isTypeP1`, `S10_MinimalSimpleBasic`).

Everything is assembled via the (5.3.a) producer `S07.irrSubcoherent` from landed bricks:

* per-member `R(χ)`-datum: `S07.dadeCharacterDifferenceImageOfDiff` (the 2-element
  `CharacterDifferenceImage` from the Dade isometry);
* family predicates ((1.5.e)-side inputs of the book proof): the
  `S08.inducedKernelFamily_{closedUnderConjugate, hasNoRealCharacters, pairwise_orthogonal}`
  suite;
* conjugate-difference support: `S08.inducedKernelFamily_conjDiff_support` fed by the (8.10)
  containment `(M')^# ⊆ A₀(M)` (`mderivSharp_subset_supportInSubgroup_typePA0` below, the
  §8-level form of `S12.Hypothesis.mderivSharp_subset_A0`);
* (5.2.b) lattice isometry: `S07.dadeIntegralCharacterMap_inner_eq_of_supported`
  (unconditional on the `A₀`-supported sublattice; for the `M^#` shape the support narrows
  through `Z[S, M^#] ⊆ CF(M, (M')^#)` — members vanish off the normal `M'`, so a span member
  vanishing at `1` is `(M')^#`-supported, `inducedKernelFamily_member_support_subset_derivedInG`
  + `S07.support_subset_of_mem_zSpan_of_supported`).

## Scope notes (issue 1042 / 9008)

* **Irreducible members only**: the book's `𝒮` may contain reducible members `μ_j`
  (`Ind θ` for `M`-invariant `θ`), whose (5.2.d) datum is the `2w₁`-element column family — not
  expressible in `S07.Hypothesis` (its `difference_image` hardcodes the 2-element
  `CharacterDifferenceImage`).  The reducible-column `R`-datum lives under the prime-TI names
  (`S06.certainTypeR`, `columnImageFamilyCohFree`) — see the corrected module note in
  `S07_Subcoherent.lean` (hub-verified 2026-07-06): every repo `S07.Hypothesis` consumer takes
  an irreducible-only family, and the reducible-column coherence is consumed directly as
  `S07.IsCoherent`.  So this irreducible producer is the honest `S07.Hypothesis`-form content
  of (8.15.3); nonemptiness of `S` is not needed for the structure fields.
* **Type `P₁` regime**: the repo `typePA = (M')^#` equals Peterfalvi's `A(M)` only in the
  type-`P₁` regime (`M_σ = M'`; issue 9008) — which is also where the claim-1 producer
  `dadeSupportHypothesisData_typePA0_of_isTypeP1` supplies the input datum `d`.  The statements
  below don't take `IsTypeP1` (they are proofs about the repo's `typePA0` set, valid for any
  `TypePData`), but their reading as the book's (8.15.3) is faithful in the `P₁` regime; the
  type-`P₂` (type II) form is gated on the 9008 `typePA` re-scoping — see issue 1042 着手順 3.
* **Claim 2 of (8.15)** (the general Hypothesis (4.6) instance, `H = M_F` / `H = M_s`) is a
  separate TODO — issue 1042 着手順 2.
-/

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-! ### 8D: the (8.10) support containment `(M')^# ⊆ A₀(M)` inside `M` (p. 47) -/

section SupportContainment

variable {M : Subgroup G}

/-- **Peterfalvi (8.10) containment for the (8.15.3) instance: `(M')^# ⊆ A₀(M)` inside `M`.**

The repo's type-`P` support satisfies `A(M) = (M')^#` (`typePA_eq_sharpSubgroup_derivedInG`)
and `A₀(M) = A(M) ∪ V^M ⊇ A(M)`, so a nonidentity element of `M' = (derivedInG M).subgroupOf M`
lies in the Dade support.  §8-level form of `S12.Hypothesis.mderivSharp_subset_A0`
(`S13_SixTwoBridge.lean`), stated for a bare `TypePData` so the (8.15.3) producers below don't
need the §10 hypothesis bundle.  This is the `hKsupp` input of the
`S08.inducedKernelFamily_*_support` lemmas: member differences of the induced family vanish off
`(M')^#`, hence are `A₀`-supported. -/
theorem mderivSharp_subset_supportInSubgroup_typePA0 (data : TypePData M) :
    ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M data) M := by
  intro x hxK hx1
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  refine Set.mem_union_left _ ?_
  rw [typePA_eq_sharpSubgroup_derivedInG]
  refine ⟨Subgroup.mem_subgroupOf.mp hxK, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hcoe
  exact hx1 (by ext; exact hcoe)

end SupportContainment

/-! ### 8D: the (8.15) claim-3 subcoherence producers (pp. 47-48) -/

section SubcoherentTypeP

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {M : Subgroup G} [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)]
variable [Invertible (Nat.card ↥((derivedInG M).subgroupOf M) : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)] in
/-- **Members of the type-`P` induced family are supported in `M'`** (inside `M`, phrased over
the ambient set `↑(derivedInG M) ⊆ G` so the span-closure lemma
`S07.support_subset_of_mem_zSpan_of_supported` applies): `Ind_{M'}^M θ` vanishes off the normal
`M'` (`ClassFunction.induce_apply_eq_zero_of_not_mem_normal`).  This is the support half of the
(8.15.3) narrowing `Z[S, M^#] ⊆ CF(M, (M')^#)` behind the book-literal (5.2.b) isometry shape. -/
theorem inducedKernelFamily_member_support_subset_derivedInG
    {X : Subgroup ↥M} {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) X) :
    φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (derivedInG M : Set G) M := by
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  obtain ⟨θ, -, -, rfl⟩ := hφ
  intro x hx
  rw [ClassFunction.mem_support] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  by_contra hxK
  refine hx (ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ _ ?_)
  exact fun hmem => hxK (Subgroup.mem_subgroupOf.mp hmem)

/-- **Peterfalvi (8.15), claim 3 (type-`P₁` regime), consumer shape `A = A₀(M)`.**

For a conjugation-closed family `S` of irreducible members of the type-`P` induced family
`S(⊥) = {Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1}`, Hypothesis (5.2) — the ported `S07.Hypothesis` —
holds with `L = M`, over the honest Dade map `τ` of the (8.15) claim-1 datum
`d : DadeSupportHypothesisData M (A₀(M))` and the support parameter `A₀(M)` that the repo's
coherence consumers (`subset_subcoherent`, `coherent_subset_of_constant_degree`,
`sixTwoDecompositionData`) instantiate.

Coq: `FTtypeP_subcoherent` (`PFsection8.v:819`) via `prDade_subcoherent` (= (5.3.b),
`PFsection5.v:683`), restricted to the irreducible members (see the module docstring for the
reducible-column scope note).  The book proof's (1.5.e) inputs are the
`S08.inducedKernelFamily_*` family suite; the (5.3.b) content is the (5.3.a) assembler
`S07.irrSubcoherent` fed with the Dade `R`-data.  The oddness input is
`hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)` at a minimal-simple-odd call site. -/
noncomputable def inducedKernelFamily_subcoherent
    (hodd : Odd (Nat.card ↥M)) (data : TypePData M)
    (d : DadeSupportHypothesisData M (typePA0 M data))
    {S : Set (ClassFunction ↥M ℂ)}
    (hsub : S ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) ⊥)
    (hirr : ∀ χ ∈ S, IsIrreducibleCharacter χ)
    (hconjS : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥M) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M data) M) := by
  classical
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hKsupp := mderivSharp_subset_supportInSubgroup_typePA0 (M := M) data
  refine OddOrder.Peterfalvi.S07.irrSubcoherent
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap d.dade
      (d.dade.fullDadeIsometryData d.hconj))
    (OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M data) M)
    (fun χ hχ => ?_) hconjS ?_ ?_ ?_ ?_
  · -- `Rdatum`: the 2-element (5.2.d) datum from the Dade isometry, per irreducible member.
    exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff d.dade d.hconj
      ⟨χ, hirr χ hχ⟩
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hsub hχ))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp (hsub hχ))
  · -- `hreal`: no real members (odd order, (1.5.e)-side).
    exact fun χ hχ =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hsub hχ)
  · -- `hortho`: distinct members are orthogonal ((1.5.e)-side).
    exact fun χ ψ hχ hψ hne =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hsub hχ) (hsub hψ) hne
  · -- `hconjsupp`: `(χ − χ̄).support ⊆ A₀` — sign flip of `inducedKernelFamily_conjDiff_support`.
    intro χ hχ
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hKsupp (hsub hχ)
    intro x hx
    refine h ?_
    rw [ClassFunction.mem_support] at hx ⊢
    intro h0
    refine hx ?_
    rw [ClassFunction.sub_apply] at h0 ⊢
    rw [sub_eq_zero] at h0 ⊢
    exact h0.symm
  · -- `hiso`: the (5.2.b) lattice isometry, unconditional on the `A₀`-supported sublattice.
    exact fun φ ψ hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        d.dade d.hconj hφ.2 hψ.2

/-- **Peterfalvi (8.15), claim 3, book-literal shape `A = M^#`.**

The same subcoherence structure with the support parameter the book's (5.2.b) uses: `τ` is an
isometry on `Z[S, M^#]` (all of `M` minus the identity).  The extra content over
`inducedKernelFamily_subcoherent` is the narrowing `Z[S, M^#] ⊆ CF(M, (M')^#) ⊆ CF(M, A₀)`:
a `ℤ`-span member vanishes off the normal `M'`
(`inducedKernelFamily_member_support_subset_derivedInG` + span closure), and `M^#`-supportedness
kills the identity, so the Dade `A₀`-isometry brick still applies. -/
noncomputable def inducedKernelFamily_subcoherent_sharp
    (hodd : Odd (Nat.card ↥M)) (data : TypePData M)
    (d : DadeSupportHypothesisData M (typePA0 M data))
    {S : Set (ClassFunction ↥M ℂ)}
    (hsub : S ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) ⊥)
    (hirr : ∀ χ ∈ S, IsIrreducibleCharacter χ)
    (hconjS : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥M) (G := G) S ({(1 : ↥M)}ᶜ) := by
  classical
  haveI : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hKsupp := mderivSharp_subset_supportInSubgroup_typePA0 (M := M) data
  -- `Z[S, M^#] ⊆ CF(M, A₀)`: span members vanish off `M'`; `M^#`-support kills the identity.
  have hnarrow : ∀ ζ : ClassFunction ↥M ℂ,
      ζ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) S ({(1 : ↥M)}ᶜ) →
      ζ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M data) M := by
    intro ζ hζ
    have hK : ζ.support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (derivedInG M : Set G) M :=
      OddOrder.Peterfalvi.S07.support_subset_of_mem_zSpan_of_supported
        (fun s hs => inducedKernelFamily_member_support_subset_derivedInG (hsub hs)) hζ.1
    intro x hx
    have hxK : (x : G) ∈ derivedInG M :=
      (OddOrder.Peterfalvi.S04.mem_supportInSubgroup).mp (hK hx)
    have hx1 : x ≠ 1 := Set.mem_compl_singleton_iff.mp (hζ.2 hx)
    exact hKsupp x (Subgroup.mem_subgroupOf.mpr hxK) hx1
  refine OddOrder.Peterfalvi.S07.irrSubcoherent
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap d.dade
      (d.dade.fullDadeIsometryData d.hconj))
    ({(1 : ↥M)}ᶜ)
    (fun χ hχ => ?_) hconjS ?_ ?_ ?_ ?_
  · -- `Rdatum`: same Dade 2-element datum (its support input is `A₀`-side, independent of `A`).
    exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff d.dade d.hconj
      ⟨χ, hirr χ hχ⟩
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hsub hχ))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp (hsub hχ))
  · exact fun χ hχ =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hsub hχ)
  · exact fun χ ψ hχ hψ hne =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hsub hχ) (hsub hψ) hne
  · -- `hconjsupp` at `M^#`: the conjugate difference vanishes at `1` (equal degrees) — take the
    -- `K^#`-support lemma with target `{1}ᶜ` (its `hKsupp` is then trivial), and flip the sign.
    intro χ hχ
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      (A0 := ({(1 : ↥M)}ᶜ : Set ↥M))
      (fun x _ hx1 => Set.mem_compl_singleton_iff.mpr hx1) (hsub hχ)
    intro x hx
    refine h ?_
    rw [ClassFunction.mem_support] at hx ⊢
    intro h0
    refine hx ?_
    rw [ClassFunction.sub_apply] at h0 ⊢
    rw [sub_eq_zero] at h0 ⊢
    exact h0.symm
  · -- `hiso` on `Z[S, M^#]`: narrow to `A₀`-support, then the Dade brick.
    exact fun φ ψ hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        d.dade d.hconj (hnarrow φ hφ) (hnarrow ψ hψ)

end SubcoherentTypeP

end OddOrder.Peterfalvi.S10
