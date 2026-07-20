/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S10_MinimalSimpleBasic
import OddOrder.Peterfalvi.S07_Subcoherent
import OddOrder.Peterfalvi.S08_SixTwoGeneral
import OddOrder.Peterfalvi.S10_TypePSupportA0
import OddOrder.Peterfalvi.S10_Hypothesis46TypeP

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
* **Type `P₁` regime (§8D only)**: the repo `typePA = (M')^#` equals Peterfalvi's `A(M)` only in
  the type-`P₁` regime (`M_σ = M'`; issue 9008).  The §8D statements don't take `IsTypeP1` (they
  are proofs about the repo's `typePA0` set, valid for any `TypePData`), but their *reading* as
  the book's (8.15.3) is faithful only there — see §8E for why.
* **Claim 2 of (8.15)** (the general Hypothesis (4.6) instance, `H = M_F` / `H = M_s`) is
  `S10_Hypothesis46TypeP` (`typePACore_toHypothesis46_core` is the book's `H = M_s` choice).

## §8E/§8F: the type-uniform (8.15.3) (issue 1042)

§8D filters the induced family by `θ ≠ 1` and gets (5.2)'s support requirement from the crude
`(M')^# ⊆ A`.  The book instead filters by **`M_s ⊄ Ker θ`**, and (5.3.b)'s proof gets
`Z[𝒮, L^#] = Z[𝒮, A]` from **(4.7)**.  The distinction is invisible in the `P₁` regime — for
`θ ∈ Irr M'` the two filters agree exactly when `M_s = M'` — but decisive elsewhere, because
`(M')^# ⊆ A(M)` is **false** in types II/V, where `A(M) = ⋃_{x ∈ M_s^#} C_{M'}(x)^# ⊊ (M')^#`.

* **§8E** supplies the book's family `inducedNonKernelFamily`, its (4.7)-based support estimate
  `inducedNonKernelFamily_conjDiff_support`, and the `A`-general producer
  `inducedNonKernelFamily_subcoherent` (= (5.3.b) verbatim).  Non-reality and pairwise
  orthogonality are inherited from the coarser §8D family along
  `inducedNonKernelFamily_subset_inducedKernelFamily_bot`.
* **§8F** instantiates it at `A = A(M) = typePACore M`, `H = M_σ`
  (`typePACore_subcoherent`) — valid for **every** type `𝒫`.
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

/-! ### 8E: the book-literal (8.15.3) family `{Ind_K^L θ | θ ∈ Irr K, H ⊄ Ker θ}` (issue 1042)

The producers of §8D above filter the induced family by `θ ≠ 1` (`S08.inducedKernelFamily … ⊥`),
whereas the book's (8.15.3) filters by **`M_s ⊄ Ker θ`**.  For `θ ∈ Irr M'` the two agree exactly
when `M_s = M'` — the type-`P₁` regime, which is why §8D reads faithfully only there.

The book filters this way for a reason: Hypothesis (5.2) needs the member differences to be
`A`-supported, and (5.3.b)'s proof gets that from **(4.7)** — *"`Z[𝒮, L^#] = Z[𝒮, A]`"* — rather
than from the crude `(M')^# ⊆ A`, which is **false** once `A = A(M) = ⋃_{x ∈ M_s^#} C_{M'}(x)^#`
is strictly smaller than `(M')^#` (types II/V).  So the `H`-nontrivial filter is what makes the
support estimate type-uniform.  This section supplies that filter and its (4.7)-based support
lemma; the `A`-general subcoherence producer then takes them as inputs. -/

section CoreNontrivialFamily

variable {M : Subgroup G} [Fintype ↥M]
variable (K : Subgroup ↥M) [Invertible (Nat.card ↥K : ℂ)]

/-- **Peterfalvi (5.3.b)/(8.15.3)'s family** `{Ind_K^L θ | θ ∈ Irr K, H ⊄ Ker θ}`.

The `H`-nontrivial analogue of `S08.inducedKernelFamily` (which filters by `θ ≠ 1` together with a
*positive* kernel condition `X ⊆ Ker θ`).

At `H = K` the two filters coincide — for irreducible `θ ∈ Irr K`, `K ⊆ Ker θ` iff `θ = 1` — which
is exactly the type-`P₁` coincidence `M_s = M'`.  ⚠ Only the direction used downstream is
formalized: `inducedNonKernelFamily_subset_inducedKernelFamily_bot` proves `H ⊄ Ker θ ⟹ θ ≠ 1`
(hence `⊆`).  The converse `θ ≠ 1 ⟹ K ⊄ Ker θ` — an irreducible character with full kernel is
trivial, via `IsIrreducibleCharacter.inner_self_eq_one` forcing degree 1 — is standard, and is
stated here as motivation, **not** as a formalized lemma. -/
def inducedNonKernelFamily (H : Subgroup ↥M) : Set (ClassFunction ↥M ℂ) :=
  {φ | ∃ θ : IrreducibleCharacter ↥K,
    ¬ ((H.subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) ∧
    φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ)}

variable {K}

theorem mem_inducedNonKernelFamily {H : Subgroup ↥M} {φ : ClassFunction ↥M ℂ} :
    φ ∈ inducedNonKernelFamily K H ↔ ∃ θ : IrreducibleCharacter ↥K,
      ¬ ((H.subgroupOf K : Set ↥K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) ∧
      φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) := Iff.rfl

/-- **The book's filter is finer than the repo's**: `{θ | H ⊄ Ker θ} ⊆ {θ | θ ≠ 1}`, so the
(8.15.3) family sits inside `S08.inducedKernelFamily K ⊥`.

The trivial character has every element in its kernel, so `H ⊄ Ker θ` forces `θ ≠ 1`; and the
`⊥`-kernel condition of `inducedKernelFamily` is vacuous.  This inclusion is what lets the whole
`S08.inducedKernelFamily_*` suite (non-reality, pairwise orthogonality, finiteness, conjugation
closure) apply verbatim to the finer family — only the *support* estimate has to be redone, and
that is `inducedNonKernelFamily_conjDiff_support`. -/
theorem inducedNonKernelFamily_subset_inducedKernelFamily_bot {H : Subgroup ↥M} :
    inducedNonKernelFamily K H ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily K ⊥ := by
  rintro φ ⟨θ, hker, rfl⟩
  refine ⟨θ, ?_, ?_, rfl⟩
  · rintro rfl
    exact hker fun x _ => by
      simp [IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  · intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx
    rw [show x = 1 from Subtype.ext hx]
    rfl

/-- **Member degrees of the (8.15.3) family are natural numbers** (hence real): `φ(1) = |L:K|·θ(1)`
with `θ(1)` a positive natural.  This is what kills the `{1}` left over by (4.7) when passing from
`Supp φ ⊆ A ∪ {1}` to `Supp (φ − φ̄) ⊆ A`. -/
theorem inducedNonKernelFamily_apply_one_eq_natCast {H : Subgroup ↥M}
    {φ : ClassFunction ↥M ℂ} (hφ : φ ∈ inducedNonKernelFamily K H) :
    ∃ n : ℕ, φ 1 = (n : ℂ) := by
  obtain ⟨θ, -, rfl⟩ := hφ
  obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  exact ⟨K.index * d, by rw [ClassFunction.induce_apply_one, hd]; push_cast; ring⟩

end CoreNontrivialFamily

section CoreNontrivialSupport

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {M : Subgroup G} [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)]

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)] in
/-- **Peterfalvi (4.7) on the (8.15.3) family**: every member vanishes outside `A ∪ {1}`.

Direct application of `S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel`,
whose ambient set `A` is already a parameter — so it applies verbatim at `A = typePACore M`
(the book-literal `A(M)`), not only at the `P₁`-regime `typePA M`. -/
theorem inducedNonKernelFamily_apply_eq_zero {A : Set G}
    (h : OddOrder.Peterfalvi.S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h.K : ℂ)]
    {φ : ClassFunction ↥M ℂ} (hφ : φ ∈ inducedNonKernelFamily h.K h.subH)
    {z : ↥M} (hz : (z : G) ∉ A ∪ ({1} : Set G)) :
    φ z = 0 := by
  obtain ⟨θ, hker, rfl⟩ := hφ
  exact OddOrder.Peterfalvi.S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel
    h θ hker hz

/-- **The `hconjsupp` input of (5.2) for the (8.15.3) family**: `Supp (φ − φ̄) ⊆ A`.

This is the type-uniform replacement for `S08.inducedKernelFamily_conjDiff_support`, which needs
`(M')^# ⊆ A` and therefore only reads correctly in the `P₁` regime.  Here (4.7) gives
`Supp φ ⊆ A ∪ {1}` outright, and the identity is removed by the degree being a natural number
(`φ(1) = φ̄(1)`), so no containment `(M')^# ⊆ A` is required. -/
theorem inducedNonKernelFamily_conjDiff_support {A : Set G}
    (h : OddOrder.Peterfalvi.S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h.K : ℂ)]
    {φ : ClassFunction ↥M ℂ} (hφ : φ ∈ inducedNonKernelFamily h.K h.subH) :
    ((φ - φ.conj : ClassFunction ↥M ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A M := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  by_contra hzA
  refine hz ?_
  rcases eq_or_ne ((z : G)) 1 with hz1 | hz1
  · -- at the identity the two degrees agree (both the same natural number)
    have hzone : z = 1 := Subtype.ext hz1
    obtain ⟨n, hn⟩ := inducedNonKernelFamily_apply_one_eq_natCast (K := h.K) (H := h.subH) hφ
    rw [ClassFunction.sub_apply, hzone, ClassFunction.conj_apply, hn, star_natCast, sub_self]
  · -- off `A ∪ {1}` the member itself vanishes, hence so does its conjugate
    have hmem : (z : G) ∉ A ∪ ({1} : Set G) := by
      rw [Set.mem_union, Set.mem_singleton_iff, not_or]
      exact ⟨hzA, hz1⟩
    have h0 : φ z = 0 := inducedNonKernelFamily_apply_eq_zero h hφ hmem
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_self]

/-- **Peterfalvi (8.15), claim 3 — type-uniform**, on the book's own family
`𝒮 ⊆ {Ind_K^L θ | θ ∈ Irr K, H ⊄ Ker θ}` and an arbitrary ambient Dade support `A`.

This is (5.3.b) verbatim: assume Hypothesis (4.6) (here its Dade-free core `h46` together with the
`A`-Dade datum `d`), (5.2.a) (`hconjS`), and that `𝒮` sits inside the `H`-nontrivial induced
family; then Hypothesis (5.2) holds for `L = M`.

Unlike `inducedKernelFamily_subcoherent` (§8D) this needs **no containment `(M')^# ⊆ A`**, so it is
not confined to the type-`P₁` regime: the book's `H ⊄ Ker θ` filter buys the support estimate
through (4.7) instead (`inducedNonKernelFamily_conjDiff_support`).  Instantiating
`A = typePACore M` with `H = M_s = M_σ` (`typePACore_toHypothesis46_core`) gives the book-literal
(8.15.3) for **every** type `𝒫`, types II and V included.

Everything except the support estimate is inherited from the coarser `S08` family along
`inducedNonKernelFamily_subset_inducedKernelFamily_bot`. -/
noncomputable def inducedNonKernelFamily_subcoherent {A : Set G}
    (hodd : Odd (Nat.card ↥M))
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h46.K : ℂ)]
    (d : DadeSupportHypothesisData M A)
    {S : Set (ClassFunction ↥M ℂ)}
    (hsub : S ⊆ inducedNonKernelFamily h46.K h46.subH)
    (hirr : ∀ χ ∈ S, IsIrreducibleCharacter χ)
    (hconjS : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥M) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup A M) := by
  classical
  -- the coarser `S08` family, for the non-support inputs
  have hbot : ∀ ⦃χ : ClassFunction ↥M ℂ⦄, χ ∈ S →
      χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily h46.K ⊥ := fun _ hχ =>
    inducedNonKernelFamily_subset_inducedKernelFamily_bot (hsub hχ)
  refine OddOrder.Peterfalvi.S07.irrSubcoherent
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap d.dade
      (d.dade.fullDadeIsometryData d.hconj))
    (OddOrder.Peterfalvi.S04.supportInSubgroup A M)
    (fun χ hχ => ?_) hconjS ?_ ?_ ?_ ?_
  · -- `Rdatum`: the (5.2.d) datum, with the **(4.7)** support estimate in place of `(M')^# ⊆ A`
    exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff d.dade d.hconj
      ⟨χ, hirr χ hχ⟩
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hbot hχ))
      (by
        have h := inducedNonKernelFamily_conjDiff_support h46 (hsub hχ)
        intro x hx
        refine h ?_
        rw [ClassFunction.mem_support] at hx ⊢
        intro h0
        refine hx ?_
        rw [ClassFunction.sub_apply] at h0 ⊢
        rw [sub_eq_zero] at h0 ⊢
        exact h0.symm)
  · exact fun χ hχ =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hbot hχ)
  · exact fun χ ψ hχ hψ hne =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal (hbot hχ) (hbot hψ) hne
  · exact fun χ hχ => inducedNonKernelFamily_conjDiff_support h46 (hsub hχ)
  · exact fun φ ψ hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        d.dade d.hconj hφ.2 hψ.2

end CoreNontrivialSupport

/-! ### 8F: (8.15.3) at the book-literal support `A(M)`, for every type `𝒫` (issue 1042)

⚠ **Instance discipline**: this section takes `[Finite G]` only and works under
`open scoped S12.FiniteInduce`, which derives `Fintype G`, `Fintype ↥H`,
`Invertible (Nat.card G : ℂ)` and `Invertible (Nat.card ↥H : ℂ)` uniformly from `Finite G`.
Mixing those with explicit `[Fintype G]` / `[Invertible …]` binders (as §8D/§8E do) makes the
`S04.Hypothesis` arguments fail to be definitionally equal — `S12.FiniteInduce.finiteGFintype`
versus the binder — which is why the instantiation lives in its own section rather than inside
`CoreNontrivialSupport`. -/

section TypePACoreSubcoherent

variable {M : Subgroup G}

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.15), claim 3 at the book-literal support `A(M)` — for every type `𝒫`.**

The instantiation the book actually states: `L = M`, `K = M'`, `H = M_s = M_σ`,
`A = A(M) = typePACore M`, with the family literally
`{Ind_{M'}^M θ | θ ∈ Irr M', M_σ ⊄ Ker θ}`.

Both Dade inputs are Peterfalvi (8.15) claim 1 and carry **no type hypothesis beyond `IsTypeP`**:
`dadeSupportHypothesisData_typePACore0` supplies the `A₀(M)`-datum that Hypothesis (4.6) needs
(through `typePACore_toHypothesis46_core`, the book's `H = M_s` choice), and
`dadeSupportHypothesisData_typePACore` supplies the `A(M)`-datum carrying the Dade isometry `τ`.

So the conclusion holds for types I–V alike — in particular for types II and V, where the
`P₁`-regime producers of §8D (`inducedKernelFamily_subcoherent`) do *not* read as the book's
statement, because there `A(M) ⊊ (M')^#` and the support estimate `(M')^# ⊆ A` they rely on
is false. -/
noncomputable def typePACore_subcoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hodd : Odd (Nat.card ↥M)) (data : TypePData M)
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1))
    (hW2σ : data.W2 ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hσK : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M)
    {S : Set (ClassFunction ↥M ℂ)}
    (hsub : S ⊆ inducedNonKernelFamily ((derivedInG M).subgroupOf M)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M))
    (hirr : ∀ χ ∈ S, IsIrreducibleCharacter χ)
    (hconjS : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥M) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (typePACore M) M) :=
  inducedNonKernelFamily_subcoherent hodd
    (typePACore_toHypothesis46_core data hG.odd hHall
      (dadeSupportHypothesisData_typePACore0 hG hM hTP data).some.dade
      (dadeSupportHypothesisData_typePACore0 hG hM hTP data).some.hconj hW2σ hσK).toCore
    (dadeSupportHypothesisData_typePACore hG hM hTP).some
    hsub hirr hconjS

end TypePACoreSubcoherent

end OddOrder.Peterfalvi.S10
