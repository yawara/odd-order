/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart1
import OddOrder.Peterfalvi.S08_RetargetReducible
import OddOrder.Peterfalvi.S08_GeneralAdjoinWeighted

/-!
# Peterfalvi §5/§8: the norm-weighted (5.6) coherence-break engine

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§5 (Theorem 5.6, under the abstract Hypothesis 5.2), in the **norm-weighted** form needed for the
certain-type case (B) of (6.8.3).

The existing X-chain machinery (`XAdjoinStepInput` / `xAdjoinStep` / `crux1_of_memberFamily` in
`S08_CoherenceCorePart1`) bakes in *orthonormality* of the member family
(`hmemortho i j = if i = j then 1 else 0`) and the unweighted degree bound `2a < ∑ deg²`.  That is
the special case `‖χᵢ‖² = 1` of Theorem (5.6); it suffices for case (A) (Frobenius), where every
member of the coherent set `S₁` is irreducible.

In case (B) the coherent set `S₁` contains **reducible** certain-type columns `μⱼ` (each with
`‖μⱼ‖² > 1`), so the genuine Peterfalvi (5.6) — with the `‖χᵢ‖²`-weighted projection coefficients
`1/‖χᵢ‖²` and the weighted bound `2a < ∑ deg²/‖χᵢ‖²` — is required (ChatGPT/Pro-verified that there
is *no* sidestep; see `notes/peterfalvi/s08_6_8_3_reducibleS_chatgpt_answer.md` Q1–Q4).  The
weighting is localized to the **member family** `χmem`; the break pair `χ, χ̄` and the anchor
`χmem i₁`
remain irreducible (norm one) in the (6.8.3) application, so their fields are unchanged.

This file develops that weighted engine additively (the unweighted version is preserved for case A):

* `XAdjoinStepInputW` — the bundled input with `χmem : ι → ClassFunction ↥L ℂ` general, the
  orthogonality `⟨χmem i, χmem j⟩ = if i = j then ⟨χmem i, χmem i⟩ else 0`, and the weighted degree
  bound `2a < ∑ deg² / ‖χmem i‖²`.
* (to come) `crux1_of_memberFamilyW`, `xAdjoinStepW`, `coherentDegreeSqNormBound_of_not_coherentW`.

Plan of record: `notes/peterfalvi/s56_reweighting_plan.md`.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

open scoped Classical in
/-- **Norm-weighted (5.6) X-adjoin input.**  The weighted analogue of `XAdjoinStepInput`: the member
family `χmem : ι → ClassFunction ↥L ℂ` is a family of (possibly reducible) characters of `S₁`, with

* orthogonality `⟨χmem i, χmem j⟩ = if i = j then ⟨χmem i, χmem i⟩ else 0` (the diagonal is the
  squared norm `‖χmem i‖²`, not forced to `1`);
* anchor `χmem i₁` of degree-ratio `1` (`ha1 : deg i₁ = 1`)
  — its **norm is unconstrained**, matching
  Peterfalvi (5.6), whose only anchor hypothesis is `χ₁(1) ∣ χ(1)` (see `crux1_of_memberFamilyW`);
* the **weighted** degree bound `2a < ∑_{i∈s} deg(i)² / ‖χmem i‖²`.

The break member `χ` is irreducible (norm one) as in the unweighted version.  Compare
`XAdjoinStepInput` (the `‖χmem i‖² = 1` special case used in case (A)). -/
structure XAdjoinStepInputW {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) where
  hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ)
  hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1
  hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ).conj = 1
  hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0
  hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0
  hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0
  hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0
  ι : Type
  s : Finset ι
  /-- The member family — **general** (possibly reducible) characters of `S₁`. -/
  χmem : ι → ClassFunction ↥L ℂ
  deg : ι → ℕ
  i₁ : ι
  hi₁ : i₁ ∈ s
  hmemdegdiffsupp : ∀ i ∈ s, (χmem i - deg i • χmem i₁).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemS1 : ∀ i ∈ s, χmem i ∈ S₁
  /-- The member squared norms `mc i = ‖χmem i‖²` (explicit, as in `xAdjoinStepW`). -/
  mc : ι → ℝ
  hmempos : ∀ i ∈ s, 0 < mc i
  /-- Orthogonality with the **squared-norm diagonal** `mc i = ‖χmem i‖²` (not forced to `1`). -/
  hmemortho : ∀ i ∈ s, ∀ j ∈ s,
    ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0
  /-- Per-member ν-aux decomposition `Dmem i : CharacterPsiDecomposition τ (χmem i) 0` — for case
  (B)
  built from `certainTypeR`/`certainTypeDecompositionDa` (reducible columns) or
  `memberExtensionDecomposition` (irreducibles). -/
  Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    (χmem i) 0
  /-- The (5.2.e) cross-family orthogonality `R(χmem i) ⊥ R(χ)`. -/
  hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hrealχ
        hdiffsuppχ)
  /-- The running-extension agreement `(Dmem i).tau1 = ν`. -/
  htau1Dmem : ∀ i (hi : i ∈ s), (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i)
  a : ℕ
  hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • χmem i₁).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
    (hyp.fullDadeIsometryData) ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G
  ha1 : deg i₁ = 1
  /-- The **norm-weighted** degree bound `2a < ∑ deg(i)² / mc i`. -/
  hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i
  hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
    (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {χmem i₁})
  hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
    Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
      {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
       (χ : ClassFunction ↥L ℂ) - a • χmem i₁})

/-- **The Dade map is an isometry on every supported sublattice** — the `hisom` input of the
general (5.6) engines (`S07.xAdjoinStepW_k_general`, `S07.adjoinPairCoherent_general`), for an
arbitrary ambient family `Samb`.  Pure repackaging of
`dadeIntegralCharacterMap_inner_eq_on_supported_span`: membership in `zSupportedSpan Samb A₀` gives
the `A₀`-support of every generator, which is all that lemma needs (it never looks at `Samb`), so
the Feit–Thompson instantiations may take `Samb = univ`. -/
theorem dade_hisom_of_zSupportedSpan {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (Samb : Set (ClassFunction ↥L ℂ)) :
    ∀ (T : Set (ClassFunction ↥L ℂ)),
      (∀ s ∈ T, s ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) Samb
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) →
      ∀ φ ζ : ClassFunction ↥L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
              (hyp.fullDadeIsometryData) φ)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
              (hyp.fullDadeIsometryData) ζ)
          = ClassFunction.inner φ ζ :=
  fun _T hT _φ _ζ hφ hζ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
      (fun s hs => (hT s hs).2) hφ hζ

open scoped Classical in
/-- **Norm-weighted crux1** (Peterfalvi (5.6.1)/(5.6.2) for a reducible member family).  The
weighted analogue of `crux1_of_memberFamily`: the member family `χmem` is orthogonal with real
squared norms `mc i` (`hmemortho i j = if i=j then mc i else 0`) and the degree bound is the
**weighted** `2a < ∑ deg(i)²/mc i`.  Then the crux inner product `⟨τ(χ−a·χ₁), ν χ₁⟩ = −a·‖χ₁‖²`.

**The anchor norm is arbitrary** — no `mc i₁ = 1` (equivalently, no anchor irreducibility).  This
tracks Peterfalvi (5.6) exactly: its hypotheses are only that `S₁` is coherent, `χ₁(1) ∣ χ(1)`, and
`2χ(1)χ₁(1) < ∑ χᵢ(1)²/‖χᵢ‖²`; the proof carries `‖χ₁‖²` symbolically throughout, e.g. (5.6.1)'s
`(Y, χ₁^τ₁) = (a − λ/‖χ₁‖²)‖χ₁‖² = a‖χ₁‖² − λ`.  Requiring `‖χ₁‖² = 1` would be a genuine
specialization: the (6.2) anchor is `Ind_K^L θ` for a linear `θ ∈ Irr(K/A)`, which is reducible
unless `θ` has inertia group `K`.

The proof is the orthonormal `crux1` with `1 ↦ mc i`: the orthogonal projection
(`exists_indexed_projection_of_orthogonal_ZIrr`) gives integer `cZ i = ⟨Da.Y, ν χᵢ⟩` and the
*rational* expansion `Da.Y = ∑ (cZ i/mc i)·ν χᵢ + Z`; with `cZ i = a·mc i₁·[i=i₁] − λ·deg i` this is
the `λ`-form `∑ (a·[i=i₁] − λ·rc i)·ν χᵢ` with `λ = a·mc i₁ + μ`, `rc i = deg i/mc i` (the anchor
coefficient `cZ i₁/mc i₁ = a − λ/mc i₁` is where the norm must be divided back out).  `λ` is an
*integer* because `mc i₁ = ⟨ν χ₁, ν χ₁⟩` is one
— `ν χ₁ ∈ ℤ[Irr G]` and `ν` is an isometry — which is
the norm-general replacement for `mc i₁ = 1`.  The (5.6.2) engine `lambda_eq_zero_and_Z_eq_zero` is
already norm-general
(`hψ : ‖ψ‖² = a²·mc i₁`, `hr₁ : rc i₁ · mc i₁ = 1` from `deg i₁ = 1`); it forces
`λ = 0`, i.e. `μ = −a·mc i₁`.  Here `∑ rc² · mc = ∑ deg²/mc` is the weighted bound. -/
theorem crux1_of_memberFamilyW {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (_hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      hyp.fullDadeIsometryData)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ) {a : ℕ}
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ
      (χ : ClassFunction ↥L ℂ) (a • χmem i₁))
    (hDaY_ZIrr : Da.Y ∈ ZIrr G)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0)
    (hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (mc i₁ : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) * (mc i₁ : ℂ) + ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ))
    (hμZ : τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i) :
    ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
      (hS₁.extension (χmem i₁)) = -((a : ℂ) * (mc i₁ : ℂ)) :=
  OddOrder.Peterfalvi.S07.crux1_of_memberFamilyW_general hS₁ χ s χmem deg i₁ hi₁ Da hDaY_ZIrr
    hmemS1 mc hmempos hmemortho hcoeffval hμZ ha1 hDeg

open scoped Classical in
/-- **Norm-weighted (5.6) forward adjoin engine (general members).**

The weighted analogue of `xAdjoinStep` (case A), generalized so the member family `χmem` may
contain **reducible** characters: the per-member ν-aux decompositions `Dmem i` and the family
orthogonalities `hortho_mem`/`htau1Dmem` are taken as **parameters** rather than constructed from
`memberExtensionDecomposition` (which is irreducible-only, requiring `χmem i : IrreducibleCharacter`
via the Dade family `dadeOrthonormalCharacterImageFamilyOfDiff`).

This is exactly the split Peterfalvi (5.6) needs for case (B) of (6.8.3): the break pair `χ, χ̄` and
the anchor `χmem i₁` stay irreducible (norm one), while a non-anchor member may be a reducible
certain-type column `μⱼ` whose orthonormal image family `R(μⱼ)` is supplied by the §6 σ-isometry
(Peterfalvi (5.3.b)).  Each `Dmem i : CharacterPsiDecomposition τ (χmem i) 0` carries that family in
`(Dmem i).imageFamily`, the running extension as `(Dmem i).tau1 = ν` (`htau1Dmem`), and the (5.2.e)
cross-family orthogonality `R(χmem i) ⊥ R(χ)` (`hortho_mem`).

* For an irreducible member, `Dmem i = memberExtensionDecomposition …`, `hortho_mem i =
  dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal …`, `htau1Dmem i = rfl` — recovering the
  case-A instantiation.
* For a reducible certain-type column, `Dmem i` is built via `ofProjection` from the σ-image family
  `R(μⱼ)` ((5.3.b)); this is the remaining §5↔§6 bridge.

The weighting enters only through `mc` (the member norms `‖χmem i‖²`), the weighted orthogonality
`hmemortho`, and the weighted degree bound `hDeg : 2a < ∑ deg² / mc`, all threaded into
`crux1_of_memberFamilyW`. -/
noncomputable def xAdjoinStepW
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i) 0)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hrealχ
        hdiffsuppχ))
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- The trivially-derived orthogonalities `χ, χ̄ ⊥ a·χ₁` for the χ-decomposition `Da`.
  have hχaχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ)
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχ_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  have hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχbar_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  -- The χ-decomposition for the degree-matched difference `χ − a·χ₁`.
  -- (`let`, not `have`/`set`, so `Da.tau1 = τ` / `Da.imageFamily = R(χ)` reduce definitionally.)
  let Da := OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp χ hrealχ hdiffsuppχ
    hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar
  -- `Da.X ∈ ZIrr` (integer combination of the orthonormal `R(χ)` family) ⟹ `Da.Y ∈ ZIrr`.
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  have hYeq : Da.Y = Da.X - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) := by
    have h : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) = Da.X - Da.Y :=
      Da.tau1_image
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁ : ClassFunction ↥L ℂ)
      (χmem i₁ : ClassFunction ↥L ℂ) = ((mc i₁ : ℝ) : ℂ) := by
    rw [hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl]
  -- (5.2.e) `⟨Da.X, ν χᵢ⟩ = 0` per member.
  have hXortho : ∀ i ∈ s, ClassFunction.inner Da.X (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      0 :=
    fun i hi =>
      inner_decomposition_X_extension_member_eq_zero hS₁ Da (Dmem i hi) (hortho_mem i hi)
        (htau1Dmem i hi)
  -- (5.6.1) cross-term `hfound` per member (`inner_dade_extension_of_supported`).
  have hfound : ∀ i ∈ s, ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ))) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ))
        ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)) := fun i hi => by
    refine inner_dade_extension_of_supported hyp hS₁ hdiffasuppχ ?_
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- The (5.6.1) member coefficient `⟨Da.Y, ν χᵢ⟩` in the `lambda_eq_zero_and_Z_eq_zero` form.
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y
      (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      (a : ℂ) * ((mc i₁ : ℝ) : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) * ((mc i₁ : ℝ) : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
            ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
          (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq hyp hS₁ χ hYeq (hXortho i hi) (hfound i hi)
      (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]; ring
  -- crux1 via the λ-form collapse.
  have hcrux1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = -((a : ℂ) * ((mc i₁ : ℝ) : ℂ)) :=
    crux1_of_memberFamilyW hyp
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) rfl
      hS₁ (χ : ClassFunction ↥L ℂ) s (fun i => (χmem i : ClassFunction ↥L ℂ)) deg i₁ hi₁ Da
      hDaY_ZIrr hmemS1
      mc hmempos hmemortho hcoeffval htau1_memaχ ha1 hDeg
  -- crux2 clean: `⟨τ(χ − χ̄), ν χ₁⟩ = 0` from `R(χ) ⊥ R(χ₁)`.
  have hcrux2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily
          (Dmem i₁ hi₁) (hortho_mem i₁ hi₁) (htau1Dmem i₁ hi₁) hα), star_zero]
  -- `(χ − χ̄)^τ ∈ ZIrr` from the `R(χ)` family (`image_eq`); `(χ − a·χ₁)^τ ∈ ZIrr` is
  -- `htau1_memaχ`.
  have hτdiffZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  -- Adjoin via the (T8.11 option A) bridge.
  exact retarget_isCoherent_of_extensionImage hyp
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) rfl
    hS₁ χ hdiffsuppχ hdiffasuppχ hχχ hχbarχbar hχχbar hχbarχ hchi1chi1 hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ hcrux1 hcrux2 hSgen hgen

open scoped Classical in
/-- **Norm-weighted (5.6) forward adjoin engine, reducible BREAK (`‖χ‖² ≠ 1`).**

The `‖χ‖² ≠ 1` analogue of `xAdjoinStepW`: the **break** pair `{χ, χ̄}` may itself be a
reducible certain-type column (`‖χ‖² = w₁ > 1`), not just the non-anchor members.  The break
decomposition `Da : CharacterPsiDecomposition τ χ (a·χ₁)` is therefore taken as a **parameter**
(constructed by `certainTypeDecompositionDa` from the (5.3.b) σ-image family `R(μ_j)`), rather than
built internally by `decompositionDaFromDadeOfDiff` (irreducible-only, via the conjugate-pair Dade
family `dadeOrthonormalCharacterImageFamilyOfDiff`).  The break image family `R(χ) = Da.imageFamily`
then feeds the (5.2.e) cross-family orthogonality `hortho_mem` and the crux-2 vanishing.

The only extra hypothesis over `xAdjoinStepW` is `hDatau1 : Da.tau1 = τ` (the break
decomposition's auxiliary isometry is the Dade base map itself — holds by `rfl` for
`certainTypeDecompositionDa`), used to read the (5.4) image equation `τ(χ − a·χ₁) = Da.X − Da.Y`
(`hYeq`) off `Da.tau1_image`.  The norm-1 hypotheses `hχχ`/`hχbarχbar` of `xAdjoinStepW` become the
non-vanishing `hχχne`/`hχbarχbarne`, and the bridge is the reducible
`retarget_isCoherent_of_extensionImage_k`. -/
noncomputable def xAdjoinStepW_k
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ)
    (hdiffsuppχ : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner χ.conj χ.conj ≠ 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i) 0)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      χ (a • χmem i₁))
    (hDatau1 : Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData))
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily)
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffasuppχ : (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {χ - χ.conj, χ - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- The Dade map is an isometry on **every** supported set, so the ambient family of the general
  -- engine is `Samb = univ` and `hisom` is `dade_hisom_of_zSupportedSpan` there.
  refine OddOrder.Peterfalvi.S07.xAdjoinStepW_k_general (Samb := Set.univ) hS₁ (Set.subset_univ _)
    (dade_hisom_of_zSupportedSpan hyp Set.univ) χ hχχne hχbarχbarne hχχbar hχbarχ hχ_S1 hχbar_S1
    s χmem deg i₁ hi₁ ?_ hmemS1 mc hmempos hmemortho Dmem Da hDatau1 hortho_mem htau1Dmem
    ?_ ?_ htau1_memaχ ha1 hDeg hSgen hgen
  -- the scaled member differences lie in the `A₀`-supported part of `ℤ[S₁]`
  · intro i hi
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- `χ − χ̄` and `χ − a·χ₁` are `A₀`-supported (`Samb = univ` makes the span clause vacuous)
  · refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_univ_iff.mpr ?_
    rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]
    exact hdiffsuppχ
  · exact OddOrder.Peterfalvi.S07.mem_zSupportedSpan_univ_iff.mpr hdiffasuppχ

/-- **The per-step weighted X-adjoin** (bundled form).  A `XAdjoinStepInputW` yields the coherence
of
`S₁ ∪ {χ, χ̄}` — the weighted analogue of `XAdjoinStepInput.adjoin`, for the (weighted) X-chain fold
`coherentOfPairChainCover`.  Pure pass-through to `xAdjoinStepW`. -/
noncomputable def XAdjoinStepInputW.adjoin
    {A : Set G}
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    {S₁ : Set (ClassFunction ↥L ℂ)}
    {hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L)}
    {χ : IrreducibleCharacter ↥L} (inp : XAdjoinStepInputW hyp hS₁ χ) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
  xAdjoinStepW hyp hS₁ χ inp.hrealχ inp.hdiffsuppχ inp.hχχ inp.hχbarχbar inp.hχχbar
    inp.hχbarχ inp.hχ_S1 inp.hχbar_S1 inp.s inp.χmem inp.deg inp.i₁ inp.hi₁
    inp.hmemdegdiffsupp inp.hmemS1 inp.mc inp.hmempos inp.hmemortho
    inp.Dmem inp.hortho_mem inp.htau1Dmem inp.hdiffasuppχ inp.htau1_memaχ inp.ha1 inp.hDeg
    inp.hSgen inp.hgen

open scoped Classical in
/-- **Norm-weighted (5.6) degree-square bound (contrapositive of `xAdjoinStepW`).**

The norm-weighted Peterfalvi (5.6) inequality: if `S₁` is coherent but `S₁ ∪ {χ, χ̄}` is **not**,
then
the weighted degree-square sum is bounded by twice the degree ratio,
`∑_{i∈s} deg(i)² / ‖χmem i‖² ≤ 2a`.  This is the reducible-member generalization of
`coherentDegreeSumBound_of_not_coherent` (the case-A `‖χmem i‖² = 1` specialization, with conclusion
`∑ deg² ≤ 2a`).

Pure contrapositive of the forward engine `xAdjoinStepW`: were the bound to fail
(`2a < ∑ deg²/mc`), `xAdjoinStepW` would produce coherence of `S₁ ∪ {χ, χ̄}`, contradicting `hnc`.
All the per-member decomposition data (`Dmem`/`hortho_mem`/`htau1Dmem`) is threaded through
unchanged — for case (B) it is supplied per member from `certainTypeDecompositionDa`/`certainTypeR`
(reducible certain-type columns) and `memberExtensionDecomposition` (irreducible members). -/
theorem coherentDegreeSqNormBound_of_not_coherentW
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i) 0)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hrealχ
        hdiffsuppχ))
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStepW hyp hS₁ χ hrealχ hdiffsuppχ hχχ hχbarχbar hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemdegdiffsupp hmemS1 mc hmempos hmemortho
    Dmem hortho_mem htau1Dmem hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

open scoped Classical in
/-- **Norm-weighted (5.6) degree-square bound, reducible BREAK (contrapositive of
`xAdjoinStepW_k`).**

The `‖χ‖² ≠ 1` analogue of `coherentDegreeSqNormBound_of_not_coherentW`: if `S₁` is coherent but
`S₁ ∪ {χ, χ̄}` is **not** — for a possibly **reducible** break `χ` whose decomposition `Da` is
supplied as a parameter — then the weighted degree-square sum is bounded,
`∑ deg(i)²/‖χmem i‖² ≤ 2a`.
Pure contrapositive of the reducible-break forward engine `xAdjoinStepW_k`. -/
theorem coherentDegreeSqNormBound_of_not_coherentW_k
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ)
    (hdiffsuppχ : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner χ.conj χ.conj ≠ 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i) 0)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      χ (a • χmem i₁))
    (hDatau1 : Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData))
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily)
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffasuppχ : (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {χ - χ.conj, χ - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStepW_k hyp hS₁ χ hdiffsuppχ hχχne hχbarχbarne hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemdegdiffsupp hmemS1 mc hmempos hmemortho
    Dmem Da hDatau1 hortho_mem htau1Dmem hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

/-- **(T-A2, norm-weighted) The X-family coherence chain fold.**

The weighted analogue of `xChainCoherent`: folds the per-step weighted adjoin `xAdjoinStepW` (via
`XAdjoinStepInputW.adjoin`) over a degree-monotone conjugate-pair cover of `X`, from a coherent base
`S₀` — for case (B), the reducible certain-type column set `certainTypeSet`, coherent via
`certainTypeSet_isCoherent_tau_canonical`.  Each step adjoins the irreducible pair `(χs i, χ̄s i)`
to
the accumulator `pairUnion S₀ pair i` through the bundled weighted input `hstep i`, whose member
family ranges over the **(possibly reducible)** accumulator members — exactly the case-(B) X-chain
the unweighted `xChainCoherent` cannot express (its `XAdjoinStepInput` bakes in member
orthonormality
`‖χmem i‖² = 1`, which fails on the reducible columns).

The construction of `hstep` (the per-step `XAdjoinStepInputW`) from the certain-type column data —
`certainTypeMemberDecomposition` for the reducible-column members,
`certainTypeR_imageSet_orthogonal_
dadeOfDiff` for their cross-family orthogonality, `memberExtensionDecomposition` for the
already-adjoined irreducibles — is the remaining per-step obligation; this fold packages it into the
full `X`-coherence `cX`. -/
noncomputable def xChainCoherentW
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {X S₀ : Set (ClassFunction ↥L ℂ)}
    (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
    (χs : ℕ → IrreducibleCharacter ↥L)
    (hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ))
    (hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj)
    (hS₀ : S₀ ⊆ X)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ X)
    (hcover : ∀ χ ∈ X, χ ∈ S₀ ∨ ∃ j, j < N ∧ χ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
    (h0 : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₀ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hstep : ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) S₀ pair i)
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L)),
      XAdjoinStepInputW hyp hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      X (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
  OddOrder.Peterfalvi.S07.coherentOfPairChainCover pair N hS₀ hpairs hcover h0
    (fun i hi hcoh => by
      rw [OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair (hpair0 i hi) (hpair1 i hi)]
      exact (hstep i hi hcoh).adjoin)

end OddOrder.Peterfalvi.S08
