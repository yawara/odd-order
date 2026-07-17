/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_YsetConjugation

/-!
# Peterfalvi §8: X/Y coherence glue

Y-set coherence, X-set character facts, and X/Y glue split under issue 0073.
-/
namespace OddOrder.Peterfalvi.S08
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis
variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]


/-- `Y = S(H')` is closed under complex conjugation. -/
theorem Yset_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.Yset := by
  intro φ hφ
  rw [Yset, SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, ?_, ?_, ?_⟩
  · intro hθc
    apply hθ_ne
    apply IrreducibleCharacter.ext
    have hval : (θ : ClassFunction ↥H ℂ).conj =
        (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ) := by
      simpa [θc] using congrArg
        (fun η : IrreducibleCharacter ↥H => (η : ClassFunction ↥H ℂ)) hθc
    calc
      (θ : ClassFunction ↥H ℂ) = ((θ : ClassFunction ↥H ℂ).conj).conj := by
        rw [ClassFunction.conj_conj]
      _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ).conj := by
        rw [hval]
      _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ) := by
        ext x
        simp
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- `Y = S(H')` has at least two members. -/
theorem two_le_Yset_ncard (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    2 ≤ hyp.Yset.ncard :=
  OddOrder.Peterfalvi.S07.two_le_ncard_of_conjugate_closed_of_noReal
    hyp.Yset_finite
    hyp.Yset_nonempty
    hyp.Yset_closedUnderConjugate
    hyp.Yset_hasNoRealCharacters

/-- `Y = S(H')` coherence, with the cardinal lower bound discharged internally. -/
noncomputable def coherentYset (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentYset_of_two_le_ncard hyp.two_le_Yset_ncard

/-- Convert the `X(Z) ≠ ∅` branch condition used in the (6.8) capstone into
the `Set.Nonempty` input consumed by the X-chain coherence constructors. -/
theorem Xset_nonempty_of_ne_empty (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    (hX : hyp.Xset Z ≠ ∅) : (hyp.Xset Z).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr hX

/-- **(6.8) coherence, `X`-empty case** (`H` abelian / no non-linear constituents).  When
`X = S − S([H,H])` is empty, the partition `S = X ∪ Y` (`Xset_union_Yset_eq_S`) collapses to
`S = Y = S([H,H])`, so the full target `IsCoherent τ S H^#` is exactly the already-built
`Y`-coherence `coherentYset` (T6: equal-degree `|W₁|` family).  This discharges the abelian branch
of the (6.8) capstone with no gluing required. -/
noncomputable def coherenceTarget_of_Xset_empty (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXe : hyp.Xset ⁅H, H⁆ = ∅) : hyp.CoherenceTarget := by
  have hSY : hyp.Yset = hyp.S := by
    rw [← hyp.Xset_union_Yset_eq_S, hXe, Set.empty_union]
  have h : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := hSY ▸ hyp.coherentYset
  exact h

/-- Glue `X = S - S(H')` coherence with the internally constructed `Y = S(H')` coherence.

This is the final algebraic assembly shape needed by Peterfalvi (6.8): callers still provide the
case-dependent `X` coherence and the two orthogonality/agreement inputs, but the `Y` side and the
set-theoretic rewrite from `X ∪ Y` to `S` are discharged here. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hsrc_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  let hY := hyp.coherentYset
  have hU : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
    OddOrder.Peterfalvi.S07.coherentUnion_of_glued
      (hX := hX) (hY := hY) ν hagreeX hagreeY hsrc_ortho himg_ortho hgen
  simpa [hyp.Xset_union_Yset_eq_S] using hU

/-- Variant of the (6.8) glue step where source-side orthogonality is discharged from
irreducibility of the `X` side and disjointness of the `X/Y` partition. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  letI : H.Normal := hyp.H_normal
  exact hyp.coherentS_of_Xset_commutator_Yset_glued hX ν hagreeX hagreeY
    (hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X hXirr) himg_ortho hgen

/-- Variant of the (6.8) glue step where source-side orthogonality is discharged from
irreducibility of `X`, and image-side orthogonality is discharged from mixed inner preservation
of the glued map `ν`. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hmixed : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner (ν u) (ν v) =
        ClassFunction.inner u v)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget := by
  let hsrc := hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X hXirr
  exact hyp.coherentS_of_Xset_commutator_Yset_glued hX ν hagreeX hagreeY hsrc
    (OddOrder.Peterfalvi.S07.image_orthogonal_of_mixed_inner_eq
      hagreeX hagreeY hmixed hsrc)
    hgen

/-- Generator-level variant of
`coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner`.

The `τ₃` candidate only has to be checked on the characters in `Xset H'` and `Yset`; agreement and
mixed-inner preservation on the integral spans are derived internally. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆, ν x = hX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner hXirr hX ν
    (fun _ hu => OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeX hu)
    (fun _ hv => OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on hagreeY hv)
    (OddOrder.Peterfalvi.S07.mixed_inner_eq_on_zSpan_of_eq_on hmixed)
    hgen

/-- **(6.8.1), case (c1):** in the Frobenius case every member of `S` is irreducible (hence
`X ⊆ Irr L`).  By [Is] Thm 6.34 (`isIrreducibleCharacter_induce_of_frobeniusGroup`), inducing any
nontrivial irreducible of the kernel `H` to the Frobenius group `L` gives an irreducible. -/
theorem isIrreducibleCharacter_of_mem_S_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.S) : IsIrreducibleCharacter φ := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hφ
  obtain ⟨θ, hθ_ne, rfl⟩ := hφ
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne

/-- **(6.8.1), case (c1):** `X ⊆ Irr L` in the Frobenius case, since `X ⊆ S` and `S ⊆ Irr L`.
This is the irreducibility input the §6 coherence engine (T8) consumes for the `X`-family (and the
`hX` hypothesis of the (6.6) characterization). -/
theorem isIrreducibleCharacter_of_mem_Xset_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Xset Z) :
    IsIrreducibleCharacter φ :=
  hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hyp.mem_Xset.mp hφ).1

/-- **`S` contains no real characters** (Frobenius case).

Each member of `S` is an irreducible induced character `Ind_H^L θ` (`θ ≠ 1_H`,
`isIrreducibleCharacter_of_mem_S_of_frobenius`) of degree `|L:H|·θ(1) = |W₁|·θ(1) ≥ |W₁| > 1`, so
it is not the trivial irreducible character; odd order of `L` then gives non-realness by Peterfalvi
(1.1) (`not_isReal_of_ne_trivial_of_odd_card'`).  This `HasNoRealCharacters` fact and its
`SsubFiltration` corollary supply the no-real input to the conjugate-pair enumeration of any
`S(A) ⊆ S` consumed on the way to the (6.2)/(6.3) degree bound. -/
theorem S_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.S := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  intro φ hφ hreal
  have hirr : IsIrreducibleCharacter φ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hφ
  let η : IrreducibleCharacter ↥L := ⟨φ, hirr⟩
  have hη_ne : η ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro hη
    have hφ_one_triv : φ (1 : ↥L) = 1 := by
      have h := congrArg (fun ψ : IrreducibleCharacter ↥L =>
        (ψ : ClassFunction ↥L ℂ) (1 : ↥L)) hη
      simpa [η, trivialClassFunction_apply] using h
    rw [hyp.S_eq] at hφ
    obtain ⟨θ, -, hφeq⟩ := hφ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hφ_one : φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) * (d : ℂ) := by
      rw [hφeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hd,
        hyp.index_H_eq_card_W1]
    refine absurd (hφ_one.symm.trans hφ_one_triv) ?_
    rw [← Nat.cast_mul]
    intro hcast
    have hnat : Nat.card hyp.W1 * d = 1 := by exact_mod_cast hcast
    exact hyp.W1_nontrivial (Subgroup.card_eq_one.mp (Nat.dvd_one.mp ⟨d, hnat.symm⟩))
  exact (OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
    hyp.card_L_odd hη_ne) hreal

/-- **`S(A)` contains no real characters** (Frobenius case), as `S(A) ⊆ S`. -/
theorem SsubFiltration_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) (A : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.SsubFiltration A) :=
  (hyp.S_hasNoRealCharacters hF).mono hyp.SsubFiltration_subset_S

/-- **`S`-member character facts** (Frobenius case): for `χ ∈ S` (irreducible by
`isIrreducibleCharacter_of_mem_S_of_frobenius`, non-real by `S_hasNoRealCharacters`) the conjugate
pair `{χ, χ̄}` is orthonormal (`‖χ‖² = ‖χ̄‖² = 1`, `⟨χ̄, χ⟩ = ⟨χ, χ̄⟩ = 0`).  These are the
per-member `hreal`/`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar` facts that the (6.2) member-family
enumeration feeds to B1 (`coherentDegreeSumBound_of_not_coherent`) for each member of `S₁ ⊆ S`. -/
theorem sMember_characterFacts (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 := by
  have hirr : IsIrreducibleCharacter χ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχS
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  have hreal : ¬ ClassFunction.IsReal χ := hyp.S_hasNoRealCharacters hF hχS
  have hbi_ne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  refine ⟨hreal, ?_, ?_, ?_, ?_⟩
  · simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
  · simpa using
      irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ.conj, hconjirr⟩
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hirr⟩
    rwa [if_neg hbi_ne] at h
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ.conj, hconjirr⟩
    rwa [if_neg (fun h => hbi_ne h.symm)] at h

/-- **`S`-member conjugate-difference support** (any irreducible `χ ∈ S`): `χ̄ − χ` is supported on
`H^# = sharpImage H`.  Since `χ = Ind_H^L θ` with `H ⊴ L`, `support χ ⊆ H`, and `χ̄ − χ` vanishes at
`1` (the degree `χ(1)` is a real natural number), so it omits `1`.  This is the per-member
`hdiffsupp` fact for the (6.2)/B1 member-family over `S₁ ⊆ S`. -/
theorem sMember_diffSupport (hyp : SibleyDadeHypothesis G L H)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hirr : IsIrreducibleCharacter χ) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hn1, star_natCast,
      sub_self])
  have hχg : χ g ≠ 0 := fun h0 =>
    hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_zero])
  have hgH : g ∈ H := by
    have hsupp : χ.support ⊆ (H : Set ↥L) := by
      rw [hχeq]
      exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)
    exact hsupp (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(6.8.1), Frobenius case:** source-side orthogonality for the final
`X = S - S(H')`, `Y = S(H')` partition. -/
theorem inner_span_Xset_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) :
    ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0 :=
  hyp.inner_span_Xset_Yset_eq_zero_of_irreducible_X
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)

/-- **(6.8.1), Frobenius case:** glue the Frobenius `X` coherence with the internally
constructed `Y` coherence, with source-side orthogonality discharged from Frobenius
irreducibility. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (himg_ortho : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset,
        ClassFunction.inner (hX.extension u) (hyp.coherentYset.extension v) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY himg_ortho hgen

/-- **(6.8.1), Frobenius case:** glue the Frobenius `X` coherence with the internally
constructed `Y` coherence, using mixed inner preservation of `ν` to discharge image-side
orthogonality. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆), ν u = hX.extension u)
    (hagreeY : ∀ v ∈ Submodule.span ℤ hyp.Yset,
      ν v = hyp.coherentYset.extension v)
    (hmixed : ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner (ν u) (ν v) =
        ClassFunction.inner u v)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY hmixed hgen

/-- **(6.8.1), Frobenius case:** generator-level mixed-inner glue adapter.

This is the Frobenius specialization of the generator-level `τ₃` interface: the `X`-side
irreducibility is discharged from `hF`, while agreement and mixed-inner preservation are required
only on members of `Xset H'` and `Yset`. -/
noncomputable def coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hX : OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆, ν x = hX.extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    hyp.CoherenceTarget :=
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hX ν hagreeX hagreeY hmixed hgen

/-- **(T7-c2 case A) `X ⊆ Irr L`.**  In case A every `χ ∈ X = S − S(Z)` is irreducible.  Writing
`χ = Ind_H^L θ` (`θ ≠ 1`, from `χ ∈ S`), membership `χ ∉ S(Z)` forces `Z.subgroupOf H ⊄ Ker θ`, so
`inertia_eq_H_of_c2_caseA` gives `I_L(θ) = H`, and [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`) makes `Ind_H^L θ = χ` irreducible.  This is the
case-A analogue of `isIrreducibleCharacter_of_mem_Xset_of_frobenius` (the Frobenius case). -/
theorem isIrreducibleCharacter_of_mem_Xset_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    letI : H.Normal := hyp.H_normal
    IsIrreducibleCharacter χ := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨hχS, hχnotZ⟩ := hχX
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, hθne, hχeq⟩ := hχS
  have hZker : ¬ ((Z.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ)) :=
    fun hsub => hχnotZ ⟨θ, hθne, hsub, hχeq⟩
  have hinertia := hyp.inertia_eq_H_of_c2_caseA hZH hZcentral hZnorm hZfpf hZker
  rw [hχeq]
  exact isIrreducibleCharacter_induce_of_inertia_eq θ hinertia

/-- **(c2)+math-(A) `X ⊆ Irr L`** (Peterfalvi (6.8.1) in the CertainType branch, math-case A).
Every `χ ∈ X = S − S(Zc)` is irreducible at the central `Zc = Z(H) ∩ H'`.  This is the (c2)
analogue of `isIrreducibleCharacter_of_mem_Xset_of_frobenius`: it discharges the four hypotheses of
the FPF-generic `isIrreducibleCharacter_of_mem_Xset_caseA` at `Z = Zc` — centrality
(`centralCommutator_subgroupOf_le_center`), normality (`Zc ◁ L`, so every `w` normalizes it), and
fixed-point-freeness (`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`, from the math-(A)
hypothesis `hA : Z(H) ⊓ W₂ = 1`). -/
theorem isIrreducibleCharacter_of_mem_Xset_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset hyp.centralCommutator) :
    letI : H.Normal := hyp.H_normal
    IsIrreducibleCharacter χ := by
  haveI := hyp.H_normal
  exact hyp.isIrreducibleCharacter_of_mem_Xset_caseA hyp.centralCommutator_le
    hyp.centralCommutator_subgroupOf_le_center
    (fun w _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr
        hyp.centralCommutator_normal]; exact Subgroup.mem_top w)
    (fun w hw hw1 => hyp.centralizer_inf_centralCommutator_eq_bot_of_c2_caseA hK hW1 hA hw hw1)
    hχX

/-- **Peterfalvi (6.6) `X`-characterization** (mmd 04.8 L74-76).  For a normal `Z ≤ H` such that
every member of `X = S − S(Z)` is irreducible (the (6.8) Frobenius/case-A input `hX`), `X` is
exactly the set of irreducible characters of `L` whose kernel does not contain `Z`:
`X = {χ ∈ Irr L | Z ⊄ Ker χ}`.

Both inclusions route the kernel comparison through a *genuine* character — `Res_H φ` for `⊆`
(via `characterKernel_subset_of_isCharacter_of_inner_ne_zero`) and `Ind_H^L θ` for `⊇` (via
`characterKernel_subset_of_inner_induce_ne_zero`) — together with the (1.6.a) forward bridge
`subsetCharacterKernel_induce_of_subgroupOf`; no use of [Is] Lemma 2.21 is needed. -/
theorem Xset_eq_irreducible_not_subset_characterKernel (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    hyp.Xset Z = {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)} := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  ext φ
  constructor
  · -- (⊆): φ ∈ X is irreducible (hX); if `Z ⊆ Ker φ` then `φ = Ind θ ∈ S(Z)`, contradiction.
    intro hφX
    have hφirr : IsIrreducibleCharacter φ := hX φ hφX
    refine ⟨hφirr, ?_⟩
    obtain ⟨hφS, hφnotSZ⟩ := hyp.mem_Xset.mp hφX
    rw [hyp.S_eq] at hφS
    obtain ⟨θ, hθ_ne, hφeq⟩ := hφS
    intro hZker
    apply hφnotSZ
    rw [hyp.mem_SsubFiltration]
    refine ⟨θ, hθ_ne, ?_, hφeq⟩
    -- `Z.subgroupOf H ⊆ Ker θ`: read off from `Res_H φ` (a genuine constituent of `θ`).
    have hRes : IsCharacter (ClassFunction.restrict H φ) := isCharacter_restrict hφirr.isCharacter H
    have hθirr : IsIrreducibleCharacter (θ : ClassFunction ↥H ℂ) := θ.property
    have hnorm : ClassFunction.inner φ φ = 1 := by
      have h := irreducibleCharacter_inner_eq_ite (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
      simpa using h
    have hinner_ne : ClassFunction.inner (ClassFunction.restrict H φ)
        (θ : ClassFunction ↥H ℂ) ≠ 0 := by
      have hfrob := ClassFunction.inner_induce_eq_inner_restrict H (θ : ClassFunction ↥H ℂ) φ
      rw [← hφeq, hnorm] at hfrob
      rw [inner_conj_symm θ (ClassFunction.restrict H φ), ← hfrob]
      simp
    intro n hn
    refine characterKernel_subset_of_isCharacter_of_inner_ne_zero hRes hθirr hinner_ne ?_
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    simp only [ClassFunction.restrict_apply]
    have hnZ : ((n : ↥L)) ∈ Z := Subgroup.mem_subgroupOf.mp hn
    have hker := hZker hnZ
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hker
    rw [hker, OneMemClass.coe_one]
  · -- (⊇): χ irreducible with `Z ⊄ Ker χ`.  Take a source `θ` of `χ`; show `Ind θ ∈ X`, hence
    -- irreducible (hX), hence `= χ` by orthonormality.
    rintro ⟨hχirr, hχZ⟩
    obtain ⟨θ, hθinner⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero (H := H)
      (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
    -- A source `θ'` of `χ` with `Z.subgroupOf H ⊆ Ker θ'` would force `Z ⊆ Ker χ` (contradiction).
    have hkey : ∀ θ' : IrreducibleCharacter ↥H,
        ClassFunction.inner (ClassFunction.induce H (θ' : ClassFunction ↥H ℂ)) φ ≠ 0 →
        ((Z.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥H ℂ)) → False := by
      intro θ' hθ'inner hθ'ker
      apply hχZ
      have hZind := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (G := ↥L) hZH (θ' : ClassFunction ↥H ℂ) hθ'ker
      intro z hz
      exact characterKernel_subset_of_inner_induce_ne_zero θ'.property.isCharacter hχirr
        hθ'inner (hZind hz)
    have hθ_ne : θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H := by
      intro hθtriv
      refine hkey θ hθinner (fun n _ => ?_)
      rw [hθtriv]
      simp [OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    have hIndnotSZ : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∉ hyp.SsubFiltration Z := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', _, hθ'ker, hθ'eq⟩ := hmem
      exact hkey θ' (by rw [← hθ'eq]; exact hθinner) hθ'ker
    have hIndX : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∈ hyp.Xset Z :=
      hyp.mem_Xset.mpr ⟨by rw [hyp.S_eq]; exact ⟨θ, hθ_ne, rfl⟩, hIndnotSZ⟩
    have hIndirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) :=
      hX _ hIndX
    have heq : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) = φ := by
      have hite := irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hIndirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      by_cases hAB : (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hIndirr⟩ :
          IrreducibleCharacter ↥L) = (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      · exact congrArg Subtype.val hAB
      · rw [if_neg hAB] at hite
        exact absurd hite hθinner
    rw [← heq]; exact hIndX

/-- **(T8 leaf 1) `X`-member character facts**, from the abstract input `X ⊆ Irr L`.

Every `χ ∈ X = S − S(Z)` is non-real (Peterfalvi (1.1), `L` odd) with
`‖χ‖² = ‖χ̄‖² = 1` and `⟨χ̄, χ⟩ = ⟨χ, χ̄⟩ = 0`.  These are the
`hreal`/`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar'` fields of `S07.DadeChainStep`.
Non-triviality is read off the (6.6) characterization
(`Z ⊄ Ker χ` via `Xset_eq_irreducible_not_subset_characterKernel`, so `χ ≠ 1`),
then (1.1) (`not_isReal_of_ne_trivial_of_odd_card'`) gives non-realness and
`irreducibleCharacter_inner_eq_ite` gives the orthonormality.

This form is shared by the Frobenius case and the case-A `X ⊆ Irr L` bridge. -/
theorem xMember_characterFacts_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  -- `Z ⊄ Ker χ` from the (6.6) characterization, hence `χ ≠ 1`.
  have hZker : ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ) := by
    have hXeq := hyp.Xset_eq_irreducible_not_subset_characterKernel hZH hX
    rw [hXeq] at hχX
    exact hχX.2
  have hne_triv : (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ≠
      OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro htriv
    apply hZker
    have hχtriv : χ = OddOrder.RepresentationTheory.trivialClassFunction ↥L :=
      congrArg Subtype.val htriv
    rw [hχtriv, OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  have hreal : ¬ ClassFunction.IsReal χ :=
    OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hyp.card_L_odd hne_triv
  have hbi_ne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  refine ⟨hreal, ?_, ?_, ?_, ?_⟩
  · simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
  · simpa using
      irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ.conj, hconjirr⟩
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hirr⟩
    rwa [if_neg hbi_ne] at h
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ.conj, hconjirr⟩
    rwa [if_neg (fun h => hbi_ne h.symm)] at h

/-- **(T8 leaf 1) `X`-member character facts** (Frobenius case). -/
theorem xMember_characterFacts (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 :=
  hyp.xMember_characterFacts_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχX

/-- **(T8 leaf 2) `X`-member difference support**, from the abstract input `X ⊆ Irr L`.

For `χ ∈ X = S − S(Z)` the conjugate difference `χ̄ − χ` is supported on
`H^# = sharpImage H` (the `hdiffsupp` field of `S07.DadeChainStep`).  Since
`χ = Ind_H^L θ` with `H ⊴ L`, `support χ ⊆ H` (`support_induce_subset_of_normal`);
`χ̄ − χ` vanishes at `1` (the degree `χ(1)` is the real `(n : ℂ)`), so it omits `1`
and lands in `H ∖ {1}`. -/
theorem xMember_diffSupport_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hχS : χ ∈ hyp.S := (hyp.mem_Xset.mp hχX).1
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hn1, star_natCast,
      sub_self])
  have hχg : χ g ≠ 0 := fun h0 =>
    hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_zero])
  have hgH : g ∈ H := by
    have hsupp : χ.support ⊆ (H : Set ↥L) := by
      rw [hχeq]
      exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)
    exact hsupp (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T8 leaf 2) `X`-member difference support** (Frobenius case). -/
theorem xMember_diffSupport (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  hyp.xMember_diffSupport_of_irreducible_X
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hχX

/-- **(T8 leaf 3a) `X` is closed under conjugation**, from the abstract input `X ⊆ Irr L`.

`Z ⊴ L` gives `Ker χ̄ = Ker χ` (`characterKernel_conj`), so the (6.6) characterization
`X = {χ ∈ Irr L | Z ⊄ Ker χ}` is conjugation-invariant.  This is the
`ClosedUnderConjugate` input to the degree-monotone enumeration of `X` into conjugate pairs
(`S07.two_le_ncard_of_conjugate_closed_of_noReal`, `S07.exists_monotoneDegreeEnum`). -/
theorem Xset_closedUnderConjugate_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (_hZH : Z ≤ H) [Z.Normal]
    (_hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
  hyp.Xset_closedUnderConjugate_unconditional Z

/-- **(T8 leaf 3a) `X` is closed under conjugation** (Frobenius case). -/
theorem Xset_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
  hyp.Xset_closedUnderConjugate_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- **(T8 leaf 3b) `X` has no real characters**, from the abstract input `X ⊆ Irr L`. -/
theorem Xset_hasNoRealCharacters_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
  fun _ hχX => (hyp.xMember_characterFacts_of_irreducible_X hZH hX hχX).1

/-- **(T8 leaf 3b) `X` has no real characters** (Frobenius case). -/
theorem Xset_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
  hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- **(T8 leaf 4) `X` is finite**, from the abstract input `X ⊆ Irr L`.

This is the `hXfin` input to the degree-monotone enumeration
`S07.exists_monotoneDegreeEnum` and the chain assembly. -/
theorem xSet_finite_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (_hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    (hyp.Xset Z).Finite :=
  hyp.Xset_finite Z

/-- **(T8 leaf 4) `X` is finite** (Frobenius case). -/
theorem xSet_finite (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} :
    (hyp.Xset Z).Finite :=
  hyp.xSet_finite_of_irreducible_X
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)


end SibleyDadeHypothesis
end OddOrder.Peterfalvi.S08
