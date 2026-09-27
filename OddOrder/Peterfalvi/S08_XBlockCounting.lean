/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CentralCommutatorRestriction

/-!
# Peterfalvi (6.8) setting: coherence of `X(Z_c) ∪ Y` and the `(6.7)` congruences

Coherence constructions for `X(Z_c) ∪ Y` (glued-with-diagonal and `himg_ortho` shells, the
`PairUnionStepData` generators), the Sylow transport lemmas, the `(6.7)` central-commutator
congruence `peterfalvi_67_centralCommutator`, and the character-value congruences / divisibility
of restricted `Y`-set extensions.

Prefix-split from `OddOrder.Peterfalvi.S08_CoherenceCore` (2000-line limit, issue 0103 第 2 パス);
the restriction/orthogonality family was further moved to
`OddOrder.Peterfalvi.S08_CentralCommutatorRestriction` (issue 0189, 1500-line limit).
-/
namespace OddOrder.Peterfalvi.S08
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis
variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- L3 outer shell at the fixed witnesses (specialization of
`coherentXunionYset_centralCommutator_of_glued_withDiagonal_general`). -/
noncomputable def coherentXunionYset_centralCommutator_of_glued_withDiagonal_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset hyp.centralCommutator,
      ν x = (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥L ℂ))
    (hDτ : ∀ d ∈ D, ν d = hyp.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentXunionYset_centralCommutator_of_glued_withDiagonal_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset ν hagreeX hagreeY hmixed D hDτ hgen

/-- **L3 (3a) shell, ν-free form:** `X(Zc) ∪ Y` is coherent given only the genuine (6.8.1) input
`himg_ortho : ⟨χ^{τ₂}, η^{τ₁}⟩ = 0`.  The `τ₃` glue `ν` is constructed internally
(`exists_integralCharacterMap_glue_of_orthonormal` with `νX = τ₂`, `νY = τ₁`); its agreement
`hagreeX`/`hagreeY` is automatic, and `hmixed` reduces to `himg_ortho` (both `⟨νx,νy⟩` and `⟨x,y⟩`
vanish — the latter by `X ⊥ Y`).  Orthonormality of `X`, `Y` and `X ⊥ Y` are read off irreducibility
(`irreducibleCharacter_inner`) + disjointness.  **The sole remaining (6.8.1) obligation is
`himg_ortho`** — the `b ≡ c ≡ 0 mod a` argument (L3 (3b), via `peterfalvi_67_centralCommutator`). -/
noncomputable def coherentXunionYset_centralCommutator_of_himg_ortho
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    (himg_ortho : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner
        ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
        (hyp.coherentYset.extension y) = 0)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset hyp.centralCommutator)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [ite_eq_left (Subtype.ext hpq), ite_eq_left hpq]
    · rw [ite_eq_right (fun heq => hpq (Subtype.ext_iff.mp heq)), ite_eq_right hpq]
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hXY : ∀ x ∈ hyp.Xset hyp.centralCommutator, ∀ y ∈ hyp.Yset,
      ClassFunction.inner x y = 0 := fun x hx y hy => by
    rw [hinner x y (hXirr x hx) (hYirr y hy),
      ite_eq_right (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
  have hglue :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthonormal
      (hyp.Xset_finite hyp.centralCommutator) hyp.Yset_finite
      (fun x hx x' hx' => hinner x x' (hXirr x hx) (hXirr x' hx'))
      (fun y hy y' hy' => hinner y y' (hYirr y hy) (hYirr y' hy')) hXY
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension)
      hyp.coherentYset.extension
  refine hyp.coherentXunionYset_centralCommutator_of_glued_of_frobenius hF hHnonab hp hp3 hHp
    hglue.choose hglue.choose_spec.1 hglue.choose_spec.2 (fun x hx y hy => ?_) hgen
  rw [hglue.choose_spec.1 x hx, hglue.choose_spec.2 y hy, himg_ortho x hx y hy, hXY x hx y hy]

/-- **(6.8.1), Frobenius case:** chain-level coherence for
`X = S - S(H')`, using common-index p-power data.

This is the `Z = H'` specialization of
`Xset_isCoherent_from_pairUnionStepData_of_irreducible_X` for the Frobenius
alternative.  The subgroup facts `H' ≤ H`, `H' ⊴ L`, and `X ⊆ Irr L` are discharged internally;
the remaining inputs are the honest (6.6) nonemptiness and per-step degree data. -/
noncomputable def Xset_commutator_isCoherent_from_pairUnionStepData_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  exact hyp.Xset_isCoherent_from_pairUnionStepData_of_irreducible_X
    (Z := ⁅H, H⁆) (Subgroup.commutator_le_left H H)
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hXne hstepData

/-- **(6.8.1), Frobenius case:** chain-level coherence for
`X = S - S(H')`, using the base-anchor common-index p-power step packages.

Compared with
`Xset_commutator_isCoherent_from_pairUnionStepData_of_frobenius`, each step data
package only supplies a base-block anchor; the sorted-degree facts are derived by the existing
base-anchor adapter. -/
noncomputable def
    Xset_commutator_isCoherent_from_anchoredPairUnionStepData_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        AnchoredPairUnionStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  exact hyp.Xset_isCoherent_from_anchoredPairUnionStepData_of_irreducible_X
    (Z := ⁅H, H⁆) (Subgroup.commutator_le_left H H)
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hXne hstepData

/-- **(6.6)/(6.8.1), central-`Zc` form (redesign L2 outer shell):** chain-level coherence for
`X = S − S(Zc)` with the **central** `Zc = Z(H) ∩ H′`, from base-anchor common-index p-power step
packages. This replaces
`Xset_commutator_isCoherent_from_anchoredPairUnionStepData_of_frobenius`
(which instantiated the general (6.6) consumer at `Z = ⁅H,H⁆`, where the per-step degree field
`hθsq_le_qtot : θχ² ≤ qtot ≤ |H:⁅H,H⁆|` is *unsatisfiable* for class ≥ 3 `p`-groups — see
`notes/peterfalvi/s08_6_8_blocker_central_Z.md`). At the central `Zc` that field is honestly
fillable
by [Is] Cor 2.30 (`exists_source_primePow_centralBound_of_mem_Xset`), so the `hstepData` hypothesis
is satisfiable here — the remaining work is to *construct* it (the producer monolith).  `hX` is
discharged Z-generically (`isIrreducibleCharacter_of_mem_Xset_of_frobenius`) and `hXne` from `H`
non-abelian (`Xset_centralCommutator_nonempty`). -/
noncomputable def
    Xset_centralCommutator_isCoherent_from_anchoredPairUnionStepData_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset hyp.centralCommutator) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L)
          (hyp.xBaseBlock hyp.centralCommutator) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        AnchoredPairUnionStepData hyp
          (Z := hyp.centralCommutator) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  exact hyp.Xset_isCoherent_from_anchoredPairUnionStepData_of_irreducible_X
    (Z := hyp.centralCommutator) hyp.centralCommutator_le
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    (hyp.Xset_centralCommutator_nonempty hF hHnonab) hstepData

/-- **(6.8.1), Frobenius case:** final glue from common-index p-power X-chain data.

This composes the Frobenius `X = S - S(H')` coherence constructor with the generator-level `τ₃`
glue adapter.  The caller supplies only the genuine (6.6) X-chain step data and generator-level
`τ₃` agreement/mixed-inner facts; the `X` coherence witness is built internally. -/
noncomputable def coherentS_of_frobenius_pairUnionStepData_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x = (hyp.Xset_commutator_isCoherent_from_pairUnionStepData_of_frobenius
        hF hXne hstepData).extension x)
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
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner hF
    (hyp.Xset_commutator_isCoherent_from_pairUnionStepData_of_frobenius
      hF hXne hstepData)
    ν hagreeX hagreeY hmixed hgen

/-- **(6.8.1), Frobenius case:** final glue from base-anchor common-index p-power X-chain data.

This is the same capstone as
`coherentS_of_frobenius_pairUnionStepData_generator_mixed_inner`, but using the
base-anchor step package that derives the sorted-degree inequalities internally. -/
noncomputable def
    coherentS_of_frobenius_anchoredPairUnionStepData_generator_mixed_inner
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        AnchoredPairUnionStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x =
      (hyp.Xset_commutator_isCoherent_from_anchoredPairUnionStepData_of_frobenius
          hF hXne hstepData).extension x)
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
  hyp.coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner hF
    (hyp.Xset_commutator_isCoherent_from_anchoredPairUnionStepData_of_frobenius
      hF hXne hstepData)
    ν hagreeX hagreeY hmixed hgen

/-- **(6.7)-wiring step (b): `N_G(H.map L.subtype) = L`.**  The normalizer (in `G`) of the kernel
realized in the ambient group is exactly `L`: `≤` is the `H^#` TI condition (`H_sharp_ti`; a
nontrivial `a ∈ Ĥ` and its conjugate witness the TI hypothesis), and `≥` holds because `H ◁ L`
(`L = range L.subtype` normalizes the image of the normal `H`, via `le_normalizer_map`). -/
theorem normalizer_map_subtype_eq (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    Subgroup.normalizer (H.map L.subtype) = L := by
  apply le_antisymm
  · have : Nontrivial ↥H := H.nontrivial_iff_ne_bot.mpr hyp.H_ne_bot
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥H)
    set a : G := ((x : ↥L) : G) with ha_def
    have haĤ : a ∈ H.map L.subtype := Subgroup.mem_map.mpr ⟨(x : ↥L), x.2, rfl⟩
    have ha1 : a ≠ 1 := by rw [ha_def]; simp only [ne_eq, OneMemClass.coe_eq_one]; exact hx1
    intro g hg
    refine hyp.H_sharp_ti g ⟨a, ⟨haĤ, ha1⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg a).mp haĤ
    · intro hc
      rw [Set.mem_singleton_iff, mul_inv_eq_one, mul_eq_left] at hc
      exact ha1 hc
  · calc L = L.subtype.range := (Subgroup.range_subtype L).symm
      _ = (⊤ : Subgroup ↥L).map L.subtype := MonoidHom.range_eq_map L.subtype
      _ = (Subgroup.normalizer H).map L.subtype := by
          rw [Subgroup.normalizer_eq_top_iff.mpr ‹H.Normal›]
      _ ≤ Subgroup.normalizer (H.map L.subtype) := H.le_normalizer_map L.subtype

/-- **`Ĥ = H.map L.subtype` is a Sylow `p`-subgroup of `G`, from the Hall coprimality** — the
coprimality-only core of `sylow_map_subtype_of_frobenius`.  Peterfalvi (6.8)(a) only assumes `H^#`
TI with normalizer `L`, which alone does *not* force `H` Sylow; the only extra input is
`gcd(|H|, |W₁|) = 1` (Frobenius: `hF.coprime_card_kernel_complement`; (6.8)(c2): the `cases` Hall
side condition).  With `H` a `p`-group and `H ◁ L` with coprime complement `W₁`, `H` is the unique
normal Sylow `p`-subgroup of `↥L`, so every `p`-subgroup of `↥L` (e.g. `Q ⊓ L` for a Sylow
`Q ⊇ Ĥ`) lies in `H`; with `N_G(Ĥ) ≤ L` (`H^#` TI) and the self-normalizing-Sylow criterion
`sylow_coe_eq_of_normalizer_inf_le`, this forces `Ĥ ∈ Syl_p(G)`.  (Lifted from `S08_CaseBCoherence`;
both Frobenius and case-(A)/(B) (6.7)-wirings delegate here.) -/
theorem sylow_map_subtype_of_coprime (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H.map L.subtype := by
  have : Fact p.Prime := ⟨hp⟩
  set Ĥ : Subgroup G := H.map L.subtype with hĤ_def
  -- `Ĥ` is a `p`-group (image of the `p`-group `H` under the injective `L.subtype`).
  have hĤp : IsPGroup p ↥Ĥ := hHp.map L.subtype
  -- `p ∣ |H|` (nontrivial `p`-group) and `gcd(|H|, |W₁|) = 1`, so `p ∤ [L : H] = |W₁|`.
  have hpH : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hHp
    have h1 : 1 < Nat.card ↥H := (Subgroup.one_lt_card_iff_ne_bot (H := H)).mpr hyp.H_ne_bot
    rw [hn] at h1 ⊢
    rcases n with _ | n
    · simp at h1
    · exact dvd_pow_self p (Nat.succ_ne_zero n)
  have hpidx : ¬ p ∣ H.index := by
    rw [hyp.index_H_eq_card_W1]
    exact (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_left hpH hcop)
  -- `H` is the unique (normal) Sylow `p`-subgroup of `↥L`.
  set HSyl : Sylow p ↥L := hHp.toSylow hpidx with hHSyl_def
  have hHSyl : (HSyl : Subgroup ↥L) = H := IsPGroup.toSylow_coe hHp hpidx
  have hHSylNormal : (HSyl : Subgroup ↥L).Normal := by rw [hHSyl]; exact ‹H.Normal›
  have : Unique (Sylow p ↥L) := Sylow.unique_of_normal HSyl hHSylNormal
  have hpsub : ∀ K : Subgroup ↥L, IsPGroup p K → K ≤ H := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.exists_le_sylow
    calc K ≤ (R : Subgroup ↥L) := hR
      _ = (HSyl : Subgroup ↥L) := by rw [Subsingleton.elim R HSyl]
      _ = H := hHSyl
  -- `N_G(Ĥ) ≤ L` from `H^#` TI (the `normalizer_map_subtype_eq` equality).
  have hNle : Subgroup.normalizer Ĥ ≤ L := hyp.normalizer_map_subtype_eq.le
  -- a Sylow overgroup `Q ⊇ Ĥ`; then `N_G(Ĥ) ⊓ Q ≤ Ĥ` via the `p`-subgroup `Q.comap L.subtype ≤ H`.
  obtain ⟨Q, hĤQ⟩ := hĤp.exists_le_sylow
  refine ⟨Q, ?_⟩
  apply OddOrder.GroupTheory.sylow_coe_eq_of_normalizer_inf_le hĤQ
  intro x hx
  have hxL : x ∈ L := hNle hx.1
  have hQLp : IsPGroup p ((Q : Subgroup G).comap L.subtype : Subgroup ↥L) :=
    Q.isPGroup'.comap_of_injective L.subtype L.subtype_injective
  have hx'H : (⟨x, hxL⟩ : ↥L) ∈ H :=
    hpsub _ hQLp (Subgroup.mem_comap.mpr (by exact hx.2))
  exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hx'H, rfl⟩

/-- **(6.7)-wiring step (a): the kernel `H`, mapped into `G`, is a Sylow `p`-subgroup of `G`.**

Peterfalvi (6.7) is stated for a Sylow `p`-subgroup `P` of `G` with `L = N_G(P)`; the (6.8.1)
application uses it at `P = H` (modulus `|H|`).  In the **Frobenius case**, `H ◁ L` with complement
`W₁` of coprime order (`hF.coprime_card_kernel_complement`) makes `H` Sylow; delegates to the
coprimality core `sylow_map_subtype_of_coprime`. -/
theorem sylow_map_subtype_of_frobenius (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H.map L.subtype :=
  hyp.sylow_map_subtype_of_coprime hF.coprime_card_kernel_complement hp hHp

open scoped OddOrder.AlgInt in
/-- **(6.7)-wiring capstone: Peterfalvi (6.7) specialized to the Sibley Frobenius setup.**

For an irreducible `ρ` whose character is **constant on `Z^# = (Z(H) ∩ H′)^#`** (the only
character-theoretic input, deferred to the caller — in (6.8.1) it is `η₁^{τ₁}`), the congruence

`ρ.character z ≡ ρ.character 1  (mod |H|)`

holds for `z ∈ Z^#`.  This discharges every structural hypothesis of `peterfalvi_67_of_odd` at
`P := Ĥ = H.map L.subtype` (Sylow in `G` by `sylow_map_subtype_of_frobenius`, with `N_G(Ĥ) = L` by
`normalizer_map_subtype_eq`) and `Z := centralCommutator.map L.subtype`: `hZP`, `hZnormal`
(`Z.subgroupOf L = centralCommutator ◁ ↥L`), `hti`/`hodd` (`H^#` TI / `|L|` odd), `hPz`
(`Ĥ ≤ C_G(z)`), and the `|C_L(·)|`-constancy clause of `hconst` (both sides `= |Ĥ|` by
`inf_centralizer_centralCommutator_map`).  The modulus `|Ĥ| = |H|` via `card_map_of_injective`. -/
theorem peterfalvi_67_centralCommutator (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ hyp.centralCommutator.map L.subtype) (hz1 : z ≠ 1)
    (hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
        ρ.character w = ρ.character z) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥H : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  classical
  obtain ⟨Q, hQeq⟩ := hyp.sylow_map_subtype_of_frobenius hF hp hHp
  have hNorm : Subgroup.normalizer ((Q : Subgroup G) : Set G) = L := by
    rw [hQeq]; exact hyp.normalizer_map_subtype_eq
  have hcard : Nat.card (Q : Subgroup G) = Nat.card ↥H := by
    rw [hQeq]; exact Subgroup.card_map_of_injective L.subtype_injective
  -- structural hypotheses of `peterfalvi_67_of_odd`
  have hZP : hyp.centralCommutator.map L.subtype ≤ (Q : Subgroup G) := by
    rw [hQeq]; exact Subgroup.map_mono hyp.centralCommutator_le
  have hZnormal : ((hyp.centralCommutator.map L.subtype).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup G) : Set G))).Normal := by
    rw [hNorm,
      show (hyp.centralCommutator.map L.subtype).subgroupOf L = hyp.centralCommutator from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact hyp.centralCommutator_normal
  have hti : OddOrder.GroupTheory.IsTISubset (((Q : Subgroup G) : Set G) \ {1})
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [hNorm, show ((Q : Subgroup G) : Set G) \ {1} = sharpImage H by rw [hQeq]; rfl]
    exact hyp.H_sharp_ti
  have hodd : Odd (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [hNorm]; exact hyp.card_L_odd
  have hPz : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hQeq]
    obtain ⟨w', hw', hw'z⟩ := Subgroup.mem_map.mp hz
    have hw'zc : (w' : G) = z := hw'z
    have hw'1 : w' ≠ 1 := fun h => hz1 (hw'zc ▸ OneMemClass.coe_eq_one.mpr h)
    have hbr := hyp.inf_centralizer_centralCommutator_map hF hw' hw'1
    rw [hw'zc] at hbr
    rw [← hbr]; exact inf_le_right
  have hconst : ∀ ⦃w : G⦄, w ∈ hyp.centralCommutator.map L.subtype → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G)) := by
    intro w hw hw1
    refine ⟨hψconst w hw hw1, ?_⟩
    obtain ⟨w', hw'cc, hw'w⟩ := Subgroup.mem_map.mp hw
    have hw'wc : (w' : G) = w := hw'w
    have hw'1 : w' ≠ 1 := fun h => hw1 (hw'wc ▸ OneMemClass.coe_eq_one.mpr h)
    obtain ⟨z', hz'cc, hz'z⟩ := Subgroup.mem_map.mp hz
    have hz'zc : (z' : G) = z := hz'z
    have hz'1 : z' ≠ 1 := fun h => hz1 (hz'zc ▸ OneMemClass.coe_eq_one.mpr h)
    rw [hNorm, ← hw'wc, ← hz'zc, hyp.inf_centralizer_centralCommutator_map hF hw'cc hw'1,
      hyp.inf_centralizer_centralCommutator_map hF hz'cc hz'1]
  have key := OddOrder.RepresentationTheory.peterfalvi_67_of_odd ρ Q hZP hZnormal hti hodd
    hz hz1 hPz hconst
  rwa [hcard] at key

open scoped OddOrder.AlgInt in
/-- **(6.7)-wiring capstone, case-(A) / c2 form.**  The (c2) analogue of
`peterfalvi_67_centralCommutator`: the (6.7) congruence `ρ.character z ≡ ρ.character 1 (mod |H|)`
for `z ∈ Zc^#` and `ρ` irreducible **constant on `Zc^#`**, *without* the Frobenius hypothesis.  `H`
is Sylow in `G` via the coprimality core `sylow_map_subtype_of_coprime` (coprimality from
`cert.card_coprime`), and the `|C_L(·)|`-constancy clause of `hconst` is the case-(A) FPF
`inf_centralizer_centralCommutator_map_c2_caseA`.  Otherwise structurally identical to the
Frobenius form. -/
theorem peterfalvi_67_centralCommutator_c2_caseA (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ hyp.centralCommutator.map L.subtype) (hz1 : z ≠ 1)
    (hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
        ρ.character w = ρ.character z) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥H : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  classical
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1) := by
    have h := cert.card_coprime; rw [hK, hW1] at h; exact h
  obtain ⟨Q, hQeq⟩ := hyp.sylow_map_subtype_of_coprime hcop hp hHp
  have hNorm : Subgroup.normalizer ((Q : Subgroup G) : Set G) = L := by
    rw [hQeq]; exact hyp.normalizer_map_subtype_eq
  have hcard : Nat.card (Q : Subgroup G) = Nat.card ↥H := by
    rw [hQeq]; exact Subgroup.card_map_of_injective L.subtype_injective
  -- structural hypotheses of `peterfalvi_67_of_odd`
  have hZP : hyp.centralCommutator.map L.subtype ≤ (Q : Subgroup G) := by
    rw [hQeq]; exact Subgroup.map_mono hyp.centralCommutator_le
  have hZnormal : ((hyp.centralCommutator.map L.subtype).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup G) : Set G))).Normal := by
    rw [hNorm,
      show (hyp.centralCommutator.map L.subtype).subgroupOf L = hyp.centralCommutator from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact hyp.centralCommutator_normal
  have hti : OddOrder.GroupTheory.IsTISubset (((Q : Subgroup G) : Set G) \ {1})
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [hNorm, show ((Q : Subgroup G) : Set G) \ {1} = sharpImage H by rw [hQeq]; rfl]
    exact hyp.H_sharp_ti
  have hodd : Odd (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [hNorm]; exact hyp.card_L_odd
  have hPz : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hQeq]
    obtain ⟨w', hw', hw'z⟩ := Subgroup.mem_map.mp hz
    have hw'zc : (w' : G) = z := hw'z
    have hw'1 : w' ≠ 1 := fun h => hz1 (hw'zc ▸ OneMemClass.coe_eq_one.mpr h)
    have hbr := hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hw' hw'1
    rw [hw'zc] at hbr
    rw [← hbr]; exact inf_le_right
  have hconst : ∀ ⦃w : G⦄, w ∈ hyp.centralCommutator.map L.subtype → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G)) := by
    intro w hw hw1
    refine ⟨hψconst w hw hw1, ?_⟩
    obtain ⟨w', hw'cc, hw'w⟩ := Subgroup.mem_map.mp hw
    have hw'wc : (w' : G) = w := hw'w
    have hw'1 : w' ≠ 1 := fun h => hw1 (hw'wc ▸ OneMemClass.coe_eq_one.mpr h)
    obtain ⟨z', hz'cc, hz'z⟩ := Subgroup.mem_map.mp hz
    have hz'zc : (z' : G) = z := hz'z
    have hz'1 : z' ≠ 1 := fun h => hz1 (hz'zc ▸ OneMemClass.coe_eq_one.mpr h)
    rw [hNorm, ← hw'wc, ← hz'zc,
      hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hw'cc hw'1,
      hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hz'cc hz'1]
  have key := OddOrder.RepresentationTheory.peterfalvi_67_of_odd ρ Q hZP hZnormal hti hodd
    hz hz1 hPz hconst
  rwa [hcard] at key

open scoped OddOrder.AlgInt in
/-- **(6.8.1) (6.7)-congruence for `η^{τ₁}`** (mmd 04.8 L168 → L176).  For `η ∈ Y` and `z ∈ Zc^#`,
`Res^G_L(η^{τ₁})(z) ≡ Res^G_L(η^{τ₁})(1) (mod |H|)`.  Wires the (6.7) adapter
`peterfalvi_67_centralCommutator` to `η^{τ₁}`: write `η^{τ₁} = ε•ξ` (`ε = ±1`, `ξ` irreducible, from
norm `1`); unpack `ξ = ρ.character` (`ρ` irreducible).  The const-on-`Zc^#`
(`restrict_extension_Yset_const_on_centralCommutator_of_frobenius`, transferred to `Zc.map`) is the
adapter's hypothesis, giving `ξ(z) ≡ ξ(1) (mod |H|)`; scale by `ε` (`Cong.smul_left`) to get
`η^{τ₁}(z) ≡ η^{τ₁}(1)`. -/
theorem restrict_extension_Yset_charValue_cong_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      ≡ (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
        [ALGMOD (Nat.card ↥H : ℤ)] := by
  classical
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hηtnorm : ClassFunction.inner (hyp.coherentYset.extension η)
      (hyp.coherentYset.extension η) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η η (Submodule.subset_span hη)
      (Submodule.subset_span hη)]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
    simpa using h
  obtain ⟨ε, ξ, hε, hηtε⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hηtZ hηtnorm
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  -- the eval identity `η^{τ₁}(g) = ε · ξ(g)`.
  have hsmul : ∀ g : G, (hyp.coherentYset.extension η) g
      = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  have : ρ.IsIrreducible := hρ
  have hzGmem : (L.subtype z) ∈ hyp.centralCommutator.map L.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hzG1 : (L.subtype z) ≠ 1 := fun h => hz1 (L.subtype_injective (by simpa using h))
  have hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
      ρ.character w = ρ.character (L.subtype z) := by
    intro w hw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; simp)
    have hRw : (hyp.coherentYset.extension η) (L.subtype w₀)
        = (hyp.coherentYset.extension η) (L.subtype z) :=
      hyp.restrict_extension_Yset_const_on_centralCommutator_of_frobenius
        hF hHnonab hp hp3 hHp hη hw₀ hw₀1 hz hz1
    rw [← congrFun hξρ (L.subtype w₀), ← congrFun hξρ (L.subtype z)]
    apply mul_left_cancel₀ hεne
    rw [← hsmul (L.subtype w₀), ← hsmul (L.subtype z)]
    exact hRw
  have hcong := hyp.peterfalvi_67_centralCommutator hF hp hHp ρ hzGmem hzG1 hψconst
  rw [← congrFun hξρ (L.subtype z), ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  simp only [← hsmul] at hcong2
  exact hcong2

open scoped OddOrder.AlgInt in
/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_charValue_cong_of_frobenius`.**  Same as the
Frobenius original, with `hF` replaced by the certain-type case-(A) bundle `cert`/`hK`/`hW1`/`hA`,
and
the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_charValue_cong_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      ≡ (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
        [ALGMOD (Nat.card ↥H : ℤ)] := by
  classical
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hηtnorm : ClassFunction.inner (hyp.coherentYset.extension η)
      (hyp.coherentYset.extension η) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η η (Submodule.subset_span hη)
      (Submodule.subset_span hη)]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
    simpa using h
  obtain ⟨ε, ξ, hε, hηtε⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hηtZ hηtnorm
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  -- the eval identity `η^{τ₁}(g) = ε · ξ(g)`.
  have hsmul : ∀ g : G, (hyp.coherentYset.extension η) g
      = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  have : ρ.IsIrreducible := hρ
  have hzGmem : (L.subtype z) ∈ hyp.centralCommutator.map L.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hzG1 : (L.subtype z) ≠ 1 := fun h => hz1 (L.subtype_injective (by simpa using h))
  have hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
      ρ.character w = ρ.character (L.subtype z) := by
    intro w hw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; simp)
    have hRw : (hyp.coherentYset.extension η) (L.subtype w₀)
        = (hyp.coherentYset.extension η) (L.subtype z) :=
      hyp.restrict_extension_Yset_const_on_centralCommutator_c2_caseA
        hK hW1 hA hHnonab hp hp3 hHp hη hw₀ hw₀1 hz hz1
    rw [← congrFun hξρ (L.subtype w₀), ← congrFun hξρ (L.subtype z)]
    apply mul_left_cancel₀ hεne
    rw [← hsmul (L.subtype w₀), ← hsmul (L.subtype z)]
    exact hRw
  have hcong := hyp.peterfalvi_67_centralCommutator_c2_caseA hK hW1 hA hp hHp ρ hzGmem hzG1 hψconst
  rw [← congrFun hξρ (L.subtype z), ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  simp only [← hsmul] at hcong2
  exact hcong2

open scoped OddOrder.AlgInt in
/-- **(6.8.1) `a ∣ c`** (mmd 04.8 L176, the `c ≡ 0 (mod a)` half of "`b ≡ c ≡ 0 (mod a)`").  For
`η ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` of degree `χ₁(1) = a·|W₁|` (`a > 0`, the degree ratio against
the `Y`-degree `|W₁|`), the multiplicity `c = ⟨Res^G_L(η^{τ₁}), χ₁⟩` is an **integer divisible by
`a`**.

This is the (6.7) divisibility step.  The value identity
`restrict_extension_Yset_degree_value_eq_of_frobenius` gives `χ₁(1)·(R(z)−R(1)) = −c·|L|` for
`z ∈ Zc^#` (`R = Res^G_L(η^{τ₁})`); with `χ₁(1) = a|W₁|` and `|L| = |H|·|W₁|`
(`index_H_eq_card_W1` + `index_mul_card`) it becomes `a·(R(z)−R(1)) = −c·|H|`, i.e.
`(R(z)−R(1))/|H| = −c/a`.  The (6.7)-congruence
`restrict_extension_Yset_charValue_cong_of_frobenius` says `(R(z)−R(1))/|H|` is an algebraic
integer;
so the rational `−c/a` is an algebraic integer, hence an integer (`isIntegral_rat_imp_int`), i.e.
`a ∣ c`.  (`c ∈ ℤ` because `R ∈ ZIrr L` and `χ₁` is irreducible, `mem_ZIrr_inner_int`.) -/
theorem dvd_inner_restrict_extension_Yset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cc : ℤ,
      ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁ = (cc : ℂ)
        ∧ (a : ℤ) ∣ cc := by
  classical
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  -- `c := ⟨R, χ₁⟩` is an integer (`R ∈ ZIrr L`, `χ₁` irreducible).
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : R ∈ ZIrr (↥L) := OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
  obtain ⟨cc, hcc⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = χ₁ from rfl] at hcc
  refine ⟨cc, hcc, ?_⟩
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hHne : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- pick `z ∈ Zc^#`.
  obtain ⟨⟨z, hz⟩, hzne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (hyp.centralCommutator_ne_bot hHnonab)
  have hz1 : z ≠ 1 := fun h => hzne (Subtype.ext h)
  -- value identity: `χ₁(1)·(R z − R 1) = −c·|L|`, with `χ₁(1) = a|W₁|`, `c = cc`, `|L| = |H||W₁|`.
  have hval := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz hz1
  rw [← hRdef, hcc, ha] at hval
  have hLcard : (Nat.card ↥L : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card hyp.W1 : ℂ) := by
    have h := Subgroup.index_mul_card H
    rw [hyp.index_H_eq_card_W1] at h
    have hc : ((Nat.card hyp.W1 * Nat.card ↥H : ℕ) : ℂ) = (Nat.card ↥L : ℂ) := by rw [h]
    push_cast at hc; linear_combination -hc
  rw [hLcard] at hval
  -- cancel `|W₁|`: `a·(R z − R 1) = −c·|H|`.
  have haD : (a : ℂ) * (R z - R 1) = -(cc : ℂ) * (Nat.card ↥H : ℂ) := by
    apply mul_left_cancel₀ hW1ne
    linear_combination hval
  -- the (6.7)-congruence: `(R z − R 1)/|H|` is an algebraic integer.
  have hcong := hyp.restrict_extension_Yset_charValue_cong_of_frobenius
    hF hHnonab hp hp3 hHp hη hz hz1
  rw [← hRdef, OddOrder.AlgInt.cong_def, Int.cast_natCast] at hcong
  -- `c/a = −((R z − R 1)/|H|)`, so `c/a` is an algebraic integer.
  have hccdiv : (cc : ℂ) / (a : ℂ) = -((R z - R 1) / (Nat.card ↥H : ℂ)) := by
    rw [← neg_div, div_eq_div_iff hane hHne]
    linear_combination haD
  have hintc : IsIntegral ℤ ((cc : ℂ) / (a : ℂ)) := by rw [hccdiv]; exact hcong.neg
  -- a rational algebraic integer is an integer ⟹ `a ∣ c`.
  have hqcast : (((cc : ℚ) / (a : ℚ) : ℚ) : ℂ) = (cc : ℂ) / (a : ℂ) := by push_cast; ring
  obtain ⟨n, hn⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int
    (q := (cc : ℚ) / (a : ℚ)) (by rw [hqcast]; exact hintc)
  rw [hqcast, div_eq_iff hane] at hn
  refine ⟨n, ?_⟩
  have : (cc : ℂ) = ((a : ℤ) * n : ℤ) := by rw [hn]; push_cast; ring
  exact_mod_cast this

end SibleyDadeHypothesis
end OddOrder.Peterfalvi.S08
