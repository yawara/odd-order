/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_SigmaIsometry
import OddOrder.Peterfalvi.S06_DadeIsometryCertain
import OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair

/-!
# Peterfalvi §6 (4.3.b): the certain-type characters

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§6, pp. 21-24.

Building on the §6 structural hypothesis (`S06.Hypothesis`) and its TI/Dade
infrastructure from `S06_DadeIsometryCertain` (the TI set `W − W₂`, the cyclic
`W = W₁ ⊔ W₂`, the §4 Dade isometry package `sdiffFullDadeIsometryData`), this
file produces the **certain-type character family** of (4.3.b).

The starting point is the abstract orthonormal difference-pair structure
`isometry_difference_pair_structure` (Peterfalvi §3 (1.4), formalized in
`IsometryDifferencePair`): inside each `W₂`-column the linear characters
`ω_{ij} = ω(omegaProdChar χ₁ χ₂)` of `W` give differences `ω_{ij} − ω_{0j}`
supported on the TI set `W − W₂`, on which `Ind_W^L` is an isometry; (1.4) turns
the image into a signed irreducible-difference family
`Ind(ω_{ij} − ω_{0j}) = δ_j • (μ_{ij} − μ_{0j})`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md`.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S05

variable {L : Type*} [Group L] [Fintype L]

/- 4.3 (b): the certain-type characters via the (1.4) difference-pair machinery -/

/-- Within a fixed `W₂`-column, the linear character `ω_{ij} = omegaProdChar χ₁ χ₂`
evaluated on `W₂` is independent of the `W₁`-index `χ₁`: on `W₂` the `W₁`-projection
`wFst` is trivial, so `omegaProdChar χ₁ χ₂ = χ₂ ∘ wSnd` there. -/
theorem omegaProdChar_apply_of_mem_W2 (hyp : TICyclicHypothesis L)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    {w : hyp.W} (hw : w ∈ hyp.W2.subgroupOf hyp.W) :
    hyp.omegaProdChar χ₁ χ₂ w = χ₂ (hyp.wSnd w) := by
  have h1 : hyp.omegaProdChar χ₁ χ₂ w = χ₁ (hyp.wFst w) * χ₂ (hyp.wSnd w) := rfl
  rw [h1, hyp.wFst_eq_one_of_mem_W2 hw, map_one, one_mul]

/-- The column difference `ω_{ij} − ω_{kj}` (same `W₂`-index `χ₂`) vanishes on `W₂`:
both characters restrict to `χ₂ ∘ wSnd` there (`omegaProdChar_apply_of_mem_W2`).
This is what makes the difference supported on the TI set `W − W₂` of (4.3.a). -/
theorem omega_omegaProdChar_sub_eq_zero_of_mem_W2 (hyp : TICyclicHypothesis L)
    (χ₁ χ₁' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    {w : hyp.W} (hw : w ∈ hyp.W2.subgroupOf hyp.W) :
    ((hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ) w
      - (hyp.omega (hyp.omegaProdChar χ₁' χ₂) : ClassFunction hyp.W ℂ) w) = 0 := by
  rw [TICyclicHypothesis.omega_apply, TICyclicHypothesis.omega_apply,
    omegaProdChar_apply_of_mem_W2 hyp χ₁ χ₂ hw,
    omegaProdChar_apply_of_mem_W2 hyp χ₁' χ₂ hw, sub_self]

namespace Hypothesis

variable (h : Hypothesis L)

/-- The column difference `ω_{ij} − ω_{kj}` (same `W₂`-index `χ₂`) packaged as an
element of `CF(W, W − W₂)`, the supported class-function space of the sdiff
TI-cyclic hypothesis (4.3.a).  Membership uses
`omega_omegaProdChar_sub_eq_zero_of_mem_W2`: the difference vanishes on `W₂`. -/
noncomputable def omegaColumnDiff
    (χ₁ χ₁' : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis :=
  ⟨(h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar χ₁ χ₂) :
        ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      - (h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar χ₁' χ₂) :
        ClassFunction h.sdiffTICyclicHypothesis.W ℂ),
   by
    rw [ClassFunction.mem_supportedSubmodule]
    intro w hw
    rw [ClassFunction.mem_support] at hw
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    refine ⟨w.2, ?_⟩
    intro hW2
    refine hw ?_
    rw [ClassFunction.sub_apply]
    exact omega_omegaProdChar_sub_eq_zero_of_mem_W2 h.sdiffTICyclicHypothesis χ₁ χ₁' χ₂
      ((Subgroup.mem_subgroupOf).mpr hW2)⟩

/-- `|W₁| ≠ 0` (it is `≥ 3` by `three_le_card_W1`), packaged as a `NeZero` instance so
that `(0 : Fin w₁)` — the distinguished index of the (1.4) machinery — is available. -/
theorem neZero_card_W1 : NeZero (Nat.card h.W1) :=
  ⟨by have h3 : 3 ≤ Nat.card h.W1 := h.sdiffTICyclicHypothesis.three_le_card_W1; omega⟩

/-- An arbitrary reindexing `Fin w₁ ≃ Ŵ₁` of the `W₁`-dual, from the cardinality match
(Pontryagin self-duality `card_charGroup_subgroupOf`: `|Ŵ₁| = |W₁| = w₁`). -/
noncomputable def w1BaseEquiv :
    Fin (Nat.card h.W1) ≃ ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
  haveI : Fintype ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  (Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card]
    exact h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      h.sdiffTICyclicHypothesis.W1_le_W)).symm

/-- The reindexing `Fin w₁ ≃ Ŵ₁` pinned at `0 ↦ 1` (trivial character).  Composing the
base equiv with the transposition swapping `0` and the preimage of `1` moves the trivial
character to the distinguished index `0`, as the (1.4) machinery (indexed by `Fin w₁`
with base index `0`) requires for the column family `i ↦ ω_{e i, j}`. -/
noncomputable def w1CharEquiv [NeZero (Nat.card h.W1)] :
    Fin (Nat.card h.W1) ≃ ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
  (Equiv.swap (0 : Fin (Nat.card h.W1)) (h.w1BaseEquiv.symm 1)).trans h.w1BaseEquiv

@[simp] theorem w1CharEquiv_zero [NeZero (Nat.card h.W1)] : h.w1CharEquiv 0 = 1 := by
  rw [w1CharEquiv, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

theorem w1CharEquiv_injective [NeZero (Nat.card h.W1)] :
    Function.Injective h.w1CharEquiv :=
  h.w1CharEquiv.injective

@[simp] theorem omegaColumnDiff_coe
    (χ₁ χ₁' : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ((h.omegaColumnDiff χ₁ χ₁' χ₂ : TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis) :
        ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar χ₁ χ₂) :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar χ₁' χ₂) :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ) :=
  rfl

/-- **The `W₂`-column character family** `i ↦ ω_{e i, j}` of (4.3.b): with `χ₂ = j`
a fixed nontrivial `W₂`-dual and `e = w1CharEquiv` (`e 0 = 1`), the linear characters
`ω_{ij} = ω(omegaProdChar (e i) χ₂)` of `W = W₁ ⊔ W₂`, indexed by `Fin w₁` with
distinguished index `0 ↦ ω_{0j}`.  This is the source family of the (1.4) machinery. -/
noncomputable def chiColumn [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    IrreducibleCharacter h.sdiffTICyclicHypothesis.W :=
  h.sdiffTICyclicHypothesis.omega
    (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂)

theorem chiColumn_zero [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    h.chiColumn χ₂ 0 =
      h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar 1 χ₂) :=
  congrArg
    (fun c => h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar c χ₂))
    h.w1CharEquiv_zero

/-- The column family is injective (`ω`, `omegaProdChar(·, χ₂)`, and `w1CharEquiv` are). -/
theorem chiColumn_injective [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    Function.Injective (h.chiColumn χ₂) := by
  intro i j hij
  exact h.w1CharEquiv_injective
    (h.sdiffTICyclicHypothesis.omegaProdChar_inj
      (h.sdiffTICyclicHypothesis.omega_injective hij)).1

/-- Every member of the column family has degree one (`ω` is linear). -/
@[simp] theorem chiColumn_apply_one [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) 1 = 1 :=
  h.sdiffTICyclicHypothesis.omega_apply_one _

section Recipe

variable [Invertible (Nat.card L : ℂ)]
  [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]

/-- Bridge instances: `Fintype`/`Invertible` for the order of `h.sdiffTICyclicHypothesis.W`,
definitionally `W₁ ⊔ W₂`.  Let `Ind_W^L`, `card_charGroup` and the §4 Dade package resolve
when the source group appears in its `sdiffTICyclicHypothesis.W` form. -/
instance instFintypeSdiffW : Fintype ↥h.sdiffTICyclicHypothesis.W :=
  ‹Fintype ↥(h.W1 ⊔ h.W2)›

instance instInvertibleCardSdiffW :
    Invertible (Nat.card ↥h.sdiffTICyclicHypothesis.W : ℂ) :=
  ‹Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)›

/-- `Ind_W^L` as a `ℤ`-linear map `CF(W) →ₗ[ℤ] CF(L)`, the map fed to the (1.4)
orthonormal difference-pair machinery (`isometry_difference_pair_structure`). -/
noncomputable def induceZ :
    ClassFunction h.sdiffTICyclicHypothesis.W ℂ →ₗ[ℤ] ClassFunction L ℂ :=
  (h.sdiffTICyclicHypothesis.induceLinear).restrictScalars ℤ

/-- The (1.4) image `τ(χ_i − χ_0)` of the column family is the induced difference
`Ind_W^L(ω_{ij} − ω_{0j})` — definitionally, since `induceZ` is `Ind_W^L` and
`isometryDifferenceImage` is the image of the source difference. -/
theorem isometryDifferenceImage_induceZ [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i =
      ClassFunction.induce h.sdiffTICyclicHypothesis.W
        ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) :=
  rfl

/-- The `W₂`-column image of the (1.4) map is the Dade isometry of the column
difference: `Ind_W^L(ω_{ij} − ω_{0j}) = τ_{W−W₂}(ω_{ij} − ω_{0j})`, because on the
TI set `W − W₂` the Dade map *is* `Ind_W^L` (`tau_eq_induce`).  This is the bridge
that transfers the isometry property of the §4 Dade package to `Ind_W^L`. -/
theorem isometryDifferenceImage_eq_dade [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i =
      h.sdiffFullDadeIsometryData.toDadeMap
        (h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂) := by
  rw [isometryDifferenceImage_induceZ]
  exact (h.sdiffTICyclicHypothesis.tau_eq_induce
    h.sdiffFullDadeIsometryData.toDadeIsometryData
    (h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂)).symm

/-- **Peterfalvi (4.3.b), per-column signed family** (mmd 04.6, the (4.5) consumer of
(1.4)).  For a fixed nontrivial `W₂`-dual `χ₂` (a "column" `j`), the (1.4) machinery
applied to `Ind_W^L` and the column family `ω_{ij}` yields a signed irreducible-difference
family `{μ_{ij}, δ_j}` of `L` with

  `Ind_W^L(ω_{ij} − ω_{0j}) = δ_j • (μ_{ij} − μ_{0j})`,  `δ_j = ±1`,  `μ_{·j}` injective.

The three (1.4) hypotheses are discharged from the §6 infrastructure: virtual-character
images by `induce_mem_ZIrr`, vanishing at `1` by `induce_apply_one` (the source
difference has degree `0`), and the isometry on the differences by the §4 Dade package
on the TI set `W − W₂` (`sdiffFullDadeIsometryData`, via `isometryDifferenceImage_eq_dade`
and `full_inner_eq`).  Distinctness within the column is the `injective` field. -/
theorem exists_columnSignedFamily [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ∃ data : SignedIrreducibleDifferenceFamily L (Nat.card h.W1),
      ∀ i, isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i = data.signedDifference i := by
  classical
  have hn : 2 ≤ Nat.card h.W1 := by
    have h3 : 3 ≤ Nat.card h.W1 := h.sdiffTICyclicHypothesis.three_le_card_W1
    omega
  -- Same degree: every member of the column family has degree one.
  have hdeg : ∀ i, ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) :
      h.sdiffTICyclicHypothesis.W → ℂ) 1 =
      ((h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) :
      h.sdiffTICyclicHypothesis.W → ℂ) 1 := by
    intro i
    rw [h.chiColumn_apply_one χ₂ i, h.chiColumn_apply_one χ₂ 0]
  -- (1.4.virtual): each image lies in `ℤ[Irr L]` (`Ind` of a difference of irreducibles).
  have h_image_virtual :
      IsometryDifferenceImagesAreVirtual h.induceZ (h.chiColumn χ₂) := by
    intro i
    rw [isometryDifferenceImage_induceZ]
    exact ClassFunction.induce_mem_ZIrr _
      (Submodule.sub_mem _ (h.chiColumn χ₂ i).mem_ZIrr (h.chiColumn χ₂ 0).mem_ZIrr)
  -- (1.4.degree): each image vanishes at `1` (`Ind` of a degree-0 difference).
  have h_image_degree_zero :
      IsometryDifferenceImagesVanishAtOne h.induceZ (h.chiColumn χ₂) := by
    intro i
    rw [isometryDifferenceImage_induceZ, ClassFunction.induce_apply_one,
      ClassFunction.sub_apply, h.chiColumn_apply_one χ₂ i, h.chiColumn_apply_one χ₂ 0,
      sub_self, mul_zero]
  -- (1.4.isometry): inner products preserved on the differences (the §4 Dade isometry).
  have h_isom : ∀ i j,
      ClassFunction.inner (isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i)
        (isometryDifferenceImage h.induceZ (h.chiColumn χ₂) j) =
      ClassFunction.inner (irreducibleCharacterDifference (h.chiColumn χ₂) i)
        (irreducibleCharacterDifference (h.chiColumn χ₂) j) := by
    intro i j
    rw [h.isometryDifferenceImage_eq_dade χ₂ i, h.isometryDifferenceImage_eq_dade χ₂ j]
    exact (TICyclicHypothesis.full_inner_eq
      (⟨h.sdiffFullDadeIsometryData⟩ : TICyclicHypothesis.FullDadeApplication
        h.sdiffTICyclicHypothesis)
      (h.omegaColumnDiff (h.w1CharEquiv i) (h.w1CharEquiv 0) χ₂)
      (h.omegaColumnDiff (h.w1CharEquiv j) (h.w1CharEquiv 0) χ₂))
  exact isometry_difference_pair_structure (G := L)
    (H := h.sdiffTICyclicHypothesis.W) hn (h.chiColumn χ₂) (h.chiColumn_injective χ₂)
    hdeg h.induceZ h_image_virtual h_image_degree_zero h_isom

end Recipe

end Hypothesis

end OddOrder.Peterfalvi.S06
