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

/-- Characters in different `W₂`-columns are distinct: `ω_{aj} ≠ ω_{bj'}` when `j ≠ j'`
(`omegaProdChar` is injective in the index pair, `omegaProdChar_inj`). -/
theorem omegaProdChar_ne_of_ne_right (hyp : TICyclicHypothesis L)
    {χ₂ χ₂' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (χ₁ χ₁' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) :
    hyp.omegaProdChar χ₁ χ₂ ≠ hyp.omegaProdChar χ₁' χ₂' :=
  hyp.omegaProdChar_ne (fun h => hne h.2)

/-- **Cross-column orthogonality of `ω`-differences**: for `χ₂ ≠ χ₂'`, the difference
`ω_{aj} − ω_{a₀j}` is orthogonal to `ω_{bj'} − ω_{b₀j'}`.  All four `ω`-terms have
distinct index pairs (the `W₂`-components differ), so each cross inner product vanishes
(`omega_inner_ne`).  This is the source-side input feeding (4.1) for the cross-column
distinctness of the certain-type characters. -/
theorem omega_diff_cross_inner_eq_zero (hyp : TICyclicHypothesis L)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    {χ₂ χ₂' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (a a₀ b b₀ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction.inner
      ((hyp.omega (hyp.omegaProdChar a χ₂) : ClassFunction hyp.W ℂ)
        - (hyp.omega (hyp.omegaProdChar a₀ χ₂) : ClassFunction hyp.W ℂ))
      ((hyp.omega (hyp.omegaProdChar b χ₂') : ClassFunction hyp.W ℂ)
        - (hyp.omega (hyp.omegaProdChar b₀ χ₂') : ClassFunction hyp.W ℂ)) = 0 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right,
    hyp.omega_inner_ne (omegaProdChar_ne_of_ne_right hyp hne a b),
    hyp.omega_inner_ne (omegaProdChar_ne_of_ne_right hyp hne a b₀),
    hyp.omega_inner_ne (omegaProdChar_ne_of_ne_right hyp hne a₀ b),
    hyp.omega_inner_ne (omegaProdChar_ne_of_ne_right hyp hne a₀ b₀)]
  ring

/-- Biorthogonality (diagonal) for the `CF(W, W − W₂)` basis: `⟨ω_{ij} − ω_{0j}, ω_{ij}⟩ = 1`
(for `χ₁ ≠ 1`).  Only the `ω_{ij}` term survives; `ω_{0j} ⊥ ω_{ij}` since `χ₁ ≠ 1`. -/
theorem omegaColumnDiff_inner_omega_self (hyp : TICyclicHypothesis L)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} (hχ₁ : χ₁ ≠ 1)
    (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction.inner
      ((hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ)
        - (hyp.omega (hyp.omegaProdChar 1 χ₂) : ClassFunction hyp.W ℂ))
      (hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ) = 1 := by
  rw [ClassFunction.inner_sub_left, hyp.omega_inner_self,
    hyp.omega_inner_ne (hyp.omegaProdChar_ne (fun h => hχ₁ h.1.symm))]
  ring

/-- Biorthogonality (off-diagonal) for the `CF(W, W − W₂)` basis: `⟨ω_{i'j'} − ω_{0j'}, ω_{ij}⟩ = 0`
for `(i', j') ≠ (i, j)` (`χ₁ ≠ 1`).  Both `ω`-terms are distinct from `ω_{ij}`. -/
theorem omegaColumnDiff_inner_omega_ne (hyp : TICyclicHypothesis L)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    {χ₁' χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} (hχ₁ : χ₁ ≠ 1)
    {χ₂' χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hne : ¬ (χ₁' = χ₁ ∧ χ₂' = χ₂)) :
    ClassFunction.inner
      ((hyp.omega (hyp.omegaProdChar χ₁' χ₂') : ClassFunction hyp.W ℂ)
        - (hyp.omega (hyp.omegaProdChar 1 χ₂') : ClassFunction hyp.W ℂ))
      (hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ) = 0 := by
  rw [ClassFunction.inner_sub_left,
    hyp.omega_inner_ne (hyp.omegaProdChar_ne hne),
    hyp.omega_inner_ne (hyp.omegaProdChar_ne (fun h => hχ₁ h.1.symm))]
  ring

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

/-- `1 < w₁` (it is `≥ 3`), giving a nonzero index `⟨1, _⟩ : Fin w₁` for the (4.1)
witnesses in the cross-column distinctness argument. -/
theorem one_lt_card_W1 : 1 < Nat.card h.W1 := by
  have h3 : 3 ≤ Nat.card h.W1 := h.sdiffTICyclicHypothesis.three_le_card_W1
  omega

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

/-- A choice of the (1.4) signed irreducible-difference family for the `W₂`-column `χ₂`
(`exists_columnSignedFamily`): the data `{μ_{ij}, δ_j}` of (4.3.b). -/
noncomputable def columnFamily [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    SignedIrreducibleDifferenceFamily L (Nat.card h.W1) :=
  (h.exists_columnSignedFamily χ₂).choose

theorem columnFamily_spec [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i =
      (h.columnFamily χ₂).signedDifference i :=
  (h.exists_columnSignedFamily χ₂).choose_spec i

/-- **Cross-column orthogonality of the (1.4) images** (4.3.b proof step): for `χ₂ ≠ χ₂'`,
`(Ind_W^L(ω_{ij} − ω_{0j}), Ind_W^L(ω_{i'j'} − ω_{0j'})) = 0`.  The §4 Dade map on
`CF(W, W − W₂)` is an isometry, so this equals the source cross inner product
`omega_diff_cross_inner_eq_zero`, which vanishes because the two columns use distinct
`W₂`-duals. -/
theorem ind_cross_inner_eq_zero [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (i i' : Fin (Nat.card h.W1)) :
    ClassFunction.inner (isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i)
      (isometryDifferenceImage h.induceZ (h.chiColumn χ₂') i') = 0 := by
  rw [h.isometryDifferenceImage_eq_dade χ₂ i, h.isometryDifferenceImage_eq_dade χ₂' i',
    h.sdiffFullDadeIsometryData.inner_eq, omegaColumnDiff_coe, omegaColumnDiff_coe]
  exact omega_diff_cross_inner_eq_zero h.sdiffTICyclicHypothesis hne _ _ _ _

/-- The (1.4) image of the column family vanishes at `1` (the source difference
`ω_{ij} − ω_{0j}` has degree `0`, and `Ind` preserves that). -/
theorem image_apply_one_eq_zero [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    isometryDifferenceImage h.induceZ (h.chiColumn χ₂) i (1 : L) = 0 := by
  rw [isometryDifferenceImage_induceZ, ClassFunction.induce_apply_one,
    ClassFunction.sub_apply, h.chiColumn_apply_one χ₂ i, h.chiColumn_apply_one χ₂ 0,
    sub_self, mul_zero]

/-- The signed differences `μ_{ij} − μ_{0j}` of the column family vanish at `1`
(same degree within a column), since the (1.4) image does and `δ_j ≠ 0`. -/
theorem columnFamily_difference_apply_one [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (h.columnFamily χ₂).difference i (1 : L) = 0 := by
  have h0 : (h.columnFamily χ₂).signedDifference i (1 : L) = 0 := by
    rw [← h.columnFamily_spec χ₂ i]; exact h.image_apply_one_eq_zero χ₂ i
  rw [SignedIrreducibleDifferenceFamily.signedDifference_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul] at h0
  have hs : ((h.columnFamily χ₂).sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂).sign_eq with he | he <;> rw [he] <;> norm_num
  exact (mul_eq_zero.mp h0).resolve_left hs

/-- **Cross-column orthogonality of the `μ`-differences** (4.3.b proof step): for `χ₂ ≠ χ₂'`,
`(μ_{ij} − μ_{0j}, μ_{i'j'} − μ_{0j'}) = 0`.  From the (1.4)-image cross orthogonality
(`ind_cross_inner_eq_zero`) after removing both signs `δ_j, δ_{j'} = ±1`. -/
theorem columnFamily_difference_cross_inner_eq_zero [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (i i' : Fin (Nat.card h.W1)) :
    ClassFunction.inner ((h.columnFamily χ₂).difference i)
      ((h.columnFamily χ₂').difference i') = 0 := by
  have h0 := h.ind_cross_inner_eq_zero hne i i'
  rw [h.columnFamily_spec χ₂ i, h.columnFamily_spec χ₂' i',
    SignedIrreducibleDifferenceFamily.signedDifference_apply,
    SignedIrreducibleDifferenceFamily.signedDifference_apply,
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign ((h.columnFamily χ₂).difference i),
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂').sign ((h.columnFamily χ₂').difference i'),
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    star_intCast] at h0
  have hs : ((h.columnFamily χ₂).sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂).sign_eq with he | he <;> rw [he] <;> norm_num
  have hs' : ((h.columnFamily χ₂').sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂').sign_eq with he | he <;> rw [he] <;> norm_num
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hs)).resolve_left hs'

/-- **The four cross inner products vanish** (4.3.b proof step, via (4.1)).  For `χ₂ ≠ χ₂'`
and nonzero `k, k'`, the signed differences `μ_{kj} − μ_{0j}` and `μ_{k'j'} − μ_{0j'}` are
orthogonal (`columnFamily_difference_cross_inner_eq_zero`) and vanish at `1`
(`columnFamily_difference_apply_one`), so Peterfalvi (4.1) forces all four cross inner
products `(μ_{kj}, μ_{k'j'})`, `(μ_{kj}, μ_{0j'})`, `(μ_{0j}, μ_{k'j'})`, `(μ_{0j}, μ_{0j'})`
to vanish. -/
theorem columnFamily_cross_products_zero [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    {k k' : Fin (Nat.card h.W1)} (hk : k ≠ 0) (hk' : k' ≠ 0) :
    ClassFunction.inner ((h.columnFamily χ₂).mu k : ClassFunction L ℂ)
        ((h.columnFamily χ₂').mu k' : ClassFunction L ℂ) = 0 ∧
      ClassFunction.inner ((h.columnFamily χ₂).mu k : ClassFunction L ℂ)
        ((h.columnFamily χ₂').mu 0 : ClassFunction L ℂ) = 0 ∧
      ClassFunction.inner ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)
        ((h.columnFamily χ₂').mu k' : ClassFunction L ℂ) = 0 ∧
      ClassFunction.inner ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ)
        ((h.columnFamily χ₂').mu 0 : ClassFunction L ℂ) = 0 := by
  have hself : ∀ (d : SignedIrreducibleDifferenceFamily L (Nat.card h.W1)) (m : Fin (Nat.card h.W1)),
      ClassFunction.inner (d.mu m : ClassFunction L ℂ) (d.mu m : ClassFunction L ℂ) = 1 := by
    intro d m; rw [irreducibleCharacter_inner, if_pos rfl]
  have horth : ∀ (d : SignedIrreducibleDifferenceFamily L (Nat.card h.W1))
      {m n : Fin (Nat.card h.W1)}, m ≠ n →
      ClassFunction.inner (d.mu m : ClassFunction L ℂ) (d.mu n : ClassFunction L ℂ) = 0 := by
    intro d m n hmn
    rw [irreducibleCharacter_inner, if_neg (fun heq => hmn (d.injective heq))]
  refine pairwise_inner_eq_zero_of_orthogonal_signedDifference (Γ := L)
    (u := 1) (v := 1) one_ne_zero one_ne_zero
    ((h.columnFamily χ₂).mu k).mem_ZIrr (hself _ k)
    ((h.columnFamily χ₂).mu 0).mem_ZIrr (hself _ 0)
    ((h.columnFamily χ₂').mu k').mem_ZIrr (hself _ k')
    ((h.columnFamily χ₂').mu 0).mem_ZIrr (hself _ 0)
    (horth _ hk) (horth _ hk') ?_ ?_ ?_
  · -- (μ_{kj} − μ_{0j}, 1•μ_{k'j'} − 1•μ_{0j'}) = 0
    simp only [Complex.ofReal_one, one_smul]
    exact h.columnFamily_difference_cross_inner_eq_zero hne k k'
  · -- (μ_{kj} − μ_{0j})(1) = 0
    exact h.columnFamily_difference_apply_one χ₂ k
  · -- (1•μ_{k'j'} − 1•μ_{0j'})(1) = 0
    simp only [Complex.ofReal_one, one_smul]
    exact h.columnFamily_difference_apply_one χ₂' k'

/-- **Peterfalvi (4.3.b), cross-column distinctness**: certain-type characters from
different `W₂`-columns are distinct — `μ_{ij} ≠ μ_{i'j'}` for `χ₂ ≠ χ₂'` and any `i, i'`.
By `columnFamily_cross_products_zero` (the four cross inner products vanish, via (4.1)),
`(μ_{ij}, μ_{i'j'}) = 0`; orthogonal irreducibles are distinct.  A case split on `i, i' = 0`
selects which of the four products to read (the (4.1) witnesses use the nonzero index `1`). -/
theorem columnFamily_mu_ne [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (i i' : Fin (Nat.card h.W1)) :
    (h.columnFamily χ₂).mu i ≠ (h.columnFamily χ₂').mu i' := by
  have hz : (⟨1, h.one_lt_card_W1⟩ : Fin (Nat.card h.W1)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  have hinner : ClassFunction.inner ((h.columnFamily χ₂).mu i : ClassFunction L ℂ)
      ((h.columnFamily χ₂').mu i' : ClassFunction L ℂ) = 0 := by
    rcases eq_or_ne i 0 with hi | hi <;> rcases eq_or_ne i' 0 with hi' | hi'
    · subst hi; subst hi'
      exact (h.columnFamily_cross_products_zero hne hz hz).2.2.2
    · subst hi
      exact (h.columnFamily_cross_products_zero hne hz hi').2.2.1
    · subst hi'
      exact (h.columnFamily_cross_products_zero hne hi hz).2.1
    · exact (h.columnFamily_cross_products_zero hne hi hi').1
  intro heq
  rw [heq, irreducibleCharacter_inner, if_pos rfl] at hinner
  exact one_ne_zero hinner

/-- **Linear independence of the `CF(W, W − W₂)` family** `ω_{ij} − ω_{0j}` (`i ≠ 0`, all `j`):
the biorthogonal system `⟨ω_{i'j'} − ω_{0j'}, ω_{ij}⟩ = δ` (`omegaColumnDiff_inner_omega_self`/`_ne`)
witnesses linear independence.  With the matching count `(w₁−1)·w₂ = |W − W₂| = dim CF(W, W − W₂)`
this gives the basis of (4.3.b) (the `ω_{ij} − ω_{0j}` comprise a basis of `CF(W, W − W₂)`). -/
theorem omegaColumnDiff_linearIndependent :
    LinearIndependent ℂ
      (fun p : {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} ×
          ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) =>
        h.omegaColumnDiff p.1.1 1 p.2) := by
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun p => (innerDual (h.sdiffTICyclicHypothesis.omega
        (h.sdiffTICyclicHypothesis.omegaProdChar p.1.1 p.2))).comp (Submodule.subtype _))
    (fun p q hpq => ?_) (fun p => ?_)
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, innerDual_apply, omegaColumnDiff_coe]
    exact omegaColumnDiff_inner_omega_ne h.sdiffTICyclicHypothesis p.1.2
      (fun heq => hpq (Prod.ext (Subtype.ext heq.1.symm) heq.2.symm))
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, innerDual_apply, omegaColumnDiff_coe]
    exact omegaColumnDiff_inner_omega_self h.sdiffTICyclicHypothesis p.1.2 p.2

/-- **Peterfalvi (4.3.b), all certain-type characters distinct**: the global family
`(χ₂, i) ↦ μ_{ij}` is injective.  Within a column by the (1.4) `injective` field;
across columns by `columnFamily_mu_ne`. -/
theorem columnFamily_mu_injective [NeZero (Nat.card h.W1)] :
    Function.Injective
      (fun p : ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) × Fin (Nat.card h.W1) =>
        (h.columnFamily p.1).mu p.2) := by
  rintro ⟨χ₂, i⟩ ⟨χ₂', i'⟩ heq
  by_cases hχ : χ₂ = χ₂'
  · subst hχ
    obtain rfl : i = i' := (h.columnFamily χ₂).injective heq
    rfl
  · exact absurd heq (h.columnFamily_mu_ne hχ i i')

/-- The count `|W − W₂| = (w₁ − 1)·w₂`: the support set of the sdiff hypothesis is the
complement of `W₂` in `W`, so `|W| − |W₂| = w₁w₂ − w₂`. -/
theorem card_supportInSubgroup_sdiff :
    Nat.card ↥(OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
        h.sdiffTICyclicHypothesis.W) = (Nat.card h.W1 - 1) * Nat.card h.W2 := by
  classical
  haveI : Finite L := Finite.of_fintype L
  haveI : Fintype ↥h.sdiffTICyclicHypothesis.W := Fintype.ofFinite _
  haveI : Fintype ↥(h.W2.subgroupOf h.sdiffTICyclicHypothesis.W) := Fintype.ofFinite _
  have hmemiff : ∀ x : ↥h.sdiffTICyclicHypothesis.W,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
        h.sdiffTICyclicHypothesis.W ↔ x ∉ h.W2.subgroupOf h.sdiffTICyclicHypothesis.W := by
    intro x
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, Subgroup.mem_subgroupOf]
    exact ⟨fun hxV => hxV.2, fun hxW2 => ⟨SetLike.coe_mem x, hxW2⟩⟩
  have hcompl := Nat.card_congr (Equiv.subtypeEquivRight hmemiff)
  have hW : Nat.card ↥h.sdiffTICyclicHypothesis.W = Nat.card h.W1 * Nat.card h.W2 :=
    h.card_sup_eq_mul
  have hW2 : Nat.card ↥(h.W2.subgroupOf h.sdiffTICyclicHypothesis.W) = Nat.card h.W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.sdiffTICyclicHypothesis.W2_le_W).toEquiv
  have hsub : Nat.card {x : ↥h.sdiffTICyclicHypothesis.W //
        x ∉ h.W2.subgroupOf h.sdiffTICyclicHypothesis.W}
      = Nat.card ↥h.sdiffTICyclicHypothesis.W
        - Nat.card ↥(h.W2.subgroupOf h.sdiffTICyclicHypothesis.W) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl]
  rw [hcompl, hsub, hW, hW2, Nat.sub_one_mul]

/-- `dim_ℂ CF(W, W − W₂) = (w₁ − 1)·w₂`, the dimension behind the `ω_{ij} − ω_{0j}` basis. -/
theorem finrank_sdiffSupported :
    Module.finrank ℂ (TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis)
      = (Nat.card h.W1 - 1) * Nat.card h.W2 := by
  haveI : Finite L := Finite.of_fintype L
  haveI : Fintype ↥h.sdiffTICyclicHypothesis.W := Fintype.ofFinite _
  haveI : IsMulCommutative ↥h.sdiffTICyclicHypothesis.W :=
    h.sdiffTICyclicHypothesis.isMulCommutative_W
  show Module.finrank ℂ ↥(ClassFunction.supportedSubmodule
      (OddOrder.Peterfalvi.S04.supportInSubgroup h.sdiffTICyclicHypothesis.V
        h.sdiffTICyclicHypothesis.W)) = _
  rw [finrank_supportedSubmodule_eq_card, h.card_supportInSubgroup_sdiff]

/-- **Peterfalvi (4.3.b) basis**: the `ω_{ij} − ω_{0j}` (`i ≠ 0`, all `j`) form a basis of
`CF(W, W − W₂)` — linearly independent (`omegaColumnDiff_linearIndependent`) with the matching
count `(w₁−1)·w₂ = dim` (`finrank_sdiffSupported`). -/
noncomputable def omegaColumnDiffBasis :
    Module.Basis ({χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} ×
        ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) ℂ
      (TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis) := by
  classical
  haveI : Finite L := Finite.of_fintype L
  haveI : Fintype ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} := Fintype.ofFinite _
  haveI : Nonempty ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := ⟨1⟩
  haveI : Nonempty {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1} :=
    h.sdiffTICyclicHypothesis.nonempty_charNeOne
      h.sdiffTICyclicHypothesis.W1_le_W h.sdiffTICyclicHypothesis.W1_nontrivial
  refine basisOfLinearIndependentOfCardEqFinrank h.omegaColumnDiff_linearIndependent ?_
  rw [h.finrank_sdiffSupported, Fintype.card_prod]
  have hc1 : Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = Nat.card h.W1 :=
    h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf h.sdiffTICyclicHypothesis.W1_le_W
  have hc2 : Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = Nat.card h.W2 :=
    h.sdiffTICyclicHypothesis.card_charGroup_subgroupOf h.sdiffTICyclicHypothesis.W2_le_W
  have e1 : Fintype.card {χ₁ : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₁ ≠ 1}
      = Nat.card h.W1 - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hc1]
  have e2 : Fintype.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) = Nat.card h.W2 := by
    rw [← Nat.card_eq_fintype_card, hc2]
  rw [e1, e2]

/-- `ω_{kl} = chiColumn l (e⁻¹ k)`: the basis index `k` (a `W₁`-dual) is `e (e⁻¹ k)` of
the column family. -/
theorem chiColumn_w1CharEquiv_symm [NeZero (Nat.card h.W1)]
    (l : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (k : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    h.chiColumn l (h.w1CharEquiv.symm k)
      = h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar k l) := by
  rw [chiColumn, Equiv.apply_symm_apply]

/-- **The (1.4) image of a basis vector** `ω_{kl} − ω_{0l}` is the column-`l` signed
difference at index `e⁻¹ k`: `Ind_W^L(ω_{kl} − ω_{0l}) = (columnFamily l).signedDifference (e⁻¹ k)`. -/
theorem induce_omegaColumnDiff_eq [NeZero (Nat.card h.W1)]
    (l : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (k : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ClassFunction.induce h.sdiffTICyclicHypothesis.W
        (h.omegaColumnDiff k 1 l : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.columnFamily l).signedDifference (h.w1CharEquiv.symm k) := by
  have hval : (h.omegaColumnDiff k 1 l : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      = (h.chiColumn l (h.w1CharEquiv.symm k) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn l 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) := by
    rw [h.chiColumn_w1CharEquiv_symm l k, h.chiColumn_zero l]
    exact h.omegaColumnDiff_coe k 1 l
  rw [hval, ← h.isometryDifferenceImage_induceZ l (h.w1CharEquiv.symm k),
    h.columnFamily_spec l (h.w1CharEquiv.symm k)]

/-- The "certain-type difference" `g = Res_W(δ_{χ₂}·μ_{ij}) − ω_{ij}` on `↥W`, whose
vanishing on `W − W₂` (the (1.3) value-match) gives the σ-identification. -/
noncomputable def certainTypeRestrictDiff [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction h.sdiffTICyclicHypothesis.W ℂ :=
  ClassFunction.restrict h.sdiffTICyclicHypothesis.W
      ((h.columnFamily χ₂).sign • ((h.columnFamily χ₂).mu i : ClassFunction L ℂ))
    - (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)

/-- **Step 4, `g ⊥ basis`.**  The certain-type difference `g = Res_W(δ_j·μ_{ij}) − ω_{ij}` is
orthogonal to every basis vector `ω_{kl} − ω_{0l}` of `CF(W, W − W₂)`.

Frobenius reciprocity (`inner_induce_eq_inner_restrict`) turns the `Res`-part into
`⟨Ind_W^L(ω_{kl} − ω_{0l}), δ_j μ_{ij}⟩`, and the (1.4) image
`Ind_W^L(ω_{kl} − ω_{0l}) = δ_l·(μ_{e⁻¹k,l} − μ_{0,l})` (`induce_omegaColumnDiff_eq`) reduces
both pairings to character orthonormality.  On the diagonal `l = χ₂` the within-column
orthonormality `(μ_{·l}, μ_{·χ₂})` matches the source pairing `(ω_{·l}, ω_{·χ₂})` once the
sign `δ_l² = 1` is removed (`k = e i ↔ e⁻¹k = i`, `1 = e i ↔ 0 = i`); off the diagonal both
sides vanish because distinct `W₂`-columns are orthogonal (`columnFamily_mu_ne` / the source
`ω`-orthogonality). -/
theorem certainTypeRestrictDiff_inner_basis [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (l : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (k : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ClassFunction.inner
      ((h.omegaColumnDiff k 1 l : TICyclicHypothesis.SupportedOnV ℂ h.sdiffTICyclicHypothesis) :
          ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      (h.certainTypeRestrictDiff χ₂ i) = 0 := by
  classical
  rw [certainTypeRestrictDiff, ClassFunction.inner_sub_right, sub_eq_zero,
    ← ClassFunction.inner_induce_eq_inner_restrict, h.induce_omegaColumnDiff_eq l k,
    SignedIrreducibleDifferenceFamily.signedDifference_apply,
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily l).sign
      ((h.columnFamily l).difference (h.w1CharEquiv.symm k)),
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign
      ((h.columnFamily χ₂).mu i : ClassFunction L ℂ),
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, star_intCast,
    SignedIrreducibleDifferenceFamily.difference_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply,
    SignedIrreducibleDifferenceFamily.classFunction_apply,
    ClassFunction.inner_sub_left, omegaColumnDiff_coe, chiColumn, ClassFunction.inner_sub_left,
    irreducibleCharacter_inner, irreducibleCharacter_inner,
    irreducibleCharacter_inner, irreducibleCharacter_inner]
  -- LHS = δ_l·(δ_χ₂·([μ_{e⁻¹k,l}=μ_{iχ₂}] − [μ_{0,l}=μ_{iχ₂}]));
  -- RHS = [ω_{kl}=ω_{e i,χ₂}] − [ω_{0l}=ω_{e i,χ₂}].
  by_cases hl : l = χ₂
  · subst hl
    -- the within-column index equalities
    have hcol : ∀ (a : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
        (h.sdiffTICyclicHypothesis.omegaProdChar a l
          = h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) l) ↔ a = h.w1CharEquiv i :=
      fun a => ⟨fun he => (h.sdiffTICyclicHypothesis.omegaProdChar_inj he).1,
        fun he => by rw [he]⟩
    have hs1 : h.w1CharEquiv.symm 1 = 0 := by rw [Equiv.symm_apply_eq, h.w1CharEquiv_zero]
    simp only [(h.columnFamily l).injective.eq_iff,
      h.sdiffTICyclicHypothesis.omega_injective.eq_iff, hcol, ← Equiv.symm_apply_eq, hs1]
    have hsign2 : ((h.columnFamily l).sign : ℂ) * ((h.columnFamily l).sign : ℂ) = 1 := by
      rcases (h.columnFamily l).sign_eq with hs | hs <;> rw [hs] <;> norm_num
    rw [← mul_assoc, hsign2, one_mul]
  · -- distinct columns: all four pairings vanish
    rw [if_neg (h.columnFamily_mu_ne hl (h.w1CharEquiv.symm k) i),
      if_neg (h.columnFamily_mu_ne hl 0 i),
      if_neg (fun he => (h.sdiffTICyclicHypothesis.omegaProdChar_ne (fun hand => hl hand.2))
        (h.sdiffTICyclicHypothesis.omega_injective he)),
      if_neg (fun he => (h.sdiffTICyclicHypothesis.omegaProdChar_ne (fun hand => hl hand.2))
        (h.sdiffTICyclicHypothesis.omega_injective he))]
    ring

end Recipe

end Hypothesis

end OddOrder.Peterfalvi.S06
