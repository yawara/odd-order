/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S06_CertainTypeIsometry

/-!
# Peterfalvi (4.9)(a): conjugation of the certain-type characters

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000),
§4, p. 24, statement (4.9)(a).

The (4.9)(a) argument relates the **complex conjugate** of a certain-type column character to
another
column: `μ̄_j = μ_{j'}` with `j' ≠ j` (because `j ≠ 0` and `|W|` is odd).  The bridge is the σ-side
Galois equivariance (3.9): conjugation is the cyclotomic automorphism `z ↦ z̄`, so `(ω_{ij}^σ)̄ =
(ω̄_{ij})^σ`, and `ω̄_{ij}` is again a grid character `ω_{i'j'}` (the conjugate of a linear character
is its inverse).

This file develops the conjugation foundation:

* `galoisMap_conj_omega`: the complex conjugate of a linear character `ω(χ)` is `ω(χ⁻¹)` — the
  Galois action by complex conjugation on `ω(χ)` inverts the underlying character (its values are
  roots of unity, where `z̄ = z⁻¹`);
* `certainTypeOmegaSigma_conj`: the complex conjugate of the σ-image `ω_{ij}^σ` is the σ-image of
  the inverse grid character `ω((P_{ij})⁻¹)`, via the (3.9) commutation `sigma_mapRingEquiv_comm`.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md` ("session 35").
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G} [Fintype ↥L]
variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

omit [Invertible (Nat.card G : ℂ)] in
/-- **Complex conjugation inverts a linear character.**  For a linear character `χ : W →* ℂˣ` of the
finite group `W`, the Galois action of complex conjugation `Complex.conjAe` on `ω(χ)` is `ω(χ⁻¹)`.
Pointwise: `(ω(χ))(w) = χ(w)` is a root of unity (`χ(w)^{|W|} = 1`), so `‖χ(w)‖ = 1` and
`χ(w)̄ = χ(w)⁻¹ = (χ⁻¹)(w)`. -/
theorem galoisMap_conj_omega (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Finite hyp.W] (χ : hyp.W →* ℂˣ) :
    IrreducibleCharacter.galoisMap Complex.conjAe.toRingEquiv (hyp.omega χ) = hyp.omega χ⁻¹ := by
  haveI : Fintype hyp.W := Fintype.ofFinite hyp.W
  apply IrreducibleCharacter.ext
  apply ClassFunction.ext
  intro w
  rw [IrreducibleCharacter.galoisMap_apply_apply, hyp.omega_apply, hyp.omega_apply,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hnorm : ‖(χ w : ℂ)‖ = 1 := by
    have hp : ((χ w : ℂ)) ^ (Fintype.card hyp.W) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one hp Fintype.card_ne_zero
  rw [Complex.inv_eq_conj hnorm]
  rfl

/-- **Conjugation of a certain-type σ-image.**  The complex conjugate of `ω_{ij}^σ` is the σ-image of
the inverse grid character `(P_{ij})⁻¹` (`P_{ij} = omegaProdCharTic h χ₂ i`).  Combines the (3.9)
Galois commutation `sigma_mapRingEquiv_comm` (σ intertwines the cyclotomic Galois action) with
`galoisMap_conj_omega` (conjugation inverts the linear character).  This is the (3.9) ingredient of
(4.9)(a): the conjugate of a σ-image stays in the σ-image grid, at the conjugate index. -/
theorem certainTypeOmegaSigma_conj (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (certainTypeOmegaSigma h χ₂ i)
      = (ticVdiff h).sigma rfl (ticVdiffFullDadeApplication h)
          ((ticVdiff h).omega (omegaProdCharTic h χ₂ i)⁻¹) := by
  rw [certainTypeOmegaSigma,
    (ticVdiff h).sigma_mapRingEquiv_comm rfl (ticVdiffFullDadeApplication h),
    galoisMap_conj_omega]

/-! ### The grid-index conjugation map

The inverse grid character `(P_{ij})⁻¹` is again a grid character: since `ω(χ₁, χ₂) = χ₁∘wFst ·
χ₂∘wSnd` and the codomain `ℂˣ` is abelian, inversion acts coordinatewise, `(ω(χ₁,χ₂))⁻¹ =
ω(χ₁⁻¹, χ₂⁻¹)`.  At the certain-type level this sends column `χ₂` to `χ₂⁻¹` and row `i` to the
row `i'` with `w1CharEquiv i' = (w1CharEquiv i)⁻¹`.  Combined with `certainTypeOmegaSigma_conj`,
this yields `(ω_{ij}^σ)̄ = ω_{i'j'}^σ`: the conjugate of a σ-image is the σ-image at the conjugate
grid index (`j' = χ₂⁻¹` independent of `i`). -/

omit [Invertible (Nat.card G : ℂ)] in
/-- **`omegaProdChar` inverts coordinatewise** (`ℂˣ` abelian): `ω(χ₁, χ₂)⁻¹ = ω(χ₁⁻¹, χ₂⁻¹)`. -/
theorem omegaProdChar_inv (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.omegaProdChar χ₁ χ₂)⁻¹ = hyp.omegaProdChar χ₁⁻¹ χ₂⁻¹ := by
  ext w
  simp only [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv]

/-- The **row-inversion index** `i'`: the unique row with `w1CharEquiv i' = (w1CharEquiv i)⁻¹`.

Stated on the structural `Hypothesis ↥L` (not `Hypothesis46`): it only reads the `Hypothesis`-level
data `w1CharEquiv`, so it is available to any `Hypothesis ↥L` (e.g. the §10 type-`P` host
`(hyp.toCertainTypeHypothesis …).toHypothesis`); `Hypothesis46` callers pass `h.toHypothesis`. -/
noncomputable def rowInv (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)]
    (i : Fin (Nat.card h.W1)) : Fin (Nat.card h.W1) :=
  h.w1CharEquiv.symm ((h.w1CharEquiv i)⁻¹)

omit [Fintype G] in
omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
@[simp] theorem w1CharEquiv_rowInv (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)]
    (i : Fin (Nat.card h.W1)) :
    h.w1CharEquiv (rowInv h i) = (h.w1CharEquiv i)⁻¹ :=
  h.w1CharEquiv.apply_symm_apply _

omit [Fintype G] in
/-- `rowInv` is an **involution** (`(w1CharEquiv i)⁻¹` inverts), hence a permutation of the rows. -/
theorem rowInv_rowInv (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)] (i : Fin (Nat.card h.W1)) :
    rowInv h (rowInv h i) = i := by
  rw [rowInv, w1CharEquiv_rowInv]
  have h_inv_inv : ((h.w1CharEquiv i)⁻¹)⁻¹ = h.w1CharEquiv i :=
    @inv_inv ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _ (h.w1CharEquiv i)
  rw [h_inv_inv, Equiv.symm_apply_apply]

/-- The row-inversion **permutation** `i ↦ rowInv i` (an involution). -/
noncomputable def rowInvEquiv (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)] :
    Fin (Nat.card h.W1) ≃ Fin (Nat.card h.W1) :=
  Function.Involutive.toPerm (rowInv h) (rowInv_rowInv h)

/-- **The inverse grid character is a grid character at the conjugate index.**
`(P_{ij})⁻¹ = P_{i'j'}` with column `j' = χ₂⁻¹` and row `i' = rowInv i`
(`w1CharEquiv i' = (w1CharEquiv i)⁻¹`).  `omegaProdCharTic` is a composition of `omegaProdChar`
with the bridge iso `ticWEquivSdiffW`; inversion passes through the composition (abelian `ℂˣ`) and
acts coordinatewise on `omegaProdChar` (`omegaProdChar_inv`). -/
theorem omegaProdCharTic_inv (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (omegaProdCharTic h χ₂ i)⁻¹ = omegaProdCharTic h χ₂⁻¹ (rowInv h.toHypothesis i) := by
  ext w
  simp only [omegaProdCharTic, MonoidHom.comp_apply, w1CharEquiv_rowInv,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.inv_apply, mul_inv]
  rfl

/-- **σ-grid conjugation closure** (the (4.9)(a) grid identity through σ).  The complex conjugate of
the certain-type σ-image `ω_{ij}^σ` is the σ-image `ω_{i'j'}^σ` at the conjugate grid index
(`j' = χ₂⁻¹`, `i' = rowInv i`).  Combines `certainTypeOmegaSigma_conj` (conjugation = inverse grid
character through σ) with `omegaProdCharTic_inv` (the inverse is the conjugate-index grid character). -/
theorem certainTypeOmegaSigma_conj_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (certainTypeOmegaSigma h χ₂ i)
      = certainTypeOmegaSigma h χ₂⁻¹ (rowInv h.toHypothesis i) := by
  rw [certainTypeOmegaSigma_conj, certainTypeOmegaSigma]
  exact congrArg
    (fun c => (ticVdiff h).sigma rfl (ticVdiffFullDadeApplication h) ((ticVdiff h).omega c))
    (omegaProdCharTic_inv h χ₂ i)

/-! ### The `L`-side conjugation closure (for the μ-bridge)

The (4.9)(a) bridge to the `L`-characters `μ_{ij}` runs through the **`L`-side** σ-isometry `σ_L`
(`toTICyclicHypothesis.sigma`), via Theorem (4.3.b) `sigma_chiColumn_eq_certainType`:
`σ_L(ω_{ij}) = δ_j μ_{ij}` (`ω_{ij} = chiColumn χ₂ i`).  The same conjugation closure as on the
`G`-side holds for `σ_L`: `chiColumn` is `ω(omegaProdChar (w1CharEquiv i) χ₂)`, so conjugation sends
it to the conjugate-index grid character, and `σ_L` intertwines the Galois action. -/

omit [Fintype G] in
/-- **Conjugation of a column source character.**  `χ_{ij}̄ = χ_{i'j'}` at the conjugate index
(`ω_{ij} = chiColumn χ₂ i`): the Galois action of complex conjugation sends `ω(χ₁, χ₂)` to
`ω(χ₁⁻¹, χ₂⁻¹) = ω(w1CharEquiv (rowInv i), χ₂⁻¹)`, i.e. `chiColumn χ₂⁻¹ (rowInv i)`. -/
theorem chiColumn_conj (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    IrreducibleCharacter.galoisMap Complex.conjAe.toRingEquiv (h.chiColumn χ₂ i)
      = h.chiColumn χ₂⁻¹ (rowInv h i) := by
  haveI : Fintype ↥h.sdiffTICyclicHypothesis.W := Fintype.ofFinite _
  rw [Hypothesis.chiColumn, Hypothesis.chiColumn, galoisMap_conj_omega, omegaProdChar_inv]
  exact congrArg
    (fun c => h.sdiffTICyclicHypothesis.omega (h.sdiffTICyclicHypothesis.omegaProdChar c χ₂⁻¹))
    (w1CharEquiv_rowInv h i).symm

omit [Fintype G] in
/-- **`L`-side σ conjugation closure** (the (4.9)(a) bridge ingredient).  The complex conjugate of
the `L`-side σ-image `σ_L(ω_{ij})` is `σ_L(ω_{i'j'})` at the conjugate grid index.  Combines the
(3.9) commutation `sigma_mapRingEquiv_comm` for `toTICyclicHypothesis` with `chiColumn_conj`.
Together with (4.3.b) `sigma_chiColumn_eq_certainType` (`σ_L(ω_{ij}) = δ_j μ_{ij}`) this yields the
`L`-character conjugation `δ_j μ_{ij}̄ = δ_{j'} μ_{i'j'}`. -/
theorem sigma_chiColumn_conj (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))
      = h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.chiColumn χ₂⁻¹ (rowInv h i) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) := by
  rw [← chiColumn_conj]
  exact h.toTICyclicHypothesis.sigma_mapRingEquiv_comm rfl h.toTICyclicFullDadeApplication
    Complex.conjAe.toRingEquiv (h.chiColumn χ₂ i)

omit [Fintype G] in
/-- **Peterfalvi (4.9)(a), the `L`-character conjugation bridge.**  `δ_j·μ_{ij}̄ = δ_{j'}·μ_{i'j'}`
at the conjugate index (`i' = rowInv i`, `j' = χ₂⁻¹`).  Apply complex conjugation `mapRingEquiv conj`
to the (4.3.b) identity `σ_L(ω_{ij}) = δ_j·μ_{ij}`: the left side becomes `σ_L(ω_{i'j'}) = δ_{j'}·
μ_{i'j'}` (`sigma_chiColumn_conj` then (4.3.b) again), the right side `δ_j·μ_{ij}̄`
(`mapRingEquiv_zsmul`, `δ_j ∈ ℤ`).  Since the `μ` are genuine irreducible characters this forces
`μ_{ij}̄ = μ_{i'j'}` (and `δ_j = δ_{j'}`), the heart of (4.9)(a). -/
theorem certainType_mu_conj_bridge (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (h.columnFamily χ₂).sign •
        ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
          ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      = (h.columnFamily χ₂⁻¹).sign •
          ((h.columnFamily χ₂⁻¹).mu (rowInv h i) : ClassFunction ↥L ℂ) := by
  have e2 := h.sigma_chiColumn_eq_certainType χ₂⁻¹ (rowInv h i)
  have key := congrArg (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv)
    (h.sigma_chiColumn_eq_certainType χ₂ i)
  rw [sigma_chiColumn_conj, e2, ClassFunction.mapRingEquiv_zsmul] at key
  exact key.symm

omit [Fintype G] in
/-- **Peterfalvi (4.9)(a), `μ_{ij}̄ = μ_{i'j'}`.**  The conjugation bridge `δ_j·μ_{ij}̄ =
δ_{j'}·μ_{i'j'}` forces the (genuine irreducible) characters equal: pairing both sides with
`μ_{i'j'}` gives `δ_j·⟨μ_{ij}̄, μ_{i'j'}⟩ = δ_{j'}` (since `‖μ_{i'j'}‖² = 1`); as the inner product
of two irreducibles is `0` or `1` and `δ_{j'} ≠ 0`, it must be `1`, i.e. `μ_{ij}̄ = μ_{i'j'}`. -/
theorem certainType_mu_conj_eq (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    IrreducibleCharacter.galoisMap Complex.conjAe.toRingEquiv ((h.columnFamily χ₂).mu i)
      = (h.columnFamily χ₂⁻¹).mu (rowInv h i) := by
  by_contra hne
  have hb := certainType_mu_conj_bridge h χ₂ i
  rw [← IrreducibleCharacter.galoisMap_apply_coe,
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign
      (IrreducibleCharacter.galoisMap Complex.conjAe.toRingEquiv ((h.columnFamily χ₂).mu i) :
        ClassFunction ↥L ℂ),
    ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂⁻¹).sign
      ((h.columnFamily χ₂⁻¹).mu (rowInv h i) : ClassFunction ↥L ℂ)] at hb
  have hI := congrArg (fun φ => ClassFunction.inner φ
    ((h.columnFamily χ₂⁻¹).mu (rowInv h i) : ClassFunction ↥L ℂ)) hb
  simp only [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite, if_neg hne,
    mul_zero] at hI
  exact absurd hI.symm (by
    rcases (h.columnFamily χ₂⁻¹).sign_eq with he | he <;> rw [he] <;> norm_num)

omit [Fintype G] in
/-- **Peterfalvi (4.9)(a), `μ̄_j = μ_{j'}`** (column-sum form).  The complex conjugate of the
certain-type column character `μ_j = ∑_i μ_{ij}` is the conjugate column `μ_{j'} = ∑_i μ_{ij'}`
(`j' = χ₂⁻¹`).  `mapRingEquiv conj` is additive (`map_sum`), each `μ_{ij}̄ = μ_{i'j'}`
(`certainType_mu_conj_eq`), and the row reindexing `i ↦ rowInv i` is a permutation (`rowInvEquiv`). -/
theorem certainType_columnSum_conj (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ))
      = ∑ i, ((h.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) := by
  rw [← ClassFunction.mapRingEquivLinear_apply, map_sum]
  simp only [ClassFunction.mapRingEquivLinear_apply]
  have hterm : ∀ i, ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      = ((h.columnFamily χ₂⁻¹).mu (rowInv h i) : ClassFunction ↥L ℂ) := fun i => by
    rw [← IrreducibleCharacter.galoisMap_apply_coe, certainType_mu_conj_eq]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact Equiv.sum_comp (rowInvEquiv h)
    (fun i => ((h.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ))

/-! ### The conjugate column is a new column (the (4.9)(a) `μ̄_j ≠ μ_j`) -/

/-- **The conjugate column index differs** (`j' = χ₂⁻¹ ≠ χ₂ = j` for nontrivial `χ₂`).  The column
character group `(W₂.subgroupOf W) →* ℂˣ` has odd order (`= |W₂|`, dividing `|W|` odd), so it has no
involutions: `χ₂ = χ₂⁻¹` would force `χ₂² = 1`, hence `orderOf χ₂ ∣ 2` and odd, so `χ₂ = 1`. -/
theorem column_inv_ne_self (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    χ₂⁻¹ ≠ χ₂ := by
  haveI : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hodd : Odd (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)) := by
    rw [h.card_charGroup_W2]
    exact h.W_odd.of_dvd_nat (Subgroup.card_dvd_of_le le_sup_right)
  intro heq
  apply hχ₂
  have hsq : χ₂ ^ 2 = 1 := by
    have hm := mul_inv_cancel χ₂
    rw [heq] at hm
    rwa [pow_two]
  have hcardodd : Odd (orderOf χ₂) := hodd.of_dvd_nat (orderOf_dvd_natCard χ₂)
  have h1 : orderOf χ₂ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ hcardodd) (by decide)
  exact orderOf_eq_one_iff.mp h1

/-- **Peterfalvi (4.9)(a), `μ̄_k ≠ μ_k`.**  For a nontrivial column `χ₂`, the conjugate column
`μ̄_k = μ_{k'}` (`certainType_columnSum_conj`, `k' = χ₂⁻¹`) is a **different** certain-type
character:
`χ₂⁻¹ ≠ χ₂` (`column_inv_ne_self`, `|W|` odd) makes the two column sums orthogonal
(`columnFamily_mu_sum_inner`), so `⟨μ̄_k, μ_k⟩ = 0 ≠ w₁ = ‖μ_k‖²`.  This is the nonvanishing
`0 ≠ μ̄_k − μ_k ∈ Z[T, A]` input to the (4.9)(a) coherence (`IsCoherent.nonzero`). -/
theorem certainType_columnSum_conj_ne (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ))
      ≠ ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) := by
  rw [certainType_columnSum_conj]
  intro heq
  have h0 := columnFamily_mu_sum_inner h χ₂⁻¹ χ₂
  rw [if_neg (column_inv_ne_self h hχ₂), heq, columnFamily_mu_sum_inner h χ₂ χ₂,
    if_pos rfl] at h0
  exact (Nat.cast_ne_zero.mpr (NeZero.ne (Nat.card h.W1))) h0

omit [Fintype G] in
omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Row inversion fixes the anchor row**: `rowInv 0 = 0` (the row-`0` character is trivial,
`w1CharEquiv_zero`, and `1⁻¹ = 1`). -/
@[simp] theorem rowInv_zero (h : Hypothesis ↥L) [NeZero (Nat.card h.W1)] :
    rowInv h 0 = 0 := by
  rw [rowInv, Hypothesis.w1CharEquiv_zero]
  have h_inv_one :
      ((1 : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)⁻¹) = 1 :=
    @inv_one ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _
  rw [h_inv_one, ← Hypothesis.w1CharEquiv_zero (h := h), Equiv.symm_apply_apply]

end OddOrder.Peterfalvi.S06
