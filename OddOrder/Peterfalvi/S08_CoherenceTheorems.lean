/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_Coherence
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.FixedPointFree
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.RepresentationTheory.SylowTICongruence
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.BG.Ch1_Preliminary.S03_FrobeniusActions
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Peterfalvi §8: Some Coherence Theorems

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37.

This module records the main carrier structures for the §8 coherence theorems:
the solvable-normal filtration setup (6.1), the odd-order specialization
(6.4), and the Sibley-style final setup (6.8).  The hard numerical and
class-sum-algebra proofs are intentionally not asserted here.

Reference note: `notes/peterfalvi/s08_coherence_theorems.md`.
-/

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {Γ : Type*} [Group Γ]

/-- The induction summand commutes with complex conjugation. -/
theorem induceTerm_conjStar (H : Subgroup Γ) (θ : ClassFunction ↥H ℂ) (x g : Γ) :
    star (induceTerm H θ x g) = induceTerm H θ.conj x g := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [induceTerm_of_mem θ hx, induceTerm_of_mem θ.conj hx, conj_apply]
  · rw [induceTerm_of_not_mem θ hx, induceTerm_of_not_mem θ.conj hx, star_zero]

variable [Fintype Γ]

/-- The unnormalized induction sum commutes with complex conjugation. -/
theorem induceSum_conj (H : Subgroup Γ) (θ : ClassFunction ↥H ℂ) :
    (induceSum H θ).conj = induceSum H θ.conj := by
  ext g
  rw [conj_apply, induceSum_apply, induceSum_apply, star_sum]
  exact Finset.sum_congr rfl fun x _ => induceTerm_conjStar H θ x g

/-- The normalized induced class function commutes with complex conjugation. -/
theorem induce_conj (H : Subgroup Γ) [Invertible (Nat.card H : ℂ)]
    (θ : ClassFunction ↥H ℂ) :
    (induce H θ).conj = induce H θ.conj := by
  ext g
  rw [conj_apply, induce_apply, induce_apply, star_mul', star_sum]
  have hscale : star (⅟(Nat.card H : ℂ)) = ⅟(Nat.card H : ℂ) := by
    rw [invOf_eq_inv, star_inv₀, star_natCast]
  rw [hscale]
  exact congrArg (fun z => ⅟(Nat.card H : ℂ) * z)
    (Finset.sum_congr rfl fun x _ => induceTerm_conjStar H θ x g)

end ClassFunction

/-! ### Peterfalvi (4.1): pairwise orthogonality of signed irreducibles (mmd 04.6 L5)

Peterfalvi **(4.1)** is the elementary character-theoretic lemma that lets one glue two coherent
families into a single isometry: it promotes orthogonality of *signed differences* to orthogonality
of the underlying signed irreducibles.  A "signed irreducible" (Peterfalvi's `±Irr X`) is a norm-`1`
element of `ZIrr Γ`, i.e. `±` an irreducible character (`exists_zsmul_irreducibleCharacter_of_inner_self_one`).
The lemma is used in §4.3, §6.8.1, §9.5, §10.3 and §14.1. -/

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]

/-- A norm-`1` virtual character has nonzero degree: if `φ = ε • ξ` with `ε = ±1` and `ξ`
irreducible, then `φ(1) = ε · ξ(1) ≠ 0` (irreducible degrees are positive). -/
theorem apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one
    {φ : ClassFunction Γ ℂ} (hφ : φ ∈ ZIrr Γ)
    (hφn : ClassFunction.inner φ φ = 1) : φ (1 : Γ) ≠ 0 := by
  obtain ⟨ε, ξ, hε, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hφn
  obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξ
  rw [← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction Γ ℂ), ClassFunction.smul_apply, hd1]
  refine mul_ne_zero ?_ ?_
  · rcases hε with h | h <;> subst h <;> norm_num
  · exact_mod_cast hd.ne'

/-- Two signed irreducibles with nonzero inner product are equal up to that inner product:
`ψ = ⟨φ, ψ⟩ • φ`.  (Writing `φ = ε•a`, `ψ = ε'•b`, the inner product `εε'·(a = b)` is nonzero only
if `a = b`, in which case `⟨φ,ψ⟩ = εε'` and `εε'·ε = ε'` since `ε² = 1`.) -/
theorem eq_inner_smul_of_inner_ne_zero
    {φ ψ : ClassFunction Γ ℂ} (hφ : φ ∈ ZIrr Γ) (hψ : ψ ∈ ZIrr Γ)
    (hφn : ClassFunction.inner φ φ = 1) (hψn : ClassFunction.inner ψ ψ = 1)
    (hne : ClassFunction.inner φ ψ ≠ 0) :
    ψ = ClassFunction.inner φ ψ • φ := by
  classical
  obtain ⟨ε, a, hε, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hφn
  obtain ⟨ε', b, hε', rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hψ hψn
  have key : ClassFunction.inner (ε • (a : ClassFunction Γ ℂ)) (ε' • (b : ClassFunction Γ ℂ)) =
      (ε : ℂ) * (ε' : ℂ) *
        ClassFunction.inner (a : ClassFunction Γ ℂ) (b : ClassFunction Γ ℂ) := by
    rw [← Int.cast_smul_eq_zsmul ℂ ε (a : ClassFunction Γ ℂ),
      ← Int.cast_smul_eq_zsmul ℂ ε' (b : ClassFunction Γ ℂ),
      ClassFunction.inner_smul_left, inner_smul_right, star_intCast]
    ring
  have hab : a = b := by
    by_contra hab
    exact hne (by rw [key, irreducibleCharacter_inner, if_neg hab, mul_zero])
  subst hab
  rw [key, irreducibleCharacter_inner, if_pos rfl, mul_one,
    ← Int.cast_smul_eq_zsmul ℂ ε' (a : ClassFunction Γ ℂ),
    ← Int.cast_smul_eq_zsmul ℂ ε (a : ClassFunction Γ ℂ), smul_smul]
  congr 1
  rcases hε with h | h <;> subst h <;> push_cast <;> ring

/-- **Peterfalvi (4.1)** (mmd 04.6 L5), cross-orthogonality core.

For signed irreducibles `α, β, γ, δ ∈ ±Irr Γ` (norm-`1` elements of `ZIrr Γ`) and nonzero reals
`u, v`, if `(α,β) = (γ,δ) = 0`, the signed difference `(α − β, u•γ − v•δ) = 0`, and both signed
differences vanish at `1`, then `(α, γ) = 0`.

Proof (mmd): if `(α,γ) ≠ 0`, then `γ = εα` (`ε = ±1`); orthogonality of `γ,δ` forces `(α,δ) = 0`,
and `(α,β) = 0` forces `(β,γ) = 0`.  Expanding `(α−β, u•γ−v•δ) = 0` gives `uε + v(β,δ) = 0`, so
`(β,δ) ≠ 0` and `v•δ = −uε•β`.  Then `u•γ − v•δ = uε•(α+β)`, and evaluating at `1` (using
`(α−β)(1) = 0`, i.e. `α(1) = β(1)`) gives `0 = 2uεα(1)`, contradicting `u ≠ 0`, `ε ≠ 0`,
`α(1) ≠ 0`. -/
theorem inner_eq_zero_of_orthogonal_signedDifference
    {α β γ δ : ClassFunction Γ ℂ} {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hα : α ∈ ZIrr Γ) (hαn : ClassFunction.inner α α = 1)
    (hβ : β ∈ ZIrr Γ) (hβn : ClassFunction.inner β β = 1)
    (hγ : γ ∈ ZIrr Γ) (hγn : ClassFunction.inner γ γ = 1)
    (hδ : δ ∈ ZIrr Γ) (hδn : ClassFunction.inner δ δ = 1)
    (hαβ : ClassFunction.inner α β = 0) (hγδ : ClassFunction.inner γ δ = 0)
    (hdiff : ClassFunction.inner (α - β) ((u : ℂ) • γ - (v : ℂ) • δ) = 0)
    (hα1 : (α - β) (1 : Γ) = 0)
    (hγδ1 : ((u : ℂ) • γ - (v : ℂ) • δ) (1 : Γ) = 0) :
    ClassFunction.inner α γ = 0 := by
  by_contra hαγ
  -- (1) `γ = ⟨α,γ⟩ • α`.
  have hγeq : γ = ClassFunction.inner α γ • α :=
    eq_inner_smul_of_inner_ne_zero hα hγ hαn hγn hαγ
  -- (2) `⟨α,δ⟩ = 0` (else `δ = ±α = ±γ`, contradicting `γ ⊥ δ`).
  have hαδ : ClassFunction.inner α δ = 0 := by
    by_contra hαδ
    have hδeq : δ = ClassFunction.inner α δ • α :=
      eq_inner_smul_of_inner_ne_zero hα hδ hαn hδn hαδ
    have hcontra : ClassFunction.inner γ δ =
        ClassFunction.inner α γ * star (ClassFunction.inner α δ) := by
      conv_lhs => rw [hγeq, hδeq]
      rw [ClassFunction.inner_smul_left, inner_smul_right, hαn, mul_one]
    exact (mul_ne_zero hαγ (star_ne_zero.mpr hαδ)) (hγδ ▸ hcontra).symm
  -- (3) `⟨β,γ⟩ = 0`.
  have hβγ : ClassFunction.inner β γ = 0 := by
    rw [hγeq, inner_smul_right, inner_conj_symm α β, hαβ, star_zero, mul_zero]
  -- (4) Expand the signed-difference orthogonality to `u⟨α,γ⟩ + v⟨β,δ⟩ = 0`.
  have hexpand : (u : ℂ) * ClassFunction.inner α γ + (v : ℂ) * ClassFunction.inner β δ = 0 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
      inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right] at hdiff
    simp only [show star ((u : ℝ) : ℂ) = ((u : ℝ) : ℂ) from by simp,
      show star ((v : ℝ) : ℂ) = ((v : ℝ) : ℂ) from by simp, hαδ, hβγ, mul_zero] at hdiff
    linear_combination hdiff
  -- (5) `⟨β,δ⟩ ≠ 0`, so `δ = ⟨β,δ⟩ • β`.
  have hβδ : ClassFunction.inner β δ ≠ 0 := by
    intro h0
    rw [h0, mul_zero, add_zero] at hexpand
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) hαγ) hexpand
  have hδeq : δ = ClassFunction.inner β δ • β :=
    eq_inner_smul_of_inner_ne_zero hβ hδ hβn hδn hβδ
  -- (6) Evaluate at `1`.  `α(1) = β(1)` from `(α−β)(1) = 0`.
  have hαβ1 : α (1 : Γ) = β (1 : Γ) := by
    have h := hα1; rw [ClassFunction.sub_apply, sub_eq_zero] at h; exact h
  have hγ1 : γ (1 : Γ) = ClassFunction.inner α γ * α (1 : Γ) := by
    conv_lhs => rw [hγeq]
    rw [ClassFunction.smul_apply]
  have hδ1 : δ (1 : Γ) = ClassFunction.inner β δ * β (1 : Γ) := by
    conv_lhs => rw [hδeq]
    rw [ClassFunction.smul_apply]
  rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.smul_apply, hγ1, hδ1,
    ← hαβ1] at hγδ1
  -- `hγδ1 : u·(⟨α,γ⟩·α(1)) − v·(⟨β,δ⟩·α(1)) = 0`.
  have hfinal : 2 * (u : ℂ) * ClassFunction.inner α γ * α (1 : Γ) = 0 := by
    linear_combination hγδ1 + α (1 : Γ) * hexpand
  -- (7) Contradiction: every factor is nonzero.
  refine (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hαγ)
    (apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one hα hαn)) hfinal
  · norm_num
  · exact Complex.ofReal_ne_zero.mpr hu

/-- **Peterfalvi (4.1)** (mmd 04.6 L5).  Signed irreducibles `α, β, γ, δ ∈ ±Irr Γ` with
`(α,β) = (γ,δ) = 0`, orthogonal signed difference `(α − β, u•γ − v•δ) = 0` (`u, v` nonzero reals)
and both signed differences vanishing at `1` are **pairwise orthogonal**: all four cross inner
products `(α,γ), (α,δ), (β,γ), (β,δ)` vanish.

Each follows from the cross-orthogonality core
`inner_eq_zero_of_orthogonal_signedDifference` applied to a sign-flipped / swapped instance
(`α ↔ β`, `γ ↔ δ` with `u ↔ v`); the permuted hypotheses are produced by conjugate symmetry
(`inner_conj_symm`) and `neg_sub`. -/
theorem pairwise_inner_eq_zero_of_orthogonal_signedDifference
    {α β γ δ : ClassFunction Γ ℂ} {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hα : α ∈ ZIrr Γ) (hαn : ClassFunction.inner α α = 1)
    (hβ : β ∈ ZIrr Γ) (hβn : ClassFunction.inner β β = 1)
    (hγ : γ ∈ ZIrr Γ) (hγn : ClassFunction.inner γ γ = 1)
    (hδ : δ ∈ ZIrr Γ) (hδn : ClassFunction.inner δ δ = 1)
    (hαβ : ClassFunction.inner α β = 0) (hγδ : ClassFunction.inner γ δ = 0)
    (hdiff : ClassFunction.inner (α - β) ((u : ℂ) • γ - (v : ℂ) • δ) = 0)
    (hα1 : (α - β) (1 : Γ) = 0)
    (hγδ1 : ((u : ℂ) • γ - (v : ℂ) • δ) (1 : Γ) = 0) :
    ClassFunction.inner α γ = 0 ∧ ClassFunction.inner α δ = 0 ∧
      ClassFunction.inner β γ = 0 ∧ ClassFunction.inner β δ = 0 := by
  -- Conjugate-symmetric companions of the orthogonality hypotheses.
  have hδγ : ClassFunction.inner δ γ = 0 := by rw [inner_conj_symm γ δ, hγδ, star_zero]
  have hβα : ClassFunction.inner β α = 0 := by rw [inner_conj_symm α β, hαβ, star_zero]
  -- The `β ↔ α` and `γ,u ↔ δ,v` sign-flipped signed differences (orthogonal + vanishing at `1`).
  have hdiffYX : ClassFunction.inner (α - β) ((v : ℂ) • δ - (u : ℂ) • γ) = 0 := by
    rw [← neg_sub ((u : ℂ) • γ) ((v : ℂ) • δ), ClassFunction.inner_neg_right, hdiff, neg_zero]
  have hdiffBA : ClassFunction.inner (β - α) ((u : ℂ) • γ - (v : ℂ) • δ) = 0 := by
    rw [← neg_sub α β, ClassFunction.inner_neg_left, hdiff, neg_zero]
  have hdiffBAYX : ClassFunction.inner (β - α) ((v : ℂ) • δ - (u : ℂ) • γ) = 0 := by
    rw [← neg_sub α β, ← neg_sub ((u : ℂ) • γ) ((v : ℂ) • δ),
      ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg, hdiff]
  have h1BA : (β - α) (1 : Γ) = 0 := by
    rw [← neg_sub α β, ClassFunction.neg_apply, hα1, neg_zero]
  have h1YX : ((v : ℂ) • δ - (u : ℂ) • γ) (1 : Γ) = 0 := by
    rw [← neg_sub ((u : ℂ) • γ) ((v : ℂ) • δ), ClassFunction.neg_apply, hγδ1, neg_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inner_eq_zero_of_orthogonal_signedDifference hu hv hα hαn hβ hβn hγ hγn hδ hδn
      hαβ hγδ hdiff hα1 hγδ1
  · exact inner_eq_zero_of_orthogonal_signedDifference hv hu hα hαn hβ hβn hδ hδn hγ hγn
      hαβ hδγ hdiffYX hα1 h1YX
  · exact inner_eq_zero_of_orthogonal_signedDifference hu hv hβ hβn hα hαn hγ hγn hδ hδn
      hβα hγδ hdiffBA h1BA hγδ1
  · exact inner_eq_zero_of_orthogonal_signedDifference hv hu hβ hβn hα hαn hδ hδn hγ hγn
      hβα hδγ hdiffBAYX h1BA h1YX

open scoped Classical in
/-- **Fourier expansion of a class function** in the orthonormal basis of irreducible characters:
`φ = ∑_{χ ∈ Irr Γ} ⟨φ, χ⟩ • χ`.  From completeness (`classFunction_eq_zero_of_orthogonal`): the
difference `φ − ∑ ⟨φ,χ⟩•χ` is orthogonal to every irreducible (orthonormality
`irreducibleCharacter_inner_eq_ite`), hence `0`.  Used in (6.8.1) to expand `Res^G_L(η₁^{τ₁})` and
split its `X`-part (whose coefficients `⟨·,χᵢ⟩` are governed by Res-orthogonality) from the
`Z ⊆ ker` part (constant on `Z`). -/
theorem classFunction_eq_sum_inner_smul (φ : ClassFunction Γ ℂ) :
    φ = ∑ a : IrreducibleCharacter Γ,
      ClassFunction.inner φ (a : ClassFunction Γ ℂ) • (a : ClassFunction Γ ℂ) := by
  refine eq_of_sub_eq_zero (classFunction_eq_zero_of_orthogonal _ (fun b => ?_))
  rw [ClassFunction.inner_sub_left, inner_sum_left]
  have hstep : (∑ a : IrreducibleCharacter Γ,
      ClassFunction.inner
        (ClassFunction.inner φ (a : ClassFunction Γ ℂ) • (a : ClassFunction Γ ℂ))
        (b : ClassFunction Γ ℂ)) = ClassFunction.inner φ (b : ClassFunction Γ ℂ) := by
    rw [Finset.sum_eq_single b]
    · rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite b b, if_pos rfl, mul_one]
    · intro a _ hab
      rw [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite a b, if_neg hab, mul_zero]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  rw [hstep, sub_self]

open scoped Classical in
/-- **Regular-character difference value over the non-inflated irreducibles** (mmd 04.8 L168,
combined `(ρ_Γ − ρ_{Γ/N})(z) − (…)(1)` value).  For `N ⊴ Γ` and `z ∈ N^#`,
`∑_{χ ∈ Irr Γ, N ⊄ ker χ} χ(1)·(χ(z) − χ(1)) = -|Γ|`.  This is
`(-|Γ⧸N|) − (|Γ| − |Γ⧸N|) = -|Γ|`, from `sumNonInflatedDegreeMulChar_of_mem` (the `χ(z)` part) and
`sumNonInflatedDegreeSq` (the `χ(1)` part). -/
theorem sum_filter_degree_mul_charValue_sub_eq (N : Subgroup Γ) [N.Normal]
    {z : Γ} (hz : z ∈ N) (hz1 : z ≠ 1) :
    ∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * ((a : ClassFunction Γ ℂ) z - (a : ClassFunction Γ ℂ) 1)
      = -(Nat.card Γ : ℂ) := by
  haveI : Finite Γ := Finite.of_fintype Γ
  have hsplit : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * ((a : ClassFunction Γ ℂ) z - (a : ClassFunction Γ ℂ) 1))
      = (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) z)
        - (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
            ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
            (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun a _ => by ring)
  have h2 : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
        ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
        (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1)
      = (Nat.card Γ : ℂ) - (Nat.card (Γ ⧸ N) : ℂ) := by
    rw [show (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          (a : ClassFunction Γ ℂ) 1 * (a : ClassFunction Γ ℂ) 1)
        = ∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter Γ =>
          ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction Γ ℂ))),
          ((a : ClassFunction Γ ℂ) 1) ^ 2 from
        Finset.sum_congr rfl (fun a _ => by rw [pow_two])]
    exact sumNonInflatedDegreeSq (N := N)
  rw [hsplit, sumNonInflatedDegreeMulChar_of_mem (N := N) hz hz1, h2]; ring

open scoped Classical in
/-- **Bessel's inequality (integer-coefficient form).**  For an orthonormal family `s` of class
functions (`⟨a,b⟩ = δ_{a,b}` on `s`) and any `v` whose Fourier coefficients on `s` are integers
(`⟨v,a⟩ = β a`), the sum of squared coefficients is bounded by the squared norm:
`∑_{a∈s} (β a)² ≤ (⟨v,v⟩).re`.

Pythagoras on `v = (v − p) + p` with `p = ∑_{a∈s} (β a)•a` the orthogonal projection:
`⟨v,p⟩ = ⟨p,v⟩ = ⟨p,p⟩ = ∑(β a)²` (Parseval `inner_self_orthonormalSum_eq_sum_sq` + conjugate
symmetry), so `⟨v−p,v−p⟩ = ⟨v,v⟩ − ∑(β a)²`; non-negativity of `‖v−p‖²`
(`inner_self_re_nonneg`) gives the bound. -/
theorem sum_sq_le_inner_self_re {s : Finset (ClassFunction Γ ℂ)}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (v : ClassFunction Γ ℂ) {β : ClassFunction Γ ℂ → ℤ}
    (hβ : ∀ a ∈ s, ClassFunction.inner v a = (β a : ℂ)) :
    ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℝ) ≤ (ClassFunction.inner v v).re := by
  classical
  set p : ClassFunction Γ ℂ := ∑ a ∈ s, (β a : ℂ) • a with hp
  have hsumcast : ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) = ∑ a ∈ s, ((β a : ℂ)) ^ 2 := by
    push_cast; ring
  have hvp : ClassFunction.inner v p = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [hp, inner_sum_right, hsumcast]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_smul_right, hβ a ha, star_intCast]; ring
  have hpp : ClassFunction.inner p p = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [hp, inner_self_orthonormalSum_eq_sum_sq horth, hsumcast]
  have hpv : ClassFunction.inner p v = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [inner_conj_symm v p, hvp, star_intCast]
  have hkey : ClassFunction.inner (v - p) (v - p)
      = ClassFunction.inner v v - ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hvp, hpv, hpp]; ring
  have hnn := inner_self_re_nonneg (v - p)
  rw [hkey, Complex.sub_re] at hnn
  have hcast : (((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℂ)).re = ((∑ a ∈ s, (β a) ^ 2 : ℤ) : ℝ) :=
    Complex.intCast_re _
  rw [hcast] at hnn
  linarith

end OddOrder.RepresentationTheory

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-! ### (6.6) `X`-characterization helpers (T7): constituent inherits a kernel containment

The (6.6) `X = {χ∈Irr L | Z⊄Ker χ}` characterization needs "an irreducible constituent `χ` of a
genuine character `ψ` inherits `g ∈ Ker ψ`".  Both directions of the characterization route this
through a *genuine* character (`Res_H φ` for `⊆`, `Ind_K^L θ` for `⊇`) — never applying the Dade
isometry to the unsupported `χ` itself — which is why [Is] Lemma 2.21 is **not** needed. -/

/-- **(H0)** the restriction `Res^Γ_H φ` of a genuine character is genuine. -/
theorem isCharacter_restrict {Γ : Type*} [Group Γ] [Finite Γ] {φ : ClassFunction Γ ℂ}
    (hφ : IsCharacter φ) (H : Subgroup Γ) :
    IsCharacter (ClassFunction.restrict H φ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  have hφeq : φ = repCharacterClassFunction ρ :=
    ClassFunction.ext fun g => by rw [repCharacterClassFunction_apply]; exact congrFun hρ g
  rw [hφeq, ClassFunction.restrict_repCharacterClassFunction H ρ]
  exact repCharacterClassFunction_isCharacter (ρ.comp H.subtype)

/-- **(H1, decomposition form)** an irreducible constituent inherits a kernel containment of a
non-negative integer combination.  If `ψ = ∑_{a ∈ supp m} (m a) • a` is a finite `ℕ`-combination
of irreducible characters (`m : ClassFunction Γ ℂ →₀ ℕ` supported on `Irr Γ`) and `χ` is a
summand with `m χ ≠ 0`, then `g ∈ Ker ψ` forces `g ∈ Ker χ`.

This repackages the (6.6) G2.2 keystone
`OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq` from a
`Finsupp` decomposition: the family of summands is totalized to an `IrreducibleCharacter`-valued
function off the support, and the kernel hypothesis `ψ(g) = ψ(1)` is read as the keystone's
value-equality hypothesis. -/
theorem characterKernel_subset_of_natFinsupp_eq_sum {Γ : Type*} [Group Γ] [Finite Γ]
    {ψ : ClassFunction Γ ℂ} {m : ClassFunction Γ ℂ →₀ ℕ}
    (hsupp : (↑m.support : Set (ClassFunction Γ ℂ)) ⊆ irreducibleCharacters Γ)
    (hsum : ψ = ∑ a ∈ m.support, (m a : ℂ) • a)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ) (hmχ : m χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel ψ) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  classical
  set χfam : ClassFunction Γ ℂ → IrreducibleCharacter Γ :=
    fun a => if h : IsIrreducibleCharacter a then (⟨a, h⟩ : IrreducibleCharacter Γ)
      else trivialIrreducibleCharacter Γ with hχfam_def
  have hfam : ∀ a, IsIrreducibleCharacter a →
      ((χfam a : IrreducibleCharacter Γ) : ClassFunction Γ ℂ) = a := by
    intro a h; simp only [hχfam_def, dif_pos h]
  have hirr : ∀ a ∈ m.support, IsIrreducibleCharacter a := fun a ha =>
    mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))
  set d : ClassFunction Γ ℂ → ℕ :=
    fun a => if h : IsIrreducibleCharacter a then
      (h.exists_natDegree_charValue_one_dvd_card).choose else 0 with hd_def
  have hdeg : ∀ a ∈ m.support, ((χfam a : ClassFunction Γ ℂ)) 1 = (d a : ℂ) := by
    intro a ha
    have h := hirr a ha
    rw [hfam a h]
    simp only [hd_def, dif_pos h]
    exact (h.exists_natDegree_charValue_one_dvd_card).choose_spec.2.1
  have hsumapp : ∀ x : Γ, ψ x = ∑ a ∈ m.support, (m a : ℂ) * a x := by
    intro x
    rw [hsum]
    simp only [ClassFunction.finset_sum_apply, ClassFunction.smul_apply]
  have hgg : ψ g = ψ 1 := by
    have h := hg
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at h
    exact h
  have hval : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) g
      = ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) 1 := by
    have eL : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) g = ψ g := by
      rw [hsumapp g]; exact Finset.sum_congr rfl fun a ha => by rw [hfam a (hirr a ha)]
    have eR : ∑ a ∈ m.support, (m a : ℂ) * ((χfam a : ClassFunction Γ ℂ)) 1 = ψ 1 := by
      rw [hsumapp 1]; exact Finset.sum_congr rfl fun a ha => by rw [hfam a (hirr a ha)]
    rw [eL, eR, hgg]
  have hkey :=
    OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq
      (g := g) m.support (fun a => m a) χfam d hdeg hval χ
      (Finsupp.mem_support_iff.mpr hmχ) hmχ
  rwa [hfam χ hχ] at hkey

/-- **(H1, genuine form)** an irreducible constituent of a genuine character inherits a kernel
containment.  If `ψ` is a genuine character, `χ` is irreducible with `⟨ψ, χ⟩ ≠ 0` (a constituent),
then `g ∈ Ker ψ` forces `g ∈ Ker χ`.  This is `characterKernel_subset_of_natFinsupp_eq_sum`
applied to the `ℕ`-decomposition `IsCharacter.exists_natFinsupp_eq_sum` of `ψ`, whose
`χ`-coefficient is the nonzero Fourier multiplicity `⟨ψ, χ⟩`. -/
theorem characterKernel_subset_of_isCharacter_of_inner_ne_zero {Γ : Type*} [Group Γ]
    [Fintype Γ] [Invertible (Nat.card Γ : ℂ)] {ψ : ClassFunction Γ ℂ} (hψ : IsCharacter ψ)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ)
    (hχψ : ClassFunction.inner ψ χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel ψ) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hψ.exists_natFinsupp_eq_sum
  have hmχ : m χ ≠ 0 := fun h0 => hχψ (by rw [← hcoeff χ hχ, h0, Nat.cast_zero])
  exact characterKernel_subset_of_natFinsupp_eq_sum hsupp hsum hχ hmχ hg

/-! ### Cross-family inner products of two coherent Dade extensions

Two coherence extensions `τ₁, τ₂` built from the **same** §4 Dade base map agree with it on their
supported lattices (`extends_on_supported`), so on *supported* virtual characters their cross inner
products and degree-`0` values are governed by the Dade isometry alone — independent of which set
each comes from.  These are the (4.1) inputs for the (6.8.1) `himg_ortho`: with `x = χᵢ − dᵢχ₁`,
`y = ηⱼ − η₁` (degree-matched differences, supported on `H^#`),
`inner_extension_eq_inner_of_supported` gives `⟨τ₂ x, τ₁ y⟩ = ⟨x, y⟩` (`= 0` by `X ⊥ Y`), the
difference-orthogonality, and `extension_apply_one_eq_zero_of_supported` gives the
`(α − β)(1) = 0` / `(u•γ − v•δ)(1) = 0` hypotheses of
`pairwise_inner_eq_zero_of_orthogonal_signedDifference`. -/

section DadeCoherenceUnion

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  {A : Set G} {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- **Difference-orthogonality (Peterfalvi (4.1) input).**  For two coherences `hX`, `hY` w.r.t. the
**same** §4 Dade base map and supported lattice elements `x ∈ ℤ[X, A]`, `y ∈ ℤ[Y, A]`, the cross
inner product of the extensions equals the source inner product:
`⟨hX.extension x, hY.extension y⟩ = ⟨x, y⟩`.  Both extensions agree with the Dade map on the
supported lattice (`extends_on_supported`), reducing to the Dade isometry
`dadeIntegralCharacterMap_inner_eq_on_supported_span` (applied on the pair `{x, y}`). -/
theorem inner_extension_eq_inner_of_supported
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {X Y : Set (ClassFunction ↥L ℂ)}
    (hX : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hY : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) Y
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {x y : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hy : y ∈ OddOrder.Peterfalvi.S07.zSupportedSpan Y
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    ClassFunction.inner (hX.extension x) (hY.extension y) = ClassFunction.inner x y := by
  rw [hX.extends_on_supported x hx, hY.extends_on_supported y hy]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj
    (S := ({x, y} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hx.2
        · exact hy.2)
    (Submodule.subset_span (Set.mem_insert x _))
    (Submodule.subset_span (Set.mem_insert_of_mem x rfl))

/-- A coherent Dade extension sends a supported lattice element to a function vanishing at `1`:
`(hX.extension x)(1) = 0` for `x ∈ ℤ[X, A]`.  (`extends_on_supported` to the Dade map, then
`dadeIntegralCharacterMap_apply_one_eq_zero`.)  Supplies the degree-`0` hypotheses of (4.1). -/
theorem extension_apply_one_eq_zero_of_supported
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {X : Set (ClassFunction ↥L ℂ)}
    (hX : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan X
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    (hX.extension x) (1 : G) = 0 := by
  rw [hX.extends_on_supported x hx]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero hyp hconj hx.2

end DadeCoherenceUnion

/-- **Peterfalvi (6.8.1) norm-bound forcing** (mmd 04.8 L176).  In the (6.8.1) `b ≡ c ≡ 0 mod a`
argument, after `(6.7)` gives `a ∣ b` (write `b = a·x`), the norm identity
`1 + a² = ‖(χ₁ − aη₁)^τ‖² = ‖X‖² + (b − a)² + (m − 1)·b²` with `‖X‖² ≥ 0` gives the bound
`(b − a)² + (m − 1)·b² ≤ 1 + a²`; with `a ≥ 2` and `m ≥ 2` (`m = |Y|`) this forces `b = 0` — or the
edge case `b = a`, `m = 2`, which the textbook reduces to `b = 0` by relabelling
`η₁^{τ₁} ↔ −η₂^{τ₁}`.  (`b = ±2a` and `b = −a` are excluded since `4a² > 1 + a²` for `a ≥ 2`.) -/
theorem eq_zero_or_edge_of_dvd_of_normBound {a b m : ℤ}
    (ha : 2 ≤ a) (hm : 2 ≤ m) (hdvd : a ∣ b)
    (hnorm : (b - a) ^ 2 + (m - 1) * b ^ 2 ≤ 1 + a ^ 2) :
    b = 0 ∨ (b = a ∧ m = 2) := by
  obtain ⟨x, rfl⟩ := hdvd
  have ha0 : (0 : ℤ) < a := by linarith
  -- `b² = (a·x)² ≤ 1 + a²` (drop `(b−a)² ≥ 0` and the `(m−2)·b² ≥ 0` slack).
  have hb2 : (a * x) ^ 2 ≤ 1 + a ^ 2 := by
    nlinarith [sq_nonneg (a * x - a), mul_nonneg (by linarith : (0 : ℤ) ≤ m - 2) (sq_nonneg (a * x))]
  -- Hence `x² ≤ 1`: otherwise `x² ≥ 2` gives `2a² ≤ a²x² ≤ 1 + a²`, i.e. `a² ≤ 1`, contradicting `a ≥ 2`.
  have hx2 : x ^ 2 ≤ 1 := by
    by_contra h
    push_neg at h
    have hx2' : 2 ≤ x ^ 2 := h
    nlinarith [hb2, mul_pos ha0 ha0, mul_le_mul_of_nonneg_left hx2' (le_of_lt (mul_pos ha0 ha0))]
  have hxlo : -1 ≤ x := by nlinarith [hx2, sq_nonneg (x + 1)]
  have hxhi : x ≤ 1 := by nlinarith [hx2, sq_nonneg (x - 1)]
  interval_cases x
  · -- `x = -1` (`b = -a`): `4a² + (m−1)a² ≤ 1 + a²` is impossible.
    exfalso; nlinarith [hnorm, ha, hm]
  · -- `x = 0`: `b = 0`.
    left; ring
  · -- `x = 1` (`b = a`): `(m−1)a² ≤ 1 + a²` forces `m = 2`.
    right
    refine ⟨by ring, ?_⟩
    nlinarith [hnorm, ha, hm]

section DadeReciprocity

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  {A : Set G} {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- In the **TI Dade situation** (`hyp.H a = ⊥`, e.g. `H^#` a TI-subset with normalizer `L`), the
(2.7) adjoint averaging map collapses to plain evaluation: `adjointAverageFun hyp χ a = χ(a)`.  The
average `|H(a)|⁻¹ ∑_{x ∈ H(a)} χ(ax)` over the trivial group `H(a) = ⊥` is the single term
`χ(a·1) = χ(a)`. -/
theorem adjointAverageFun_eq_of_H_eq_bot
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (χ : ClassFunction G ℂ)
    (a : {a : G // a ∈ A}) (hH : hyp.H a = ⊥) :
    OddOrder.Peterfalvi.S04.adjointAverageFun hyp χ ⟨a.1, hyp.subset_L a.2⟩ = χ a.1 := by
  classical
  simp only [OddOrder.Peterfalvi.S04.adjointAverageFun]
  rw [dif_pos a.2]
  have hHa : hyp.H ⟨a.1, a.2⟩ = ⊥ := hH
  have hconst : ∀ x : ↥(hyp.H ⟨a.1, a.2⟩), χ (a.1 * (x : G)) = χ a.1 := by
    intro x
    have hx1 : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hHa]; exact x.2
    rw [Subgroup.mem_bot.mp hx1, mul_one]
  have hHne : (Nat.card (hyp.H ⟨a.1, a.2⟩) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (hyp.H ⟨a.1, a.2⟩) := Nat.card_pos
    exact_mod_cast this.ne'
  rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hHne, one_mul]

/-- **Dade reciprocity (TI case).**  For the §4 Dade base map of a TI Hypothesis (`hyp.H a = ⊥`),
a *supported* `α ∈ CF(L, A)` and any `ψ ∈ CF(G)`:

`⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L`.

This is the (2.7) `adjoint_formula` specialized to the TI situation, where the adjoint average of
`ψ` is `Res_L^G ψ` (`adjointAverageFun_eq_of_H_eq_bot`).  It is the gateway to the (6.8.1)
`Res_L(η₁^{τ₁})` decomposition: it converts the `G`-side pairing of a Dade image with `ψ` into the
`L`-side pairing of the supported source with `Res_L ψ`. -/
theorem inner_dadeIntegralCharacterMap_eq_inner_restrict
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj) α) ψ
      = ClassFunction.inner α (ClassFunction.restrict L ψ) := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp _ hαsupp]
  refine OddOrder.Peterfalvi.S04.adjoint_formula hyp (hyp.dadeMap (k := ℂ))
    (hyp.isDadeMap_dadeMap (k := ℂ)) hconj
    ⟨α, (ClassFunction.mem_supportedSubmodule).mpr hαsupp⟩ ψ (ClassFunction.restrict L ψ)
    (fun a => ?_)
  rw [adjointAverageFun_eq_of_H_eq_bot hyp ψ a (hH a), ClassFunction.restrict_apply]

end DadeReciprocity

open scoped ComplexOrder in
/-- The inner product of two genuine characters is `≥ 0`.  Decompose the right argument into a
non-negative integer combination of irreducibles (`exists_natFinsupp_eq_sum`); each summand
`⟨χ, a⟩` is `≥ 0` by `inner_irreducible_nonneg`, and the multiplicities are non-negative. -/
theorem inner_isCharacter_nonneg {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {χ ψ : ClassFunction Γ ℂ}
    (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    0 ≤ ClassFunction.inner χ ψ := by
  obtain ⟨m, hsupp, hsum, _⟩ := hψ.exists_natFinsupp_eq_sum
  rw [hsum, inner_sum_right]
  refine Finset.sum_nonneg fun a ha => ?_
  have ha' : IsIrreducibleCharacter a :=
    mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))
  rw [OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  exact mul_nonneg (Nat.cast_nonneg _) (hχ.inner_irreducible_nonneg ha')

set_option linter.unusedFintypeInType false in
open scoped ComplexOrder in
/-- **(H2)** the induced character `Ind_H^Γ θ` of a genuine character `θ` decomposes as a
non-negative integer combination of irreducibles, with multiplicity `⟨Ind θ, ψ⟩` at `ψ ∈ Irr Γ`.
Since `induce` lives only at the class-function level (`IsCharacter (Ind θ)` is not directly
available), the decomposition is reconstructed from `Ind θ ∈ ZIrr Γ` (`induce_mem_ZIrr`) plus the
non-negativity of `⟨Ind θ, ψ⟩ = ⟨θ, Res ψ⟩` (Frobenius reciprocity and `inner_isCharacter_nonneg`),
pushed through `Int.toNat`. -/
theorem induce_exists_natFinsupp_eq_sum {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ) :
    ∃ m : ClassFunction Γ ℂ →₀ ℕ, (↑m.support ⊆ irreducibleCharacters Γ) ∧
      ClassFunction.induce H θ = ∑ a ∈ m.support, (m a : ℂ) • a ∧
      ∀ ψ : ClassFunction Γ ℂ, IsIrreducibleCharacter ψ →
        (m ψ : ℂ) = ClassFunction.inner (ClassFunction.induce H θ) ψ := by
  classical
  obtain ⟨c, hsupp, hsum⟩ := mem_ZIrr_repr (ClassFunction.induce_mem_ZIrr H hθ.mem_ZIrr)
  have hcoeff : ∀ ψ : ClassFunction Γ ℂ, ψ ∈ irreducibleCharacters Γ →
      (c ψ : ℂ) = ClassFunction.inner (ClassFunction.induce H θ) ψ := by
    intro ψ hψ
    have h := inner_eq_coeff_of_repr (⟨ψ, hψ⟩ : IrreducibleCharacter Γ) hsupp
    rw [show ((⟨ψ, hψ⟩ : IrreducibleCharacter Γ) : ClassFunction Γ ℂ) = ψ from rfl] at h
    rw [← h, hsum]
  have hcnn : ∀ ψ : ClassFunction Γ ℂ, ψ ∈ c.support → 0 ≤ c ψ := by
    intro ψ hψsupp
    have hψ : ψ ∈ irreducibleCharacters Γ := hsupp (Finset.mem_coe.mpr hψsupp)
    have hψirr : IsIrreducibleCharacter ψ := mem_irreducibleCharacters.mp hψ
    have hnn : (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.induce H θ) ψ := by
      rw [ClassFunction.inner_induce_eq_inner_restrict]
      exact inner_isCharacter_nonneg hθ (isCharacter_restrict hψirr.isCharacter H)
    have : (0 : ℂ) ≤ (c ψ : ℂ) := by rw [hcoeff ψ hψ]; exact hnn
    exact_mod_cast this
  refine ⟨Finsupp.mapRange Int.toNat Int.toNat_zero c, ?_, ?_, ?_⟩
  · refine subset_trans ?_ hsupp
    intro ψ hψ
    exact Finset.mem_coe.mpr (Finsupp.support_mapRange (Finset.mem_coe.mp hψ))
  · have hsupp_eq : (Finsupp.mapRange Int.toNat Int.toNat_zero c).support = c.support := by
      apply Finset.Subset.antisymm Finsupp.support_mapRange
      intro a ha
      rw [Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
      omega
    rw [hsum, hsupp_eq]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finsupp.mapRange_apply]
    have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c a)), Int.toNat_of_nonneg (le_of_lt this)]
  · intro ψ hψ
    rw [Finsupp.mapRange_apply, ← hcoeff ψ hψ]
    have hnn : 0 ≤ c ψ := by
      by_cases hsupp_mem : ψ ∈ c.support
      · exact hcnn ψ hsupp_mem
      · rw [Finsupp.notMem_support_iff.mp hsupp_mem]
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c ψ)), Int.toNat_of_nonneg hnn]

set_option linter.unusedFintypeInType false in
/-- **(H2, character form)** the induced character `Ind_H^Γ θ` of a genuine character `θ` is
itself a genuine character.  Combines the non-negative-integer decomposition
`induce_exists_natFinsupp_eq_sum` (`Ind θ = ∑ mₐ·a` with `mₐ ∈ ℕ`, `a ∈ Irr Γ`) with its
converse `isCharacter_of_natFinsupp_eq_sum` (a `ℕ`-combination of irreducible characters is a
genuine character).  This is **brick 2** of the Frobenius-reciprocity route to the Peterfalvi
`(6.2)` `θ`-bound a-half. -/
theorem isCharacter_induce {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ) :
    IsCharacter (ClassFunction.induce H θ) := by
  obtain ⟨m, hsupp, hsum, _⟩ := induce_exists_natFinsupp_eq_sum hθ
  exact isCharacter_of_natFinsupp_eq_sum m hsupp hsum

set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (6.2) `θ`-bound, a-half** (the Clifford/induction half).  For an irreducible
character `θ` of a finite group `K` and a subgroup `C ≤ K`, there is an irreducible character
`φ` of `C` of which `θ` is a constituent of `Ind_C^K φ` (`⟨Ind_C^K φ, θ⟩ ≠ 0`), and whose
degree controls `θ`'s: `θ(1) ≤ |K : C|·φ(1)`.

By Frobenius reciprocity `θ` is a constituent of `Ind_C^K φ` for some `φ ∈ Irr C`
(`exists_inner_induce_ne_zero`, equivalently `φ` is a constituent of `Res^K_C θ`).  Since `φ` is
a genuine character, so is `Ind_C^K φ` (`isCharacter_induce`, brick 2), so the
constituent-degree bound `IsCharacter.apply_one_re_le_of_inner_ne_zero` (brick 1) gives
`θ(1) ≤ (Ind_C^K φ)(1) = |K : C|·φ(1)` (`induce_apply_one`).  Combined with the section degree
bound `degree_sq_le_index_of_central_quotient` (`φ(1)² ≤ |C : D|`, the b-half) this yields the
full `(6.2)` degree bound `θ(1) ≤ |K : C|·√|C : D|`. -/
theorem theta_degree_le_index_mul_constituent {K : Type*} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (C : Subgroup K) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] (θ : IrreducibleCharacter K) :
    ∃ φ : IrreducibleCharacter C,
      ClassFunction.inner (ClassFunction.induce C (φ : ClassFunction ↥C ℂ))
          (θ : ClassFunction K ℂ) ≠ 0 ∧
      ((θ : ClassFunction K ℂ) 1).re ≤ (C.index : ℝ) * ((φ : ClassFunction ↥C ℂ) 1).re := by
  obtain ⟨φ, hφ⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero (H := C) θ
  refine ⟨φ, hφ, ?_⟩
  have hind : IsCharacter (ClassFunction.induce C (φ : ClassFunction ↥C ℂ)) :=
    isCharacter_induce φ.isIrreducible.isCharacter
  have hbound := hind.apply_one_re_le_of_inner_ne_zero θ.isIrreducible hφ
  rw [ClassFunction.induce_apply_one] at hbound
  rwa [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hbound

set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (6.2) `θ`-bound** (full degree bound).  For an irreducible character `θ` of a
finite group `K`, a subgroup `C ≤ K`, and a section `N ◁ C` with `N ≤ D ≤ C`, `θ` trivial on `N`
(after restriction to `C`) and `D ⧸ N` central in `C ⧸ N`, the degree of `θ` is bounded:
`θ(1) ≤ |K : C|·√|C : D|`.

Assembled from the two halves: the a-half `theta_degree_le_index_mul_constituent`
(`θ(1) ≤ |K:C|·φ(1)` for an `Ind`-constituent `φ ∈ Irr C` of `θ`) and the section b-half
`degree_sq_le_index_of_central_quotient` (`φ(1)² ≤ |C:D|`).  The `φ` produced by the a-half is a
constituent of `Res^K_C θ` (Frobenius reciprocity `inner_induce_eq_inner_restrict` +
`inner_conj_symm`), so `N ⊆ Ker(Res^K_C θ)` forces `N ⊆ Ker φ` (constituent kernel inheritance
`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), discharging the b-half's kernel
hypothesis.  Then `φ(1) = d` with `d² ≤ |C:D|` gives `φ(1) ≤ √|C:D|` (`Real.le_sqrt_of_sq_le`),
and multiplying by `|K:C| ≥ 0` closes the bound. -/
theorem theta_degree_le_index_mul_sqrt_index {K : Type*} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (θ : IrreducibleCharacter K) (C : Subgroup K) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] {N : Subgroup ↥C} [N.Normal] (D : Subgroup ↥C) (hND : N ≤ D)
    (hθN : (↑N : Set ↥C) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict C (θ : ClassFunction K ℂ)))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥C ⧸ N)) :
    ((θ : ClassFunction K ℂ) 1).re ≤ (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  obtain ⟨φ, hφne, hφbound⟩ := theta_degree_le_index_mul_constituent C θ
  -- `φ` is a constituent of `Res^K_C θ`: reciprocity turns `⟨Ind φ, θ⟩ ≠ 0` into `⟨φ, Res θ⟩ ≠ 0`,
  -- and conjugate symmetry flips it to `⟨Res θ, φ⟩ ≠ 0`.
  have hφRes : ClassFunction.inner (φ : ClassFunction ↥C ℂ)
      (ClassFunction.restrict C (θ : ClassFunction K ℂ)) ≠ 0 := by
    rw [← ClassFunction.inner_induce_eq_inner_restrict]; exact hφne
  have hres_inner : ClassFunction.inner (ClassFunction.restrict C (θ : ClassFunction K ℂ))
      (φ : ClassFunction ↥C ℂ) ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]; exact star_ne_zero.mpr hφRes
  -- constituent kernel inheritance: `N ⊆ Ker(Res θ) ⟹ N ⊆ Ker φ`.
  have hkerφ : (↑N : Set ↥C) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥C ℂ) := fun n hn =>
    characterKernel_subset_of_isCharacter_of_inner_ne_zero
      (isCharacter_restrict θ.isIrreducible.isCharacter C) φ.isIrreducible hres_inner (hθN hn)
  -- the b-half: `φ(1) = d` with `d² ≤ |C:D|`.
  obtain ⟨d, hd1, hd2⟩ :=
    degree_sq_le_index_of_central_quotient (N := N) φ D hND hkerφ hcentral
  have hφ1re : ((φ : ClassFunction ↥C ℂ) 1).re = (d : ℝ) := by
    rw [hd1]; exact Complex.natCast_re d
  have hd_le : (d : ℝ) ≤ Real.sqrt (D.index : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hd2)
  calc ((θ : ClassFunction K ℂ) 1).re
      ≤ (C.index : ℝ) * ((φ : ClassFunction ↥C ℂ) 1).re := hφbound
    _ = (C.index : ℝ) * (d : ℝ) := by rw [hφ1re]
    _ ≤ (C.index : ℝ) * Real.sqrt (D.index : ℝ) :=
        mul_le_mul_of_nonneg_left hd_le (Nat.cast_nonneg _)

/-- **Restriction kernel inheritance.**  If `θ` is trivial on a subgroup `M ≤ K` (i.e.
`M ⊆ characterKernel θ`), then its restriction `Res_C θ` to a subgroup `C ≤ K` is trivial on
`M.subgroupOf C = M ∩ C` (viewed in `C`).  Used by (6.2): a member `ψ = Ind_H^L θ ∈ S(B)` has
source `θ` trivial on `B`, so `Res_C θ` is trivial on `B.subgroupOf C`, discharging the `θ`-bound's
kernel hypothesis. -/
theorem characterKernel_restrict_subgroupOf {K : Type*} [Group K] {θ : ClassFunction K ℂ}
    (C : Subgroup K) {M : Subgroup K}
    (hM : (M : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel θ) :
    ((M.subgroupOf C : Subgroup ↥C) : Set ↥C) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.restrict C θ) := by
  intro c hc
  have hker : (θ : ClassFunction K ℂ) (↑c : K) = (θ : ClassFunction K ℂ) 1 :=
    hM (Subgroup.mem_subgroupOf.mp hc)
  simp only [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def, ClassFunction.restrict_apply,
    OneMemClass.coe_one]
  exact hker

set_option linter.unusedFintypeInType false in
/-- **(H2, kernel form)** an irreducible constituent `χ` of an induced character `Ind_H^Γ θ`
(`θ` genuine, `⟨Ind θ, χ⟩ ≠ 0`) inherits a kernel containment of `Ind θ`.  The `ℕ`-decomposition
`induce_exists_natFinsupp_eq_sum` feeds `characterKernel_subset_of_natFinsupp_eq_sum`. -/
theorem characterKernel_subset_of_inner_induce_ne_zero {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] {θ : ClassFunction ↥H ℂ} (hθ : IsCharacter θ)
    {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ)
    (hχψ : ClassFunction.inner (ClassFunction.induce H θ) χ ≠ 0)
    {g : Γ} (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce H θ)) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := induce_exists_natFinsupp_eq_sum hθ
  have hmχ : m χ ≠ 0 := fun h0 => hχψ (by rw [← hcoeff χ hχ, h0, Nat.cast_zero])
  exact characterKernel_subset_of_natFinsupp_eq_sum hsupp hsum hχ hmχ hg

/- 6: Some coherence theorems (pp. 30-37) -/

/-- **Finite set of irreducible characters → injective `Fin k` enumeration.**  A finite set `T` of
class functions all of which are irreducible characters is enumerated by an injective family
`χ : Fin k → IrreducibleCharacter Γ` whose underlying-class-function range is exactly `T`.  This is
the bridge to the `Fin n`-indexed family interface of `coherentEqualDegree_fromDade` (the base
block `S₀`). -/
theorem exists_finEnum_irreducible {Γ : Type*} [Group Γ] {T : Set (ClassFunction Γ ℂ)}
    (hTfin : T.Finite) (hTirr : ∀ χ ∈ T, IsIrreducibleCharacter χ) :
    ∃ (k : ℕ) (χ : Fin k → IrreducibleCharacter Γ),
      Function.Injective χ ∧ Set.range (fun j => (χ j : ClassFunction Γ ℂ)) = T := by
  classical
  haveI : Fintype T := hTfin.fintype
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun j => ⟨(e.symm j : ClassFunction Γ ℂ), hTirr _ (e.symm j).2⟩, ?_, ?_⟩
  · intro i j hij
    have h : (e.symm i : ClassFunction Γ ℂ) = (e.symm j : ClassFunction Γ ℂ) :=
      congrArg (fun c : IrreducibleCharacter Γ => (c : ClassFunction Γ ℂ)) hij
    exact e.symm.injective (Subtype.ext h)
  · ext φ
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).2
    · intro hφ
      exact ⟨e ⟨φ, hφ⟩, by simp⟩

/-- Reindex a sum over the `Finset` of a range by the indexing family: for an injective `f` over a
finite domain, `∑_{x ∈ (Set.range f).toFinset} g x = ∑ j, g (f j)`.  Used to turn the `S₁`-set
degree-square sum of the (6.2) bound into the `Fin k` member-family sum produced by B1. -/
theorem sum_toFinset_range_eq {α β M : Type*} [Fintype α] [DecidableEq β] [AddCommMonoid M]
    {f : α → β} (hinj : Function.Injective f) (g : β → M) :
    ∑ x ∈ (Set.range f).toFinset, g x = ∑ j, g (f j) := by
  rw [Set.toFinset_range, Finset.sum_image (fun a _ b _ h => hinj h)]

/-- **(T8 leaf 10, combinatorial core) the conjugate-pair cover of `X` over a base `S₀`.**

Given a finite set `X` of irreducible characters of `Γ`, closed under conjugation and with no real
characters (Peterfalvi (1.1): for `|Γ|` odd a nontrivial irreducible is non-self-conjugate), and a
conjugation-closed base `S₀ ⊆ X`, the complement `X ∖ S₀` is a disjoint union of conjugate pairs
`{χ, χ̄}`.  This packages the data and facts consumed by `peterfalvi_66_coherence_of_X_from_dade`:
the degree-monotone enumeration `e` (`exists_monotoneDegreeEnum`), the pair list `pair`/`N` with its
irreducible first components `hpairχ`, the inclusions and index-level cover, plus the two facts the
per-step (5.6) `DadeChainStep` needs — each adjoined pair is **disjoint from the prefix**
`pairUnion S₀ pair j` (so `χⱼ, χ̄ⱼ ⊥ S₁`) and **degree-monotone** (so the (5.6) degree gap
can hold).

Construction: the conjugate-index involution `cidx i` (`e (cidx i) = (e i).conj`, fixed-point-free
by no-real, preserving `∉ S₀`), the index transversal `T = {i | e i ∉ S₀ ∧ i < cidx i}` sorted by
`Finset.orderEmbOfFin`, and `pair j = (e tⱼ, (e tⱼ).conj)` for the `j`-th transversal index `tⱼ`. -/
theorem exists_conjugatePairCover {Γ : Type*} [Group Γ]
    {X S₀ : Set (ClassFunction Γ ℂ)}
    (hXfin : X.Finite)
    (hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate X)
    (hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters X)
    (hXirr : ∀ χ ∈ X, IsIrreducibleCharacter χ)
    (hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₀) :
    ∃ (e : Fin X.ncard → ClassFunction Γ ℂ)
      (pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ) (N : ℕ)
      (hpairχ : ∀ i, i < N → IrreducibleCharacter Γ),
      (∀ χ ∈ X, ∃ i, e i = χ) ∧
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j ⊆ X) ∧
      (∀ i : Fin X.ncard, e i ∈ S₀ ∨
        ∃ j, j < N ∧ e i ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j) ∧
      (∀ (i : ℕ) (hi : i < N),
        (pair i).1 = ((hpairχ i hi : IrreducibleCharacter Γ) : ClassFunction Γ ℂ)) ∧
      (∀ (i : ℕ) (hi : i < N),
        (pair i).2 = ((hpairχ i hi : IrreducibleCharacter Γ) : ClassFunction Γ ℂ).conj) ∧
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair j)) ∧
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) := by
  classical
  obtain ⟨e, he_inj, he_mem, he_surj, he_mono⟩ :=
    OddOrder.Peterfalvi.S07.exists_monotoneDegreeEnum (L := Γ) hXfin
  -- conjugate-index involution `cidx`
  have hconjX : ∀ i, (e i).conj ∈ X := fun i => hXconj (he_mem i)
  let cidx : Fin X.ncard → Fin X.ncard := fun i => (he_surj _ (hconjX i)).choose
  have hcidx : ∀ i, e (cidx i) = (e i).conj := fun i => (he_surj _ (hconjX i)).choose_spec
  have hcidx_invol : ∀ i, cidx (cidx i) = i := fun i =>
    he_inj (by rw [hcidx (cidx i), hcidx i, ClassFunction.conj_conj])
  have hcidx_inj : Function.Injective cidx := fun a b h => by
    rw [← hcidx_invol a, h, hcidx_invol b]
  have hcidx_ne : ∀ i, cidx i ≠ i := by
    intro i hfix
    apply hXreal (he_mem i)
    show (e i).conj = e i
    rw [← hcidx i, hfix]
  have hcidx_notS₀ : ∀ {i}, e i ∉ S₀ → e (cidx i) ∉ S₀ := by
    intro i hi hc
    rw [hcidx i] at hc
    exact hi (by simpa using hS₀conj hc)
  -- index transversal `T`, enumerated by `orderEmbOfFin`
  let T : Finset (Fin X.ncard) := Finset.univ.filter (fun i => e i ∉ S₀ ∧ i < cidx i)
  let t : Fin T.card → Fin X.ncard := fun j => T.orderEmbOfFin rfl j
  have htmono : StrictMono t := (T.orderEmbOfFin rfl).strictMono
  have ht_mem : ∀ j, t j ∈ T := fun j => T.orderEmbOfFin_mem rfl j
  have ht_spec : ∀ j, e (t j) ∉ S₀ ∧ t j < cidx (t j) := fun j =>
    (Finset.mem_filter.mp (ht_mem j)).2
  have ht_range : ∀ i ∈ T, ∃ j, t j = i := by
    intro i hi
    have hmem : i ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hi
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj⟩
  -- the pair list
  let pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ := fun j =>
    if hj : j < T.card then (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) else (0, 0)
  have hpair_eq : ∀ (j : ℕ) (hj : j < T.card),
      pair j = (e (t ⟨j, hj⟩), (e (t ⟨j, hj⟩)).conj) := fun j hj => dif_pos hj
  have hfst : ∀ (j : ℕ) (hj : j < T.card), (pair j).1 = e (t ⟨j, hj⟩) := by
    intro j hj; rw [hpair_eq j hj]
  have hsnd : ∀ (j : ℕ) (hj : j < T.card), (pair j).2 = e (cidx (t ⟨j, hj⟩)) := by
    intro j hj; rw [hpair_eq j hj]; exact (hcidx _).symm
  refine ⟨e, pair, T.card, fun i hi => ⟨e (t ⟨i, hi⟩), hXirr _ (he_mem _)⟩,
    he_surj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- each pair lies in `X`
    intro j hj φ hφ
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφ
    rcases hφ with rfl | rfl
    · exact he_mem _
    · exact he_mem _
  · -- index-level cover
    intro i
    by_cases hiS₀ : e i ∈ S₀
    · exact Or.inl hiS₀
    · refine Or.inr ?_
      rcases lt_or_gt_of_ne (hcidx_ne i) with hlt | hgt
      · -- `cidx i < i` ⟹ `cidx i ∈ T`, and `e i` is the second component of its pair
        have hcT : cidx i ∈ T := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcidx_notS₀ hiS₀, by rw [hcidx_invol]; exact hlt⟩
        obtain ⟨j, hj⟩ := ht_range _ hcT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inr ?_
        rw [hsnd j.val j.isLt]
        have hci : cidx (t ⟨j.val, j.isLt⟩) = i := by
          rw [(hj : t ⟨j.val, j.isLt⟩ = cidx i)]; exact hcidx_invol i
        rw [hci]
      · -- `i < cidx i` ⟹ `i ∈ T`, and `e i` is the first component of its pair
        have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS₀, hgt⟩
        obtain ⟨j, hj⟩ := ht_range _ hiT
        refine ⟨j.val, j.isLt, ?_⟩
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        refine Or.inl ?_
        rw [hfst j.val j.isLt]
        exact congrArg e hj.symm
  · -- `(pair i).1 = χᵢ`
    intro i hi; rw [hfst i hi]
  · -- `(pair i).2 = χ̄ᵢ`
    intro i hi; rw [hsnd i hi, hcidx]
  · -- each pair is disjoint from the prefix accumulated before it
    intro j hj
    rw [Set.disjoint_left]
    intro φ hφj hφu
    rw [OddOrder.Peterfalvi.S07.mem_pairUnion] at hφu
    simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      hfst j hj, hsnd j hj] at hφj
    rcases hφu with hS₀mem | ⟨k, hkj, hφk⟩
    · rcases hφj with rfl | rfl
      · exact (ht_spec ⟨j, hj⟩).1 hS₀mem
      · exact hcidx_notS₀ (ht_spec ⟨j, hj⟩).1 hS₀mem
    · have hk : k < T.card := hkj.trans hj
      simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff, Set.mem_singleton_iff,
        hfst k hk, hsnd k hk] at hφk
      have htlt : t ⟨k, hk⟩ < t ⟨j, hj⟩ := htmono (Fin.mk_lt_mk.mpr hkj)
      have hjT := (ht_spec ⟨j, hj⟩).2
      rcases hφj with hj1 | hj1 <;> rcases hφk with hk1 | hk1
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
      · have heq : t ⟨j, hj⟩ = cidx (t ⟨k, hk⟩) := he_inj (hj1.symm.trans hk1)
        have hc : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := by rw [heq, hcidx_invol]
        rw [hc] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have heq : cidx (t ⟨j, hj⟩) = t ⟨k, hk⟩ := he_inj (hj1.symm.trans hk1)
        rw [heq] at hjT; exact absurd (hjT.trans htlt) (lt_irrefl _)
      · have hee : t ⟨j, hj⟩ = t ⟨k, hk⟩ := hcidx_inj (he_inj (hj1.symm.trans hk1))
        rw [hee] at htlt; exact absurd htlt (lt_irrefl _)
  · -- adjacent pairs are degree-monotone
    intro j hj1
    have hj : j < T.card := by omega
    rw [hfst j hj, hfst (j + 1) hj1]
    exact he_mono (htmono.monotone (Fin.mk_le_mk.mpr (by omega)))

/-- A predicate true at `0` and false at `N` must flip somewhere: there is an index `i < N` with
`P i` true and `P (i + 1)` false.  (Discrete first-failure / boundary extraction, by induction on
`N`.) -/
theorem exists_index_predicate_break {P : ℕ → Prop} (h0 : P 0) :
    ∀ N, ¬ P N → ∃ i, i < N ∧ P i ∧ ¬ P (i + 1)
  | 0, hN => absurd h0 hN
  | N + 1, hN => by
    by_cases hPN : P N
    · exact ⟨N, Nat.lt_succ_self N, hPN, hN⟩
    · obtain ⟨i, hiN, hPi, hnPi⟩ := exists_index_predicate_break h0 N hPN
      exact ⟨i, hiN.trans (Nat.lt_succ_self N), hPi, hnPi⟩

open scoped Classical in
/-- **First obstruction to coherence — the Peterfalvi (6.2) `S₁`/`S₂` decomposition.**

Given conjugation-closed sets `Sa ⊆ Sb` of irreducible characters of `↥L`, with `Sb` finite and
real-free, if `Sa` is coherent for an integral character map `τ` (on the support set `A`) but `Sb`
is not, then there is an intermediate conjugation-closed set `S₁` (`Sa ⊆ S₁ ⊆ Sb`) and a character
`ψ ∈ Sb` such that `S₁` is coherent but adjoining the conjugate pair `{ψ, ψ̄}` destroys coherence:
`S₁ ∪ {ψ, ψ̄}` is not coherent.

This is the decomposition cited at the start of the (6.2) proof ("By (b), there are sets `S₁` and
`S₂ = {ψ, ψ̄}` … such that `S₁` is coherent but `S₁ ∪ S₂` is not coherent").  Construction:
enumerate `Sb ∖ Sa` as conjugate pairs (`exists_conjugatePairCover`), so the running union
`pairUnion Sa pair i` rises from `Sa` (coherent) to `Sb` (not), and take the first pair whose
adjunction breaks coherence (`exists_index_predicate_break`). -/
theorem exists_coherentBreakPair
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) {A : Set ↥L}
    {Sa Sb : Set (ClassFunction ↥L ℂ)}
    (hsub : Sa ⊆ Sb) (hSbfin : Sb.Finite)
    (hSbconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sb)
    (hSbreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sb)
    (hSbirr : ∀ χ ∈ Sb, IsIrreducibleCharacter χ)
    (hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sa)
    (hSacoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sa A))
    (hSbncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sb A)) :
    ∃ (S₁ : Set (ClassFunction ↥L ℂ)) (ψ : ClassFunction ↥L ℂ),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ ∧ Sa ⊆ S₁ ∧ S₁ ⊆ Sb ∧ ψ ∈ Sb ∧
      ψ ∉ S₁ ∧ ψ.conj ∉ S₁ ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A) ∧
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A) := by
  classical
  obtain ⟨e, pair, N, hpairχ, hsurj, hpairs, hcoverIdx, hpair0, hpair1, hdisj, _hmono⟩ :=
    exists_conjugatePairCover hSbfin hSbconj hSbreal hSbirr hSaconj
  -- the running union reaches `Sb` after `N` steps
  have hUN : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N = Sb :=
    OddOrder.Peterfalvi.S07.pairUnion_eq_of_enumCover hsurj hsub hpairs hcoverIdx
  -- the coherence predicate along the chain rises from `Sa` (true) to `Sb` (false)
  have hP0 : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair 0) A) := by
    rw [OddOrder.Peterfalvi.S07.pairUnion_zero]; exact hSacoh
  have hPN : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair N) A) := by
    rw [hUN]; exact hSbncoh
  obtain ⟨i, hiN, hPi, hnPi⟩ := exists_index_predicate_break
    (P := fun i => Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i) A)) hP0 N hPN
  -- the breaking pair `{ψ, ψ̄}` lies in `Sb` and is disjoint from the prefix `S₁`
  have hψpair : (pair i).1 ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet]
  have hconj2 : (pair i).2 = ((pair i).1).conj := by rw [hpair1 i hiN, hpair0 i hiN]
  have hψcpair : ((pair i).1).conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    rw [← hconj2]; simp [OddOrder.Peterfalvi.S07.pairSet]
  refine ⟨OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i, (pair i).1,
    ?_, ?_, ?_, hpairs i hiN hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψpair,
    Set.disjoint_left.mp (hdisj i hiN) hψcpair, hPi, ?_⟩
  · -- `S₁` is closed under conjugation (base `Sa` is, each adjoined pair is)
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hSaconj hbase))
    · have hjN : j < N := hji.trans hiN
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ' | hφ'
        · right; rw [hφ', hpair0 j hjN, hpair1 j hjN]
        · left; rw [hφ', hpair1 j hjN, hpair0 j hjN]; simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  · -- `Sa ⊆ S₁`
    exact fun φ hφ => OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hφ)
  · -- `S₁ ⊆ Sb`
    rw [← hUN]; exact OddOrder.Peterfalvi.S07.pairUnion_mono Sa pair hiN.le
  · -- `S₁ ∪ {ψ, ψ̄}` is not coherent (it is the next accumulator, where coherence fails)
    have hsplit : OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair (i + 1) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) Sa pair i ∪ {(pair i).1, ((pair i).1).conj} :=
      OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair rfl hconj2
    rw [← hsplit]; exact hnPi

/-- **In a finite nilpotent group, a nontrivial normal subgroup meets the centre.**
If `N ◁ G` is nontrivial and `G` is finite nilpotent, then `N ⊓ Z(G) ≠ ⊥`.  Proof: take the least
`m` with `N ⊓ ζₘ ≠ ⊥` (the upper central series reaches `⊤`, so `m` exists; `m = k+1 > 0`); a
nontrivial `x ∈ N ⊓ ζ_{k+1}` has `x·y·x⁻¹·y⁻¹ ∈ ζₖ` (definition of `ζ_{k+1}`) and `∈ N` (`N`
normal), so `∈ N ⊓ ζₖ = ⊥` by minimality; hence `x` is central, `x ∈ N ⊓ Z(G)`.

This is the nilpotency central step of Peterfalvi (6.3): `H/M` nilpotent and `A/B` a nontrivial
normal subgroup give `(A/B) ⊓ Z(H/B) ≠ 1`, which (with maximality of `B`) forces `A/B ⊆ Z(H/B)`. -/
theorem isNilpotent_normal_inf_center_ne_bot {Γ : Type*} [Group Γ] [Finite Γ]
    [Group.IsNilpotent Γ] {N : Subgroup Γ} (hN : N.Normal) (hNne : N ≠ ⊥) :
    N ⊓ Subgroup.center Γ ≠ ⊥ := by
  classical
  have hexists : ∃ i, N ⊓ upperCentralSeries Γ i ≠ ⊥ := by
    refine ⟨Group.nilpotencyClass Γ, ?_⟩
    rw [upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr (le_refl _), inf_top_eq]
    exact hNne
  have hm := Nat.find_spec hexists
  have hm0 : Nat.find hexists ≠ 0 := by
    intro h0
    rw [h0, upperCentralSeries_zero, inf_bot_eq] at hm
    exact hm rfl
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hkbot : N ⊓ upperCentralSeries Γ k = ⊥ := by
    by_contra h
    exact Nat.find_min hexists (m := k) (by rw [hk_eq]; exact Nat.lt_succ_self k) h
  rw [hk_eq] at hm
  obtain ⟨⟨x, hxmem⟩, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hm
  have hx1 : x ≠ 1 := fun h => hxne (Subtype.ext h)
  rw [Subgroup.mem_inf] at hxmem
  obtain ⟨hxN, hxU⟩ := hxmem
  have hxcenter : x ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hcomm_U : x * y * x⁻¹ * y⁻¹ ∈ upperCentralSeries Γ k :=
      mem_upperCentralSeries_succ_iff.mp hxU y
    have hcomm_N : x * y * x⁻¹ * y⁻¹ ∈ N := by
      have hconj : y * x⁻¹ * y⁻¹ ∈ N := hN.conj_mem x⁻¹ (N.inv_mem hxN) y
      have := N.mul_mem hxN hconj
      rwa [← mul_assoc, ← mul_assoc] at this
    have hbot : x * y * x⁻¹ * y⁻¹ = 1 := by
      have hin : x * y * x⁻¹ * y⁻¹ ∈ N ⊓ upperCentralSeries Γ k :=
        Subgroup.mem_inf.mpr ⟨hcomm_N, hcomm_U⟩
      rw [hkbot, Subgroup.mem_bot] at hin
      exact hin
    have h2 : x * y * x⁻¹ = y := mul_inv_eq_one.mp hbot
    conv_lhs => rw [← h2]
    group
  intro hbot
  have : x ∈ N ⊓ Subgroup.center Γ := Subgroup.mem_inf.mpr ⟨hxN, hxcenter⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hx1 this

/-- **A maximal normal subgroup strictly between `M` and `A`.**
For a finite group, if `M < A` (with `M` normal) there is a normal `B` with `M ≤ B < A` that is
maximal with this property: any normal `C` with `B ≤ C < A` equals `B`.  This is the maximal-`B`
step of the Peterfalvi (6.3) minimal-`A` induction (find a maximal proper normal subgroup below the
minimal coherent `A`). -/
theorem exists_maximal_normal_between {Γ : Type*} [Group Γ] [Finite Γ] {M A : Subgroup Γ}
    [M.Normal] (hMA : M < A) :
    ∃ B : Subgroup Γ, B.Normal ∧ M ≤ B ∧ B < A ∧
      ∀ C : Subgroup Γ, C.Normal → B ≤ C → C < A → C = B := by
  classical
  haveI : Finite (Subgroup Γ) := Finite.of_injective (fun H : Subgroup Γ => (H : Set Γ))
    (fun _ _ h => SetLike.coe_injective h)
  obtain ⟨B, hBmem, hBmax⟩ :=
    Set.Finite.exists_maximalFor (id : Subgroup Γ → Subgroup Γ)
      {N | N.Normal ∧ M ≤ N ∧ N < A} (Set.toFinite _) ⟨M, ‹M.Normal›, le_refl M, hMA⟩
  obtain ⟨hBnorm, hMB, hBA⟩ := hBmem
  refine ⟨B, hBnorm, hMB, hBA, fun C hCnorm hBC hCA => ?_⟩
  exact le_antisymm (hBmax ⟨hCnorm, hMB.trans hBC, hCA⟩ hBC) hBC

/-- **Maximality forces centrality** — the central step of Peterfalvi (6.3).

If `H ◁ Γ` is nilpotent and `A`, `B` are normal subgroups of `Γ` with `B < A ≤ H`, where `B` is
maximal among normal subgroups of `Γ` strictly below `A`, then `A/B ⊆ Z(H/B)`.

Indeed `A/B` is a nontrivial normal subgroup of the nilpotent group `H/B`, so `(A/B) ⊓ Z(H/B) ≠ 1`
(`isNilpotent_normal_inf_center_ne_bot`).  Its full preimage `C` in `Γ` is a normal subgroup with
`B < C ≤ A` (`C` is normal because conjugation by `Γ` preserves both `A/B` and the centre of `H/B`);
by maximality of `B`, `C = A`, i.e. `A/B ⊆ Z(H/B)`.

This discharges the `hcentral` hypothesis of `six_three_index_bound` in the minimal-`A`/maximal-`B`
induction of Peterfalvi (6.3). -/
theorem normal_central_of_maximal_normal_below {Γ : Type*} [Group Γ] [Finite Γ]
    {H A B : Subgroup Γ} (hH : H.Normal) [Group.IsNilpotent ↥H]
    [A.Normal] [B.Normal] (hAH : A ≤ H) (hBA : B < A)
    (hmax : ∀ C : Subgroup Γ, C.Normal → B ≤ C → C < A → C = B) :
    (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H) := by
  classical
  haveI hNnorm : (B.subgroupOf H).Normal := (‹B.Normal›).subgroupOf H
  haveI hANnorm : (A.subgroupOf H).Normal := (‹A.Normal›).subgroupOf H
  have hBH : B ≤ H := hBA.le.trans hAH
  -- `mk' (B.subgroupOf H) a = 1 ↔ a ∈ B.subgroupOf H`
  have mk_eq_one : ∀ a : ↥H,
      QuotientGroup.mk' (B.subgroupOf H) a = 1 ↔ a ∈ B.subgroupOf H := by
    intro a; rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  -- centrality of `mk' x` ⟺ all commutators `h x h⁻¹ x⁻¹` land in `B.subgroupOf H`
  have center_iff : ∀ x : ↥H,
      QuotientGroup.mk' (B.subgroupOf H) x ∈ Subgroup.center (↥H ⧸ B.subgroupOf H) ↔
        ∀ h : ↥H, h * x * h⁻¹ * x⁻¹ ∈ B.subgroupOf H := by
    intro x
    rw [Subgroup.mem_center_iff]
    refine ⟨fun hx h => ?_, fun hx q => ?_⟩
    · have h2 := hx (QuotientGroup.mk' (B.subgroupOf H) h)
      rw [← mk_eq_one]
      simp only [map_mul, map_inv]
      rw [h2]; group
    · obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf H) q
      have hcomm := (mk_eq_one (h * x * h⁻¹ * x⁻¹)).2 (hx h)
      simp only [map_mul, map_inv] at hcomm
      calc QuotientGroup.mk' (B.subgroupOf H) h * QuotientGroup.mk' (B.subgroupOf H) x
          = (QuotientGroup.mk' (B.subgroupOf H) h * QuotientGroup.mk' (B.subgroupOf H) x *
              (QuotientGroup.mk' (B.subgroupOf H) h)⁻¹ *
              (QuotientGroup.mk' (B.subgroupOf H) x)⁻¹) *
              (QuotientGroup.mk' (B.subgroupOf H) x * QuotientGroup.mk' (B.subgroupOf H) h) := by
            group
        _ = QuotientGroup.mk' (B.subgroupOf H) x * QuotientGroup.mk' (B.subgroupOf H) h := by
            rw [hcomm, one_mul]
  -- `A/B` is nontrivial in `H/B`
  have hAbar_ne : (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have hAB : A ≤ B := by
      intro y hy
      have hy' : (⟨y, hAH hy⟩ : ↥H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
      exact Subgroup.mem_subgroupOf.mp (hbot hy')
    exact lt_irrefl _ (hBA.trans_le hAB)
  -- nilpotency: `(A/B) ⊓ Z(H/B) ≠ 1`
  have hinf := isNilpotent_normal_inf_center_ne_bot
    (Subgroup.Normal.map hANnorm (QuotientGroup.mk' (B.subgroupOf H))
      (QuotientGroup.mk'_surjective _)) hAbar_ne
  -- the pullback subgroup of `Γ`
  set Zc := (Subgroup.center (↥H ⧸ B.subgroupOf H)).comap (QuotientGroup.mk' (B.subgroupOf H))
    with hZc
  set CH := A.subgroupOf H ⊓ Zc with hCH
  set C := CH.map H.subtype with hC
  -- `B ≤ C`
  have hBC : B ≤ C := by
    rw [hC, ← Subgroup.map_subgroupOf_eq_of_le hBH]
    apply Subgroup.map_mono
    rw [hCH]
    refine le_inf (Subgroup.subgroupOf_mono H hBA.le) (fun x hx => ?_)
    rw [hZc, Subgroup.mem_comap, (mk_eq_one x).2 hx]
    exact Subgroup.one_mem _
  -- `C ≤ A`
  have hCA : C ≤ A := by
    rw [hC, ← Subgroup.map_subgroupOf_eq_of_le hAH]
    exact Subgroup.map_mono (by rw [hCH]; exact inf_le_left)
  -- `C` is normal in `Γ`
  have hCnorm : C.Normal := by
    rw [hC]
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_map] at hn
    obtain ⟨c, hcCH, rfl⟩ := hn
    rw [hCH, Subgroup.mem_inf] at hcCH
    obtain ⟨hcA, hcZ⟩ := hcCH
    have hc_center : ∀ k : ↥H, k * c * k⁻¹ * c⁻¹ ∈ B.subgroupOf H := by
      apply (center_iff c).mp
      rw [hZc] at hcZ; exact Subgroup.mem_comap.mp hcZ
    have hc'H : g * (c : Γ) * g⁻¹ ∈ H := hH.conj_mem _ c.2 g
    rw [Subgroup.mem_map]
    refine ⟨⟨g * (c : Γ) * g⁻¹, hc'H⟩, ?_, rfl⟩
    rw [hCH, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (‹A.Normal›).conj_mem _ (Subgroup.mem_subgroupOf.mp hcA) g
    · rw [hZc, Subgroup.mem_comap, center_iff]
      intro h
      have hkH : g⁻¹ * (h : Γ) * g ∈ H := by
        have := hH.conj_mem (h : Γ) h.2 g⁻¹; rwa [inv_inv] at this
      have hk := hc_center ⟨g⁻¹ * (h : Γ) * g, hkH⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      have hrel : (((h * ⟨g * (c : Γ) * g⁻¹, hc'H⟩ * h⁻¹ *
            (⟨g * (c : Γ) * g⁻¹, hc'H⟩ : ↥H)⁻¹ : ↥H) : Γ))
          = g * (((⟨g⁻¹ * (h : Γ) * g, hkH⟩ * c *
              (⟨g⁻¹ * (h : Γ) * g, hkH⟩ : ↥H)⁻¹ * c⁻¹ : ↥H) : Γ)) * g⁻¹ := by
        push_cast
        group
      rw [hrel]
      exact (‹B.Normal›).conj_mem _ hk g
  -- a nontrivial element of `(A/B) ⊓ Z(H/B)` gives `B ≠ C`
  obtain ⟨⟨q, hqmem⟩, hqne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  rw [Subgroup.mem_inf] at hqmem
  obtain ⟨hqA, hqZ⟩ := hqmem
  rw [Subgroup.mem_map] at hqA
  obtain ⟨c₀, hc₀A, hc₀q⟩ := hqA
  have hq1 : q ≠ 1 := fun hq => hqne (Subtype.ext hq)
  have hc₀CH : c₀ ∈ CH := by
    rw [hCH, Subgroup.mem_inf]
    exact ⟨hc₀A, by rw [hZc, Subgroup.mem_comap, hc₀q]; exact hqZ⟩
  have hc₀C : (c₀ : Γ) ∈ C := by
    rw [hC]; exact Subgroup.mem_map_of_mem H.subtype hc₀CH
  have hc₀notB : (c₀ : Γ) ∉ B := by
    intro hb
    exact hq1 (by rw [← hc₀q]; exact (mk_eq_one c₀).2 (Subgroup.mem_subgroupOf.mpr hb))
  have hBneC : B ≠ C := fun heq => hc₀notB (heq.symm ▸ hc₀C)
  have hBC_lt : B < C := lt_of_le_of_ne hBC hBneC
  have hCeqA : C = A := by
    rcases eq_or_lt_of_le hCA with h | h
    · exact h
    · exact absurd (hmax C hCnorm hBC h) (Ne.symm (ne_of_lt hBC_lt))
  have hCHmap : CH.map H.subtype = A := by rw [← hC, hCeqA]
  have hCHeq : CH = A.subgroupOf H := by
    rw [← Subgroup.map_subtype_inj, hCHmap, Subgroup.map_subgroupOf_eq_of_le hAH]
  have hle : A.subgroupOf H ≤ Zc := by
    rw [← hCHeq, hCH]; exact inf_le_right
  rw [Subgroup.map_le_iff_le_comap, ← hZc]
  exact hle

/-- For `H ≤ G`, the commutator subgroup of the subtype group `↥H` is the `subgroupOf` of the
ambient commutator `⁅H, H⁆`.  In particular `Abelianization ↥H = ↥H ⧸ ⁅H, H⁆.subgroupOf H`, so the
index `|H : ⁅H,H⁆|` equals `|Abelianization ↥H|`. -/
theorem commutator_subgroupOf_self {G : Type*} [Group G] (H : Subgroup G) :
    (⁅H, H⁆ : Subgroup G).subgroupOf H = _root_.commutator ↥H := by
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : (_root_.commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    show (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆).map H.subtype = ⁅H, H⁆
    rw [Subgroup.map_commutator, htop]
  rw [← h1]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

/-- For a finite `p`-group `K`, every irreducible character has degree a power of `p`
(its degree divides `|K| = pⁿ`).  This supplies the `θ = p^m` source-degree fields of the X-chain
step data once `H` is known to be a `p`-group (Peterfalvi (6.5)/(6.6)). -/
theorem exists_primePow_natDegree_of_isPGroup {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsPGroup p K) (θ : IrreducibleCharacter K) :
    ∃ k : ℕ, (θ : ClassFunction K ℂ) 1 = ((p ^ k : ℕ) : ℂ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, _hpos, hval, hdvd⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  obtain ⟨N, hN⟩ := hK.exists_card_eq
  rw [hN] at hdvd
  obtain ⟨k, _hk_le, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨k, by rw [hval, hk]⟩

/-- A nontrivial finite `p`-group of odd order has `p ≥ 3` (its order `pⁿ` is odd, so `p` is odd).
Supplies the `3 ≤ p` field of the X-chain step data (in the (6.8) setup `|L|`, hence `|H|`, is
odd). -/
theorem three_le_prime_of_isPGroup_of_odd {K : Type*} [Group K] [Finite K] [Nontrivial K]
    {p : ℕ} (hp : p.Prime) (hK : IsPGroup p K) (hodd : Odd (Nat.card K)) : 3 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hcard : Nat.card K ≠ 1 := by
    simpa using (Finite.one_lt_card (α := K)).ne'
  have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; exact hcard hn
  have hpdvd : p ∣ Nat.card K := hn ▸ dvd_pow_self p hn0
  obtain ⟨m, hm⟩ := Odd.of_dvd_nat hodd hpdvd
  have := hp.two_le
  omega

/-- A quotient of a finite `p`-group is a `p`-group, so its order is a power of `p`.  In the (6.6)
setup this gives `|H:Z| = p^k` (`H` a `p`-group), the key to `θχ(1)² ∣ |H:Z|` (both `p`-powers). -/
theorem exists_primePow_card_quotient_of_isPGroup {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsPGroup p K) (N : Subgroup K) [N.Normal] :
    ∃ k : ℕ, Nat.card (K ⧸ N) = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (hK.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).exists_card_eq

/-- Peterfalvi (6.1): the filtration `S(A)` attached to the base character set
`S`.  In the text, larger kernel conditions give smaller subsets:
if `A ≤ B`, then `S(B) ⊆ S(A)`. -/
structure FiltrationData (S : Set (ClassFunction L ℂ)) where
  carrier : Subgroup L → Set (ClassFunction L ℂ)
  subset_base : ∀ A, carrier A ⊆ S
  mono : ∀ ⦃A B : Subgroup L⦄, A ≤ B → carrier B ⊆ carrier A

namespace FiltrationData

variable {S : Set (ClassFunction L ℂ)}

theorem subset_base_apply (F : FiltrationData (L := L) S) (A : Subgroup L) :
    F.carrier A ⊆ S :=
  F.subset_base A

theorem mem_base (F : FiltrationData (L := L) S) {A : Subgroup L}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ F.carrier A) : χ ∈ S :=
  F.subset_base A hχ

theorem mono_apply (F : FiltrationData (L := L) S) {A B : Subgroup L}
    (hAB : A ≤ B) : F.carrier B ⊆ F.carrier A :=
  F.mono hAB

theorem zSupportedSpan_subset_base (F : FiltrationData (L := L) S)
    (A : Subgroup L) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S B := by
  intro φ hφ
  exact OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left (L := L)
    (F.subset_base A) hφ

theorem zSupportedSpan_mono_apply (F : FiltrationData (L := L) S)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A₂) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A₁) B := by
  intro φ hφ
  exact OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left (L := L)
    (F.mono hA) hφ

end FiltrationData

/-- Peterfalvi (6.1): solvable-normal filtration setup for applying coherence
descent. -/
structure DescentHypothesis (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  coherence : OddOrder.Peterfalvi.S07.Hypothesis (L := L) (G := G) S A
  K : Subgroup L
  K_normal : K.Normal
  K_solvable : IsSolvable K
  filtration : FiltrationData (L := L) S

namespace DescentHypothesis

variable {S : Set (ClassFunction L ℂ)} {A : Set L}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

theorem filtration_subset_base (hyp : DescentHypothesis (L := L) (G := G) S A)
    (A' : Subgroup L) : hyp.filtration.carrier A' ⊆ S :=
  hyp.filtration.subset_base A'

theorem filtration_mem_base (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A' : Subgroup L} {χ : ClassFunction L ℂ}
    (hχ : χ ∈ hyp.filtration.carrier A') : χ ∈ S :=
  hyp.filtration.mem_base hχ

theorem filtration_mono (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) :
    hyp.filtration.carrier A₂ ⊆ hyp.filtration.carrier A₁ :=
  hyp.filtration.mono hA

theorem filtration_zSupportedSpan_subset_base
    (hyp : DescentHypothesis (L := L) (G := G) S A)
    (A' : Subgroup L) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A') B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S B :=
  hyp.filtration.zSupportedSpan_subset_base A' B

theorem filtration_zSupportedSpan_mono
    (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A₂) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A₁) B :=
  hyp.filtration.zSupportedSpan_mono_apply hA B

end DescentHypothesis

/-- Peterfalvi (6.4): the odd-order specialization used before (6.5)-(6.6). -/
structure OddOrderSpecialization (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] : Type _ extends
    DescentHypothesis (L := L) (G := G) S A where
  card_L_odd : Odd (Nat.card L)
  M : Subgroup L
  M_le_K : M ≤ K
  quotient_nilpotent : Prop

-- The legacy `SibleySetup`/`CoherenceTarget` (which carried an opaque `coherence.tau` with a
-- *global* `IsIntegralIsometry`, nonexistent in Feit–Thompson) is replaced by the Dade-based
-- `SibleyDadeHypothesis` below (T1; see issue 0046 / notes/peterfalvi/s08_6_8_assembly_plan.md).

/-- `H^# = H ∖ {1}` viewed as a subset of the ambient group `G`, for `H ≤ L ≤ G`.  This is the
support set `A` of the §4 Dade hypothesis in Peterfalvi (6.8): the nonidentity elements of `H`,
mapped from `↥L` into `G` along the inclusions. -/
def sharpImage {G : Type*} [Group G] {L : Subgroup G} (H : Subgroup ↥L) : Set G :=
  ((Subgroup.map L.subtype H : Subgroup G) : Set G) \ {1}

/-- **(5.6.1) supported-difference pairing: the Dade map `τ` pairs with the coherent extension `ν`
as the source inner product.**

For a supported `u` (`u.support ⊆ A`, e.g. the degree-matched difference `χ − a·χ₁`) and a
*supported* lattice element `δ ∈ ℤ[S₁] ∩ CF(L,A)` (e.g. a member difference `χⱼ − aⱼ·χ₁`), the Dade
image of `u` pairs with the running extension `ν = hS₁.extension` of `δ` exactly as the source pair:
`⟨τ u, ν δ⟩ = ⟨u, δ⟩`.

This is the recurring move of the (5.6.1) coefficient computation (mmd 04.7 L79): the cross terms
`⟨(χ − a·χ₁)^τ, (χⱼ − aⱼ·χ₁)^τ⟩` are evaluated by the Dade isometry on the supported pair, with
`(χⱼ − aⱼ·χ₁)^τ = (χⱼ − aⱼ·χ₁)^{τ₁} = ν δ` since `δ` is supported (`ν = τ` there,
`extends_on_supported`).

Note this does **not** apply with `δ = χ₁` itself: the induced anchor `χ₁ = Ind θ` is *unsupported*
(`χ₁(1) ≠ 0`, so `1 ∈ supp χ₁ ∉ A`), which is precisely why crux1 `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a` is not
a direct corollary but needs the full (5.6.1)→(5.6.2) `Y`-collapse. -/
theorem inner_dade_extension_of_supported
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {u : ClassFunction ↥L ℂ}
    (husupp : u.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {δ : ClassFunction ↥L ℂ}
    (hδ : δ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj) u)
        (hS₁.extension δ) =
      ClassFunction.inner u δ := by
  -- `ν δ = τ δ` since `δ` is supported (the coherent extension agrees with `τ` on `CF(L,A)`).
  rw [hS₁.extends_on_supported δ hδ]
  -- Dade isometry on the supported pair `{u, δ}`.
  have hδsupp : δ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hδ).2
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj
    (S := {u, δ}) ?_ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact husupp
  · exact hδsupp

/-- **crux1 from the (5.6.2) `Y`-collapse.**  The bridge `retarget_isCoherent_of_extensionImage`
consumes `crux1 : ⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`.  This lemma reduces crux1 to its two genuine
ingredients, isolating the remaining (5.6.1)/(5.6.2) content:

* `hcollapse : Y = a·(ν χ₁)` — the (5.6.2) collapse `Da.Y = a·χ₁^{τ₁}` (mmd 04.7 (5.6.2)), where
  `Y` is the orthogonal residual of `τ(χ − a·χ₁) = X − Y` against `R(χ)`;
* `hXortho : ⟨X, ν χ₁⟩ = 0` — the (5.2.e) orthogonality `R(χ) ⊥ R(χ₁)` (since `X ∈ ℤ[R(χ)]` and
  `ν χ₁ ∈ ℤ[R(χ₁)]`).

Given `himg : τ(χ − a·χ₁) = X − Y` (the decomposition, from `Da.tau1_image` with `Da.tau1 = τ`) and
the unit norm `‖ν χ₁‖² = 1` (from the ν-isometry, `⟨χ₁, χ₁⟩ = 1`), crux1 is then pure inner-product
algebra: `⟨X − a·νχ₁, νχ₁⟩ = ⟨X, νχ₁⟩ − a·‖νχ₁‖² = 0 − a = −a`.

Stated abstractly over `G` (no Dade/coherence structure): the remaining work is to *produce*
`hcollapse` (the λ-form `Y = a·νχ₁ − λ·∑ rᵢ·νχᵢ + Z` collapsed via `lambda_eq_zero_and_Z_eq_zero`)
and `hXortho` (per-`α` member orthogonality summed over `R(χ)`). -/
theorem crux1_of_collapse {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {w X Y νchi1 : ClassFunction G ℂ} {a : ℕ}
    (himg : w = X - Y)
    (hcollapse : Y = a • νchi1)
    (hXortho : ClassFunction.inner X νchi1 = 0)
    (hνnorm : ClassFunction.inner νchi1 νchi1 = 1) :
    ClassFunction.inner w νchi1 = -(a : ℂ) := by
  rw [himg, hcollapse, ClassFunction.inner_sub_left, hXortho,
    ← Nat.cast_smul_eq_nsmul ℂ a νchi1, ClassFunction.inner_smul_left, hνnorm]
  ring

/-- **(5.2.e) member R-orthogonality `⟨X, ν χ₁⟩ = 0` — the `hXortho` ingredient of `crux1_of_collapse`.**

The `R(χ)`-part `X = D.X ∈ ℤ[R(χ)]` of the χ-decomposition `D` is orthogonal to the running image
`ν χ₁ = hS₁.extension χ₁` of any member `χ₁ ∈ S₁`, given the member's own `ψ = 0` decomposition `D'`
(so `ν χ₁ = D'.X ∈ ℤ[R(χ₁)]` by (5.5)) and the family orthogonality `R(χ₁) ⊥ R(χ)` ((5.2.e)).

Per-`α` orthogonality `⟨ν χ₁, α⟩ = 0` for `α ∈ R(χ)` (`inner_extension_member_orthogonal_imageSet`,
from `D'`/`hortho`/`htau1`) is summed over `R(χ)` by `inner_X_eq_zero_of_orthogonal_imageSet` to give
`⟨ν χ₁, X⟩ = 0`; conjugate symmetry flips it to `⟨X, ν χ₁⟩ = 0`.  The remaining work for the actual
`hXortho` is to *build* `D'` (the member ν-aux decomposition, needing `ν χ₁ ∈ ZIrr` injected since
`IsCoherent` carries no ZIrr-codomain) and `hortho` (the Dade `R(·)`-family orthogonality). -/
theorem inner_decomposition_X_extension_member_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S₁ : Set (ClassFunction L ℂ)} {A' : Set L}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A')
    {χ ψ chi1 : ClassFunction L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (D' : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := L) (G := G) τ chi1 0)
    (hortho : D'.imageFamily.Orthogonal D.imageFamily)
    (htau1 : D'.tau1 chi1 = hS₁.extension chi1) :
    ClassFunction.inner D.X (hS₁.extension chi1) = 0 := by
  have h1 : ClassFunction.inner (hS₁.extension chi1) D.X = 0 :=
    D.inner_X_eq_zero_of_orthogonal_imageSet
      (fun α hα => OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet
        hS₁ D.imageFamily D' hortho htau1 hα)
  rw [OddOrder.RepresentationTheory.inner_conj_symm, h1, star_zero]

/-- **(5.5) member ν-aux decomposition: the running extension `ν` as the auxiliary isometry `τ₁`.**

For a member `χ ∈ S₁` (non-real irreducible, with `χ̄ ∈ S₁` and `χ̄ − χ` supported), builds the (5.5)
`ψ = 0` decomposition `D' : CharacterPsiDecomposition τ χ 0` whose **auxiliary isometry `τ₁` is the
running extension `ν = hS₁.extension`** (not the Dade base map `τ`).  Then `D'.tau1 χ = ν χ`
(definitionally) and, via (5.5) (`eq_sum_of_psi_eq_zero`), `ν χ = D'.X ∈ ℤ[R(χ)]`.

This is the member family input that discharges the `D'`/`htau1` hypotheses of
`inner_decomposition_X_extension_member_eq_zero` (and the (5.6.1) λ-form), built from the Dade
`R(χ)` family (`dadeOrthonormalCharacterImageFamilyOfDiff`) and the coherent extension:

* `htau1_inner_eq` — `ν` is a `ℤ[χ−χ̄, χ]`-isometry: both generators lie in `ℤ[S₁]` (since
  `χ, χ̄ ∈ S₁`), where `hS₁.extension_inner_eq` applies;
* `htau1_agrees` — `ν(χ−χ̄) = τ(χ−χ̄)` since `χ−χ̄` is supported (`extends_on_supported`);
* `htau1_mem` — `ν χ ∈ ZIrr G` is the hypothesis `hνZ`.  Since `IsCoherent` gained the
  `extension_mem_ZIrr` field (route A), this is now derivable from `χ ∈ S₁ ⊆ ℤ[S₁]` via
  `hS₁.extension_mem_ZIrr`; callers discharge it from the field (it is kept as an explicit argument
  here only because this `def` predates the field).

The remaining (5.4) orthogonality scalars `⟨χ, 0⟩ = ⟨χ̄, 0⟩ = 0` are trivial and `⟨χ, χ̄⟩ = 0` is
`hχχbar`. -/
noncomputable def memberExtensionDecomposition
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχ_S1 : (χ : ClassFunction ↥L ℂ) ∈ S₁)
    (hχbar_S1 : (χ : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hνZ : hS₁.extension (χ : ClassFunction ↥L ℂ) ∈ ZIrr G)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χ : ClassFunction ↥L ℂ) 0 := by
  classical
  have hχmem : (χ : ClassFunction ↥L ℂ) ∈ Submodule.span ℤ S₁ := Submodule.subset_span hχ_S1
  have hχbarmem : (χ : ClassFunction ↥L ℂ).conj ∈ Submodule.span ℤ S₁ :=
    Submodule.subset_span hχbar_S1
  -- The (5.4) sponsoring set `{χ − χ̄, χ − 0}` lies in `ℤ[S₁]`.
  have hle : Submodule.span ℤ ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
      (χ : ClassFunction ↥L ℂ) - 0} : Set (ClassFunction ↥L ℂ)) ≤ Submodule.span ℤ S₁ := by
    rw [Submodule.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.sub_mem _ hχmem hχbarmem
    · rw [sub_zero]; exact hχmem
  -- `χ − χ̄` is supported (vanishes off `A`), hence in `ℤ[S₁] ∩ CF(L,A)`.
  have hdiffsupported : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ hχmem hχbarmem, by
        rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
            -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) by abel,
          ClassFunction.support_neg]
        exact hdiffsupp⟩
  exact OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ hreal hdiffsupp)
    hS₁.extension
    (fun φ ζ hφ hζ => hS₁.extension_inner_eq φ ζ (hle hφ) (hle hζ))
    (hS₁.extends_on_supported _ hdiffsupported)
    (by rw [sub_zero]; exact hνZ)
    (by simp)
    (by simp)
    hχχbar

/-- **(5.2.e) conjugate-difference orthogonality via *difference* supports (induced case).**

`⟨(x − x̄)^τ, (χ − χ̄)^τ⟩ = 0` whenever the **conjugate differences** `x̄ − x` and `χ̄ − χ` are
supported in `CF(L,A)` and `x, x̄ ⊥ χ, χ̄`.  Unlike
`dadeIntegralCharacterMap_inner_conjDifference_eq_zero` (which needs the *individual* supports of
`x, x̄, χ, χ̄`), this evaluates the Dade isometry directly on the two supported differences `x − x̄`,
`χ − χ̄` (`dadeIntegralCharacterMap_inner_eq_on_supported_span` on the set `{x − x̄, χ − χ̄}`), so it
applies to **induced** `x = Ind θ`, `χ = Ind θ'` whose individual values at `1` are nonzero.  The
reduced source pairing `⟨x − x̄, χ − χ̄⟩` expands to the four cross terms, all zero. -/
theorem inner_dadeDiff_conjDifference_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {x χ : ClassFunction ↥L ℂ}
    (hxdiffsupp : (x.conj - x).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχdiffsupp : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hxχ : ClassFunction.inner x χ = 0) (hxχbar : ClassFunction.inner x χ.conj = 0)
    (hxbarχ : ClassFunction.inner x.conj χ = 0) (hxbarχbar : ClassFunction.inner x.conj χ.conj = 0) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          (x - x.conj))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          (χ - χ.conj)) = 0 := by
  classical
  have hS : ∀ s ∈ ({x - x.conj, χ - χ.conj} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show x - x.conj = -(x.conj - x) by abel, ClassFunction.support_neg]; exact hxdiffsupp
    · rw [show χ - χ.conj = -(χ.conj - χ) by abel, ClassFunction.support_neg]; exact hχdiffsupp
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj hS
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    hxχ, hxχbar, hxbarχ, hxbarχbar, sub_zero, sub_self]

/-- **(5.2.e) Dade `R(·)`-family orthogonality via *difference* supports (induced case).**

`R(x) ⊥ R(χ)` for the difference-support Dade families `dadeOrthonormalCharacterImageFamilyOfDiff`
whenever `x, x̄ ⊥ χ, χ̄`.  Mirrors `dadeOrthonormalCharacterImageFamily_orthogonal` but reduces — via
`toOrthonormalImage_orthogonal` and `orthogonal_of_signedDifference_inner_eq_zero` — to the
*difference-support* orthogonality `inner_dadeDiff_conjDifference_eq_zero`, so it applies to the
**unsupported induced** X-members.  This is the `hortho` ingredient of
`inner_decomposition_X_extension_member_eq_zero`. -/
theorem dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {x χ : IrreducibleCharacter ↥L}
    (hxreal : ¬ ClassFunction.IsReal (x : ClassFunction ↥L ℂ))
    (hxdiffsupp : ((x : ClassFunction ↥L ℂ).conj - (x : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hχdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hxχ : ClassFunction.inner (x : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 0)
    (hxχbar : ClassFunction.inner (x : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hxbarχ : ClassFunction.inner (x : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hxbarχbar :
      ClassFunction.inner (x : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ).conj = 0) :
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj x hxreal
        hxdiffsupp).Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ hreal
        hχdiffsupp) := by
  unfold OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_orthogonal _ _
    (OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
      _ _ ?_)
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference,
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference]
  exact inner_dadeDiff_conjDifference_eq_zero hyp hconj hxdiffsupp hχdiffsupp
    hxχ hxχbar hxbarχ hxbarχbar

/-- **Member-side R-orthogonality `⟨Da.X, ν χ₁⟩ = 0`, fully assembled for the induced `Da`.**

The `hXortho` ingredient of `crux1_of_collapse`, with *every* member-side input discharged from the
injected data: `Da = decompositionDaFromDadeOfDiff` (the χ-decomposition), the member ν-aux
decomposition `D' = memberExtensionDecomposition` of `χ₁` (so `ν χ₁ = D'.X ∈ ℤ[R(χ₁)]` and
`D'.tau1 χ₁ = ν χ₁` definitionally), and the difference-support family orthogonality `R(χ₁) ⊥ R(χ)`
(`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`).  Chained through
`inner_decomposition_X_extension_member_eq_zero`.

This leaves only the (5.6.1)/(5.6.2) `Y`-collapse `Da.Y = a·ν χ₁` as the remaining input for crux1
(via `crux1_of_collapse` + `Da.tau1_image`). -/
theorem inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ chi1 : IrreducibleCharacter ↥L) {a : ℕ}
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (chi1 : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (chi1 : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (a • (chi1 : ClassFunction ↥L ℂ)) = 0)
    (hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (a • (chi1 : ClassFunction ↥L ℂ)) = 0)
    (hχχbar' : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hrealc1 : ¬ ClassFunction.IsReal (chi1 : ClassFunction ↥L ℂ))
    (hdiffsuppc1 : ((chi1 : ClassFunction ↥L ℂ).conj - (chi1 : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hc1S1 : (chi1 : ClassFunction ↥L ℂ) ∈ S₁) (hc1barS1 : (chi1 : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hνZc1 : hS₁.extension (chi1 : ClassFunction ↥L ℂ) ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ)
      (chi1 : ClassFunction ↥L ℂ).conj = 0)
    (hc1χ : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 0)
    (hc1χbar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hc1barχ : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hc1barχbar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 0) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp hconj χ hrealχ hdiffsuppχ
          hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar').X
        (hS₁.extension (chi1 : ClassFunction ↥L ℂ)) = 0 :=
  inner_decomposition_X_extension_member_eq_zero hS₁
    (OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp hconj χ hrealχ hdiffsuppχ
      hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar')
    (memberExtensionDecomposition hyp hconj hS₁ chi1 hrealc1 hdiffsuppc1 hc1S1 hc1barS1 hνZc1
      hc1c1bar)
    (dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp hconj hrealc1 hdiffsuppc1 hrealχ
      hdiffsuppχ hc1χ hc1χbar hc1barχ hc1barχbar)
    rfl

/-- **(5.6.1) member coefficient `⟨Da.Y, ν χⱼ⟩` — the heart of the λ-form.**

The (5.6.1) projection coefficient (mmd 04.7 L79): for a member `χⱼ` with degree-matched difference
`χⱼ − aⱼ·χ₁` (the value enters via `hfound`, `inner_dade_extension_of_supported` applied to the
supported `δ = χⱼ − aⱼ·χ₁`),

`⟨Y, ν χⱼ⟩ = a·⟨χ₁, χⱼ⟩ − (a + μ)·aⱼ`,    where `Y = X − τ(χ − a·χ₁)`, `μ = ⟨τ(χ − a·χ₁), ν χ₁⟩`.

The computation: `⟨Y, νχⱼ⟩ = −⟨τ(χ−a·χ₁), νχⱼ⟩` (since `⟨X, νχⱼ⟩ = 0`, the member R-orthogonality);
split `νχⱼ = ν(χⱼ − aⱼ·χ₁) + aⱼ·νχ₁` (ν is `ℤ`-linear); the first part is `⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩`
(`hfound`), which expands via `χ ⊥ χⱼ, χ₁` and `‖χ₁‖² = 1` to `−a·⟨χ₁, χⱼ⟩ + a·aⱼ`; the second is
`aⱼ·μ`.  With `λ := a + μ` this is `a·⟨χ₁,χⱼ⟩ − λ·aⱼ`, the `lambda_eq_zero_and_Z_eq_zero`
coefficient (`χ₁,χⱼ` orthonormal ⟹ `⟨χ₁,χⱼ⟩ = δ`, giving `a·[j=1] − λ·aⱼ`). -/
theorem inner_Y_extension_member_eq
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {chi1 cj : ClassFunction ↥L ℂ} {a aj : ℕ} {Xχ Y : ClassFunction G ℂ}
    (hYeq : Y = Xχ - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj) ((χ : ClassFunction ↥L ℂ) - a • chi1))
    (hXortho : ClassFunction.inner Xχ (hS₁.extension cj) = 0)
    (hfound : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension (cj - aj • chi1)) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • chi1) (cj - aj • chi1))
    (hχcj : ClassFunction.inner (χ : ClassFunction ↥L ℂ) cj = 0)
    (hχchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) chi1 = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1) :
    ClassFunction.inner Y (hS₁.extension cj) =
      (a : ℂ) * ClassFunction.inner chi1 cj -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
            ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1)) * (aj : ℂ) := by
  -- `ν cj = ν(cj − aⱼ·χ₁) + aⱼ·ν χ₁` (ν is ℤ-linear).
  have hνcj : hS₁.extension cj
      = hS₁.extension (cj - aj • chi1) + aj • hS₁.extension chi1 := by
    rw [map_sub, map_nsmul]; abel
  -- The source-side expansion `⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩ = −a·⟨χ₁, χⱼ⟩ + a·aⱼ`.
  have hsrc : ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • chi1) (cj - aj • chi1)
      = -(a : ℂ) * ClassFunction.inner chi1 cj + (a : ℂ) * (aj : ℂ) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a chi1, ← Nat.cast_smul_eq_nsmul ℂ aj chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχcj, hχchi1, hchi1chi1, star_natCast]
    ring
  -- The χ₁-side `⟨τ(χ − a·χ₁), aⱼ·ν χ₁⟩ = aⱼ·μ`.
  have hsmul : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (aj • hS₁.extension chi1) =
      (aj : ℂ) * ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ aj (hS₁.extension chi1),
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  rw [hYeq, ClassFunction.inner_sub_left, hXortho, zero_sub, hνcj,
    ClassFunction.inner_add_right, hfound, hsrc, hsmul]
  ring

open scoped Classical in
/-- **Indexed integral orthogonal projection onto a ZIrr-orthonormal family.**

The `ι`-indexed form of `exists_intProjection_of_orthonormal_ZIrr`, the shape the (5.6.2)
integer-forcing `lambda_eq_zero_and_Z_eq_zero` consumes: for `φ ∈ ZIrr G` and an **injective**
orthonormal family `vc : ι → CF G` over `s : Finset ι` (each `vc i ∈ ZIrr G`), there are integer
coefficients `c i = ⟨φ, vc i⟩` and an orthogonal residual `Z` with

`φ = (∑_{i ∈ s} c i • vc i) + Z`    and    `⟨Z, vc i⟩ = 0`.

Reindexes the image-indexed primitive (`R = s.image vc`, `Finset.sum_image` with `hvcinj`). -/
theorem exists_indexed_intProjection_of_orthonormal_ZIrr
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {ι : Type*} (s : Finset ι) (vc : ι → ClassFunction G ℂ)
    (hvcZ : ∀ i ∈ s, vc i ∈ ZIrr G)
    (hvcinj : ∀ i ∈ s, ∀ j ∈ s, vc i = vc j → i = j)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (vc i) (vc j) = if i = j then (1 : ℂ) else 0) :
    ∃ (c : ι → ℤ) (Z : ClassFunction G ℂ),
      (∀ i ∈ s, ClassFunction.inner φ (vc i) = (c i : ℂ)) ∧
      φ = (∑ i ∈ s, (c i : ℂ) • vc i) + Z ∧
      ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0 := by
  classical
  have hZR : ∀ α ∈ s.image vc, α ∈ ZIrr G := by
    intro α hα; rw [Finset.mem_image] at hα; obtain ⟨i, hi, rfl⟩ := hα; exact hvcZ i hi
  have horthR : ∀ α ∈ s.image vc, ∀ β ∈ s.image vc,
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0 := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨i, hi, rfl⟩ := hα; obtain ⟨j, hj, rfl⟩ := hβ
    rw [horth i hi j hj]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij (hvcinj i hi j hj h))]
  obtain ⟨c, Y, hcoeff, hsum, hY⟩ :=
    ClassFunction.exists_intProjection_of_orthonormal_ZIrr hφ hZR horthR
  refine ⟨fun i => c (vc i), Y, fun i hi => hcoeff (vc i) (Finset.mem_image_of_mem vc hi), ?_,
    fun i hi => hY (vc i) (Finset.mem_image_of_mem vc hi)⟩
  rw [hsum, Finset.sum_image hvcinj]

open scoped Classical in
/-- **(5.6.1)/(5.6.2) crux1 from the member family: `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`.**

The capstone of the crux1 discharge — the genuine (5.6.1)/(5.6.2) `Y`-collapse for the induced
X-family, producing crux1 directly.  Given the finite orthonormal member family `{χᵢ = χmem i}` (all
in `S₁`, `‖χᵢ‖² = 1` — the case-A `X ⊆ Irr L`), the per-member (5.6.1) coefficient values
`hcoeffval` (from `inner_Y_extension_member_eq`), `a₁ = 1`, and the (6.6) degree inequality
`2a < ∑ aᵢ²`:

* the indexed projection (`exists_indexed_intProjection_of_orthonormal_ZIrr`) writes
  `Da.Y = ∑ᵢ (cᵢ:ℂ)·νχᵢ + Z` with integer `cᵢ = ⟨Da.Y, νχᵢ⟩`;
* `hcoeffval` identifies `cᵢ = a·[i=i₁] − λ·aᵢ` with the integer `λ = a + μ`, `μ = ⟨τ(χ−a·χ₁), νχ₁⟩`
  (an integer since both are virtual characters);
* the (5.6.2) integer-forcing `lambda_eq_zero_and_Z_eq_zero` then forces `λ = 0` (`Z = 0`), i.e.
  `μ = −a` — which **is** crux1.

`μ ∈ ℤ` is the load-bearing fact making `λ = a + μ` an integer; the degree inequality (6.6) is what
forces it to vanish. -/
theorem crux1_of_memberFamily
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {a : ℕ}
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ
      (χ : ClassFunction ↥L ℂ) (a • χmem i₁))
    (hDaY_ZIrr : Da.Y ∈ ZIrr G)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (1 : ℂ) else 0)
    (hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ))
    (hμZ : τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2) :
    ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
      (hS₁.extension (χmem i₁)) = -(a : ℂ) := by
  classical
  -- `hνZ` is derived (route A): `χmem i ∈ S₁ ⊆ ℤ[S₁]`, so `ν (χmem i) ∈ ℤ[Irr G]` by the
  -- `IsCoherent.extension_mem_ZIrr` field — it need not be injected as a hypothesis.
  have hνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1 i hi))
  obtain ⟨μ, hμeq⟩ := ClassFunction.inner_mem_ZIrr_int hμZ (hνZ i₁ hi₁)
  -- Orthonormality of the family `vc i = ν χᵢ` (ν isometry on `ℤ[S₁]` + member orthonormality).
  have horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (hS₁.extension (χmem i)) (hS₁.extension (χmem j)) =
        if i = j then (1 : ℂ) else 0 := by
    intro i hi j hj
    rw [hS₁.extension_inner_eq (χmem i) (χmem j) (Submodule.subset_span (hmemS1 i hi))
      (Submodule.subset_span (hmemS1 j hj)), hmemortho i hi j hj]
  have hvcinj : ∀ i ∈ s, ∀ j ∈ s,
      hS₁.extension (χmem i) = hS₁.extension (χmem j) → i = j := by
    intro i hi j hj hij
    by_contra hne
    have h0 := horth i hi j hj
    rw [if_neg hne, hij, horth j hj j hj, if_pos rfl] at h0
    exact one_ne_zero h0
  obtain ⟨c, Z, hc_coeff, hYsum, hZortho⟩ :=
    exists_indexed_intProjection_of_orthonormal_ZIrr hDaY_ZIrr s
      (fun i => hS₁.extension (χmem i)) hνZ hvcinj horth
  -- Coefficient identification `(c i : ℂ) = a·[i=i₁] − (a+μ)·aᵢ`.
  have hcoeff_eq : ∀ i ∈ s, (c i : ℂ) =
      (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ) := by
    intro i hi
    rw [← hc_coeff i hi, hcoeffval i hi, hμeq]
    by_cases h : i = i₁
    · simp only [if_pos h]; push_cast; ring
    · simp only [if_neg h]; push_cast; ring
  -- The (5.6.1) λ-form and the (5.6.2) integer-forcing.
  have hY : Da.Y =
      (∑ i ∈ s, (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ)
        • hS₁.extension (χmem i)) + Z := by
    rw [hYsum]; congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hcoeff_eq i hi]
  have hψ : (ClassFunction.inner (a • χmem i₁ : ClassFunction ↥L ℂ) (a • χmem i₁)).re
      = (a : ℝ) ^ 2 * 1 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl,
      star_natCast, mul_one,
      show (a : ℂ) * (a : ℂ) = (((a : ℝ) ^ 2 * 1 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  obtain ⟨hlam0, -⟩ := Da.lambda_eq_zero_and_Z_eq_zero s i₁ hi₁ (a : ℝ) ((a : ℤ) + μ) Z
    (fun i => hS₁.extension (χmem i)) (fun _ => 1) (fun i => (deg i : ℝ))
    hY horth hZortho hψ (by simp [ha1]) (by positivity)
    (by simp only [mul_one]; exact hDeg)
  -- `λ = a + μ = 0 ⟹ μ = −a`, which is crux1.
  have hμval : μ = -(a : ℤ) := by omega
  rw [hμeq, hμval]; push_cast; ring

/-- **(T8.11 surgery, option A) coherence from the corrected extension image.**

The (5.6) adjoining step for the *induced (unsupported)* X-family.  Instead of mapping the new pair
`{χ, χ̄}` to a supported `ψ = 0` decomposition image (which needs `τχ ∈ ZIrr`, false for the
unsupported `χ = Ind θ`), `χ` is mapped to the **corrected extension image**
`X := τ(χ − a·χ₁) + a·νχ₁` (both terms integral).  This makes the (5.6.2) image equation `himg`
definitional, **bypassing** the `htau1_chi1` requirement `τχ₁ = νχ₁` that fails for unsupported `χ₁`.

Every remaining obligation of `retarget_isCoherent` is discharged from the source/Dade/ν isometries
plus the two crux inner products `hcrux1 : ⟨τ(χ−a·χ₁), νχ₁⟩ = −a` and `hcrux2 : ⟨τ(χ−χ̄), νχ₁⟩ = 0`
(the genuine (5.6) Feit–Sibley content, to be discharged separately via the degree inequality).  The
lattice orthogonality `hX_ortho`/`hXbar_ortho` is a span induction over
`ℤ[S₁] ⊆ span(ℤ[S₁,A] ∪ {χ₁})` (`hSgen`): clean on a supported `ξ` (`νξ = τξ` + Dade isometry) and
on `χ₁` via `hcrux1`/`hcrux2`. -/
noncomputable def retarget_isCoherent_of_extensionImage
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {chi1 : ClassFunction ↥L ℂ} {a : ℕ}
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdiffasupp : ((χ : ClassFunction ↥L ℂ) - a • chi1).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hchi1chi1 : ClassFunction.inner chi1 chi1 = 1)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    (hchi1 : chi1 ∈ S₁)
    (hτaχ1Z : τ ((χ : ClassFunction ↥L ℂ) - a • chi1) ∈ ZIrr G)
    (hτdiffZ : τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G)
    (hcrux1 : ClassFunction.inner
      (τ
        ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1) = -(a : ℂ))
    (hcrux2 : ClassFunction.inner
      (τ
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) (hS₁.extension chi1) = 0)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • chi1})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      τ
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- `χ₁ ⊥ χ, χ̄` (both directions, from `hχ_S1`/`hχbar_S1` and conjugate symmetry).
  have hχchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) chi1 = 0 := hχ_S1 chi1 hchi1
  have hchi1χ : ClassFunction.inner chi1 (χ : ClassFunction ↥L ℂ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχchi1, star_zero]
  have hχbarchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj chi1 = 0 := hχbar_S1 chi1 hchi1
  have hchi1χbar : ClassFunction.inner chi1 (χ : ClassFunction ↥L ℂ).conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbarchi1, star_zero]
  -- The supported difference lattice `{χ−χ̄, χ−a·χ₁}` and the Dade isometry on it.
  have hSdiff : ∀ s ∈ ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
      (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
          -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
        ClassFunction.support_neg]
      exact hdiffsupp
    · exact hdiffasupp
  have hmemu : (χ : ClassFunction ↥L ℂ) - a • chi1 ∈ Submodule.span ℤ
      ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
        (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) :=
    Submodule.subset_span (by simp)
  have hmemd : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈ Submodule.span ℤ
      ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
        (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) :=
    Submodule.subset_span (by simp)
  have hdade : ∀ φ ψ, φ ∈ Submodule.span ℤ
        ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) →
      ψ ∈ Submodule.span ℤ
        ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ := fun φ ψ hφ hψ => by
    rw [hτ]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hconj
      hSdiff hφ hψ
  -- Dade-image inner products (Dade isometry + source orthonormality).
  have huu : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • chi1))
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = 1 + (a : ℂ) ^ 2 := by
    rw [hdade _ _ hmemu hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hchi1χ, hchi1chi1, star_natCast]
    ring
  have hud : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • chi1))
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 1 := by
    rw [hdade _ _ hmemu hmemd, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχχbar, hchi1χ, hchi1χbar, star_natCast]
    ring
  have hdd : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 2 := by
    rw [hdade _ _ hmemd hmemd]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hχχ, hχχbar, hχbarχ, hχbarχbar]
    ring
  have hdu : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = 1 := by
    rw [hdade _ _ hmemd hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hχbarχ, hχbarchi1, star_natCast]
    ring
  -- `hS₁.extension χ₁` norm and the conjugates of the two crux inner products.
  have hvv : ClassFunction.inner (hS₁.extension chi1) (hS₁.extension chi1) = 1 := by
    rw [hS₁.extension_inner_eq chi1 chi1 (Submodule.subset_span hchi1)
      (Submodule.subset_span hchi1), hchi1chi1]
  have hvu : ClassFunction.inner (hS₁.extension chi1)
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux1]; simp
  have hvd : ClassFunction.inner (hS₁.extension chi1)
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux2, star_zero]
  set X : ClassFunction G ℂ :=
    τ ((χ : ClassFunction ↥L ℂ) - a • chi1) + a • hS₁.extension chi1 with hX
  set Xbar : ClassFunction G ℂ := X - τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
    with hXbar
  -- `X, X̄ ∈ ℤ[Irr G]`: the supported Dade images `(χ−a·χ₁)^τ`, `(χ−χ̄)^τ` are virtual (hypotheses),
  -- and `ν χ₁ ∈ ZIrr` is now recorded by the coherence's `extension_mem_ZIrr` field (`χ₁ ∈ S₁`).
  have hνchi1Z : hS₁.extension chi1 ∈ ZIrr G :=
    hS₁.extension_mem_ZIrr chi1 (Submodule.subset_span hchi1)
  have hXZ : X ∈ ZIrr G := by
    rw [hX]
    refine Submodule.add_mem _ hτaχ1Z ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ a (hS₁.extension chi1)]
    exact Submodule.smul_mem _ (a : ℤ) hνchi1Z
  have hXbarZ : Xbar ∈ ZIrr G := by rw [hXbar]; exact Submodule.sub_mem _ hXZ hτdiffZ
  -- `‖X‖² = 1`.
  have hXX : ClassFunction.inner X X = 1 := by
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hcrux1, hvu, hvv, star_natCast]
    ring
  -- `‖X̄‖² = 1`.
  have hXbarXbar : ClassFunction.inner Xbar Xbar = 1 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hdd, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  -- `⟨X, X̄⟩ = 0`.
  have hXXbar : ClassFunction.inner X Xbar = 0 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  -- `⟨X̄, X⟩ = 0`.
  have hXbarX : ClassFunction.inner Xbar X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXXbar, star_zero]
  -- `⟨ντ, τ(χ−a·χ₁)⟩ = −a·⟨ξ, χ₁⟩` on the generating set `ℤ[S₁,A] ∪ {χ₁}`, then on `ℤ[S₁]`.
  have hkey : ∀ ξ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ) (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) =
        -(a : ℂ) * ClassFunction.inner ξ chi1 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner (χ : ClassFunction ↥L ℂ) y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hyχ : ClassFunction.inner y (χ : ClassFunction ↥L ℂ) = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hySdiff : ∀ s ∈ ({y, (χ : ClassFunction ↥L ℂ) - a • chi1} :
              Set (ClassFunction ↥L ℂ)),
              s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · exact hdiffasupp
          rw [hνy, hτ, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
            hyp hconj hySdiff (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)),
            ← Nat.cast_smul_eq_nsmul ℂ a chi1]
          simp only [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
            hyχ, star_natCast]
          ring
        · rw [Set.mem_singleton_iff.mp hy1, hvu, hchi1chi1, mul_one]
    | zero => simp
    | add y z _ _ ihy ihz =>
        rw [map_add, ClassFunction.inner_add_left, ihy, ihz, ClassFunction.inner_add_left]; ring
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih,
          ← Int.cast_smul_eq_zsmul ℂ c y, ClassFunction.inner_smul_left]; ring
  have hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) X = 0 := by
    intro ξ hξ
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1), ClassFunction.inner_add_right,
      OddOrder.RepresentationTheory.inner_smul_right, hkey ξ (hSgen hξ),
      hS₁.extension_inner_eq ξ chi1 hξ (Submodule.subset_span hchi1)]
    simp only [star_natCast]; ring
  -- `⟨hS₁.extension ξ, τ(χ−χ̄)⟩ = 0` on `ℤ[S₁]` (similar span induction; clean — no `χ₁` term).
  have hkeyd : ∀ ξ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ)
        (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 0 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner (χ : ClassFunction ↥L ℂ) y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hχbary : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hmem.1
          have hyχ : ClassFunction.inner y (χ : ClassFunction ↥L ℂ) = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hyχbar : ClassFunction.inner y (χ : ClassFunction ↥L ℂ).conj = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbary, star_zero]
          have hySdiff : ∀ s ∈ ({y, (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj} :
              Set (ClassFunction ↥L ℂ)),
              s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
                  -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
                ClassFunction.support_neg]
              exact hdiffsupp
          rw [hνy, hτ, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
            hyp hconj hySdiff (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))]
          simp only [ClassFunction.inner_sub_right, hyχ, hyχbar, sub_zero]
        · rw [Set.mem_singleton_iff.mp hy1, hvd]
    | zero => simp
    | add y z _ _ ihy ihz => rw [map_add, ClassFunction.inner_add_left, ihy, ihz, add_zero]
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih,
          mul_zero]
  have hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) Xbar = 0 := by
    intro ξ hξ
    rw [hXbar, ClassFunction.inner_sub_right, hX_ortho ξ hξ, hkeyd ξ (hSgen hξ), sub_zero]
  have himg : τ ((χ : ClassFunction ↥L ℂ) - a • chi1) = X - a • hS₁.extension chi1 := by
    rw [hX]; abel
  exact OddOrder.Peterfalvi.S07.retarget_isCoherent hS₁ hχχ hχbarχbar hχχbar hχbarχ
    hXX hXbarXbar hXXbar hXbarX hXZ hXbarZ hX_ortho hXbar_ortho rfl hχ_S1 hχbar_S1 hchi1 himg hgen

open scoped Classical in
/-- **(T-A1) Per-step X-family coherence adjoin from a member family.** (`noncomputable def`: the
conclusion `IsCoherent` lives in `Type`, carrying the new extension `ν`.)

The (5.6)/(6.6) per-step adjoining of a new induced X-pair `{χ, χ̄}` to a coherent set `S₁`, packaged
as a function of the member-family enumeration data.  This wires the landed crux1 chain (the genuine
(5.6.1)/(5.6.2) `Y`-collapse, `crux1_of_memberFamily`) into the adjoining bridge
(`retarget_isCoherent_of_extensionImage`).

Inputs: `IsCoherent τ S₁ A` for the Dade map `τ`, a non-real irreducible `χ` orthogonal to all of
`S₁` (with `χ̄` likewise), and a finite orthonormal member family `{χmem i}ᵢ∈ₛ ⊆ S₁` with degree
ratios `deg i` (base member `i₁` of ratio `1`), the degree-matched supported differences
`χmem i − deg i·χmem i₁` and `χ − a·χmem i₁`, and the supported Dade-image ZIrr fact
`(χ − a·χmem i₁)^τ ∈ ZIrr`.  The members' ZIrr-codomain `ν χmem i ∈ ZIrr` is read off the
`IsCoherent.extension_mem_ZIrr` field (route A: `χmem i ∈ S₁ ⊆ ℤ[S₁]`), not passed as a hypothesis.
The construction:

* `Da := decompositionDaFromDadeOfDiff …` (the χ-decomposition for `χ − a·χ₁`), with `Da.Y ∈ ZIrr`
  derived from `Da.X ∈ ℤ[R(χ)]` and `(χ − a·χ₁)^τ ∈ ZIrr`;
* per member `i`, the (5.2.e) orthogonality `⟨Da.X, ν χᵢ⟩ = 0`
  (`inner_decomposition_X_extension_member_eq_zero`) and the (5.6.1) cross-term `hfound`
  (`inner_dade_extension_of_supported`) assemble the coefficient `⟨Da.Y, ν χᵢ⟩`
  (`inner_Y_extension_member_eq`);
* `crux1_of_memberFamily` collapses the λ-form (degree inequality `2a < ∑ aᵢ²`) into
  crux1 `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`;
* crux2 `⟨τ(χ − χ̄), ν χ₁⟩ = 0` is clean from `R(χ) ⊥ R(χ₁)`;
* the bridge concludes `IsCoherent τ (S₁ ∪ {χ, χ̄}) A`.

The lattice-generation conditions `hSgen`/`hgen` (structural facts about the accumulator `S₁`) are
threaded to the bridge; the chain fold (`xChainCoherent`) discharges them from the X-family
enumeration. -/
noncomputable def xAdjoinStep
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
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
    {ι : Type*} (s : Finset ι) (χmem : ι → IrreducibleCharacter ↥L) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χmem i : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (1 : ℂ) else 0)
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2)
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
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- The ZIrr-codomain of each member is now recorded by the coherence's `extension_mem_ZIrr` field
  -- (`χmem i ∈ S₁ ⊆ ℤ[S₁]`), so it need not be passed as a hypothesis (route A).
  have hmemνZ : ∀ i ∈ s, hS₁.extension (χmem i : ClassFunction ↥L ℂ) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr _ (Submodule.subset_span (hmemS1 i hi))
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
  let Da := OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp hconj χ hrealχ hdiffsuppχ
    hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar
  -- `Da.X ∈ ZIrr` (integer combination of the orthonormal `R(χ)` family) ⟹ `Da.Y ∈ ZIrr`.
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  have hYeq : Da.Y = Da.X - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) := by
    have h : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) = Da.X - Da.Y :=
      Da.tau1_image
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁ : ClassFunction ↥L ℂ)
      (χmem i₁ : ClassFunction ↥L ℂ) = 1 := by rw [hmemortho i₁ hi₁ i₁ hi₁]; simp
  -- The four `χmem i ⊥ {χ, χ̄}` orthogonalities (conjugate symmetry of `hχ_S1`/`hχbar_S1`).
  have hmemχ : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χ : ClassFunction ↥L ℂ) = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 _ (hmemS1 i hi), star_zero]
  have hmemχbar : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χ : ClassFunction ↥L ℂ).conj = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 _ (hmemS1 i hi), star_zero]
  have hmembarχ : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ) = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 _ (hmembarS1 i hi), star_zero]
  have hmembarχbar : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 _ (hmembarS1 i hi), star_zero]
  -- Per-member ν-aux decomposition `D'` and the (5.2.e) family orthogonality `R(χᵢ) ⊥ R(χ)`.
  -- (`let`, not `have`, so `(Dmem i hi).tau1 = ν` reduces definitionally for the `rfl` arguments.)
  let Dmem : ∀ i, i ∈ s → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χmem i : ClassFunction ↥L ℂ) 0 := fun i hi =>
    memberExtensionDecomposition hyp hconj hS₁ (χmem i) (hmemreal i hi) (hmemdiffsupp i hi)
      (hmemS1 i hi) (hmembarS1 i hi) (hmemνZ i hi) (hmemconjortho i hi)
  have hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily :=
    fun i hi =>
      dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp hconj (hmemreal i hi)
        (hmemdiffsupp i hi) hrealχ hdiffsuppχ (hmemχ i hi) (hmemχbar i hi) (hmembarχ i hi)
        (hmembarχbar i hi)
  -- (5.2.e) `⟨Da.X, ν χᵢ⟩ = 0` per member.
  have hXortho : ∀ i ∈ s, ClassFunction.inner Da.X (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) = 0 :=
    fun i hi => inner_decomposition_X_extension_member_eq_zero hS₁ Da (Dmem i hi) (hortho_mem i hi) rfl
  -- (5.6.1) cross-term `hfound` per member (`inner_dade_extension_of_supported`).
  have hfound : ∀ i ∈ s, ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ))) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ))
        ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)) := fun i hi => by
    refine inner_dade_extension_of_supported hyp hconj hS₁ hdiffasuppχ ?_
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- The (5.6.1) member coefficient `⟨Da.Y, ν χᵢ⟩` in the `lambda_eq_zero_and_Z_eq_zero` form.
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y
      (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
            ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
          (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq hyp hconj hS₁ χ hYeq (hXortho i hi) (hfound i hi)
      (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]
  -- crux1 via the λ-form collapse.
  have hcrux1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = -(a : ℂ) :=
    crux1_of_memberFamily hyp hconj
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
      hS₁ χ s (fun i => (χmem i : ClassFunction ↥L ℂ)) deg i₁ hi₁ Da hDaY_ZIrr hmemS1
      hmemortho hcoeffval htau1_memaχ ha1 hDeg
  -- crux2 clean: `⟨τ(χ − χ̄), ν χ₁⟩ = 0` from `R(χ) ⊥ R(χ₁)`.
  have hcrux2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily
          (Dmem i₁ hi₁) (hortho_mem i₁ hi₁) rfl hα), star_zero]
  -- `(χ − χ̄)^τ ∈ ZIrr` from the `R(χ)` family (`image_eq`); `(χ − a·χ₁)^τ ∈ ZIrr` is `htau1_memaχ`.
  have hτdiffZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  -- Adjoin via the (T8.11 option A) bridge.
  exact retarget_isCoherent_of_extensionImage hyp hconj
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
    hS₁ χ hdiffsuppχ hdiffasuppχ hχχ hχbarχbar hχχbar hχbarχ hchi1chi1 hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ hcrux1 hcrux2 hSgen hgen

open scoped Classical in
/-- **Peterfalvi (5.6)** — quantitative coherence, contrapositive form ("B1").

The converse of the forward adjoining engine `xAdjoinStep`: under the same Dade /
member-family hypotheses, if `S₁ ∪ {χ, χ̄}` fails to be coherent then the degree
sum is bounded by `∑ᵢ (deg i)² ≤ 2 a`.  Writing `a = ψ(1)/χ₁(1)` and
`deg i = χᵢ(1)/χ₁(1)` this is Peterfalvi's non-coherence bound
`∑_{χ∈S₁} χ(1)² ≤ 2 ψ(1) χ₁(1)`, the quantitative input consumed by (6.2) on the
way to the degree bound (6.3)/(6.5).  Proof: contrapose `xAdjoinStep` over its
degree hypothesis `hDeg : 2 a < ∑ᵢ (deg i)²`. -/
theorem coherentDegreeSumBound_of_not_coherent
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
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
    {ι : Type*} (s : Finset ι) (χmem : ι → IrreducibleCharacter ↥L) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χmem i : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (1 : ℂ) else 0)
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
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
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push_neg at hlt
  exact hnc ⟨xAdjoinStep hyp hconj hS₁ χ hrealχ hdiffsuppχ hχχ hχbarχbar hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemreal hmemdiffsupp hmemdegdiffsupp hmemS1 hmembarS1
    hmemconjortho hmemortho hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

open scoped Classical in
/-- **Peterfalvi (6.2), step (ii) — the `S(A)` degree-sum (B2 assembled).**
For `H ⊴ G`, `A ⊴ G`, `A ≤ H`, the induced family
`S(A) = {Ind_H^G θ | θ ∈ Irr H, A ⊆ Ker θ, θ ≠ 1}` satisfies
`∑_{χ ∈ S(A)} χ(1)²/‖χ‖² = [G:H]·(|H : A| − 1)`.

This assembles the orbit-counted identity `sum_div_normSq_induce_image_eq`
(`∑ = [G:H]·∑_{θ∈T}θ(1)²`, fibres of `θ ↦ Ind θ` are `G`-conjugacy orbits) with the inflation
degree-sum `sumInflatedDegreeSq_ntrivial` (`∑_{θ∈T}θ(1)² = |H ⧸ A| − 1`, Burnside on `H ⧸ A`).
The index set `T = {θ ∈ Irr H | A ⊆ Ker θ, θ ≠ 1}` is `G`-conjugation-invariant because `A ⊴ G`:
`Ker(θ^g) = g·(Ker θ)·g⁻¹ ⊇ g·A·g⁻¹ = A`.  This is the (6.2) input "step (ii)" that, with the
(5.6) bound B1 and the θ-bound, yields `2|L:C|√|C:D| ≥ |K:A| − 1`. -/
theorem sum_div_normSq_induce_kernelFilter_eq {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {H : Subgroup G} [H.Normal] [Invertible (Nat.card ↥H : ℂ)]
    {A : Subgroup G} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        χ 1 ^ 2 / ClassFunction.inner χ χ
      = (H.index : ℂ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℂ) - 1) := by
  classical
  have hconj : ∀ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
      (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H),
      ∀ g : G, IrreducibleCharacter.conjBy g θ ∈ Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥H =>
          (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H) := by
    intro θ hθ g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
    obtain ⟨hker, hne⟩ := hθ
    refine ⟨?_, ?_⟩
    · -- `A ⊆ Ker(θ^g)`: each `a ∈ A` has `g·a·g⁻¹ ∈ A ⊆ Ker θ`.
      intro a ha
      have hmemA : (⟨g * (a : G) * g⁻¹, ‹H.Normal›.conj_mem (a : G) a.2 g⟩ : ↥H)
          ∈ A.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact ‹A.Normal›.conj_mem (a : G) (Subgroup.mem_subgroupOf.mp ha) g
      have hk := hker hmemA
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hk
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def, conjBy_apply_one,
        IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply, hk,
        OddOrder.Peterfalvi.S03.characterDegree_def]
    · -- `θ^g ≠ 1`: conjugation is injective and fixes the trivial character.
      intro hc
      apply hne
      have h1 : IrreducibleCharacter.conjBy g⁻¹ (IrreducibleCharacter.conjBy g θ) = θ := by
        rw [← IrreducibleCharacter.conjBy_mul, mul_inv_cancel, IrreducibleCharacter.conjBy_one]
      rw [← h1, hc, IrreducibleCharacter.ext_iff]
      ext h
      rw [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
      simp
  rw [sum_div_normSq_induce_image_eq _ hconj]
  congr 1
  exact sumInflatedDegreeSq_ntrivial (N := A.subgroupOf H)

open scoped Classical in
/-- **(T-A2 input) Per-step `xAdjoinStep` data bundle.**

Bundles the `xAdjoinStep` premises for one adjoining step of the X-family chain — the member family
`{χmem i}ᵢ∈ₛ ⊆ S₁` (orthonormal, with the ZIrr-codomain injections `ν χmem i ∈ ZIrr`), the new
character `χ`, the degree data, and the anchor-generation condition `hSgen` — into a single
structure, so the chain fold `xChainCoherent` can take the per-step data as a function of the
(inductively produced) accumulator coherence `hS₁`.  The full `hgen` field is derived in `adjoin`
from `hSgen` and the degree-matched support of `χ - aχ₁`.  The index type `ι` is a field (each step
has its own enumerated family). -/
structure XAdjoinStepInput
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
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
  χmem : ι → IrreducibleCharacter ↥L
  deg : ι → ℕ
  i₁ : ι
  hi₁ : i₁ ∈ s
  hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ)
  hmemdiffsupp : ∀ i ∈ s,
    ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemdegdiffsupp : ∀ i ∈ s,
    ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁
  hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁
  hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
    (χmem i : ClassFunction ↥L ℂ).conj = 0
  hmemortho : ∀ i ∈ s, ∀ j ∈ s,
    ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
      if i = j then (1 : ℂ) else 0
  a : ℕ
  hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
    (hyp.fullDadeIsometryData hconj)
    ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G
  ha1 : deg i₁ = 1
  hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2
  hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
    (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)})

/-- `xAdjoinStep` applied to a bundled `XAdjoinStepInput`, concluding coherence of
`S₁ ∪ {χ, χ̄}`. -/
noncomputable def XAdjoinStepInput.adjoin
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L} {hconj : hyp.HConjInvariant}
    {S₁ : Set (ClassFunction ↥L ℂ)}
    {hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L)}
    {χ : IrreducibleCharacter ↥L} (inp : XAdjoinStepInput hyp hconj hS₁ χ) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  have h1notA : (1 : G) ∉ A := by
    intro h
    exact hyp.ne_one h rfl
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro h
    exact h1notA (by simpa using h)
  have hdegχ : ((χ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 =
      (inp.a : ℂ) * ((inp.χmem inp.i₁ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    have hzero :
        (((χ : ClassFunction ↥L ℂ) - inp.a •
          (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)) : ClassFunction ↥L ℂ) 1 = 0 := by
      by_contra h
      exact h1A (inp.hdiffasuppχ (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ inp.a
      (inp.χmem inp.i₁ : ClassFunction ↥L ℂ), ClassFunction.smul_apply] at hzero
    exact sub_eq_zero.mp hzero
  have hchi1_ne : ((inp.χmem inp.i₁ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 ≠ 0 := by
    obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (inp.χmem inp.i₁)
    rw [hd1]
    exact_mod_cast hd.ne'
  have hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - inp.a •
          (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)}) :=
    OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
      (L := ↥L) (S₁ := S₁)
      (A := OddOrder.Peterfalvi.S04.supportInSubgroup A L)
      (χ := (χ : ClassFunction ↥L ℂ)) (chibar := (χ : ClassFunction ↥L ℂ).conj)
      (chi1 := (inp.χmem inp.i₁ : ClassFunction ↥L ℂ)) (a := inp.a)
      inp.hSgen hdegχ (OddOrder.Peterfalvi.S07.irreducibleCharacter_conj_apply_one χ)
      hchi1_ne h1A
  exact xAdjoinStep hyp hconj hS₁ χ inp.hrealχ inp.hdiffsuppχ inp.hχχ inp.hχbarχbar
    inp.hχχbar inp.hχbarχ inp.hχ_S1 inp.hχbar_S1 inp.s inp.χmem inp.deg inp.i₁ inp.hi₁
    inp.hmemreal inp.hmemdiffsupp inp.hmemdegdiffsupp inp.hmemS1 inp.hmembarS1
    inp.hmemconjortho inp.hmemortho inp.hdiffasuppχ inp.htau1_memaχ inp.ha1 inp.hDeg
    inp.hSgen hgen

/-- **(T-A2) The X-family coherence chain fold.**

Folds the per-step adjoining `xAdjoinStep` (via `XAdjoinStepInput.adjoin`) over a degree-monotone
conjugate-pair cover of `X` using the `coherentOfPairChainCover` engine: the base `S₀` is coherent
(`h0`), the `i`-th step adjoins the pair `(pair i) = (χₛ i, (χₛ i)̄)` to the accumulator
`pairUnion S₀ pair i` via `hstep i`, and the cover (`hS₀`/`hpairs`/`hcover`) recovers `X`.

This is the route-B custom fold of the §J.3.6 plan: rather than strengthening `IsCoherent` with a
ZIrr-codomain field (route A, T-A3), the per-step ZIrr-codomain facts are carried as fields of
`XAdjoinStepInput hyp hconj hcoh (χₛ i)`, supplied as a function of the *inductively produced*
accumulator coherence `hcoh`.  The construction of `hstep` from the actual degree-monotone
enumeration of `X` (the `exists_conjugatePairCover` data) is the remaining T-A4 wiring. -/
noncomputable def xChainCoherent
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {X S₀ : Set (ClassFunction ↥L ℂ)}
    (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
    (χs : ℕ → IrreducibleCharacter ↥L)
    (hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ))
    (hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj)
    (hS₀ : S₀ ⊆ X)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ X)
    (hcover : ∀ χ ∈ X, χ ∈ S₀ ∨ ∃ j, j < N ∧ χ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
    (h0 : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₀ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hstep : ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) S₀ pair i)
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L)),
      XAdjoinStepInput hyp hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      X (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
  OddOrder.Peterfalvi.S07.coherentOfPairChainCover pair N hS₀ hpairs hcover h0
    (fun i hi hcoh => by
      rw [OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair (hpair0 i hi) (hpair1 i hi)]
      exact (hstep i hi hcoh).adjoin)

/-- A pair disjoint from the accumulated prefix is orthogonal to that prefix.

This is the set-to-inner-product bridge used by the X-chain per-step builder: once the
conjugate-pair cover has proved `pairSet pair i` is disjoint from `pairUnion S0 pair i`, every
irreducible member of the prefix is distinct from both `χ_i` and `χ_i.conj`, so row
orthogonality gives the two `XAdjoinStepInput` fields `hχ_S1` and `hχbar_S1`. -/
theorem pairCover_orthogonal_to_prefix
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X S₀ : Set (ClassFunction Γ ℂ)} {pair : ℕ → ClassFunction Γ ℂ × ClassFunction Γ ℂ}
    {N i : ℕ} {χ : IrreducibleCharacter Γ}
    (hXirr : ∀ φ ∈ X, IsIrreducibleCharacter φ)
    (hS₀X : S₀ ⊆ X)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair j ⊆ X)
    (hpair0 : (pair i).1 = (χ : ClassFunction Γ ℂ))
    (hpair1 : (pair i).2 = (χ : ClassFunction Γ ℂ).conj)
    (hdisj : Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i)
      (OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i))
    (hi : i < N) :
    (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i,
        ClassFunction.inner (χ : ClassFunction Γ ℂ) x = 0) ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i,
        ClassFunction.inner (χ : ClassFunction Γ ℂ).conj x = 0) := by
  classical
  have hprefixX : OddOrder.Peterfalvi.S07.pairUnion (L := Γ) S₀ pair i ⊆ X := by
    intro x hx
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hx with hbase | ⟨j, hji, hjpair⟩
    · exact hS₀X hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hχpair : (χ : ClassFunction Γ ℂ) ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0]
  have hχbarpair : (χ : ClassFunction Γ ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair1]
  have hχbarIrr : IsIrreducibleCharacter (χ : ClassFunction Γ ℂ).conj :=
    hXirr _ (hpairs i hi hχbarpair)
  have hdisj_left := Set.disjoint_left.mp hdisj
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxirr : IsIrreducibleCharacter x := hXirr x (hprefixX hx)
    let ψ : IrreducibleCharacter Γ := ⟨x, hxirr⟩
    have hne : χ ≠ ψ := by
      intro hEq
      have hx_eq : x = (χ : ClassFunction Γ ℂ) :=
        (congrArg (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hEq).symm
      have hxpair : x ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
        simpa [hx_eq] using hχpair
      exact hdisj_left hxpair hx
    simpa [ψ, hne] using irreducibleCharacter_inner_eq_ite χ ψ
  · intro x hx
    have hxirr : IsIrreducibleCharacter x := hXirr x (hprefixX hx)
    let χbar : IrreducibleCharacter Γ := ⟨(χ : ClassFunction Γ ℂ).conj, hχbarIrr⟩
    let ψ : IrreducibleCharacter Γ := ⟨x, hxirr⟩
    have hne : χbar ≠ ψ := by
      intro hEq
      have hx_eq : x = (χ : ClassFunction Γ ℂ).conj :=
        (congrArg (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hEq).symm
      have hxpair : x ∈ OddOrder.Peterfalvi.S07.pairSet (L := Γ) pair i := by
        simpa [hx_eq] using hχbarpair
      exact hdisj_left hxpair hx
    simpa [χbar, ψ, hne] using irreducibleCharacter_inner_eq_ite χbar ψ

/-- **Peterfalvi (6.3) degree-bound arithmetic core.**  The real/integer inequality at the heart of
Theorem (6.3) (mmd 04.8 L33): from the (6.2) consequence `b·x − 1 ≤ 2·a·b·√x` (with `a = |L:K|`,
`b = |K:H| ≥ 1`, `x = |H:A| ≥ 1`) one gets `x ≤ 4a² + 1`.

Proof: dividing by `b` and using `b ≥ 1` gives `x − 1 ≤ 2a√x`; squaring (`x − 1 ≥ 0`) gives
`(x − 1)² ≤ 4a²x`, i.e. `x² − (4a² + 2)x + 1 ≤ 0`; for a natural `x`, `x ≥ 4a² + 2` would give
`x² − (4a² + 2)x + 1 = x·(x − (4a² + 2)) + 1 ≥ 1 > 0`, a contradiction.  This is what (6.3) combines
with its hypothesis `|H:H₁| > 4|L:K|² + 1 ≤ x` to reach a contradiction (so `𝒮(M)` is coherent). -/
theorem degreeBound_le_of_sqrt_bound {a b x : ℕ} (hb : 1 ≤ b) (hx : 1 ≤ x)
    (h : (b : ℝ) * x - 1 ≤ 2 * a * b * Real.sqrt x) : x ≤ 4 * a ^ 2 + 1 := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hsx : Real.sqrt x ^ 2 = (x : ℝ) := Real.sq_sqrt hx0
  have hsx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  -- `x − 1 ≤ 2a√x` (divide `h` by `b`, drop `1/b ≤ 1`).
  have key : (x : ℝ) - 1 ≤ 2 * a * Real.sqrt x := by
    have hbx : (b : ℝ) * ((x : ℝ) - 1) ≤ (b : ℝ) * (2 * a * Real.sqrt x) := by
      have e1 : (b : ℝ) * ((x : ℝ) - 1) = (b : ℝ) * x - b := by ring
      have e2 : (b : ℝ) * (2 * a * Real.sqrt x) = 2 * a * b * Real.sqrt x := by ring
      rw [e1, e2]; nlinarith [h, hb1]
    exact le_of_mul_le_mul_left hbx hbpos
  -- `(x − 1)² ≤ (2a√x)² = 4a²x`.
  have hkey0 : (0 : ℝ) ≤ (x : ℝ) - 1 := by linarith
  have hrhs0 : (0 : ℝ) ≤ 2 * a * Real.sqrt x := by positivity
  have hsq : ((x : ℝ) - 1) ^ 2 ≤ 4 * (a : ℝ) ^ 2 * x := by
    have hprod := mul_le_mul key key hkey0 hrhs0
    have hrw : (2 * (a : ℝ) * Real.sqrt x) * (2 * (a : ℝ) * Real.sqrt x) = 4 * (a : ℝ) ^ 2 * x := by
      rw [show (2 * (a : ℝ) * Real.sqrt x) * (2 * (a : ℝ) * Real.sqrt x)
          = 4 * (a : ℝ) ^ 2 * (Real.sqrt x * Real.sqrt x) by ring, Real.mul_self_sqrt hx0]
    rw [hrw] at hprod
    nlinarith [hprod]
  -- `x² − 2x + 1 ≤ 4a²x` gives `x² < (4a²+2)x`, so `x < 4a²+2`, i.e. `x ≤ 4a²+1`.
  have hxlt : (x : ℝ) < 4 * (a : ℝ) ^ 2 + 2 := by
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    nlinarith [hsq, hxpos]
  have hxltN : x < 4 * a ^ 2 + 2 := by exact_mod_cast hxlt
  omega

/-- **Peterfalvi (6.5)(a) chief-factor arithmetic.**  If `c` and `a` are odd, `c ∣ a − 1`, and
`a > 1`, then `a ≥ 2c + 1` (mmd 04.8 L40).  Indeed `a − 1 = c·m` is even (as `a` is odd) and `c` is
odd, so `m` is even and nonzero, hence `m ≥ 2` and `a − 1 = c·m ≥ 2c`.

This is the step in (6.5)(a) ruling out an intermediate normal subgroup `H₁ ⊊ H₂ ⊊ K`: with
`a = |K : H₂|` (odd, dividing the odd `|L|`) and `c = |L : K|`, hypothesis (6.4.c) gives `c ∣ a − 1`,
so `|K : H₂| ≥ 2|L : K| + 1`; likewise `|H₂ : H₁| ≥ 2|L : K| + 1`, whence
`|K : H₁| ≥ (2|L : K| + 1)² > 4|L : K|² + 1`, contradicting the (6.3) bound. -/
theorem two_mul_add_one_le_of_odd_dvd {c a : ℕ} (hc : Odd c) (ha : Odd a) (hdvd : c ∣ a - 1)
    (ha1 : 1 < a) : 2 * c + 1 ≤ a := by
  obtain ⟨m, hm⟩ := hdvd
  have hcodd : c % 2 = 1 := Nat.odd_iff.mp hc
  have haodd : a % 2 = 1 := Nat.odd_iff.mp ha
  have hmeven : m % 2 = 0 := by
    have h1 : (c * m) % 2 = 0 := by
      have h2 : (a - 1) % 2 = 0 := by omega
      rwa [hm] at h2
    rw [Nat.mul_mod, hcodd, one_mul] at h1
    omega
  have hm2 : 2 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hz | hpos
    · rw [hz, mul_zero] at hm; omega
    · omega
  have h2c : 2 * c ≤ c * m := by nlinarith [hm2]
  omega

/-- **Peterfalvi (6.3)** index reduction.  From the degree bound (6.2) applied
with `C = H, D = A`, in index form `|K:H|·|H:A| − 1 ≤ 2·|L:K|·|K:H|·√|H:A|`,
together with `|H:H₁| ≤ |H:A|` (from `A ⊆ H₁`), the index `|H:H₁|` is at most
`4|L:K|² + 1`.  (Peterfalvi states the contrapositive: `|H:H₁| > 4|L:K|² + 1`
forces `S(M)` coherent.)  The `√`-manipulation is `degreeBound_le_of_sqrt_bound`
with `a = |L:K|, b = |K:H|, x = |H:A|`. -/
theorem six_three_HH1_le {LK KH HA HH1 : ℕ} (hKH : 1 ≤ KH) (hHH1le : HH1 ≤ HA)
    (hbound : (KH : ℝ) * (HA : ℝ) - 1 ≤ 2 * (LK : ℝ) * (KH : ℝ) * Real.sqrt (HA : ℝ)) :
    HH1 ≤ 4 * LK ^ 2 + 1 := by
  rcases Nat.eq_zero_or_pos HA with hHA0 | hHA
  · subst hHA0; omega
  · have hx := degreeBound_le_of_sqrt_bound hKH hHA hbound
    omega

/-- Arithmetic core of **Peterfalvi (6.5)(a),(c)**: since
`(2c+1)² = 4c²+4c+1 > 4c²+1` for `c ≥ 1`, an index `n` cannot satisfy both
`(2c+1)² ≤ n` and `n ≤ 4c²+1`. -/
theorem six_five_index_contradiction {LK n : ℕ} (hLK : 1 ≤ LK)
    (hge : (2 * LK + 1) * (2 * LK + 1) ≤ n) (hle : n ≤ 4 * LK ^ 2 + 1) : False := by
  nlinarith [hge, hle, hLK]

/-- **Peterfalvi (6.5)(a)** chief-factor step.  If a normal subgroup `H₂` sits
strictly between `H₁` and `K`, then (6.4.c) + odd order force
`|K:H₂|, |H₂:H₁| ≥ 2|L:K|+1` (via `two_mul_add_one_le_of_odd_dvd`), so
`|K:H₁| = |K:H₂|·|H₂:H₁| ≥ (2|L:K|+1)² > 4|L:K|²+1`, contradicting the (6.3)
bound `|K:H₁| ≤ 4|L:K|²+1`.  Hence `K/H₁` is a chief factor of `L`. -/
theorem six_five_chief_factor_contradiction {LK KH2 H2H1 KH1 : ℕ} (hLK : 1 ≤ LK)
    (hKH2 : 2 * LK + 1 ≤ KH2) (hH2H1 : 2 * LK + 1 ≤ H2H1)
    (hmul : KH1 = KH2 * H2H1) (hKH1le : KH1 ≤ 4 * LK ^ 2 + 1) :
    False :=
  six_five_index_contradiction hLK
    (by rw [hmul]; exact Nat.mul_le_mul hKH2 hH2H1) hKH1le

/-- **Peterfalvi (6.5)(c)** : `|L:K|` does not divide `p − 1`.  If it did then
`p ≥ 2|L:K|+1` (`two_mul_add_one_le_of_odd_dvd`), and since `K/M` is a
non-abelian `p`-group `|K:H₁| ≥ p² ≥ (2|L:K|+1)² > 4|L:K|²+1`, contradicting the
(6.5)(a) bound `|K:H₁| ≤ 4|L:K|²+1`. -/
theorem six_five_c_contradiction {LK p KH1 : ℕ} (hLK : 1 ≤ LK)
    (hpge : 2 * LK + 1 ≤ p) (hp2 : p * p ≤ KH1) (hKH1le : KH1 ≤ 4 * LK ^ 2 + 1) :
    False :=
  six_five_index_contradiction hLK (le_trans (Nat.mul_le_mul hpge hpge) hp2) hKH1le

/-- **Extension of `p`-groups is a `p`-group.**  If a normal subgroup `N` and the quotient `Γ ⧸ N`
are both `p`-groups (and `Γ` is finite), then `Γ` is a `p`-group: `|Γ| = |Γ ⧸ N|·|N| = p^b·p^a`
(Lagrange, `card_eq_card_quotient_mul_card_subgroup`), so `|Γ|` is a `p`-power (`IsPGroup.iff_card`).

A general group-theory brick; used by Peterfalvi (6.5)(b) to assemble "`K/M` is a `p`-group" from
its commutator subgroup `H₁/M` and the chief factor `K/H₁` (a `p`-group). -/
theorem isPGroup_of_quotient_of_subgroup {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Normal] (hN : IsPGroup p ↥N) (hQ : IsPGroup p (Γ ⧸ N)) :
    IsPGroup p Γ := by
  rw [IsPGroup.iff_card] at hN hQ ⊢
  obtain ⟨a, ha⟩ := hN
  obtain ⟨b, hb⟩ := hQ
  exact ⟨b + a, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hb, ha, pow_add]⟩

/-- `Abelianization.map` of a surjective homomorphism is surjective. -/
theorem Abelianization.map_surjective {Γ Δ : Type*} [Group Γ] [Group Δ] {f : Γ →* Δ}
    (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | _ b =>
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨Abelianization.of a, Abelianization.map_of f a⟩

/-- A finite `p`-group whose order is coprime to `p` is trivial. -/
theorem subsingleton_of_isPGroup_of_not_dvd {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Finite Δ]
    (hΔ : IsPGroup p Δ) (hnd : ¬ p ∣ Nat.card Δ) : Subsingleton Δ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΔ
  have hk0 : k = 0 := by
    by_contra hk0
    exact hnd (by rw [hk]; exact dvd_pow_self p hk0)
  rw [hk0, pow_zero] at hk
  exact (Nat.card_eq_one_iff_unique.mp hk).1

/-- **Peterfalvi (6.5)(b) reduction core: a finite nilpotent group with `p`-group abelianization is
a `p`-group.**

Let `P` be the Sylow `p`-subgroup, normal since `Γ` is nilpotent.  The quotient `Q = Γ ⧸ P` has order
`[Γ:P]` coprime to `p`, so `Abelianization Q` — both a `p`-group (a homomorphic image of
`Abelianization Γ`, `Abelianization.map` of `Γ ↠ Q`) and of order dividing `[Γ:P]` — is trivial.
Hence `Q` is perfect (`commutator Q = ⊤`); being nilpotent (a quotient of `Γ`) and hence solvable, it
is therefore trivial (`commutator_lt_top` for a nontrivial solvable group).  So `P = ⊤` and `Γ` is a
`p`-group (`isPGroup_of_quotient_of_subgroup`).

This is the (6.5)(b) step "since `K/M` is nilpotent with commutator `H₁/M` and `K/H₁` a chief factor,
`K/M` is a `p`-group" (mmd 04.8 L45). -/
theorem isPGroup_of_isNilpotent_of_isPGroup_abelianization {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsNilpotent Γ]
    (h : IsPGroup p (Abelianization Γ)) : IsPGroup p Γ := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p Γ) := inferInstance
  haveI hPnormal : (↑P : Subgroup Γ).Normal := by
    have htfae := (isNilpotent_of_finite_tfae (G := Γ)).out 0 3
    exact htfae.mp ‹_› p ‹_› P
  -- `Abelianization Q` is a `p`-group (image of `Abelianization Γ`).
  have hQab_p : IsPGroup p (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    h.of_surjective _ (Abelianization.map_surjective (QuotientGroup.mk'_surjective _))
  -- ... and trivial: its order divides `Nat.card Q = [Γ:P]`, coprime to `p`.
  have hofsurj : Function.Surjective (Abelianization.of :
      (Γ ⧸ (↑P : Subgroup Γ)) →* Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    fun y => QuotientGroup.induction_on y fun a => ⟨a, rfl⟩
  haveI hQab_triv : Subsingleton (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    subsingleton_of_isPGroup_of_not_dvd hQab_p
      (fun hp => P.not_dvd_index (hp.trans (Subgroup.card_dvd_of_surjective _ hofsurj)))
  -- `Abelianization Q` trivial ⟹ `commutator Q = ⊤` ⟹ (nilpotent ⟹ solvable) `Q` trivial.
  haveI hQ_triv : Subsingleton (Γ ⧸ (↑P : Subgroup Γ)) := by
    rcases subsingleton_or_nontrivial (Γ ⧸ (↑P : Subgroup Γ)) with hs | hns
    · exact hs
    · exfalso
      haveI := hns
      have hlt : commutator (Γ ⧸ (↑P : Subgroup Γ)) < ⊤ :=
        IsSolvable.commutator_lt_top_of_nontrivial (G := Γ ⧸ (↑P : Subgroup Γ))
      refine absurd ?_ hlt.ne
      rw [← Subgroup.index_eq_one]
      exact @Nat.card_of_subsingleton (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) 1 hQab_triv
  -- `Q` trivial ⟹ `Γ` is a `p`-group (Sylow `P` is `p`, quotient `Q` trivially `p`).
  refine isPGroup_of_quotient_of_subgroup P.isPGroup' ?_
  rw [IsPGroup.iff_card]
  exact ⟨0, by rw [pow_zero]; exact @Nat.card_of_subsingleton (Γ ⧸ (↑P : Subgroup Γ)) 1 hQ_triv⟩

/-- **Group-theory core of Peterfalvi (6.5)(a),(b): a Frobenius-acted abelian section obeying the
(6.3) index bound is a `p`-group.**

Let a finite group `R` act on a finite abelian group `A` by automorphisms, *fixed-point-freely*
(`IsFrobeniusAction R A`: no nonidentity `r ∈ R` fixes a nonidentity `a ∈ A`).  If `|A|` and `|R|`
are odd and `|A| ≤ 4|R|² + 1`, then `A` is a `p`-group for some prime `p`.

This is the abstract content of Peterfalvi (6.5).  In the Sibley setting `A = K/H₁` is the
abelianization section and `R = L/K` is the Frobenius complement; (6.5)(a) says `K/H₁` is a chief
factor.  Here the chief-factor argument is run through the `p`-primary component: if `A` had a prime
divisor `p` whose Sylow subgroup `P` were proper (i.e. `A` were not a `p`-group), then `P`
(characteristic in the abelian `A`, hence `R`-invariant) and the quotient index `|A : P|` would both
be nontrivial, odd, and `≡ 1 (mod |R|)` — the first two by Frobenius `card_modEq_one` applied to the
whole action and the restricted action on `P` (`IsFrobeniusAction.subgroup`), the index by the
arithmetic `|A| = |A:P|·|P|`, `|A| ≡ |P| ≡ 1`.  Oddness then forces `|P|, |A:P| ≥ 2|R| + 1`
(`two_mul_add_one_le_of_odd_dvd`), so `|A| = |A:P|·|P| ≥ (2|R|+1)² > 4|R|² + 1`, contradicting the
bound (`six_five_chief_factor_contradiction`).

The `|A| ≤ 4|R|² + 1` bound is the single character-theoretic input ((6.2)/(6.3); in the Sibley
setup supplied by `theta_degree_le_index_mul_sqrt_index`).  Everything else is discharged here. -/
theorem isPGroup_of_card_le_of_isFrobeniusAction {A R : Type*} [CommGroup A] [Finite A]
    [Group R] [Finite R] [MulDistribMulAction R A]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R A)
    (hAodd : Odd (Nat.card A)) (hRodd : Odd (Nat.card R))
    (hbound : Nat.card A ≤ 4 * Nat.card R ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p A := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype R := Fintype.ofFinite R
  by_contra hcon
  -- `A` is nontrivial: a trivial group is a `p`-group for every prime.
  rcases eq_or_ne (Nat.card A) 1 with hA1 | hA1
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hcon ⟨2, Nat.prime_two, IsPGroup.iff_card.mpr ⟨0, by rw [pow_zero, hA1]⟩⟩
  -- Otherwise take a prime divisor `p` of `|A|` and its Sylow `p`-subgroup `P`.
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card A).exists_prime_and_dvd hA1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p A) := inferInstance
  -- `|P| > 1` because `p ∣ |P|`.
  have hpP : p ∣ Nat.card (P : Subgroup A) := P.dvd_card_of_dvd_card hpdvd
  have hcardP : 1 < Nat.card (P : Subgroup A) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hpP)
  -- `P` is normal (abelian ambient), hence characteristic.
  have hPnormal : (P : Subgroup A).Normal :=
    ⟨fun n hn g => by
      have heq : g * n * g⁻¹ = n := by rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]; exact hn⟩
  have hPchar : (P : Subgroup A).Characteristic := P.characteristic_of_normal hPnormal
  -- `R` acts by automorphisms, which fix the characteristic `P` setwise: `P` is `R`-invariant.
  have hinv : ∀ r : R, ∀ m ∈ (P : Subgroup A), r • m ∈ (P : Subgroup A) := by
    intro r m hm
    have hmap : (P : Subgroup A).map (MulDistribMulAction.toMulAut R A r).toMonoidHom
        = (P : Subgroup A) :=
      Subgroup.characteristic_iff_map_eq.mp hPchar (MulDistribMulAction.toMulAut R A r)
    have hmem : (MulDistribMulAction.toMulAut R A r).toMonoidHom m ∈ (P : Subgroup A) := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- `A` not a `p`-group ⟹ `P ≠ ⊤` ⟹ `|A : P| > 1`.
  have hindex : 1 < (P : Subgroup A).index := by
    by_contra hle
    have h : (P : Subgroup A).index ≤ 1 := Nat.not_lt.mp hle
    have hidxpos : 0 < (P : Subgroup A).index := by
      have hmc := Subgroup.index_mul_card (P : Subgroup A)
      rcases Nat.eq_zero_or_pos (P : Subgroup A).index with h0 | h0
      · rw [h0, zero_mul] at hmc; exact absurd hmc.symm Nat.card_pos.ne'
      · exact h0
    have hidx1 : (P : Subgroup A).index = 1 := by omega
    have hPtop : (P : Subgroup A) = ⊤ := Subgroup.index_eq_one.mp hidx1
    have hcardeq : Nat.card (P : Subgroup A) = Nat.card A := by
      rw [hPtop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    exact hcon ⟨p, hp, IsPGroup.iff_card.mpr ⟨n, by rw [← hcardeq, hn]⟩⟩
  -- Frobenius `card ≡ 1 (mod |R|)` for the whole action and the restricted action on `P`.
  haveI : Fintype (P : Subgroup A) := Fintype.ofFinite _
  have hAmod : Nat.card A ≡ 1 [MOD Nat.card R] := by
    simpa only [Fintype.card_eq_nat_card] using hFrob.card_modEq_one
  letI instP : MulDistribMulAction R (P : Subgroup A) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction
      (P : Subgroup A) hinv
  have hFrobP : @OddOrder.Isaacs.Ch06.IsFrobeniusAction R (P : Subgroup A) _ _ instP :=
    hFrob.subgroup (P : Subgroup A) hinv
  have hPmod : Nat.card (P : Subgroup A) ≡ 1 [MOD Nat.card R] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobP.card_modEq_one
  -- `|R| ∣ |P| - 1` and (via `|A| = |A:P|·|P|`) `|R| ∣ |A:P| - 1`.
  have hRdvdP : Nat.card R ∣ Nat.card (P : Subgroup A) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hPmod.symm
  have hmul : (P : Subgroup A).index * Nat.card (P : Subgroup A) = Nat.card A :=
    Subgroup.index_mul_card _
  have hidxmod : (P : Subgroup A).index ≡ 1 [MOD Nat.card R] := by
    have h1 : (P : Subgroup A).index * Nat.card (P : Subgroup A)
        ≡ (P : Subgroup A).index * 1 [MOD Nat.card R] := Nat.ModEq.mul_left _ hPmod
    rw [mul_one, hmul] at h1
    exact h1.symm.trans hAmod
  have hRdvdidx : Nat.card R ∣ (P : Subgroup A).index - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hidxmod.symm
  -- Oddness of both factors (they multiply to the odd `|A|`).
  have hAodd' : Odd ((P : Subgroup A).index * Nat.card (P : Subgroup A)) := by
    rw [hmul]; exact hAodd
  obtain ⟨hidxodd, hcardPodd⟩ := Nat.odd_mul.mp hAodd'
  -- Each factor is `≥ 2|R| + 1`; their product exceeds the bound — contradiction.
  have hbP : 2 * Nat.card R + 1 ≤ Nat.card (P : Subgroup A) :=
    two_mul_add_one_le_of_odd_dvd hRodd hcardPodd hRdvdP hcardP
  have hbidx : 2 * Nat.card R + 1 ≤ (P : Subgroup A).index :=
    two_mul_add_one_le_of_odd_dvd hRodd hidxodd hRdvdidx hindex
  exact six_five_chief_factor_contradiction Nat.card_pos hbidx hbP hmul.symm hbound

/-- **Peterfalvi (6.5)(b) reduction: `H` is a `p`-group.**  Assemble the chief-factor core
`isPGroup_of_card_le_of_isFrobeniusAction` (the abelianization `Abelianization H` is a `p`-group)
with `isPGroup_of_isNilpotent_of_isPGroup_abelianization` (a nilpotent group with `p`-group
abelianization is a `p`-group).

Let `H` be a finite nilpotent group whose abelianization `Abelianization H` carries a
fixed-point-free action of a finite group `R` (in the Sibley setting `R = L/H` is the Frobenius
complement acting on `H/H'` by conjugation), with `|Abelianization H|` and `|R|` odd and
`|Abelianization H| ≤ 4|R|² + 1`.  Then `H` is a `p`-group for some prime `p`.

This is the group-theory conclusion of Peterfalvi (6.5) ("we may assume `H` is a non-abelian
`p`-group") in the form the (6.8) capstone consumes; the `≤ 4|R|² + 1` bound is the single
character-theoretic input ((6.2)/(6.3)), and the fixed-point-free `R`-action on `Abelianization H`
is supplied from the Frobenius alternative (6.8)(c1) / (6.4.c). -/
theorem isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {R : Type*} [Group R] [Finite R] [MulDistribMulAction R (Abelianization H)]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R (Abelianization H))
    (hHodd : Odd (Nat.card (Abelianization H))) (hRodd : Odd (Nat.card R))
    (hbound : Nat.card (Abelianization H) ≤ 4 * Nat.card R ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H := by
  obtain ⟨p, hp, hPab⟩ :=
    isPGroup_of_card_le_of_isFrobeniusAction hFrob hHodd hRodd hbound
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, isPGroup_of_isNilpotent_of_isPGroup_abelianization hPab⟩

/-- **Peterfalvi (6.5)(b) reduction in the Frobenius case (6.8)(c1): the kernel is a `p`-group.**
If `G = N ⋊ A` is a Frobenius group with nilpotent kernel `N`, `|Abelianization N|` and `|A|` are
odd, and `|Abelianization N| ≤ 4|A|² + 1`, then `N` is a `p`-group for some prime `p`.

This is `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` with the fixed-point-free
`A`-action on `Abelianization N` supplied directly from the Frobenius group: `A` acts
fixed-point-freely on `N` by conjugation (`toFrobeniusAction`), and since `⁅N,N⁆` is characteristic
in `N` (hence `A`-invariant), the action descends fixed-point-freely to the abelianization
`N / ⁅N,N⁆` (`IsFrobeniusAction.quotient`).  In the (6.8) capstone this is the Frobenius alternative
`hyp.cases.inl : IsFrobeniusGroup ↥L H W₁` (with `N = H`, `A = W₁`); the only remaining input is the
`≤ 4|W₁|² + 1` bound from the character theory ((6.2)/(6.3)). -/
theorem isPGroup_of_isFrobeniusGroup_of_card_le {G : Type*} [Group G] [Finite G]
    {N A : Subgroup G} [Group.IsNilpotent ↥N]
    (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G N A)
    (hHodd : Odd (Nat.card (Abelianization ↥N))) (hAodd : Odd (Nat.card ↥A))
    (hbound : Nat.card (Abelianization ↥N) ≤ 4 * Nat.card ↥A ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥N := by
  letI : N.Normal := h.isNormal
  letI actN : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have hFrobN : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥A ↥N := h.toFrobeniusAction
  -- `⁅N,N⁆` is characteristic in `N`, hence preserved by the automorphism `A`-action.
  have hM : ∀ a : ↥A, ∀ m ∈ commutator ↥N, a • m ∈ commutator ↥N := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator ↥N).Characteristic) (MulDistribMulAction.toMulAut ↥A ↥N a)
    have hmem : (MulDistribMulAction.toMulAut ↥A ↥N a).toMonoidHom m ∈ commutator ↥N := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- The fixed-point-free action descends to the abelianization quotient.
  letI actAb : MulDistribMulAction ↥A (Abelianization ↥N) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction (commutator ↥N) hM
  have hFrobAb : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥A (Abelianization ↥N) :=
    hFrobN.quotient (commutator ↥N) hM
  exact isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrobAb hHodd hAodd hbound

/-- **Peterfalvi (6.5)(b) reduction in the certain-type case (6.8)(c2): the kernel is a `p`-group.**
If a finite group `W` acts on a finite nilpotent group `H` with `(|W|, |H|) = 1`, such that for
every nonidentity `w ∈ W` the `w`-fixed points of `H` lie in `⁅H,H⁆` (the certain-type centralizer
condition `C_H(x) = W₂ ⊆ ⁅H,H⁆`), and `|Abelianization H|`, `|W|` are odd with
`|Abelianization H| ≤ 4|W|² + 1`, then `H` is a `p`-group for some prime `p`.

This is the (6.8)(c2) analogue of `isPGroup_of_isFrobeniusGroup_of_card_le`.  Here `W` does *not*
act fixed-point-freely on `H` (the fixed points `C_H(x) = W₂` are nontrivial), but since
`W₂ ⊆ ⁅H,H⁆` the action descends fixed-point-freely to `Abelianization H` (`IsFrobeniusAction`'s
`quotient_of_fixedPoints_le`, via the coprime fixed-point lifting Isaacs Cor 3.28); then the
(6.5)(b) reduction `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` applies.  In the
(6.8) capstone the fixed-points hypothesis is discharged from the certain-type fields
`centralizer_W2` (`C_L(x) ⊓ H = W₂`) and `W₂ ⊆ ⁅H,H⁆`, and the coprimality from the Hall datum
`gcd(|H|, |W₁|) = 1`. -/
theorem isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator {H W : Type*}
    [Group H] [Finite H] [Group.IsNilpotent H] [Group W] [Finite W] [MulDistribMulAction W H]
    (hCop : Nat.Coprime (Nat.card W) (Nat.card H))
    (hfix : ∀ w : W, w ≠ 1 → ∀ x : H, w • x = x → x ∈ commutator H)
    (hHodd : Odd (Nat.card (Abelianization H))) (hWodd : Odd (Nat.card W))
    (hbound : Nat.card (Abelianization H) ≤ 4 * Nat.card W ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H := by
  have hMinv : ∀ a : W, ∀ m ∈ commutator H, a • m ∈ commutator H := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator H).Characteristic) (MulDistribMulAction.toMulAut W H a)
    have hmem : (MulDistribMulAction.toMulAut W H a).toMonoidHom m ∈ commutator H := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  letI actAb : MulDistribMulAction W (Abelianization H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction (commutator H) hMinv
  have hFrobAb : OddOrder.Isaacs.Ch06.IsFrobeniusAction W (Abelianization H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.quotient_of_fixedPoints_le hCop (commutator H) hMinv hfix
  exact isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrobAb hHodd hWodd hbound

/-- A finite group with non-trivial abelianization carries a non-trivial linear character
`Γ →* ℂˣ`. Equivalently (via `IsSolvable.commutator_lt_top_of_nontrivial`) every non-trivial
finite solvable group has one.

This is the existence ingredient feeding **Peterfalvi (6.2)**: the section `K/A` (solvable and
non-trivial, since `A ⊊ K`) carries an irreducible character of degree `1`, which is what makes
`S(A)` non-empty so the degree bound `2|L:C|√|C:D| ≥ |K:A| − 1` has content. The proof reduces to
the abelianization `Γ ⧸ ⁅Γ,Γ⁆` (non-trivial exactly when `⁅Γ,Γ⁆ ≠ ⊤`) and uses that `ℂ` is
separably closed of characteristic zero, hence has enough roots of unity
(`IsSepClosed.hasEnoughRootsOfUnity`, instantiated at `n = exponent` via the supplied `NeZero`). -/
theorem exists_monoidHom_units_ne_one_of_commutator_ne_top {Γ : Type*} [Group Γ] [Finite Γ]
    (h : commutator Γ ≠ ⊤) : ∃ χ : Γ →* ℂˣ, χ ≠ 1 := by
  -- `Abelianization Γ = Γ ⧸ ⁅Γ,Γ⁆` is non-trivial precisely because `⁅Γ,Γ⁆ ≠ ⊤`.
  haveI : Nontrivial (Abelianization Γ) := by
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    exact h (by
      rw [← Subgroup.index_eq_one]
      exact @Nat.card_of_subsingleton (Abelianization Γ) 1 hns)
  obtain ⟨a, ha⟩ := exists_ne (1 : Abelianization Γ)
  -- `ℂ` separably closed + characteristic zero ⟹ enough roots of unity at `n = exponent`.
  haveI : NeZero ((Monoid.exponent (Abelianization Γ) : ℂ)) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization Γ) ℂ ha
  -- Pull `φ` back along the surjection `Abelianization.of`; non-triviality transports.
  refine ⟨φ.comp Abelianization.of, fun hcon => hφ ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  simpa using DFunLike.congr_fun hcon g

/-- A finite group with non-trivial abelianization carries a non-trivial **degree-one irreducible
character**. This is the `IrreducibleCharacter`-level form of the **Peterfalvi (6.2)** existence
ingredient: bridging `exists_monoidHom_units_ne_one_of_commutator_ne_top` through the linear
character functor `linearIrreducibleCharacter`. Applied to the section `K/A` (non-trivial solvable)
and inflated to `K`, it furnishes a non-trivial `θ ∈ Irr K` with `A ⊆ ker θ`, i.e. a member of
`S(A)`. -/
theorem exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top {Γ : Type*}
    [Group Γ] [Finite Γ] (h : commutator Γ ≠ ⊤) :
    ∃ χ : IrreducibleCharacter Γ,
      χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ ∧
      (χ : ClassFunction Γ ℂ) (1 : Γ) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_monoidHom_units_ne_one_of_commutator_ne_top h
  refine ⟨OddOrder.RepresentationTheory.linearIrreducibleCharacter φ, ?_,
    OddOrder.RepresentationTheory.linearIrreducibleCharacter_apply_one φ⟩
  rw [Ne, OddOrder.RepresentationTheory.linearIrreducibleCharacter_eq_trivial_iff]
  exact hφ

/-- **Peterfalvi (6.2): `S(A)` is non-empty when `K/A` is non-trivial.**  If `A ◁ K` is normal with
`K/A` of non-trivial abelianization (in particular when `K/A` is a non-trivial solvable group, e.g.
`A ⊊ K` with `K` solvable), then `K` carries a non-trivial irreducible character `θ` of degree `1`
with `A ⊆ ker θ` — i.e. a member of `S(A) = {Ind_K^L θ | θ ∈ Irr K, A ⊆ ker θ, θ ≠ 1}`.

This is the concrete, `(K, A)`-level existence ingredient for the (6.2) degree bound: it inflates
the degree-one character produced on the section `K/A`
(`exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`) back up to `K` via
`OddOrder.RepresentationTheory.inflate`, transporting non-triviality
(`inflate_eq_trivial_iff`), the kernel containment (`subset_characterKernel_inflate`) and the
degree (`inflate_apply_one`). -/
theorem exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top {K : Type*}
    [Group K] [Finite K] (N : Subgroup K) [N.Normal] (h : commutator (K ⧸ N) ≠ ⊤) :
    ∃ θ : IrreducibleCharacter K,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter K ∧
      (N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction K ℂ) ∧
      (θ : ClassFunction K ℂ) (1 : K) = 1 := by
  obtain ⟨χbar, hne, hdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top h
  refine ⟨OddOrder.RepresentationTheory.inflate N χbar, ?_,
    OddOrder.RepresentationTheory.subset_characterKernel_inflate N χbar, ?_⟩
  · rw [Ne, OddOrder.RepresentationTheory.inflate_eq_trivial_iff]; exact hne
  · rw [OddOrder.RepresentationTheory.inflate_apply_one]; exact hdeg

/-- **Peterfalvi (6.8): Dade-based carrier** (T1, faithful replacement of `SibleySetup`).

The legacy `SibleySetup` carried an opaque `coherence.tau` with a *global* `IsIntegralIsometry`,
which does not exist in Feit–Thompson (`dim CF(L) > dim CF(G)`); its `CoherenceTarget` was
therefore undischargeable. This carrier instead packages the genuine §4 Dade datum
`dade : S04.Hypothesis G H^# L`, so the coherence map `tau` is the **real**
`dadeIntegralCharacterMap` and `CoherenceTarget` is `IsCoherent` for that map — exactly the shape
the §7 coherence engine produces (`coherentUnion_of_glued`, `coherentEqualDegree_fromDade`, …),
realizing "τ coincides with the Dade isometry relative to (A,L,G)" (mmd 04.8 L150).

**Migration status (T1, `notes/peterfalvi/s08_6_8_assembly_plan.md`)**: this commit lands the
re-parametrization (`L : Subgroup G`, source type `↥L`) and the real-`tau` `CoherenceTarget`. The
remaining (6.8) hypotheses — `S = {Ind_H^L θ | θ ≠ 1}`, the split `L = H ⋊ W₁`, `H` nilpotent, and
the case (c1)/(c2) disjunction (`S06.CertainTypeHypothesis`) — are added next, after which
`sibleySetup_is_coherent` is restated against this carrier and the legacy `SibleySetup` removed. -/
structure SibleyDadeHypothesis (G : Type*) [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (L : Subgroup G) [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (H : Subgroup ↥L) [Invertible (Nat.card ↥H : ℂ)] where
  /-- A complement-side subgroup `W₁`; the split `L = H ⋊ W₁` is added in the next migration step. -/
  W1 : Subgroup ↥L
  H_ne_bot : H ≠ ⊥
  H_normal : H.Normal
  /-- `H` is nilpotent (Peterfalvi (6.8.a)). -/
  H_nilpotent : Group.IsNilpotent ↥H
  /-- `L = H ⋊ W₁`: `W₁` is a complement to the normal `H` (Peterfalvi (6.8.a)). -/
  split : Subgroup.IsComplement' H W1
  W1_nontrivial : W1 ≠ ⊥
  card_L_odd : Odd (Nat.card L)
  /-- `H^#` is a TI-subset of `G` relative to `L` (corrected ambient: TI in `G`, not in `↥L`). -/
  H_sharp_ti : OddOrder.GroupTheory.IsTISubset (sharpImage H) L
  /-- The §4 Dade datum on `A = H^#`; its Dade isometry *is* `tau`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G (sharpImage H) L
  hconj : dade.HConjInvariant
  /-- In the TI situation ((6.8.a): `H^#` is a TI-subset of `G` with normalizer `L`), the §4 Dade
  datum's local subgroups are trivial, `dade.H a = ⊥` — i.e. `dade` is the Dade map of the
  TI-subset construction (`S04.of_isTISubset`, whose `H a = ⊥`, S04:308).  This faithful (6.8.a)
  fact makes the Dade map agree with `Ind_L^G` on the supported lattice, yielding the (2.7)
  reciprocity `⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L` (`inner_tau_eq_inner_restrict`), the gateway to the
  (6.8.1) `Res_L(η₁^{τ₁})` decomposition. -/
  dade_H_eq_bot : ∀ a : {a : G // a ∈ sharpImage H}, dade.H a = ⊥
  /-- The base character set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (Peterfalvi (6.8.b)). -/
  S : Set (ClassFunction ↥L ℂ)
  /-- `S` is exactly the set of characters induced from nontrivial irreducibles of `H`. -/
  S_eq : S = {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}
  /-- Peterfalvi (6.8)(c): the configuration is one of two cases.

  * **(c1)** `L` is a Frobenius group with kernel `H` and complement `W₁`.
  * **(c2)** Hypothesis (4.6) holds — encoded by a `S06.CertainTypeHypothesis` on the *same* Dade
    datum (`cert.dade = dade`) whose kernel is `K = H` — with `w₂ = |W₂|` prime, `W₂ ⊆ [H,H]`, and
    the Hall coprimality `gcd(|H|, |W₁|) = 1` (Peterfalvi (4.2.a): `W₁` is a cyclic *Hall* subgroup
    of `L = H ⋊ W₁`, so its order is coprime to `|H| = [L : W₁]`).  This coprimality is the input to
    Isaacs (3.28) that lifts a `W₁`-fixed coset of `H/[H,H]` to a `W₁`-fixed element of `H`.

  The (4.6)↔(6.8) renaming sets the (4.6)-kernel `K` to the (6.8) `H` (hence `cert.K = H`), and the
  (4.2)/(6.8) complement is shared (`cert.W1 = W1`, both giving `L = H ⋊ W₁`). With the S06 audit
  done (`S06.CertainTypeHypothesis` now faithfully encodes (4.2): the false `W₁ ⊔ W₂ = ⊤` removed,
  and complement / cyclic / `W₂ ≤ K` / `C_K(x) = W₂` / odd-`W` added), this matches textbook
  (6.8)(c2). -/
  cases :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H W1 ∨
    ∃ cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L,
      cert.dade = dade ∧ cert.K = H ∧ cert.W1 = W1 ∧
        (Nat.card cert.W2).Prime ∧ cert.W2 ≤ ⁅H, H⁆ ∧
        Nat.Coprime (Nat.card ↥H) (Nat.card W1)

/-- **(T7-c2 case A, brick ①)** A multiplicative `ℂ`-valued function `f` (e.g. a linear character)
that is *invariant* under a fixed-point-free endomorphism `σ` is identically `1`.  Indeed
`z ↦ z·(σ z)⁻¹` is surjective (`MonoidHom.FixedPointFree.commutatorMap_surjective`), and
`f (z₀·(σ z₀)⁻¹) = f z₀ · f (σ z₀)⁻¹ = f z₀ · (f z₀)⁻¹ = 1` using `f ∘ σ = f`. -/
theorem eq_one_of_fixedPointFree_invariant {Z : Type*} [Group Z] [Finite Z]
    {F : Type*} [FunLike F Z Z] [MonoidHomClass F Z Z] {σ : F}
    (hσ : MonoidHom.FixedPointFree σ)
    {f : Z → ℂ} (hf_mul : ∀ a b, f (a * b) = f a * f b) (hf_one : f 1 = 1)
    (hinv : ∀ z, f (σ z) = f z) (z : Z) : f z = 1 := by
  have hne : ∀ a : Z, f a ≠ 0 := fun a ha => one_ne_zero
    (show (1 : ℂ) = 0 by rw [← hf_one, ← mul_inv_cancel a, hf_mul, ha, zero_mul])
  have hf_inv : ∀ a : Z, f a⁻¹ = (f a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← hf_mul, mul_inv_cancel, hf_one])
  obtain ⟨z₀, hz₀⟩ := hσ.commutatorMap_surjective z
  rw [MonoidHom.commutatorMap_apply, div_eq_mul_inv] at hz₀
  calc f z = f (z₀ * (σ z₀)⁻¹) := by rw [hz₀]
    _ = f z₀ * f (σ z₀)⁻¹ := hf_mul _ _
    _ = f z₀ * (f (σ z₀))⁻¹ := by rw [hf_inv]
    _ = f z₀ * (f z₀)⁻¹ := by rw [hinv]
    _ = 1 := mul_inv_cancel₀ (hne z₀)

/-- **(T8.11p0) natural degree witnesses for one X-adjoin member family.**

This packages the positive natural degree of the new character, the anchor, and every member of a
finite accumulator family, together with the member square-sum `D`.  The hypothesis `i₁ ∈ s`
ensures `D` is positive. -/
theorem exists_natDegreeData_for_xAdjoinMemberFamily
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {i₁ : ι} (hi₁ : i₁ ∈ s) :
    ∃ dχ d₁ D : ℕ, ∃ dmem : ι → ℕ,
      (χ : ClassFunction G ℂ) 1 = (dχ : ℂ) ∧
      (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ) ∧
      (∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ)) ∧
      (∑ i ∈ s, dmem i * dmem i = D) ∧
      0 < d₁ ∧ 0 < D := by
  classical
  obtain ⟨dχ, _hdχpos, hχone⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  obtain ⟨d₁, hd₁pos, hχ₁one⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  let dmem : ι → ℕ := fun i =>
    (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i)).choose
  have hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ) := by
    intro i _hi
    exact (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i)).choose_spec.2
  let D : ℕ := ∑ i ∈ s, dmem i * dmem i
  have hDsum : ∑ i ∈ s, dmem i * dmem i = D := rfl
  have hDpos : 0 < D := by
    have hpos_i₁ : 0 < dmem i₁ :=
      (irreducibleCharacter_apply_one_eq_pos_natCast (χmem i₁)).choose_spec.1
    have hterm_pos : 0 < dmem i₁ * dmem i₁ := Nat.mul_pos hpos_i₁ hpos_i₁
    have hsum_pos : 0 < ∑ i ∈ s, dmem i * dmem i := by
      exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₁, hi₁, hterm_pos⟩
    simpa [D] using hsum_pos
  exact ⟨dχ, d₁, D, dmem, hχone, hχ₁one, hmemone, hDsum, hd₁pos, hDpos⟩

/-- A natural witness for the degree of an irreducible character is positive. -/
theorem natDegree_pos_of_irreducibleCharacter_apply_one_eq
    {G : Type*} [Group G] {χ : IrreducibleCharacter G} {d : ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) : 0 < d := by
  obtain ⟨e, hepos, heq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  have hde : d = e := Nat.cast_injective (hχone.symm.trans heq)
  rwa [hde]

/-- A common index in a factorization of an irreducible character degree is positive. -/
theorem commonIndex_pos_of_natDegree_factor
    {G : Type*} [Group G] {χ : IrreducibleCharacter G} {idx d θ : ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) (hd : d = idx * θ) :
    0 < idx := by
  have hdpos : 0 < d := natDegree_pos_of_irreducibleCharacter_apply_one_eq hχone
  by_contra hidx
  have hidx0 : idx = 0 := Nat.eq_zero_of_not_pos hidx
  have hd0 : d = 0 := by simp [hd, hidx0]
  omega

/-- A common index coprime to `p` is coprime to any residual degree that is a power of `p`. -/
theorem coprime_commonIndex_primePower
    {idx p θ m : ℕ} (hidx_p : Nat.Coprime idx p) (hθ : θ = p ^ m) :
    Nat.Coprime idx θ := by
  rw [hθ]
  exact hidx_p.pow_right m

/-- A member-family square sum is positive once it contains one irreducible character. -/
theorem natDegreeSquareSum_pos_of_memberFamily
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χmem : ι → IrreducibleCharacter G} {i₁ : ι} {D : ℕ} {dmem : ι → ℕ}
    (hi₁ : i₁ ∈ s)
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D) :
    0 < D := by
  have hpos_i₁ : 0 < dmem i₁ :=
    natDegree_pos_of_irreducibleCharacter_apply_one_eq (hmemone i₁ hi₁)
  have hterm_pos : 0 < dmem i₁ * dmem i₁ := Nat.mul_pos hpos_i₁ hpos_i₁
  have hsum_pos : 0 < ∑ i ∈ s, dmem i * dmem i := by
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₁, hi₁, hterm_pos⟩
  exact hDsum ▸ hsum_pos

/-- A common-index factorization of every member degree makes the common-index square divide the
member degree square sum. -/
theorem sq_dvd_natDegreeSquareSum_of_commonIndex
    {ι : Type*} {s : Finset ι} {idx D : ℕ}
    {dmem θmem : ι → ℕ}
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hdmem : ∀ i ∈ s, dmem i = idx * θmem i) :
    idx * idx ∣ D := by
  rw [← hDsum]
  apply Finset.dvd_sum
  intro i hi
  refine ⟨θmem i * θmem i, ?_⟩
  rw [hdmem i hi]
  ring


namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- The coherence map `τ` of the (6.8) setup, realized as the genuine §4 Dade isometry
(`dadeIntegralCharacterMap`) — **not** an opaque global isometry. -/
noncomputable abbrev tau (hyp : SibleyDadeHypothesis G L H) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
    (hyp.dade.fullDadeIsometryData hyp.hconj)

/-- The (6.8) coherence target: `S` is coherent for the **real Dade map** `tau`.  This is exactly
the conclusion shape produced by the §7 engine, hence honestly dischargeable — unlike the legacy
`SibleySetup.CoherenceTarget`, which required a nonexistent global isometry. -/
abbrev CoherenceTarget (hyp : SibleyDadeHypothesis G L H) :=
  OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.S
    (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)

/-- **(6.8.1) Dade reciprocity for the Sibley carrier.**  Since `H^#` is TI (`dade_H_eq_bot`), the
real Dade map `tau` satisfies `⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L` for supported `α ∈ CF(L, H^#)` and any
`ψ ∈ CF(G)` (`inner_dadeIntegralCharacterMap_eq_inner_restrict`).  This is the move the (6.8.1)
proof (mmd L176) uses to rewrite `⟨η₁^{τ₁}, (χᵢ − dᵢχ₁)^τ⟩ = ⟨Res_L(η₁^{τ₁}), χᵢ − dᵢχ₁⟩`, feeding
the `Res_L(η₁^{τ₁}) = c∑dᵢχᵢ + χ′` decomposition. -/
theorem inner_tau_eq_inner_restrict (hyp : SibleyDadeHypothesis G L H)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (hyp.tau α) ψ = ClassFunction.inner α (ClassFunction.restrict L ψ) :=
  inner_dadeIntegralCharacterMap_eq_inner_restrict hyp.dade hyp.hconj hyp.dade_H_eq_bot hαsupp ψ

/-- (6.8)(a) consequence: `[L : H] = |W₁|`.  From the complement `L = H ⋊ W₁` (`hyp.split`).
This is the common degree of the members of `Y = S(H')`: by [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`), `(Ind_H^L θ)(1) = [L:H]·θ(1) = |W₁|` for the
degree-`1` characters `θ ∈ Irr(H/H')`. -/
theorem index_H_eq_card_W1 (hyp : SibleyDadeHypothesis G L H) :
    H.index = Nat.card hyp.W1 :=
  (Subgroup.IsComplement.card_right (Subgroup.isComplement'_def.mp hyp.split)).symm

/-- Degree-one source characters induce to class functions of degree |W1| in the (6.8)
setup. This is the degree side of the Y = S(Hprime) family used in the final coherence assembly. -/
theorem induce_apply_one_eq_card_W1_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L) =
      (Nat.card hyp.W1 : ℂ) := by
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ_one, mul_one,
    hyp.index_H_eq_card_W1]

/-- If two source class functions induce to the same value at 1, their induced difference is
supported on H-sharp in the (6.8) Dade support. -/
theorem support_sub_induce_subset_sharpImage_of_apply_one_eq
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : ClassFunction ↥H ℂ)
    (hone : OddOrder.RepresentationTheory.ClassFunction.induce H θ (1 : ↥L) =
      OddOrder.RepresentationTheory.ClassFunction.induce H ψ (1 : ↥L)) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H θ -
        OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  intro x hx
  have hθsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H θ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H θ
  have hψsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H ψ
  have hxH : x ∈ H := by
    rcases OddOrder.RepresentationTheory.ClassFunction.support_sub_subset
        (OddOrder.RepresentationTheory.ClassFunction.induce H θ)
        (OddOrder.RepresentationTheory.ClassFunction.induce H ψ) hx with hxθ | hxψ
    · exact hθsupp hxθ
    · exact hψsupp hxψ
  have hxne : x ≠ 1 := by
    intro hx1
    apply hx
    rw [hx1, OddOrder.RepresentationTheory.ClassFunction.sub_apply, hone, sub_self]
  change (x : G) ∈ sharpImage H
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  · intro hx1G
    exact hxne (Subtype.ext hx1G)

/-- Degree-one source characters give induced differences supported on H-sharp. -/
theorem support_sub_induce_subset_sharpImage_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hψ_one : (ψ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) -
        OddOrder.RepresentationTheory.ClassFunction.induce H (ψ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  hyp.support_sub_induce_subset_sharpImage_of_apply_one_eq
    (θ : ClassFunction ↥H ℂ) (ψ : ClassFunction ↥H ℂ) (by
      rw [hyp.induce_apply_one_eq_card_W1_of_degree_one θ hθ_one,
        hyp.induce_apply_one_eq_card_W1_of_degree_one ψ hψ_one])

/-- Equal-degree induced irreducible families from degree-one source characters are coherent for
Sibley's Dade map. This is the engine-call form of the (6.8) Y = S(Hprime) step: once the
eta-family of irreducible induced characters is constructed and shown injective, the remaining
(1.1)+(1.4) equal-degree coherence hypotheses are discharged by the Sibley carrier. -/
noncomputable def coherentInducedDegreeOneFamily
    (hyp : SibleyDadeHypothesis G L H) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (θ : Fin n → IrreducibleCharacter ↥H) (η : Fin n → IrreducibleCharacter ↥L)
    (hη_ind : ∀ j,
      (η j : ClassFunction ↥L ℂ) =
        OddOrder.RepresentationTheory.ClassFunction.induce H (θ j : ClassFunction ↥H ℂ))
    (hηinj : Function.Injective η)
    (hθ_one : ∀ j, (θ j : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => (η j : ClassFunction ↥L ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hdeg : ∀ j, ((η j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 =
      ((η 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    rw [hη_ind j, hη_ind 0,
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ j) (hθ_one j),
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ 0) (hθ_one 0)]
  have hsuppdiff : ∀ j,
      (OddOrder.RepresentationTheory.irreducibleCharacterDifference η j).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    simpa [OddOrder.RepresentationTheory.irreducibleCharacterDifference, hη_ind j, hη_ind 0] using
      hyp.support_sub_induce_subset_sharpImage_of_degree_one (θ j) (θ 0)
        (hθ_one j) (hθ_one 0)
  have h1notA : (1 : G) ∉ sharpImage H := by
    intro h
    exact h.2 rfl
  exact OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hyp.hconj hn η hηinj
    hdeg hsuppdiff h1notA

/-- **(6.8)(c2) inertia equality** for a nontrivial linear `θ`.

Under the (4.6)/(c2) data — `H ⋊ W₁`, `C_H(w) = W₂ ⊆ ⁅H,H⁆` for `w ∈ W₁∖1`, and the Hall
coprimality `gcd(|H|,|W₁|) = 1` — the inertia group of a nontrivial degree-one `θ` is exactly `H`.

Proof.  Pass to `Ḡ = L/⁅H,H⁆`, `H̄ = H/⁅H,H⁆` (abelian).  `θ` is linear, so inflates from a
nontrivial `θ̄ ∈ Irr H̄`.  The coprimality + Isaacs (3.28) lift gives `C_{H̄}(w̄) = 1` for
`w̄ ∈ W̄₁∖1`; since `H̄` is abelian, Brauer's permutation lemma turns this into "`w̄` fixes only the
trivial irreducible", so `w̄ ∉ I_{Ḡ}(θ̄)`.  The inertia-transfer bridge then gives `w ∉ I_L(θ)` for
`w ∈ W₁∖1`, and the complement `L = H ⋊ W₁` reduces a general `g ∉ H` to this case (`I_L(θ) ⊇ H`, so
the `H`-part is absorbed). -/
theorem inertia_eq_H_of_c2 (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  -- The quotient `Ḡ = L/⁅H,H⁆` and the image `H̄ = H/⁅H,H⁆`.
  set M : Subgroup ↥L := ⁅H, H⁆ with hM_def
  haveI hMnormal : M.Normal := by rw [hM_def]; infer_instance
  set mkM : ↥L →* (↥L ⧸ M) := QuotientGroup.mk' M with hmkM_def
  set Hbar : Subgroup (↥L ⧸ M) := H.map mkM with hHbar_def
  haveI hHbar_normal : Hbar.Normal := by rw [hHbar_def, hmkM_def]; infer_instance
  -- `H̄` is abelian: images of `H` commute since their commutators land in `⁅H,H⁆ = ker mkM`.
  have hHbar_comm : ∀ a b : ↥Hbar, Commute a b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [hHbar_def, Subgroup.mem_map] at ha hb
    obtain ⟨x, hxH, rfl⟩ := ha
    obtain ⟨y, hyH, rfl⟩ := hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    -- `mkM x` and `mkM y` commute because `⁅x,y⁆ ∈ ⁅H,H⁆ = ker mkM`.
    have hcomm_elt : ⁅(x : ↥L), (y : ↥L)⁆ ∈ M := by
      rw [hM_def]; exact Subgroup.commutator_mem_commutator hxH hyH
    have hmk_one : mkM ⁅(x : ↥L), (y : ↥L)⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm_elt
    rw [map_commutatorElement] at hmk_one
    exact commutatorElement_eq_one_iff_mul_comm.mp hmk_one
  -- The corestriction `q : ↥H →* ↥H̄` with `(q x : Ḡ) = mkM x`.
  set q : ↥H →* ↥Hbar :=
    (mkM.comp H.subtype).codRestrict Hbar (fun x => by
      rw [hHbar_def]; exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩) with hq_def
  have hq : ∀ x : ↥H, ((q x : ↥Hbar) : ↥L ⧸ M) = mkM (x : ↥L) := fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩
    rw [hHbar_def, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz
    exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q : ClassFunction ↥Hbar ℂ → ClassFunction ↥H ℂ) :=
    ClassFunction.compHom_injective_of_surjective hq_surj
  -- `θ` is linear, hence kills `⁅H,H⁆.subgroupOf H = commutator ↥H`, so inflates from `H̄`.
  set N : Subgroup ↥H := M.subgroupOf H with hN_def
  haveI hN_normal : N.Normal := by rw [hN_def, hM_def]; exact hMnormal.subgroupOf H
  have hN_eq : N = _root_.commutator ↥H := by
    rw [hN_def, hM_def, ← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hker : (N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro n hn
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, hθ_one]
    -- `θ` is multiplicative with `θ(1)=1`, so `{x | θ x = 1}` is a subgroup containing commutators.
    have hθ1 : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1 := hθ_one
    have hn' : n ∈ Subgroup.closure (commutatorSet ↥H) := by
      have : n ∈ N := hn
      rwa [hN_eq, _root_.commutator_eq_closure] at this
    refine Subgroup.closure_induction
      (p := fun g _ => (θ : ClassFunction ↥H ℂ) g = 1) ?_ ?_ ?_ ?_ hn'
    · rintro _ ⟨a, b, rfl⟩
      exact θ.isIrreducible.apply_commutatorElement_eq_one_of_apply_one_eq_one hθ1 a b
    · exact hθ1
    · intro a b _ _ ha hb
      rw [θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1, ha, hb, one_mul]
    · intro a _ ha
      have hai := θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1 a a⁻¹
      rw [mul_inv_cancel, hθ1, ha, one_mul] at hai
      exact hai.symm
  have hkerq : q.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    change q x = 1 ↔ (x : ↥L) ∈ M
    constructor
    · intro hx
      have hx1 : mkM (x : ↥L) = 1 := by rw [← hq x, hx]; rfl
      rw [hmkM_def] at hx1
      exact (QuotientGroup.eq_one_iff _).mp hx1
    · intro hx
      apply Subtype.ext
      rw [hq x, hmkM_def]
      exact (QuotientGroup.eq_one_iff _).mpr hx
  -- `θ` inflates from a `θ̄ : Irr ↥H̄` along the surjection `q` (linear ⟹ `ker q = N ⊆ ker θ`).
  obtain ⟨θbar, hcompq⟩ :=
    exists_compHom_eq_of_subset_characterKernel hq_surj θ (by rw [hkerq]; exact hker)
  -- `θ̄` is nontrivial, else `θ = compHom q (triv) = triv`.
  have hθbar_ne : θbar ≠ trivialIrreducibleCharacter ↥Hbar := by
    intro hbar
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hcompq, hbar]
    ext x
    simp [ClassFunction.compHom_apply, trivialIrreducibleCharacter,
      trivialClassFunction_apply]
  -- **B1′** (fixed-point-free action of `W̄₁` on `H̄`): `C_{H̄}(w̄) = 1` for `w̄ ∈ W̄₁∖1`.
  -- We only need the specific `w̄ = mkM w`; the S03 `≤ N` quotient lemma supplies it.
  have hNK : (⁅H, H⁆ : Subgroup ↥L) ≤ H := Subgroup.commutator_le_left H H
  have hcentral : ∀ x ∈ hyp.W1, x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥L) ⊓ H ≤ M := by
    intro x hxW1 hxne
    have hcw2 : Subgroup.centralizer ({x} : Set ↥L) ⊓ cert.K = cert.W2 :=
      cert.centralizer_W2 x (hW1 ▸ hxW1) hxne
    rw [hK] at hcw2
    rw [hcw2, hM_def]; exact hW2
  have hlift : ∀ x ∈ hyp.W1, x ≠ 1 → ∀ y ∈ H,
      mkM (x * y * x⁻¹) = mkM y →
        ∃ c : ↥L, c ∈ H ∧ mkM c = mkM y ∧ x * c * x⁻¹ = c := by
    intro x hxW1 hxne y hyH hfix
    have hcop_x : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥H) := by
      rw [Nat.card_zpowers]
      have hdvd : orderOf x ∣ Nat.card hyp.W1 := hyp.W1.orderOf_dvd_natCard hxW1
      exact (hcop.coprime_dvd_right hdvd).symm
    exact OddOrder.BG.Ch1.S03.fixedPoint_lift_of_generator_quotient_fixed
      hNK hcop_x (Or.inl (by infer_instance)) hyH hfix
  have hB1 : ∀ qx ∈ hyp.W1.map mkM, qx ≠ 1 →
      Subgroup.centralizer ({qx} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ := by
    rw [hHbar_def, hmkM_def]
    exact OddOrder.BG.Ch1.S03.quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift_of_le
      hcentral hlift
  -- Assemble: `I_L(θ) = H` by `le_antisymm`.
  apply le_antisymm
  · -- `I_L(θ) ≤ H`: a `g ∉ H` is `h·w` with `w ∈ W₁∖1`, and `w ∉ I_L(θ)`.
    intro g hg
    by_contra hgH
    -- Write `g = h * w` via the complement `L = H ⋊ W₁`.
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    -- `w ≠ 1`, else `g = h ∈ H`.
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1
      apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    -- `h ∈ H ⊆ I_L(θ)`, so `w = h⁻¹·g ∈ I_L(θ)`.
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).mul_mem
        ((ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).inv_mem hhinertia)
        (ClassFunction.mem_inertia.mpr hg)
    -- Transfer `w ∈ I_L(θ)` to `w̄ ∈ I_{Ḡ}(θ̄)`.
    rw [← hcompq] at hwinertia
    have hwbar : mkM (w : ↥L) ∈ ClassFunction.inertia (θbar : ClassFunction ↥Hbar ℂ) :=
      (mem_inertia_compHom_iff q hq hqinj (θbar : ClassFunction ↥Hbar ℂ) (w : ↥L)).mp hwinertia
    -- But `w̄ ∉ I_{Ḡ}(θ̄)`: `C_{H̄}(w̄) = 1`, abelian Brauer, `θ̄ ≠ triv`.
    have hwbar_mem : mkM (w : ↥L) ∈ hyp.W1.map mkM :=
      Subgroup.mem_map.mpr ⟨w, w.property, rfl⟩
    have hwbar_ne : mkM (w : ↥L) ≠ 1 := by
      intro hw1
      have hwM : (w : ↥L) ∈ M := by
        rw [hmkM_def, QuotientGroup.mk'_apply] at hw1
        exact (QuotientGroup.eq_one_iff _).mp hw1
      exact hwne (Subgroup.disjoint_def.mp hyp.split.disjoint (hNK (hM_def ▸ hwM)) w.property)
    have hfree : Subgroup.centralizer ({mkM (w : ↥L)} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ :=
      hB1 (mkM (w : ↥L)) hwbar_mem hwbar_ne
    have hclass : Nat.card (Function.fixedPoints
        (ConjClasses.conjByPerm (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)))) = 1 :=
      card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot
        (mkM (w : ↥L)) hHbar_comm hfree
    exact not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one
      (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)) hclass hθbar_ne hwbar
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **(T7-c2 case A) Inertia `I_L(θ) = H`** via the **fixed-point-free action on `Z`**.  Here
`Z ≤ H` is central in `H` (`Z.subgroupOf H ≤ Z(H)`), normalized by `W₁`, with `W₁∖1` acting
fixed-point-freely (`C_Z(w) = Z ∩ W₂ = 1` in case A).  If `w ∈ W₁∖1` fixed `θ`, the central linear
character `φ` of `Res_Z θ` ([Is] 2.27) would be `σ = (·)^w`-invariant, hence `≡ 1`
(`eq_one_of_fixedPointFree_invariant`), forcing `Z.subgroupOf H ⊆ Ker θ`, contradicting `hZker`.
So `I_L(θ) ∩ W₁ = 1` and the complement split `L = H ⋊ W₁` gives `I_L(θ) = H`.  Needs no Hall
coprimality and works for an arbitrary (not necessarily linear) `θ`. -/
theorem inertia_eq_H_of_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    {θ : IrreducibleCharacter ↥H}
    (hZker : ¬ ((Z.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  obtain ⟨φ, hφirr, hφ1, -, hφpt⟩ :=
    θ.isIrreducible.exists_central_linear_restriction (Z.subgroupOf H) hZcentral
  have hφmul : ∀ a b : ↥(Z.subgroupOf H), φ (a * b) = φ a * φ b :=
    hφirr.map_mul_of_apply_one_eq_one hφ1
  have hθ1_ne : (θ : ClassFunction ↥H ℂ) 1 ≠ 0 := by
    obtain ⟨n, hpos, hn1, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
    rw [hn1]; exact_mod_cast hpos.ne'
  apply le_antisymm
  · intro g hg
    by_contra hgH
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1; apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia _).mul_mem
        ((ClassFunction.inertia _).inv_mem hhinertia) (ClassFunction.mem_inertia.mpr hg)
    have hwW1 : (w : ↥L) ∈ hyp.W1 := w.property
    -- Conjugation `σ` by `w` on `Z`, fixed-point-free (`C_Z(w) = Z ∩ W₂ = 1`).
    set σ : MulAut ↥Z := Z.normalizerMonoidHom ⟨(w : ↥L), hZnorm (w : ↥L) hwW1⟩ with hσ_def
    have hσval : ∀ z : ↥Z, ((σ z : ↥Z) : ↥L) = (w : ↥L) * (z : ↥L) * (w : ↥L)⁻¹ := fun _ => rfl
    have hσfpf : MonoidHom.FixedPointFree σ := by
      intro z hz
      have hzmem : ((z : ↥Z) : ↥L) ∈ Subgroup.centralizer ({(w : ↥L)} : Set ↥L) ⊓ Z := by
        refine Subgroup.mem_inf.mpr ⟨?_, z.property⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
        have hzL := congrArg (Subtype.val : ↥Z → ↥L) hz
        rw [hσval] at hzL
        rw [mul_inv_eq_iff_eq_mul] at hzL
        exact hzL
      rw [hZfpf (w : ↥L) hwW1 hwne, Subgroup.mem_bot] at hzmem
      exact Subtype.ext hzmem
    -- `f = φ ∘ iso` is multiplicative and `σ`-invariant; brick ① gives `φ ≡ 1`.
    set iso : ↥Z ≃* ↥(Z.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hZH).symm with hiso_def
    have hisoL : ∀ z : ↥Z, (((iso z : ↥(Z.subgroupOf H)) : ↥H) : ↥L) = (z : ↥L) := fun _ => rfl
    set f : ↥Z → ℂ := fun z => φ (iso z) with hf_def
    have hfmul : ∀ a b : ↥Z, f (a * b) = f a * f b := fun a b => by
      simp only [hf_def, map_mul, hφmul]
    have hfone : f 1 = 1 := by simp only [hf_def, map_one, hφ1]
    have hfinv : ∀ z : ↥Z, f (σ z) = f z := by
      intro z
      have hconj : ClassFunction.conjBy (w : ↥L) (θ : ClassFunction ↥H ℂ)
          = (θ : ClassFunction ↥H ℂ) := ClassFunction.mem_inertia.mp hwinertia
      have hval : (θ : ClassFunction ↥H ℂ) ((iso (σ z) : ↥(Z.subgroupOf H)) : ↥H)
          = (θ : ClassFunction ↥H ℂ) ((iso z : ↥(Z.subgroupOf H)) : ↥H) := by
        have hc := congrArg (fun ψ : ClassFunction ↥H ℂ => ψ ((iso z : ↥(Z.subgroupOf H)) : ↥H))
          hconj
        simp only [ClassFunction.conjBy_apply] at hc
        rw [← hc]
        congr 1
      have e1 := hφpt (iso (σ z))
      have e2 := hφpt (iso z)
      have hmul : φ (iso (σ z)) * (θ : ClassFunction ↥H ℂ) 1
          = φ (iso z) * (θ : ClassFunction ↥H ℂ) 1 := by rw [← e1, hval]; exact e2
      simp only [hf_def]
      exact mul_right_cancel₀ hθ1_ne hmul
    -- `φ ≡ 1` forces `Z.subgroupOf H ⊆ Ker θ`, contradicting `hZker`.
    apply hZker
    intro x hx
    rw [SetLike.mem_coe] at hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    have hφx : φ (⟨x, hx⟩ : ↥(Z.subgroupOf H)) = 1 := by
      have hfx := eq_one_of_fixedPointFree_invariant hσfpf hfmul hfone hfinv
        (iso.symm ⟨x, hx⟩)
      simpa only [hf_def, MulEquiv.apply_symm_apply] using hfx
    have hpt := hφpt (⟨x, hx⟩ : ↥(Z.subgroupOf H))
    rw [hφx, one_mul] at hpt
    exact hpt
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **Peterfalvi (6.8) Y-family irreducibility.**  For a nontrivial degree-one (linear) source
character `θ` of `H`, the induced character `Ind_H^L θ` is irreducible.  Inertia `I_L(θ) = H`
(free action of `W₁`) is discharged via the (6.8)(c) disjunction and fed to [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`):

* **(c1)** `L` Frobenius with kernel `H`: `isIrreducibleCharacter_induce_of_frobeniusGroup`
  (needs only `θ ≠ 1`; degree-one not used).
* **(c2)** Hyp (4.6): the inertia bridge `inertia_eq_H_of_c2` from
  `CertainTypeHypothesis.centralizer_W2` + Hall coprimality + Isaacs 3.28 on `H/H'` (T6 §5). -/
theorem isIrreducibleCharacter_induce_of_degree_one (hyp : SibleyDadeHypothesis G L H)
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rcases hyp.cases with hF | ⟨cert, _hdade, hK, hW1, _hprime, hW2, hcop⟩
  · exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne
  · -- (c2) inertia bridge: `I_L(θ) = H` via the abelian quotient `H/⁅H,H⁆` (Brauer + Isaacs 3.28).
    exact isIrreducibleCharacter_induce_of_inertia_eq θ
      (hyp.inertia_eq_H_of_c2 cert hK hW1 hW2 hcop hθ_one hθ_ne)

/-- **(6.8) `Y = S(H')` coherence (engine call from a constructed family).**  Given a family of
nontrivial linear source characters `χ_j : H →* ℂˣ` indexed by `Fin n` (`n ≥ 2`), pairwise
non-`L`-conjugate, with each `Ind_H^L (linear χ_j)` irreducible (`hirr`), the induced family
`Y = {Ind_H^L (linear χ_j)}` is coherent for Sibley's Dade map `tau`.

This is the (6.8) `Y`-step: the `χ_j` are the `Irr(H/H') ∖ {1}` orbit representatives (degree one,
so each `Ind` has the common degree `|W₁|`).  `hirr` and the pairwise non-conjugacy come from the
free `W₁`-action (`isIrreducibleCharacter_induce_of_degree_one`).  Injectivity of
`j ↦ Ind_H^L (linear χ_j)` is the cross-Mackey orthogonality `inner_induce_eq_zero_of_not_conj`;
the equal-degree coherence is then `coherentInducedDegreeOneFamily`. -/
noncomputable def coherentYFamily (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j))
    (hirr : ∀ j, IsIrreducibleCharacter
      (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hηinj : Function.Injective
      (fun j => (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
        hirr j⟩ : IrreducibleCharacter ↥L)) := by
    intro i j hij
    by_contra hne
    have h0 := inner_induce_eq_zero_of_not_conj
      (linearIrreducibleCharacter (χ i)) (linearIrreducibleCharacter (χ j))
      (fun g => hpairwise i j hne g)
    have hcoe : ClassFunction.induce H (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
        ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      congrArg Subtype.val hij
    rw [hcoe] at h0
    have h1 : ClassFunction.inner
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)) = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
          hirr j⟩ : IrreducibleCharacter ↥L)
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ), hirr j⟩)
    rw [h1] at h0
    exact one_ne_zero h0
  exact coherentInducedDegreeOneFamily hyp hn
    (fun j => linearIrreducibleCharacter (χ j))
    (fun j => ⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
      hirr j⟩)
    (fun _ => rfl) hηinj (fun j => linearIrreducibleCharacter_apply_one (χ j))

/-- **(6.8) `Y = S(H')` coherence, with induced irreducibility discharged internally.**
Compared with `coherentYFamily`, the caller supplies only nontrivial linear source characters and
pairwise non-`L`-conjugacy.  The irreducibility of each induced member is the genuine T6/c1-c2
brick `isIrreducibleCharacter_induce_of_degree_one`, not an extra hypothesis. -/
noncomputable def coherentYFamily_of_pairwiseNonconj
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hχ_ne : ∀ j, χ j ≠ 1)
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j)) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.coherentYFamily hn χ hpairwise ?_
  intro j
  exact hyp.isIrreducibleCharacter_induce_of_degree_one
    (linearIrreducibleCharacter_apply_one (χ j)) (by
      rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
      exact hχ_ne j)

/-! ### Peterfalvi (6.8) `X`-characterization (T7): the sets `S(A)`, `X = S − S(Z)`, `Y = S(H')`

mmd 04.8 L150-164.  The (6.8) proof denotes `H' = [H,H]`, sets `Z = Z(H) ∩ H'` in case (A) and
`Z = W₂` in case (B), and forms `X = S − S(Z)`, `Y = S(H')` (`Z ⊆ H'` makes `X ∩ Y = ∅`).
`S(A)` is the (6.1) filtration: the members of `S` whose source `θ` has `A` in its kernel. -/

/-- **Peterfalvi (6.1) filtration `S(A)`** in the (6.8) setup: the members `Ind_H^L θ` of `S`
(`θ ∈ Irr H`, `θ ≠ 1_H`) whose source `θ` has `A` (as a subgroup of `H`) inside its kernel.
`S(1) = S`, and the (6.8) sets are `X = S − S(Z)` and `Y = S(H')`. -/
def SsubFiltration (_hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    (A.subgroupOf H : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}

/-- The (6.8) set `X = S − S(Z)` (the (6.6) `X`-set) for a normal `Z ⊆ Z(H)`. -/
def Xset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  hyp.S \ hyp.SsubFiltration Z

/-- The (6.8) set `Y = S(H')` (`H' = [H,H]`), the equal-degree family handled by T6. -/
def Yset (hyp : SibleyDadeHypothesis G L H) : Set (ClassFunction ↥L ℂ) :=
  hyp.SsubFiltration ⁅H, H⁆

/-- **(6.8) case (A) central subgroup `Z = Z(H) ∩ H′`** (Peterfalvi (6.8), p.34: *"Set
`Z = Z(H) ∩ H′` in case (A)"*).  This is the **correct** `(6.6)` `Z` for the `X = S − S(Z)`
coherence step: it is **central in `H`** (so [Is] Cor 2.30 `exists_degree_sq_le_index` bounds
`θ(1)² ≤ |H:Z|`, making the per-step degree field fillable) and contained in `H′ = ⁅H,H⁆`.

The earlier capstone route mis-instantiated the `(6.6)` producer at `Z = ⁅H,H⁆`, which is **not**
central for class `≥ 3` `p`-groups (e.g. `UT(4,p)`), so its degree field `θχ² ≤ qtot ≤ |H:⁅H,H⁆|`
was unsatisfiable.  See `notes/peterfalvi/s08_6_8_blocker_central_Z.md`. -/
def centralCommutator (hyp : SibleyDadeHypothesis G L H) : Subgroup ↥L :=
  (Subgroup.center ↥H).map H.subtype ⊓ ⁅H, H⁆

theorem centralCommutator_le_commutator (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator ≤ ⁅H, H⁆ := by
  simp only [centralCommutator]; exact inf_le_right

theorem centralCommutator_le (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator ≤ H := by
  haveI := hyp.H_normal
  exact le_trans hyp.centralCommutator_le_commutator (Subgroup.commutator_le_left H H)

/-- `Z = Z(H) ∩ H′` is central in `H`: its trace `Z.subgroupOf H` lies in `Z(↥H)`.  This is the
hypothesis [Is] Cor 2.30 / `IsIrreducibleCharacter.exists_degree_sq_le_index` needs to bound
`θ(1)² ≤ |H : Z|` for the `(6.6)` per-step degree field. -/
theorem centralCommutator_subgroupOf_le_center (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.subgroupOf H ≤ Subgroup.center ↥H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  simp only [centralCommutator] at hx
  have hx2 : (x : ↥L) ∈ (Subgroup.center ↥H).map H.subtype := (Subgroup.mem_inf.mp hx).1
  rw [Subgroup.mem_map] at hx2
  obtain ⟨z, hz, hzx⟩ := hx2
  have hzx' : z = x := Subtype.ext (by simpa using hzx)
  rwa [← hzx']

/-- `Z = Z(H) ∩ H′` is normal in `L`: `(center ↥H).map H.subtype` is normal (characteristic in the
normal `H`, via `normal_of_characteristic_of_normal`) and `⁅H,H⁆` is normal, so their inf is. -/
instance centralCommutator_normal (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.Normal := by
  haveI := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  simp only [centralCommutator]
  infer_instance

/-- `Z = Z(H) ∩ H′` traced into `H` is `Z(↥H) ⊓ commutator ↥H`. -/
theorem centralCommutator_subgroupOf_eq (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.subgroupOf H
      = Subgroup.center ↥H ⊓ _root_.commutator ↥H := by
  have h1 : hyp.centralCommutator.subgroupOf H
      = ((Subgroup.center ↥H).map H.subtype).subgroupOf H
        ⊓ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H := by
    rw [centralCommutator]; exact Subgroup.comap_inf _ _ _
  rw [h1, commutator_subgroupOf_self]
  congr 1
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

/-- `Z = Z(H) ∩ H′ ≠ 1` when `H` is non-abelian: a non-trivial nilpotent group has
`Z(H) ∩ H′ ≠ 1` (`isNilpotent_normal_inf_center_ne_bot` with `N = H′`). -/
theorem centralCommutator_ne_bot (hyp : SibleyDadeHypothesis G L H)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) : hyp.centralCommutator ≠ ⊥ := by
  haveI := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hkey : Subgroup.center ↥H ⊓ _root_.commutator ↥H ≠ ⊥ := by
    rw [inf_comm]
    exact isNilpotent_normal_inf_center_ne_bot (Subgroup.commutator_normal ⊤ ⊤) hHnonab
  intro hbot
  apply hkey
  rw [← hyp.centralCommutator_subgroupOf_eq, hbot, Subgroup.bot_subgroupOf]

/-- **(6.7)-wiring step (c): the centralizer in `↥L` of a nontrivial `z ∈ Z = Z(H) ∩ H′` is `H`.**
`z ∈ Z(H)` gives `H ≤ C_L(z)`; `z ∈ H^#` with `L` Frobenius (kernel `H`) gives `C_L(z) ≤ H`
(`centralizer_kernel_le`).  Hence `|C_L(z)| = |H|` is **constant on `Z^#`** — the `|C_L(·)|`-constancy
input of Peterfalvi (6.7). -/
theorem centralizer_centralCommutator_eq (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set ↥L) = H := by
  apply le_antisymm
  · exact hF.centralizer_kernel_le z (hyp.centralCommutator_le hz) hz1
  · intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzH : (z : ↥L) ∈ H := hyp.centralCommutator_le hz
    have hzc : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.center ↥H :=
      hyp.centralCommutator_subgroupOf_le_center (Subgroup.mem_subgroupOf.mpr hz)
    have hcomm := (Subgroup.mem_center_iff.mp hzc) ⟨h, hh⟩
    have hcoe := congrArg (H.subtype) hcomm
    simpa using hcoe

/-- **(6.7)-wiring step (c′): the ambient-`G` form `(L:Subgroup G) ⊓ C_G(↑w) = H.map L.subtype`.**
Realizes `centralizer_centralCommutator_eq` (`C_↥L(w) = H`) in `G`: an element `g ∈ L` centralizes
`↑w` iff (as an element of `↥L`) it centralizes `w`, iff it lies in `H = C_↥L(w)`.  Hence
`|N_G(Ĥ) ⊓ C_G(w)| = |C_L(w)| = |Ĥ|` is **constant on `Z^#`** (`N_G(Ĥ) = L`), the centralizer-card
clause of Peterfalvi (6.7)'s `hconst`. -/
theorem inf_centralizer_centralCommutator_map (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {w : ↥L} (hw : w ∈ hyp.centralCommutator) (hw1 : w ≠ 1) :
    (L : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G) = H.map L.subtype := by
  have hCH := hyp.centralizer_centralCommutator_eq hF hw hw1
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgc⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    refine Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, ?_, rfl⟩
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using hgc)
  · intro hg
    obtain ⟨c, hcH, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff] at hcH
    refine ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (L.subtype) hcH
    simpa using this

/-- **(6.8.3) case-(A) fixed-point-free bound** `|Z| ≥ 2|W₁| + 1` (hence `|Z| − 1 ≥ 2|W₁|`).
`W₁` acts fixed-point-freely on `H` (`hF.toFrobeniusAction`), and `Z.subgroupOf H = Z(↥H) ⊓ H′` is
characteristic, so the action restricts fixed-point-freely to it (`IsFrobeniusAction.subgroup`);
`card_modEq_one` gives `|Z| ≡ 1 (mod |W₁|)`, and as `|Z|, |W₁|` are odd and `|Z| > 1`
(`H` non-abelian), `two_mul_add_one_le_of_odd_dvd` yields `2|W₁| + 1 ≤ |Z|`. -/
theorem centralCommutator_card_subgroupOf_lower (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    2 * Nat.card hyp.W1 + 1 ≤ Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
  classical
  letI : H.Normal := hyp.H_normal
  letI actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hFrobH : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥hyp.W1 ↥H := hF.toFrobeniusAction
  have hMeq : hyp.centralCommutator.subgroupOf H = Subgroup.center ↥H ⊓ _root_.commutator ↥H :=
    hyp.centralCommutator_subgroupOf_eq
  have hcprod : ∀ (K : Subgroup ↥H) [K.Characteristic] (a : ↥hyp.W1) (m : ↥H),
      m ∈ K → a • m ∈ K := by
    intro K _ a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp ‹K.Characteristic›
      (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a)
    have hmem : (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a).toMonoidHom m ∈ K := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  have hinv : ∀ a : ↥hyp.W1, ∀ m ∈ hyp.centralCommutator.subgroupOf H,
      a • m ∈ hyp.centralCommutator.subgroupOf H := by
    intro a m hm
    rw [hMeq, Subgroup.mem_inf] at hm ⊢
    exact ⟨hcprod (Subgroup.center ↥H) a m hm.1, hcprod (_root_.commutator ↥H) a m hm.2⟩
  letI instM : MulDistribMulAction ↥hyp.W1 ↥(hyp.centralCommutator.subgroupOf H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction _ hinv
  have hFrobM : @OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥hyp.W1
      ↥(hyp.centralCommutator.subgroupOf H) _ _ instM := hFrobH.subgroup _ hinv
  haveI : Fintype ↥hyp.W1 := Fintype.ofFinite _
  haveI : Fintype ↥(hyp.centralCommutator.subgroupOf H) := Fintype.ofFinite _
  have hMmod : Nat.card ↥(hyp.centralCommutator.subgroupOf H) ≡ 1 [MOD Nat.card hyp.W1] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobM.card_modEq_one
  have hMne : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    rw [hMeq, inf_comm]
    letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
    exact isNilpotent_normal_inf_center_ne_bot (Subgroup.commutator_normal ⊤ ⊤) hHnonab
  have hMgt1 : 1 < Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
    haveI : Nontrivial ↥(hyp.centralCommutator.subgroupOf H) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hMne
    exact Finite.one_lt_card
  have hRdvd : Nat.card hyp.W1 ∣ Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hMmod.symm
  have hW1odd : Odd (Nat.card hyp.W1) :=
    Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hModd : Odd (Nat.card ↥(hyp.centralCommutator.subgroupOf H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card H))
      (Subgroup.card_subgroup_dvd_card (hyp.centralCommutator.subgroupOf H))
  exact two_mul_add_one_le_of_odd_dvd hW1odd hModd hRdvd hMgt1

/-- Membership in `S(A)`, unfolded. -/
theorem mem_SsubFiltration (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.SsubFiltration A ↔ ∃ θ : IrreducibleCharacter ↥H,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
      (A.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
      φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
  Iff.rfl

/-- `S(⊥) = S`: the kernel condition `⊥ ⊆ Ker θ` is vacuous, so the bottom filtration is all of
`S`.  (Peterfalvi writes `S(1) = S`.) -/
theorem SsubFiltration_bot (hyp : SibleyDadeHypothesis G L H) :
    hyp.SsubFiltration ⊥ = hyp.S := by
  ext φ
  rw [hyp.mem_SsubFiltration, hyp.S_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨θ, hθ, -, hφ⟩
    exact ⟨θ, hθ, hφ⟩
  · rintro ⟨θ, hθ, hφ⟩
    refine ⟨θ, hθ, ?_, hφ⟩
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _

/-- Membership in `X = S − S(Z)`, unfolded. -/
theorem mem_Xset (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Xset Z ↔ φ ∈ hyp.S ∧ φ ∉ hyp.SsubFiltration Z :=
  Iff.rfl

/-- Every member of the filtration `S(A)` is a member of the ambient set `S`. -/
theorem SsubFiltration_subset_S (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L} :
    hyp.SsubFiltration A ⊆ hyp.S := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ
  obtain ⟨θ, hθ_ne, _hker, hφeq⟩ := hφ
  rw [hyp.S_eq]
  exact ⟨θ, hθ_ne, hφeq⟩

/-- `X(Z) = S - S(Z)` is contained in `S`. -/
theorem Xset_subset_S (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} :
    hyp.Xset Z ⊆ hyp.S := by
  intro φ hφ
  exact (hyp.mem_Xset.mp hφ).1

/-- `Y = S(H')` is contained in `S`. -/
theorem Yset_subset_S (hyp : SibleyDadeHypothesis G L H) :
    hyp.Yset ⊆ hyp.S := by
  intro φ hφ
  rw [Yset] at hφ
  exact hyp.SsubFiltration_subset_S hφ

/-- `X(Z) = S - S(Z)` is disjoint from `S(Z)`. -/
theorem disjoint_Xset_SsubFiltration
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Disjoint (hyp.Xset Z) (hyp.SsubFiltration Z) := by
  rw [Set.disjoint_left]
  intro φ hφX hφZ
  exact (hyp.mem_Xset.mp hφX).2 hφZ

/-- `X(Z)` and `S(Z)` partition `S`. -/
theorem Xset_union_SsubFiltration_eq_S
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.Xset Z ∪ hyp.SsubFiltration Z = hyp.S := by
  ext φ
  constructor
  · intro hφ
    rcases hφ with hφX | hφZ
    · exact hyp.Xset_subset_S hφX
    · exact hyp.SsubFiltration_subset_S hφZ
  · intro hφS
    by_cases hφZ : φ ∈ hyp.SsubFiltration Z
    · exact Or.inr hφZ
    · exact Or.inl (hyp.mem_Xset.mpr ⟨hφS, hφZ⟩)

/-- The Peterfalvi filtration is antitone: a larger subgroup imposes a stronger kernel
condition. -/
theorem SsubFiltration_antitone
    (hyp : SibleyDadeHypothesis G L H) {A B : Subgroup ↥L} (hAB : A ≤ B) :
    hyp.SsubFiltration B ⊆ hyp.SsubFiltration A := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  refine ⟨θ, hθ_ne, ?_, hφeq⟩
  intro x hxA
  exact hker (Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hxA)))

/-- `X(A) = S - S(A)` grows with the subgroup parameter. -/
theorem Xset_mono
    (hyp : SibleyDadeHypothesis G L H) {A B : Subgroup ↥L} (hAB : A ≤ B) :
    hyp.Xset A ⊆ hyp.Xset B := by
  intro φ hφ
  obtain ⟨hφS, hφnotA⟩ := hyp.mem_Xset.mp hφ
  exact hyp.mem_Xset.mpr ⟨hφS, fun hφB => hφnotA (hyp.SsubFiltration_antitone hAB hφB)⟩

/-- If `Z ≤ H'`, then the larger capstone set `S - S(H')` splits into the smaller
`X(Z) = S - S(Z)` plus the filtration layer between `Z` and `H'`.  This is the set-theoretic
bridge needed by the case-A/case-B route, where the textbook first proves coherence for a smaller
central/fixed-point-free subgroup `Z`. -/
theorem Xset_commutator_eq_Xset_union_filtrationDiff
    (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} (hZH' : Z ≤ ⁅H, H⁆) :
    hyp.Xset ⁅H, H⁆ =
      hyp.Xset Z ∪ (hyp.SsubFiltration Z \ hyp.SsubFiltration ⁅H, H⁆) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨hφS, hφnotH'⟩ := hyp.mem_Xset.mp hφ
    by_cases hφZ : φ ∈ hyp.SsubFiltration Z
    · exact Or.inr ⟨hφZ, hφnotH'⟩
    · exact Or.inl (hyp.mem_Xset.mpr ⟨hφS, hφZ⟩)
  · rintro (hφZ | ⟨hφFilZ, hφnotH'⟩)
    · exact hyp.Xset_mono hZH' hφZ
    · exact hyp.mem_Xset.mpr ⟨hyp.SsubFiltration_subset_S hφFilZ, hφnotH'⟩

/-- The (6.8) sets `X = S - S(H')` and `Y = S(H')` are disjoint. -/
theorem disjoint_Xset_Yset (hyp : SibleyDadeHypothesis G L H) :
    Disjoint (hyp.Xset ⁅H, H⁆) hyp.Yset := by
  simpa [Yset] using hyp.disjoint_Xset_SsubFiltration (Z := ⁅H, H⁆)

/-- The (6.8) sets `X = S - S(H')` and `Y = S(H')` partition `S`. -/
theorem Xset_union_Yset_eq_S (hyp : SibleyDadeHypothesis G L H) :
    hyp.Xset ⁅H, H⁆ ∪ hyp.Yset = hyp.S := by
  simpa [Yset] using hyp.Xset_union_SsubFiltration_eq_S (Z := ⁅H, H⁆)

/-- A nontrivial irreducible character remains nontrivial after complex conjugation. -/
theorem irreducibleCharacter_conj_ne_trivial {Γ : Type*} [Group Γ] [Finite Γ]
    {θ : IrreducibleCharacter Γ}
    (hθ_ne : θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ) :
    (⟨(θ : ClassFunction Γ ℂ).conj, θ.isIrreducible.conj⟩ :
      IrreducibleCharacter Γ) ≠
        OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ := by
  intro hθc
  apply hθ_ne
  apply IrreducibleCharacter.ext
  have hval : (θ : ClassFunction Γ ℂ).conj =
      (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ) := by
    simpa using congrArg
      (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hθc
  calc
    (θ : ClassFunction Γ ℂ) = ((θ : ClassFunction Γ ℂ).conj).conj := by
      rw [ClassFunction.conj_conj]
    _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ).conj := by
      rw [hval]
    _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ) := by
      ext x
      simp

/-- `S = {Ind_H^L θ | θ ∈ Irr(H), θ ≠ 1}` is finite, directly from the finite source
irreducible-character set. -/
theorem S_finite (hyp : SibleyDadeHypothesis G L H) :
    hyp.S.Finite := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥H) :=
    OddOrder.RepresentationTheory.finite_irreducibleCharacter (G := ↥H)
  refine (Set.finite_range
    (fun θ : {θ : IrreducibleCharacter ↥H //
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H} =>
      ClassFunction.induce H (θ.1 : ClassFunction ↥H ℂ))).subset ?_
  intro φ hφ
  rw [hyp.S_eq] at hφ
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  exact ⟨⟨θ, hθ_ne⟩, hφeq.symm⟩

/-- Every filtration layer `S(A)` is finite, because it is a subset of `S`. -/
theorem SsubFiltration_finite (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    (hyp.SsubFiltration A).Finite :=
  hyp.S_finite.subset hyp.SsubFiltration_subset_S

/-- `X(Z) = S - S(Z)` is finite, because it is a subset of `S`. -/
theorem Xset_finite (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    (hyp.Xset Z).Finite :=
  hyp.S_finite.subset hyp.Xset_subset_S

/-- `S` is closed under complex conjugation.  This is a source-side fact:
`conj (Ind_H^L θ) = Ind_H^L (conj θ)`. -/
theorem S_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.S := by
  intro φ hφ
  rw [hyp.S_eq] at hφ ⊢
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, irreducibleCharacter_conj_ne_trivial hθ_ne, ?_⟩
  rw [hφeq]
  simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- Each Peterfalvi filtration layer `S(A)` is closed under complex conjugation.  The
kernel condition is preserved by conjugating the source character. -/
theorem SsubFiltration_closedUnderConjugate
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.SsubFiltration A) := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, irreducibleCharacter_conj_ne_trivial hθ_ne, ?_, ?_⟩
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- `X(Z) = S - S(Z)` is closed under complex conjugation, without first proving
`X(Z) ⊆ Irr(L)`. -/
theorem Xset_closedUnderConjugate_unconditional
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) := by
  intro φ hφ
  obtain ⟨hφS, hφnotZ⟩ := hyp.mem_Xset.mp hφ
  refine hyp.mem_Xset.mpr ⟨hyp.S_closedUnderConjugate hφS, ?_⟩
  intro hφcZ
  have hφccZ := hyp.SsubFiltration_closedUnderConjugate Z hφcZ
  exact hφnotZ (by simpa [ClassFunction.conj_conj] using hφccZ)

/-- **Peterfalvi (6.2), filtration form.**  If the quotient `H/A` has nontrivial
abelianization, then the filtration layer `S(A)` is nonempty.

The source character is the degree-one irreducible obtained on `H/A`, inflated to `H`; inducing it
to `L` gives an element of the Peterfalvi filtration by construction. -/
theorem SsubFiltration_nonempty_of_commutator_quotient_ne_top
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L)
    [(A.subgroupOf H).Normal]
    (hcomm : commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤) :
    (hyp.SsubFiltration A).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨θ, hθ_ne, hker, _hdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top
      (K := ↥H) (A.subgroupOf H) hcomm
  refine ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), ?_⟩
  rw [hyp.mem_SsubFiltration]
  exact ⟨θ, hθ_ne, hker, rfl⟩

/-- **Peterfalvi (6.2), solvable quotient form.**  A nontrivial finite solvable quotient `H/A`
has proper commutator subgroup, hence supplies a nontrivial degree-one source character and a
member of `S(A)`. -/
theorem SsubFiltration_nonempty_of_nontrivial_solvable_quotient
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L)
    [(A.subgroupOf H).Normal] [IsSolvable (↥H ⧸ A.subgroupOf H)]
    [Nontrivial (↥H ⧸ A.subgroupOf H)] :
    (hyp.SsubFiltration A).Nonempty :=
  hyp.SsubFiltration_nonempty_of_commutator_quotient_ne_top A
    (IsSolvable.commutator_lt_top_of_nontrivial
      (G := ↥H ⧸ A.subgroupOf H)).ne

/-- **Peterfalvi (6.2), proper nilpotent quotient form.**  If `A` is a proper
normal subgroup of the nilpotent kernel `H`, then the filtration layer `S(A)` is nonempty.

The quotient `H/A` is nontrivial and nilpotent, hence solvable, so the solvable-quotient
filtration form supplies a nontrivial degree-one source character. -/
theorem SsubFiltration_nonempty_of_subgroupOf_ne_top
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L)
    [(A.subgroupOf H).Normal] (hA : A.subgroupOf H ≠ ⊤) :
    (hyp.SsubFiltration A).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : Group.IsNilpotent (↥H ⧸ A.subgroupOf H) :=
    nilpotent_of_surjective (QuotientGroup.mk' (A.subgroupOf H))
      (QuotientGroup.mk'_surjective (A.subgroupOf H))
  haveI : IsSolvable (↥H ⧸ A.subgroupOf H) := IsNilpotent.to_isSolvable
  haveI : Nontrivial (↥H ⧸ A.subgroupOf H) :=
    Subgroup.nontrivial_quotient_of_ne_top hA
  exact hyp.SsubFiltration_nonempty_of_nontrivial_solvable_quotient A

/-- A nontrivial linear source character induces to a member of `Y = S(H')`.

The witness in `S(H')` is `linearIrreducibleCharacter χ`.  Its kernel contains
`H' = [H,H]` because a degree-one character kills commutators. -/
theorem induce_linearIrreducibleCharacter_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {χ : ↥H →* ℂˣ}
    (hχ_ne : χ ≠ 1) :
    ClassFunction.induce H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) ∈
      hyp.Yset := by
  rw [Yset]
  refine ⟨linearIrreducibleCharacter χ, ?_, ?_, rfl⟩
  · rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
    exact hχ_ne
  · intro x hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, linearIrreducibleCharacter_apply_one]
    have hsubgroupOf_eq :
        ((⁅H, H⁆ : Subgroup ↥L).subgroupOf H) = _root_.commutator ↥H := by
      rw [← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    have hxcomm : x ∈ _root_.commutator ↥H := by
      rwa [hsubgroupOf_eq] at hx
    have hxclosure : x ∈ Subgroup.closure (commutatorSet ↥H) := by
      rwa [_root_.commutator_eq_closure] at hxcomm
    refine Subgroup.closure_induction
      (p := fun y _ => (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) y = 1)
      ?_ ?_ ?_ ?_ hxclosure
    · rintro _ ⟨a, b, rfl⟩
      have hlin := (linearIrreducibleCharacter χ).isIrreducible
      exact hlin.apply_commutatorElement_eq_one_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ) a b
    · exact linearIrreducibleCharacter_apply_one χ
    · intro a b _ _ ha hb
      rw [(linearIrreducibleCharacter χ).isIrreducible.map_mul_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ), ha, hb, one_mul]
    · intro a _ ha
      have hai := (linearIrreducibleCharacter χ).isIrreducible.map_mul_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ) a a⁻¹
      rw [mul_inv_cancel, linearIrreducibleCharacter_apply_one χ, ha, one_mul] at hai
      exact hai.symm


/-- A source character whose kernel contains `H'` comes from a linear character of `H`.

The proof factors the source through the abelianization `H/H'`; irreducible characters of a finite
commutative group are degree one, hence are `linearIrreducibleCharacter`s, and pulling that linear
character back along `Abelianization.of` recovers the original source. -/
theorem exists_linearIrreducibleCharacter_eq_of_YsetSource
    (_hyp : SibleyDadeHypothesis G L H) {θ : IrreducibleCharacter ↥H}
    (hker : (((⁅H, H⁆ : Subgroup ↥L).subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    ∃ χ : ↥H →* ℂˣ,
      (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) = (θ : ClassFunction ↥H ℂ) := by
  classical
  have hsubgroupOf_eq :
      ((⁅H, H⁆ : Subgroup ↥L).subgroupOf H) = _root_.commutator ↥H := by
    rw [← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  let q : ↥H →* Abelianization ↥H := Abelianization.of
  have hq_surj : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator ↥H) y
    exact ⟨x, rfl⟩
  have hker_q :
      ((q.ker : Subgroup ↥H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro x hx
    apply hker
    have hxcomm : x ∈ _root_.commutator ↥H := by
      rwa [show q.ker = _root_.commutator ↥H by
        change Abelianization.of.ker = _root_.commutator ↥H
        exact Abelianization.ker_of ↥H] at hx
    rwa [hsubgroupOf_eq]
  obtain ⟨θbar, hθbar⟩ := exists_compHom_eq_of_subset_characterKernel hq_surj θ hker_q
  haveI : Finite (Abelianization ↥H) := Finite.of_surjective q hq_surj
  obtain ⟨χbar, hχbar⟩ :=
    θbar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  refine ⟨χbar.comp q, ?_⟩
  rw [← ClassFunction.compHom_linearIrreducibleCharacter, hχbar, hθbar]

/-- Every member of `Y = S(H')` is induced from a nontrivial linear character of `H`. -/
theorem exists_linear_source_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    ∃ χ : ↥H →* ℂˣ, χ ≠ 1 ∧
      φ = ClassFunction.induce H
        (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) := by
  rw [Yset, SsubFiltration] at hφ
  obtain ⟨θ, hθ_ne, hker, hφ⟩ := hφ
  obtain ⟨χ, hχθ⟩ := hyp.exists_linearIrreducibleCharacter_eq_of_YsetSource hker
  refine ⟨χ, ?_, ?_⟩
  · intro hχ
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hχθ]
    exact congrArg (fun η : IrreducibleCharacter ↥H => (η : ClassFunction ↥H ℂ))
      ((linearIrreducibleCharacter_eq_trivial_iff (χ := χ)).mpr hχ)
  · rw [hφ, ← hχθ]

/-- `Y = S(H')` is exactly the image of the nontrivial linear characters of `H` under induction. -/
theorem mem_Yset_iff_exists_linear_source
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Yset ↔ ∃ χ : ↥H →* ℂˣ, χ ≠ 1 ∧
      φ = ClassFunction.induce H
        (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) := by
  constructor
  · exact hyp.exists_linear_source_of_mem_Yset
  · rintro ⟨χ, hχ_ne, rfl⟩
    exact hyp.induce_linearIrreducibleCharacter_mem_Yset hχ_ne

/-- Every `Y = S(H')` member has degree `|W₁|` (`Ind_H^L` of a degree-`1` source of `H`).  The
common degree of the equal-degree `Y`-family; used for the equal-degree difference support
(`sMember_diffSupport_of_charValue_eq`) in the (6.8.1) `himg_ortho`. -/
theorem Yset_apply_one (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) := by
  obtain ⟨χ, _hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [hφeq]
  simpa [linearIrreducibleCharacter_coe] using
    hyp.induce_apply_one_eq_card_W1_of_degree_one
      (linearIrreducibleCharacter χ) (linearIrreducibleCharacter_apply_one χ)

/-- Family form of `induce_linearIrreducibleCharacter_mem_Yset`. -/
theorem range_induce_linearIrreducibleCharacter_subset_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ}
    (χ : Fin n → (↥H →* ℂˣ)) (hχ_ne : ∀ j, χ j ≠ 1) :
    Set.range (fun j => ClassFunction.induce H
      (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)) ⊆ hyp.Yset := by
  rintro φ ⟨j, rfl⟩
  exact hyp.induce_linearIrreducibleCharacter_mem_Yset (hχ_ne j)

/-- If an index family covers all nontrivial linear sources after induction, its induced range is
exactly `Y = S(H')`.

This is the orbit-representative form needed for (6.8): the family need only hit each induced
character in `Y`, not each nontrivial linear source before quotienting by `L`-conjugacy. -/
theorem range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {ι : Type*}
    (χ : ι → (↥H →* ℂˣ)) (hχ_ne : ∀ j, χ j ≠ 1)
    (hχ_cover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η)) :
    Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) = hyp.Yset := by
  ext φ
  constructor
  · rintro ⟨j, rfl⟩
    simpa [linearIrreducibleCharacter_coe] using
      hyp.induce_linearIrreducibleCharacter_mem_Yset (hχ_ne j)
  · intro hφ
    obtain ⟨η, hη_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
    obtain ⟨j, hηj⟩ := hχ_cover η hη_ne
    refine ⟨j, ?_⟩
    rw [hφeq, linearIrreducibleCharacter_coe]
    exact hηj

/-- There are finitely many linear characters `Γ →* ℂˣ` for a finite group `Γ`.

Local to §8 because the immediate consumer is the finiteness of `Y = S(H')`; a more global API can
move this later if it gets reused outside the Peterfalvi assembly. -/
theorem finite_linearCharacters_of_finite {Γ : Type*} [Group Γ] [Finite Γ] :
    Finite (Γ →* ℂˣ) := by
  haveI : Finite (IrreducibleCharacter Γ) := finite_irreducibleCharacter (G := Γ)
  exact Finite.of_injective (linearIrreducibleCharacter (H := Γ))
    linearIrreducibleCharacter_injective

/-- `Y = S(H')` is finite: it is covered by inducing the finite set of nontrivial
linear source characters of `H`. -/
theorem Yset_finite (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    hyp.Yset.Finite := by
  classical
  haveI : Finite (↥H →* ℂˣ) := finite_linearCharacters_of_finite (Γ := ↥H)
  let T : Set (↥H →* ℂˣ) := {χ | χ ≠ 1}
  refine ((Set.toFinite T).image
    (fun χ => ClassFunction.induce H (linearClassFunction χ))).subset ?_
  intro φ hφ
  obtain ⟨χ, hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  refine ⟨χ, hχ_ne, ?_⟩
  rw [hφeq, linearIrreducibleCharacter_coe]

/-- Every member of `Y = S(H')` is irreducible. -/
theorem isIrreducibleCharacter_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    IsIrreducibleCharacter φ := by
  obtain ⟨χ, hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [hφeq]
  exact hyp.isIrreducibleCharacter_induce_of_degree_one
    (linearIrreducibleCharacter_apply_one χ) (by
      rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
      exact hχ_ne)

/-- Disjoint families of irreducible characters are orthogonal after passing to their
integer spans. -/
theorem inner_eq_zero_of_mem_span_of_disjoint_irreducible
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X Y : Set (ClassFunction Γ ℂ)}
    (hXirr : ∀ χ ∈ X, IsIrreducibleCharacter χ)
    (hYirr : ∀ η ∈ Y, IsIrreducibleCharacter η)
    (hdisj : Disjoint X Y) :
    ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem χ hχ =>
      intro v hv
      refine OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan ?_ hv
      intro η hη
      have hχη : χ ≠ η := by
        intro h
        exact (Set.disjoint_left.mp hdisj) hχ (by simpa [← h] using hη)
      have hχirr : IsIrreducibleCharacter χ := hXirr χ hχ
      have hηirr : IsIrreducibleCharacter η := hYirr η hη
      have hneq :
          (⟨χ, hχirr⟩ : IrreducibleCharacter Γ) ≠ ⟨η, hηirr⟩ := by
        intro h
        exact hχη (congrArg Subtype.val h)
      simpa [hneq] using
        irreducibleCharacter_inner_eq_ite
          (⟨χ, hχirr⟩ : IrreducibleCharacter Γ) ⟨η, hηirr⟩
  | zero =>
      intro v _hv
      exact ClassFunction.inner_zero_left v
  | add x y _hx _hy ihx ihy =>
      intro v hv
      rw [ClassFunction.inner_add_left, ihx v hv, ihy v hv, zero_add]
  | smul a x _hx ih =>
      intro v hv
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih v hv, mul_zero]

/-- Source-side orthogonality of the (6.8) partition `X = S - S(H')` and `Y = S(H')`,
assuming the `X` side has already been shown irreducible. -/
theorem inner_span_Xset_Yset_eq_zero_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    (hXirr : ∀ φ ∈ hyp.Xset ⁅H, H⁆, IsIrreducibleCharacter φ) :
    ∀ u ∈ Submodule.span ℤ (hyp.Xset ⁅H, H⁆),
      ∀ v ∈ Submodule.span ℤ hyp.Yset, ClassFunction.inner u v = 0 := by
  letI : H.Normal := hyp.H_normal
  exact inner_eq_zero_of_mem_span_of_disjoint_irreducible hXirr
    (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hyp.disjoint_Xset_Yset

/-- Enumerating `Yset` gives nontrivial linear source representatives for its induced members.

The returned family is indexed by `Fin n`, covers `Yset` after induction, and is pairwise
non-`L`-conjugate.  The cardinal lower bound is kept as an explicit input because the later
coherence engine requires `2 ≤ n`. -/
theorem exists_Yset_linearRepresentativeFamily
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] (hYtwo : 2 ≤ hyp.Yset.ncard) :
    ∃ (n : ℕ) (_ : NeZero n) (χ : Fin n → ↥H →* ℂˣ),
      2 ≤ n ∧
      (∀ j, χ j ≠ 1) ∧
      (∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
        ClassFunction.induce H (linearClassFunction (χ j)) =
          ClassFunction.induce H (linearClassFunction η)) ∧
      (∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
        IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
          linearIrreducibleCharacter (χ j)) ∧
      Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) = hyp.Yset := by
  classical
  obtain ⟨n, ζ, hζinj, hζrange⟩ :=
    exists_finEnum_irreducible (hyp.Yset_finite)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ)
  have hζmem : ∀ j, (ζ j : ClassFunction ↥L ℂ) ∈ hyp.Yset := by
    intro j
    rw [← hζrange]
    exact Set.mem_range_self j
  choose χ hχ_ne hχeq using fun j => hyp.exists_linear_source_of_mem_Yset (hζmem j)
  have hindRange : Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) =
      hyp.Yset := by
    ext φ
    constructor
    · rintro ⟨j, rfl⟩
      have hζeq :
          (ζ j : ClassFunction ↥L ℂ) =
            ClassFunction.induce H (linearClassFunction (χ j)) := by
        simpa [linearIrreducibleCharacter_coe] using hχeq j
      change ClassFunction.induce H (linearClassFunction (χ j)) ∈ hyp.Yset
      rw [← hζeq]
      exact hζmem j
    · intro hφ
      rw [← hζrange] at hφ
      obtain ⟨j, hj⟩ := hφ
      refine ⟨j, ?_⟩
      rw [← hj]
      simpa [linearIrreducibleCharacter_coe] using (hχeq j).symm
  have hcover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η) := by
    intro η hη_ne
    have hmem : ClassFunction.induce H (linearClassFunction η) ∈ hyp.Yset := by
      simpa [linearIrreducibleCharacter_coe] using
        hyp.induce_linearIrreducibleCharacter_mem_Yset hη_ne
    rw [← hindRange] at hmem
    exact hmem
  have hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j) := by
    intro i j hij g hconj
    apply hij
    apply hζinj
    apply IrreducibleCharacter.ext
    have hind :
        ClassFunction.induce H
            (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
          ClassFunction.induce H
            (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      (induce_eq_induce_iff_conj
        (G := ↥L) (H := H)
        (linearIrreducibleCharacter (χ i))
        (linearIrreducibleCharacter (χ j))).mpr ⟨g, hconj⟩
    rw [hχeq i, hχeq j]
    exact hind
  have hcoeinj : Function.Injective (fun j => (ζ j : ClassFunction ↥L ℂ)) := by
    intro i j hij
    exact hζinj (IrreducibleCharacter.ext hij)
  have hncard : hyp.Yset.ncard = n := by
    rw [← hζrange, Set.ncard_range_of_injective hcoeinj, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  exact ⟨n, inferInstance, χ, hn2, hχ_ne, hcover, hpairwise, hindRange⟩

/-- `Y = S(H')` coherence from finite orbit representatives of nontrivial linear characters.

The caller supplies representatives whose induced characters cover `Y`, together with the usual
pairwise non-`L`-conjugacy input that makes the constructed family orthonormal.  The exact range
equality rewrites `coherentYFamily` from the constructed range to `hyp.Yset`. -/
noncomputable def coherentYset_of_pairwiseNonconj
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hχ_ne : ∀ j, χ j ≠ 1)
    (hχ_cover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j)) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hcoh := hyp.coherentYFamily_of_pairwiseNonconj hn χ hχ_ne hpairwise
  have hrange :=
    hyp.range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective χ hχ_ne hχ_cover
  simpa [hrange] using hcoh

/-- `Y = S(H')` coherence from the finite `Yset` representative construction.

This packages `exists_Yset_linearRepresentativeFamily` with the concrete coherence engine; the
remaining downstream input is the cardinal lower bound `2 ≤ |Y|`. -/
noncomputable def coherentYset_of_two_le_ncard
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] (hYtwo : 2 ≤ hyp.Yset.ncard) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  choose n hnzero χ hn2 hχ_ne hχ_cover hpairwise _hrange using
    hyp.exists_Yset_linearRepresentativeFamily hYtwo
  letI : NeZero n := hnzero
  exact hyp.coherentYset_of_pairwiseNonconj hn2 χ hχ_ne hχ_cover hpairwise

/-- `Y = S(H')` is nonempty.

The nontrivial nilpotent group `H` is solvable, hence has proper commutator subgroup.  The
abelianization therefore has a nontrivial linear character, whose induced character lies in
`Yset`. -/
theorem Yset_nonempty (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    hyp.Yset.Nonempty := by
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hcomm : _root_.commutator ↥H ≠ ⊤ :=
    (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H)).ne
  obtain ⟨χ, hχ_ne⟩ := exists_monoidHom_units_ne_one_of_commutator_ne_top hcomm
  exact ⟨ClassFunction.induce H (linearClassFunction χ),
    by simpa [linearIrreducibleCharacter_coe] using
      hyp.induce_linearIrreducibleCharacter_mem_Yset hχ_ne⟩

/-- `Y = S(H')` contains no real characters.

Each member of `Yset` is an irreducible induced character of degree `|W₁|`; since `W₁` is
nontrivial this degree is not `1`, so the member is not the trivial irreducible character.  Odd
order of `L` then gives non-realness by Peterfalvi (1.1). -/
theorem Yset_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Yset := by
  intro φ hφ hreal
  let η : IrreducibleCharacter ↥L := ⟨φ, hyp.isIrreducibleCharacter_of_mem_Yset hφ⟩
  have hη_ne : η ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro hη
    have hφ_one_triv : φ (1 : ↥L) = 1 := by
      have h := congrArg (fun ψ : IrreducibleCharacter ↥L =>
        (ψ : ClassFunction ↥L ℂ) (1 : ↥L)) hη
      simpa [η, trivialClassFunction_apply] using h
    obtain ⟨χ, _hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
    have hφ_one : φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) := by
      rw [hφeq]
      simpa [linearIrreducibleCharacter_coe] using
        hyp.induce_apply_one_eq_card_W1_of_degree_one
          (linearIrreducibleCharacter χ) (linearIrreducibleCharacter_apply_one χ)
    have hcard_ne : (Nat.card hyp.W1 : ℂ) ≠ 1 := by
      have hcard_nat : Nat.card hyp.W1 ≠ 1 := by
        intro hcard
        exact hyp.W1_nontrivial (Subgroup.card_eq_one.mp hcard)
      exact_mod_cast hcard_nat
    exact hcard_ne (hφ_one.symm.trans hφ_one_triv)
  exact (OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
    hyp.card_L_odd hη_ne) hreal

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
    exact hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hn1, star_natCast, sub_self])
  have hχg : χ g ≠ 0 := fun h0 =>
    hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_zero])
  have hgH : g ∈ H := by
    have hsupp : χ.support ⊆ (H : Set ↥L) := by
      rw [hχeq]
      exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)
    exact hsupp (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
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
      irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ⟨χ.conj, hconjirr⟩
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
    rwa [if_neg hbi_ne] at h
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ.conj, hconjirr⟩
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
    exact hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hn1, star_natCast, sub_self])
  have hχg : χ g ≠ 0 := fun h0 =>
    hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_zero])
  have hgH : g ∈ H := by
    have hsupp : χ.support ⊆ (H : Set ↥L) := by
      rw [hχeq]
      exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)
    exact hsupp (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
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

/-- **(T8 leaf 5) the base block `S₀`**: the minimal-(real-)degree members of `X`.  This is the
equal-minimal-degree prefix `{χ₁,…,χₖ}` of (6.6), on which (1.1)+(1.4) supplies the base coherence
`coherentEqualDegree_fromDade` before the (5.6) adjoining of the strictly-higher-degree conjugate
pairs.  `S₀` must contain **all** minimal-degree members (not just one pair): the first (5.6)
adjoining of a pair of degree ratio `a` needs `2a < ∑_{S₀} aⱼ²`, which fails at equal degree. -/
def xBaseBlock (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {χ ∈ hyp.Xset Z | ∀ ψ ∈ hyp.Xset Z,
    (OddOrder.Peterfalvi.S03.characterDegree χ).re ≤
      (OddOrder.Peterfalvi.S03.characterDegree ψ).re}

theorem xBaseBlock_subset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.xBaseBlock Z ⊆ hyp.Xset Z :=
  fun _ hχ => hχ.1

/-- The minimal-degree base block of `X(Z)` is closed under conjugation.  This uses only the
direct conjugation-invariance of `X(Z)` and degree preservation under conjugation. -/
theorem xBaseBlock_closedUnderConjugate_unconditional
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) := by
  intro χ hχ
  refine ⟨hyp.Xset_closedUnderConjugate_unconditional Z hχ.1, fun ψ hψ => ?_⟩
  have hre : (OddOrder.Peterfalvi.S03.characterDegree χ.conj).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ).re := by
    simp
  rw [hre]
  exact hχ.2 ψ hψ

/-- Any two members of the base block have the same degree (the base is an *equal*-degree family,
the input shape of `coherentEqualDegree_fromDade`). -/
theorem xBaseBlock_degree_re_eq (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.xBaseBlock Z) (hχ' : χ' ∈ hyp.xBaseBlock Z) :
    (OddOrder.Peterfalvi.S03.characterDegree χ).re =
      (OddOrder.Peterfalvi.S03.characterDegree χ').re :=
  le_antisymm (hχ.2 χ' hχ'.1) (hχ'.2 χ hχ.1)

/-- If `χ₁` is a base-block anchor and `χ ∈ X`, then the natural degree of `χ₁` is no larger
than the natural degree of `χ`. -/
theorem natDegree_le_of_xBaseBlock_anchor (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ₁ χ : IrreducibleCharacter ↥L} {d₁ d : ℕ}
    (hχ₁base : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχ₁one : (χ₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hχone : (χ : ClassFunction ↥L ℂ) 1 = (d : ℂ)) :
    d₁ ≤ d := by
  have hre := hχ₁base.2 (χ : ClassFunction ↥L ℂ) hχX
  rw [OddOrder.Peterfalvi.S03.characterDegree_def,
    OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one, hχone] at hre
  exact_mod_cast hre

/-- If `χ₁` is a base-block anchor and `χ ∈ X` is not itself in the base block, then the
natural degree of `χ` is strictly larger. -/
theorem natDegree_lt_of_xBaseBlock_anchor_of_not_mem
    (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {χ₁ χ : IrreducibleCharacter ↥L} {d₁ d : ℕ}
    (hχ₁base : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχnotbase : (χ : ClassFunction ↥L ℂ) ∉ hyp.xBaseBlock Z)
    (hχ₁one : (χ₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hχone : (χ : ClassFunction ↥L ℂ) 1 = (d : ℂ)) :
    d₁ < d := by
  have hle : d₁ ≤ d :=
    hyp.natDegree_le_of_xBaseBlock_anchor hχ₁base hχX hχ₁one hχone
  have hne : d₁ ≠ d := by
    intro hEq
    apply hχnotbase
    refine ⟨hχX, ?_⟩
    intro ψ hψX
    have hbase_le := hχ₁base.2 ψ hψX
    have hχre :
        (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction ↥L ℂ)).re =
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction ↥L ℂ)).re := by
      rw [OddOrder.Peterfalvi.S03.characterDegree_def,
        OddOrder.Peterfalvi.S03.characterDegree_def, hχone, hχ₁one]
      exact_mod_cast hEq.symm
    rw [hχre]
    exact hbase_le
  omega

/-- The base block is closed under conjugation, from the abstract input `X ⊆ Irr L`:
conjugation preserves the degree (`characterDegree_conj`) and `X`
(`Xset_closedUnderConjugate_of_irreducible_X`).  With the no-real property this makes `S₀`
contain a conjugate pair, so `2 ≤ |S₀|`. -/
theorem xBaseBlock_closedUnderConjugate_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (_hZH : Z ≤ H) [Z.Normal]
    (_hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
  hyp.xBaseBlock_closedUnderConjugate_unconditional Z

/-- The base block is closed under conjugation (Frobenius case). -/
theorem xBaseBlock_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
  hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)

/-- A member `χ = Ind_H^L θ` of `S` is supported on `H` (its induced character vanishes off the
normal subgroup `H`). -/
theorem sMember_support_subset_H (hyp : SibleyDadeHypothesis G L H)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) :
    χ.support ⊆ (H : Set ↥L) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  rw [hχeq]
  exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)

/-- **(T8 leaf 6) equal-degree difference support.**  For two members `χ, χ'` of `S` of equal
degree (`χ(1) = χ'(1)`) the difference `χ − χ'` is supported on `H^# = sharpImage H`: both are
supported on `H` (`sMember_support_subset_H`) and the difference vanishes at `1` (equal degree).
This is the `hsuppdiff` input of `coherentEqualDegree_fromDade` for the equal-minimal-degree base
block `S₀` (`irreducibleCharacterDifference χ j = χⱼ − χ₀`), and the (5.6) `χ − a·χ₁` support shape. -/
theorem sMember_diffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) (hdeg : χ 1 = χ' 1) :
    (χ - χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  have hgH : g ∈ H := by
    rcases eq_or_ne (χ g) 0 with hχg | hχg
    · have hχ'g : χ' g ≠ 0 := fun h0 =>
        hg (by rw [ClassFunction.sub_apply, hχg, h0, sub_self])
      exact hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr hχ'g)
    · exact hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T8.11d) scaled degree-matched support.**

For two `S`-members whose degrees satisfy `χ(1) = a χ₁(1)`, the scaled difference
`χ - aχ₁` is supported on `H^# = sharpImage H`.  This is the support bridge used for the
`hmemdegdiffsupp` and `hdiffasuppχ` fields once the integer degree ratios are available. -/
theorem sMember_scaledDiffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) {a : ℕ}
    (hdeg : χ 1 = (a : ℂ) * χ' 1) :
    (χ - a • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by
      rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ a χ', ClassFunction.smul_apply,
        hdeg, sub_self])
  have hgH : g ∈ H := by
    rcases eq_or_ne (χ g) 0 with hχg | hχg
    · have hχ'g : χ' g ≠ 0 := fun h0 =>
        hg (by
          rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ a χ',
            ClassFunction.smul_apply, hχg, h0, mul_zero, sub_self])
      exact hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr hχ'g)
    · exact hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **Two-coefficient degree-matched difference support.**  For two `S`-members `χ, χ'` and naturals
`m, n` with `m·χ(1) = n·χ'(1)`, the combination `m·χ − n·χ'` is supported on `H^# = sharpImage H`.
Both are supported on `H` (`sMember_support_subset_H`) and the combination vanishes at `1`.  Unlike
`sMember_scaledDiffSupport_of_charValue_eq` (`χ − a·χ'`, requiring `χ'(1) ∣ χ(1)`), the symmetric
coefficients `m = χ'(1)`, `n = χ(1)` make `m·χ − n·χ'` supported **without** any divisibility — the
(4.1) supported-difference input `χ'(1)·χ − χ(1)·χ'` used in the (6.8.1) `himg_ortho`. -/
theorem sMember_smulDiffSupport_of_charValue_eq (hyp : SibleyDadeHypothesis G L H)
    {χ χ' : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hχ'S : χ' ∈ hyp.S) {m n : ℕ}
    (hdeg : (m : ℂ) * χ 1 = (n : ℂ) * χ' 1) :
    (m • χ - n • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  have hval : ∀ x : ↥L, (m • χ - n • χ') x = (m : ℂ) * χ x - (n : ℂ) * χ' x := by
    intro x
    rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ m χ, ← Nat.cast_smul_eq_nsmul ℂ n χ',
      ClassFunction.smul_apply, ClassFunction.smul_apply]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [hval, hdeg, sub_self])
  have hgH : g ∈ H := by
    by_contra hgnH
    have hχg : χ g = 0 := by
      by_contra h
      exact hgnH (hyp.sMember_support_subset_H hχS (ClassFunction.mem_support.mpr h))
    have hχ'g : χ' g = 0 := by
      by_contra h
      exact hgnH (hyp.sMember_support_subset_H hχ'S (ClassFunction.mem_support.mpr h))
    exact hg (by rw [hval, hχg, hχ'g, mul_zero, mul_zero, sub_zero])
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **`S`-member degree ratio against a degree-`|W₁|` anchor.**

For `χ = Ind_H^L θ ∈ S` and an anchor `χ₁` of the minimal degree `χ₁(1) = |W₁|` (induced from a
degree-`1` source of `H`), the degree ratio `χ(1)/χ₁(1)` is the source degree `θ(1)`, a positive
natural number: `χ(1) = θ(1)·χ₁(1)` (`χ(1) = |L:H|·θ(1) = |W₁|·θ(1)`, `induce_apply_one`).  This
produces the integer degree `a = deg i` and the equation `χ(1) = a·χ₁(1)` that
`sMember_scaledDiffSupport_of_charValue_eq` (and `scaledDiff_dadeImage_mem_ZIrr`) consume for the
`hmemdegdiffsupp`/`hdiffasuppχ`/`htau1_memaχ` fields of the (6.2)/B1 member-family.  Applied with
`χ = χ₁` it gives the anchor ratio `a = 1` (`ha1`). -/
theorem sMember_charValue_one_eq_mul_anchor (hyp : SibleyDadeHypothesis G L H)
    {χ χ₁ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ)) :
    ∃ a : ℕ, 0 < a ∧ χ 1 = (a : ℂ) * χ₁ 1 := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨a, ha_pos, ha⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  refine ⟨a, ha_pos, ?_⟩
  rw [hχeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, ha,
    hyp.index_H_eq_card_W1, hχ₁deg]
  ring

/-- **(6.2) member-family core for `S₁ ⊆ S`** (Frobenius case): the flat enumeration of `S₁` with
its per-member orthonormality, non-realness, conjugate-difference support, and `S₁`-membership
facts.

For a finite conjugation-closed `S₁ ⊆ S`, `exists_finEnum_irreducible` gives an injective family
`χmem : Fin k → Irr L` with range `S₁`; the per-member helpers (`sMember_characterFacts`,
`sMember_diffSupport`) and conjugation-closure of `S₁` discharge the `hmemreal`/`hmemconjortho`/
`hmemortho`/`hmemdiffsupp`/`hmemS1`/`hmembarS1` fields that B1
(`coherentDegreeSumBound_of_not_coherent`) consumes.  The degree data
(`deg`/`hmemdegdiffsupp`, from `sMember_charValue_one_eq_mul_anchor`) is layered on separately. -/
theorem exists_sMemberOrthonormalFamily (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁) ∧
      (∀ j, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ i j, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ) = if i = j then (1 : ℂ) else 0) := by
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hφ)
  obtain ⟨k, χmem, hχinj, hrange⟩ := exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact Set.mem_range_self j
  refine ⟨k, χmem, hχinj, hrange, ?_, ?_, hmemS1, ?_, ?_, ?_⟩
  · intro j
    exact (hyp.sMember_characterFacts hF (hS₁sub (hmemS1 j))).1
  · intro j
    exact hyp.sMember_diffSupport (hS₁sub (hmemS1 j)) (χmem j).2
  · intro j
    exact hS₁conj (hmemS1 j)
  · intro j
    exact (hyp.sMember_characterFacts hF (hS₁sub (hmemS1 j))).2.2.2.2
  · intro i j
    rw [irreducibleCharacter_inner_eq_ite (χmem i) (χmem j)]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg (fun he => h (hχinj he)), if_neg h]

/-- **(6.2) member-family degree data** (Frobenius case): integer degree ratios against a
degree-`|W₁|` anchor.

Given a family `χmem` of `S`-members and a distinguished index `i₁` whose member has the minimal
degree `χmem i₁ (1) = |W₁|`, every member has a positive integer degree ratio
`χmem j (1) = (deg j)·χmem i₁ (1)` (the source degree, `sMember_charValue_one_eq_mul_anchor`), the
anchor ratio is `deg i₁ = 1` (cancel the nonzero `|W₁|`), and each scaled difference
`χmem j − deg j·χmem i₁` is supported on `H^#` (`sMember_scaledDiffSupport_of_charValue_eq`).  This
is the `deg`/`ha1`/`hmemdegdiffsupp` data that layers on `exists_sMemberOrthonormalFamily` to
complete the (6.2)/B1 member-family. -/
theorem exists_sMemberDegreeData (hyp : SibleyDadeHypothesis G L H)
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L} {i₁ : Fin k}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S)
    (hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ)) :
    ∃ deg : Fin k → ℕ, deg i₁ = 1 ∧ (∀ j, 0 < deg j) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ) - deg j • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  choose deg hdeg_pos hdeg_eq using fun j =>
    hyp.sMember_charValue_one_eq_mul_anchor (hmemS j) hanchordeg
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨deg, ?_, hdeg_pos, hdeg_eq, fun j =>
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hmemS j) (hmemS i₁) (hdeg_eq j)⟩
  have h := hdeg_eq i₁
  rw [hanchordeg] at h
  have hdeg1 : (deg i₁ : ℂ) = 1 :=
    mul_right_cancel₀ hW1ne (by rw [one_mul]; exact h.symm)
  exact_mod_cast hdeg1

/-- **(6.2) anchor existence: `S(A)` contains a member of the minimal degree `|W₁|`.**

When the section `H/(A.subgroupOf H)` has a proper commutator subgroup (e.g. `A ⊊ H` with `H`
solvable, so `H/A` is a nontrivial solvable group), it carries a nontrivial degree-`1` character
trivial on `A` (`exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top`); its
induction `Ind_H^L θ ∈ S(A)` has degree `|L:H|·1 = |W₁|`
(`induce_apply_one_eq_card_W1_of_degree_one`).  This furnishes the degree-`|W₁|` anchor `χ₁`
consumed by `exists_sMemberDegreeData` (its `hanchordeg`). -/
theorem exists_mem_SsubFiltration_degree_W1 (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {A : Subgroup ↥L} [A.Normal]
    (h : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤) :
    ∃ φ, φ ∈ hyp.SsubFiltration A ∧ (φ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ) := by
  obtain ⟨θ, hθne, hθker, hθdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top (A.subgroupOf H) h
  refine ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), ?_, ?_⟩
  · rw [hyp.mem_SsubFiltration]; exact ⟨θ, hθne, hθker, rfl⟩
  · exact hyp.induce_apply_one_eq_card_W1_of_degree_one θ hθdeg

/-- **(6.2) adjoined-pair fields for the breaking pair `{ψ, ψ̄}`** (Frobenius case).

For `ψ ∈ S` whose conjugate pair `{ψ, ψ̄}` is disjoint from `S₁ ⊆ S`, this packages the per-`ψ`
fields B1 (`coherentDegreeSumBound_of_not_coherent`) consumes: non-realness and orthonormality of
`{ψ, ψ̄}` (`sMember_characterFacts`), the conjugate-difference support on `H^#`
(`sMember_diffSupport`), and the orthogonality of `ψ` and `ψ̄` to every member of `S₁` (distinct
irreducibles, since `ψ, ψ̄ ∉ S₁` but the members lie in `S₁`).  Together with
`exists_coherentBreakPair` (which supplies `ψ ∉ S₁`, `ψ̄ ∉ S₁`) this is the adjoined-pair side of
the (6.2) member-family. -/
theorem sBreakPair_fields (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {ψ : ClassFunction ↥L ℂ} {S₁ : Set (ClassFunction ↥L ℂ)}
    (hψS : ψ ∈ hyp.S) (hS₁sub : S₁ ⊆ hyp.S) (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
      ClassFunction.inner ψ ψ = 1 ∧ ClassFunction.inner ψ.conj ψ.conj = 1 ∧
      ClassFunction.inner ψ.conj ψ = 0 ∧ ClassFunction.inner ψ ψ.conj = 0 ∧
      ((ψ.conj - ψ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ χ = 0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ.conj χ = 0) := by
  have hψirr : IsIrreducibleCharacter ψ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS
  obtain ⟨hreal, hψψ, hψbarψbar, hψbarψ, hψψbar⟩ := hyp.sMember_characterFacts hF hψS
  refine ⟨hreal, hψψ, hψbarψbar, hψbarψ, hψψbar,
    hyp.sMember_diffSupport hψS hψirr, ?_, ?_⟩
  · intro χ hχS1
    have hχirr : IsIrreducibleCharacter χ :=
      hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hχS1)
    have hne : ψ ≠ χ := fun h => hψnotS1 (by rw [h]; exact hχS1)
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hψirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hχirr⟩
    rwa [if_neg (fun he => hne (congrArg Subtype.val he))] at h
  · intro χ hχS1
    have hχirr : IsIrreducibleCharacter χ :=
      hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hS₁sub hχS1)
    have hne : ψ.conj ≠ χ := fun h => hψcnotS1 (by rw [h]; exact hχS1)
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ.conj, hψirr.conj⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hχirr⟩
    rwa [if_neg (fun he => hne (congrArg Subtype.val he))] at h

/-- **(T8.11e) scaled supported differences map to virtual characters.**

Once the degree-ratio support field for `χ - aχ₁` is known, the real Dade map sends that
scaled difference to `ℤ[Irr G]`.  This is exactly the `htau1_memaχ` field of
`XAdjoinStepInput`, separated from the arithmetic that produces the ratio and support. -/
theorem scaledDiff_dadeImage_mem_ZIrr (hyp : SibleyDadeHypothesis G L H)
    {χ χ₁ : IrreducibleCharacter ↥L} {a : ℕ}
    (hdiffasupp : ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    hyp.tau ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G := by
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dade hyp.hconj hdiffasupp
    (Submodule.sub_mem _ χ.mem_ZIrr (nsmul_mem χ₁.mem_ZIrr a))

/-- **(T8.11f) X-members with a degree ratio have supported scaled difference.**

This is the `X = S - S(Z)` adapter for `sMember_scaledDiffSupport_of_charValue_eq`: once
the degree-ratio equation `χ(1)=aχ₁(1)` is available, the scaled difference
`χ-aχ₁` is supported on `H^#`. -/
theorem xMember_scaledDiffSupport_of_degreeData (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} {χ χ₁ : IrreducibleCharacter ↥L} {a : ℕ}
    (hχX : (χ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hχ₁X : (χ₁ : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hdeg : (χ : ClassFunction ↥L ℂ) 1 = (a : ℂ) * (χ₁ : ClassFunction ↥L ℂ) 1) :
    ((χ : ClassFunction ↥L ℂ) - a • (χ₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  exact hyp.sMember_scaledDiffSupport_of_charValue_eq
    (hyp.mem_Xset.mp hχX).1 (hyp.mem_Xset.mp hχ₁X).1 hdeg

/-- **(T8.11g) member-family scaled supports from degree data.**

Given a finite accumulator family inside `X` and degree ratios against the distinguished member
`χ₁`, all scaled member differences `χᵢ-degᵢχ₁` are supported on `H^#`.  This is the
`hmemdegdiffsupp` half of `XAdjoinStepInput`, separated from the arithmetic that constructs the
ratios. -/
theorem xMember_scaledDiffSupports_of_degreeData (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} {ι : Type*} {s : Finset ι}
    {χmem : ι → IrreducibleCharacter ↥L} {deg : ι → ℕ} {i₁ : ι}
    (hmemX : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z)
    (hi₁ : i₁ ∈ s)
    (hdeg : ∀ i ∈ s,
      (χmem i : ClassFunction ↥L ℂ) 1 =
        (deg i : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) :
    ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  intro i hi
  exact hyp.xMember_scaledDiffSupport_of_degreeData (hmemX i hi) (hmemX i₁ hi₁) (hdeg i hi)

open scoped Classical in
/-- **(6.2) member-family → B1 degree-sum bound.**

Assembles the (6.2) member-family for a coherent `S₁` and the breaking pair `{ψ, ψ̄}`, feeding it to
B1 (`coherentDegreeSumBound_of_not_coherent`).  When `S₁` (conjugation-closed, coherent, `⊆ S`)
contains the degree-`|W₁|` anchor `χ₁`, `ψ ∈ S` with `{ψ, ψ̄}` disjoint from `S₁`, and `S₁ ∪ {ψ, ψ̄}`
is not coherent, the degree-ratio sum is bounded by `∑ⱼ (degⱼ)² ≤ 2·a`, where `degⱼ = χⱼ(1)/χ₁(1)`
and `a = ψ(1)/χ₁(1)`.

All member-family fields are discharged from the landed pieces: the per-member core
(`exists_sMemberOrthonormalFamily`), the degree data (`exists_sMemberDegreeData`), the adjoined-pair
fields (`sBreakPair_fields`), the scaled-difference support + Dade image
(`sMember_scaledDiffSupport_of_charValue_eq`, `scaledDiff_dadeImage_mem_ZIrr`), and the abstract
S07 generation bridges (`…_scaledDiffs`, `…_anchorGeneration`).  This is the (6.2) step
"`2ψ(1)|L:K| ≥ ∑_{χ∈S₁} χ(1)²/‖χ‖²`" in normalized integer form. -/
theorem sMember_degreeSumBound_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L) (deg : Fin k → ℕ) (a : ℕ),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * χ₁ 1) ∧
      ψ 1 = (a : ℂ) * χ₁ 1 ∧
      ∑ j : Fin k, ((deg j : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  classical
  -- (1) enumerate `S₁` with the per-member fields
  obtain ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1,
    hmemconjortho, hmemortho⟩ := hyp.exists_sMemberOrthonormalFamily hF hS₁sub hS₁conj hS₁fin
  -- (2) locate the anchor index `i₁` (the anchor lies in `S₁ = range χmem`)
  have hχ₁range : χ₁ ∈ Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]; exact hχ₁S₁
  obtain ⟨i₁, hi₁eq0⟩ := hχ₁range
  have hi₁eq : (χmem i₁ : ClassFunction ↥L ℂ) = χ₁ := hi₁eq0
  have hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S := fun j => hS₁sub (hmemS1 j)
  have hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (Nat.card hyp.W1 : ℂ) := by
    rw [hi₁eq]; exact hχ₁deg
  -- (3) degree data
  obtain ⟨deg, hdeg_i₁, _hdeg_pos, hdeg_eq, hmemdegdiffsupp⟩ :=
    hyp.exists_sMemberDegreeData hmemS hanchordeg
  -- (4) breaking-pair fields
  obtain ⟨hrealψ, hψψ, hψbarψbar, hψbarψ, hψψbar, hdiffsuppψ, hψ_S1, hψbar_S1⟩ :=
    hyp.sBreakPair_fields hF hψS hS₁sub hψnotS1 hψcnotS1
  -- (5) the `ψ` degree ratio `a`
  obtain ⟨a, _ha_pos, hψratio⟩ := hyp.sMember_charValue_one_eq_mul_anchor hψS hanchordeg
  -- (6) `ψ` scaled-difference support + Dade image (the `ψ`-side `hdiffasuppχ`/`htau1_memaχ`)
  have hdiffasuppψ : (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq hψS (hmemS i₁) hψratio
  have htau1ψ : hyp.tau (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G :=
    hyp.scaledDiff_dadeImage_mem_ZIrr (χ := ⟨ψ, hψirr⟩) (χ₁ := χmem i₁) hdiffasuppψ
  -- (7) generation fields via the abstract S07 bridges (`hSgen`, `hgen`)
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := fun j => (χmem j : ClassFunction ↥L ℂ))
    (deg := deg) (i₁ := i₁) hcover (Finset.mem_univ i₁) (fun j _ => hmemS1 j)
    (fun j _ => hmemdegdiffsupp j)
  have hbar1 : ψ.conj 1 = ψ 1 := by
    rw [ClassFunction.conj_apply]
    obtain ⟨n, -, hn1, -⟩ := hψirr.exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast]
  have hchi1_ne : (χmem i₁ : ClassFunction ↥L ℂ) 1 ≠ 0 := by
    rw [hanchordeg]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    intro hmem
    exact hmem.2 (by simp)
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := ψ) (chibar := ψ.conj) (chi1 := (χmem i₁ : ClassFunction ↥L ℂ)) (a := a)
    hSgen hψratio hbar1 hchi1_ne h1A
  -- (8) feed everything to B1
  refine ⟨k, χmem, deg, a, hχinj, hrange, fun j => by rw [hdeg_eq j, hi₁eq],
    by rw [hψratio, hi₁eq], ?_⟩
  have hbound := coherentDegreeSumBound_of_not_coherent hyp.dade hyp.hconj hS₁coh
    ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ hψψ hψbarψbar hψψbar hψbarψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    (fun j _ => hmemreal j) (fun j _ => hmemdiffsupp j) (fun j _ => hmemdegdiffsupp j)
    (fun j _ => hmemS1 j) (fun j _ => hmembarS1 j) (fun j _ => hmemconjortho j)
    (fun i _ j _ => by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h])
    hdiffasuppψ htau1ψ hdeg_i₁ hSgen hgen hnc
  simpa using hbound

/-- **(6.2) member-family degree-square bound** (real form).

The degree-sum bound `sMember_degreeSumBound_of_not_coherent` (`∑ⱼ (degⱼ)² ≤ 2a`), rescaled by the
anchor degree `χ₁(1) = |W₁|`, gives the character-degree-square sum over the enumerated `S₁`-family:
`∑ⱼ (χⱼ(1))² ≤ 2·ψ(1)·χ₁(1)` (real parts), since `χⱼ(1) = degⱼ·χ₁(1)` and `ψ(1) = a·χ₁(1)`.  This is
the (6.2) bound `∑_{χ∈S₁} χ(1)² ≤ 2ψ(1)χ₁(1)` in the form ready to be compared, via `S(A) ⊆ S₁`,
with the `S(A)` degree-sum identity B2. -/
theorem sMember_degreeSqReBound_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 ≤
        2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, deg, a, hχinj, hrange, hdeg_eq, hψ_eq, hbound⟩ :=
    hyp.sMember_degreeSumBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact ⟨j, rfl⟩
  refine ⟨k, χmem, hχinj, hrange, hmemS1, ?_⟩
  -- real parts of the degree relations
  have hdegre : ∀ j, ((χmem j : ClassFunction ↥L ℂ) 1).re = (deg j : ℝ) * (χ₁ 1).re := by
    intro j
    rw [hdeg_eq j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hψre : (ψ 1).re = (a : ℝ) * (χ₁ 1).re := by
    rw [hψ_eq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hre_nonneg : (0 : ℝ) ≤ (χ₁ 1).re ^ 2 := sq_nonneg _
  calc ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2
      = ∑ j : Fin k, ((deg j : ℝ) * (χ₁ 1).re) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (χ₁ 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (χ₁ 1).re ^ 2 * (2 * (a : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hbound hre_nonneg
    _ = 2 * ((a : ℝ) * (χ₁ 1).re) * (χ₁ 1).re := by ring
    _ = 2 * (ψ 1).re * (χ₁ 1).re := by rw [hψre]

open scoped Classical in
/-- **(6.2) B2 in real / Frobenius form.**

In the Frobenius case every member of `S(A)` is an irreducible induced character
(`isIrreducibleCharacter_of_mem_S_of_frobenius`), so `χ(1)²/‖χ‖² = (χ(1).re)²` (`‖χ‖² = 1`, `χ(1)`
a real natural number), and B2 (`sum_div_normSq_induce_kernelFilter_eq`) becomes the real
degree-square identity `∑_{χ∈S(A)} (χ(1).re)² = |L:H|·(|H:A| − 1)`. -/
theorem sum_re_sq_induce_kernelFilter_eq (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {A : Subgroup ↥L} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        ((χ 1).re) ^ 2
      = (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hB2 := sum_div_normSq_induce_kernelFilter_eq (G := ↥L) (H := H) (A := A)
  have hsummand : ∀ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
      (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥H ℂ) ∧
        θ ≠ trivialIrreducibleCharacter ↥H)).image
      (fun θ => ClassFunction.induce H θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ = ((((χ 1).re) ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    have hθne : θ ≠ trivialIrreducibleCharacter ↥H := (Finset.mem_filter.mp hθ).2.2
    have hχS : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
    have hirr := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχS
    have hinner : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite (⟨_, hirr⟩ : IrreducibleCharacter ↥L) ⟨_, hirr⟩
    obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
    rw [hinner, div_one, hn1, Complex.natCast_re]; push_cast; ring
  have key : ((∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        ((χ 1).re) ^ 2 : ℝ) : ℂ)
      = (((H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hsummand χ hχ).symm), hB2]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped Classical in
/-- **(6.6) X degree-sum identity (Frobenius case).**

The degree-square sum over `X = S − S(Z)` is `|L:H| · (|H| − |H:Z|)`.  Since `S = S(⊥)` and
`S(Z) ⊆ S`, this is the difference of two instances of the `S(A)` degree-sum identity
`sum_re_sq_induce_kernelFilter_eq` (at `A = ⊥`, using `|H ⧸ ⊥| = |H|`, and at `A = Z`).  This is
the `total` of the X-chain step data: the (6.6) divisibility argument shows the source degree
`θχ(1)²` divides it. -/
theorem sum_re_sq_Xset_eq (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} [Z.Normal] :
    ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
  letI : H.Normal := hyp.H_normal
  have hbotker : ∀ θ : IrreducibleCharacter ↥H,
      (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro θ x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsub : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) ⊆
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) := by
    apply Finset.image_subset_image
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    exact ⟨hθ.1, hbotker θ, hθ.2.2⟩
  have hsd := Finset.sum_sdiff (f := fun χ : ClassFunction ↥L ℂ => ((χ 1).re) ^ 2) hsub
  have h0 := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := (⊥ : Subgroup ↥L))
  have hZ := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := Z)
  have hbotcard : Nat.card (↥H ⧸ (⊥ : Subgroup ↥L).subgroupOf H) = Nat.card ↥H := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥H)).toEquiv
  rw [hbotcard] at h0
  rw [eq_sub_of_add_eq hsd, h0, hZ]
  ring

open scoped Classical in
/-- **Reindexing `X(Z)` to the `Irr L`-filter** (Frobenius case).  Any Finset `T` member-wise equal
to the central `(6.6)` set `X(Z) = {χ ∈ Irr L | Z ⊄ ker χ}`
(`Xset_eq_irreducible_not_subset_characterKernel`) sums the same as the `IrreducibleCharacter ↥L`
filter `{ψ | Z ⊄ ker ψ}` for any `ℂ`-valued function: the injective coercion
`IrreducibleCharacter ↥L ↪ ClassFunction ↥L ℂ` (`IrreducibleCharacter.ext`) is a bijection between
them.  This bridges the regular-character sums (`sumNonInflatedDegreeMulChar_of_mem`,
`sumNonInflatedDegreeSq`), stated over the `Irr`-filter, to the Sibley `X(Z)` index set. -/
theorem sum_Xset_eq_sum_filter_irreducible_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z)
    (f : ClassFunction ↥L ℂ → ℂ) :
    ∑ φ ∈ T, f φ = ∑ ψ ∈ Finset.univ.filter (fun ψ : IrreducibleCharacter ↥L =>
        ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction ↥L ℂ))),
        f (ψ : ClassFunction ↥L ℂ) := by
  classical
  have hXc : hyp.Xset Z = {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)} :=
    hyp.Xset_eq_irreducible_not_subset_characterKernel hZH
      (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)
  have hirrT : ∀ φ, φ ∈ T → IsIrreducibleCharacter φ := by
    intro φ hφ; have := (hT φ).mp hφ; rw [hXc] at this; exact this.1
  have hkerT : ∀ φ, φ ∈ T →
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel φ) := by
    intro φ hφ; have := (hT φ).mp hφ; rw [hXc] at this; exact this.2
  have hmemT : ∀ ψ : IrreducibleCharacter ↥L,
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction ↥L ℂ)) →
      (ψ : ClassFunction ↥L ℂ) ∈ T := by
    intro ψ hψ; rw [hT, hXc]; exact ⟨ψ.2, hψ⟩
  refine Finset.sum_bij'
    (fun φ hφ => (⟨φ, hirrT φ hφ⟩ : IrreducibleCharacter ↥L))
    (fun ψ _ => (ψ : ClassFunction ↥L ℂ))
    (fun φ hφ => ?_) (fun ψ hψ => ?_) (fun φ hφ => rfl) (fun ψ hψ => ?_) (fun φ hφ => rfl)
  · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hkerT φ hφ⟩
  · rw [Finset.mem_filter] at hψ; exact hmemT ψ hψ.2
  · apply IrreducibleCharacter.ext; rfl

open scoped Classical in
/-- **(6.8.1) regular-character value over `X(Z)`** (mmd 04.8 L168).  For the central `(6.6)` set
`X(Z)` and `z ∈ Z^#`, `∑_{χ ∈ X(Z)} χ(1)·χ(z) = -|L ⧸ Z|` — the off-identity value of
`∑ χ(1)·χ = ρ_L − ρ_{L/Z}` (the step showing `η₁^{τ₁}` is constant on `Z^#`).  Reindex
(`sum_Xset_eq_sum_filter_irreducible_of_frobenius`) + `sumNonInflatedDegreeMulChar_of_mem`. -/
theorem sum_degree_mul_charValue_Xset_eq_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z)
    {z : ↥L} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∑ φ ∈ T, (φ 1) * (φ z) = -(Nat.card (↥L ⧸ Z) : ℂ) := by
  rw [hyp.sum_Xset_eq_sum_filter_irreducible_of_frobenius hF hZH hT (fun φ => φ 1 * φ z)]
  exact OddOrder.RepresentationTheory.sumNonInflatedDegreeMulChar_of_mem (N := Z) hz hz1

open scoped Classical in
/-- **(6.8.1) degree-square value over `X(Z)`** (mmd 04.8, the `z = 1` companion).  For the central
`(6.6)` set `X(Z)`, `∑_{χ ∈ X(Z)} χ(1)·χ(1) = |L| − |L ⧸ Z|`.  Reindex
(`sum_Xset_eq_sum_filter_irreducible_of_frobenius`) + `sumNonInflatedDegreeSq`. -/
theorem sum_degree_sq_Xset_eq_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z) :
    ∑ φ ∈ T, (φ 1) * (φ 1) = (Nat.card ↥L : ℂ) - (Nat.card (↥L ⧸ Z) : ℂ) := by
  rw [hyp.sum_Xset_eq_sum_filter_irreducible_of_frobenius hF hZH hT (fun φ => φ 1 * φ 1)]
  rw [← OddOrder.RepresentationTheory.sumNonInflatedDegreeSq (N := Z)]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  rw [pow_two]

open scoped Classical in
/-- **(6.8.1) regular-character difference value over `X(Z)`** (mmd 04.8 L168, combined form).  For
the central `(6.6)` set `X(Z)` and `z ∈ Z^#`, `∑_{χ ∈ X(Z)} χ(1)·(χ(z) − χ(1)) = -|L|`.  This is
`(ρ_L − ρ_{L/Z})(z) − (ρ_L − ρ_{L/Z})(1) = -|L:Z| − (|L| − |L:Z|) = -|L|` (the off-identity minus the
degree value), which divided by `a|W₁| = χ₁(1)` gives `∑dᵢχᵢ(z) − ∑dᵢχᵢ(1) = -|H|/a` — the key
constant in showing `η₁^{τ₁}` is constant on `Z^#`. -/
theorem sum_degree_mul_charValue_sub_Xset_eq_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    {T : Finset (ClassFunction ↥L ℂ)} (hT : ∀ φ, φ ∈ T ↔ φ ∈ hyp.Xset Z)
    {z : ↥L} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∑ φ ∈ T, (φ 1) * (φ z - φ 1) = -(Nat.card ↥L : ℂ) := by
  have hexpand : ∑ φ ∈ T, (φ 1) * (φ z - φ 1)
      = (∑ φ ∈ T, (φ 1) * φ z) - (∑ φ ∈ T, (φ 1) * φ 1) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun φ _ => ?_); ring
  rw [hexpand, hyp.sum_degree_mul_charValue_Xset_eq_of_frobenius hF hZH hT hz hz1,
    hyp.sum_degree_sq_Xset_eq_of_frobenius hF hZH hT]
  ring

/-- **(6.6) `htotal` factorization.**  `|L:H|·(|H| − |H:Z|) = |H:Z| · (|L:H|·(|Z| − 1))` (Lagrange
`|H| = |H:Z|·|Z|`).  With the X degree-sum `total = |L:H|·(|H| − |H:Z|)` (`sum_re_sq_Xset_eq`), this
is the `total = qtot · c` of the X-chain step data with `qtot = |H:Z|`, `c = |L:H|·(|Z| − 1)`. -/
theorem index_mul_card_sub_factor (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} [Z.Normal] :
    H.index * (Nat.card ↥H - Nat.card (↥H ⧸ Z.subgroupOf H))
      = Nat.card (↥H ⧸ Z.subgroupOf H) * (H.index * (Nat.card ↥(Z.subgroupOf H) - 1)) := by
  have hlag : Nat.card ↥H
      = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
  have hz : 1 ≤ Nat.card ↥(Z.subgroupOf H) := Nat.card_pos
  obtain ⟨w, hw⟩ : ∃ w, Nat.card ↥(Z.subgroupOf H) = w + 1 := ⟨_, (Nat.sub_add_cancel hz).symm⟩
  rw [hlag, hw]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
  ring

/-- **(6.8.3) arithmetic core.**  The numeric contradiction closing the (6.8.3) extension in case
(A).  From the break-pair (5.6) bound `∑_{χ∈X} χ(1)² < 2ψ(1)η₁(1)` — i.e.
`|W₁|·|H:Z|·(|Z|−1) < 2·|W₁|²·d` with `ψ(1) = |W₁|d`, `η₁(1) = |W₁|` — together with [Is] Cor 2.30
`d² ≤ |H:Z|` (valid since `Z` is central) and the fixed-point-free bound `|Z|−1 ≥ 2|W₁|`
(`W₁` acts FPF on the odd-order `Z`), one derives `|H:Z| < d ≤ d² ≤ |H:Z|`, a contradiction.

Here `w1 = |W₁|`, `d = θ(1)` (the degree of the `H`-source of `ψ`), `hZ = |H:Z|`, `cZ = |Z|`.
The hypothesis `2 ≤ hZ` holds because `Z ⊆ H′ ⊊ H` (`H` non-abelian), so `|H:Z| ≥ |H:H′| ≥ 2`. -/
theorem false_of_centralCommutator_break_arith {w1 d hZ cZ : ℕ}
    (hw1 : 1 ≤ w1) (hd : 1 ≤ d) (hdsq : d ^ 2 ≤ hZ) (hZ2 : 2 ≤ hZ)
    (hfpf : 2 * w1 ≤ cZ - 1)
    (hbreak : w1 * hZ * (cZ - 1) ≤ 2 * w1 ^ 2 * d) : False := by
  set m := cZ - 1 with hm
  have hge : 2 * w1 ^ 2 * hZ ≤ w1 * hZ * m := by
    calc 2 * w1 ^ 2 * hZ = w1 * hZ * (2 * w1) := by ring
      _ ≤ w1 * hZ * m := mul_le_mul_left' hfpf (w1 * hZ)
  have hle : 2 * w1 ^ 2 * hZ ≤ 2 * w1 ^ 2 * d := le_trans hge hbreak
  have hZd : hZ ≤ d := Nat.le_of_mul_le_mul_left hle (by positivity)
  have h2d : 2 ≤ d := le_trans hZ2 hZd
  have hdd : 2 * d ≤ d ^ 2 := by nlinarith [h2d]
  omega

/-- **(6.6) per-member degree shape.**  Every member `χ = Ind_H^L θ` of `S` (`θ ∈ Irr H`) has degree
`χ(1) = |L:H| · θ(1)`; when `H` is a `p`-group `θ(1) = p^k`, so `χ(1) = |L:H| · p^k`.  This is the
common-index `p`-power degree shape (`idx = |L:H|`) of every X-chain member. -/
theorem exists_index_primePow_degree_of_mem_S (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.S) :
    ∃ k : ℕ, χ 1 = ((H.index * p ^ k : ℕ) : ℂ) := by
  rw [hyp.S_eq, Set.mem_setOf_eq] at hχ
  obtain ⟨θ, _hθ, rfl⟩ := hχ
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hHp θ
  refine ⟨k, ?_⟩
  rw [ClassFunction.induce_apply_one, hk]
  push_cast; ring

/-- **(6.6) per-member degree data for an X-member family.**  Vectorizes
`exists_index_primePow_degree_of_mem_S` over a finite family `χmem : Fin k → Irr L` of `S`-members:
there are exponents `mmem j` with `χmem j (1) = |L:H| · p^(mmem j)`.  Supplies the `dmem`/`θmem`/`mmem`
fields of the X-chain step data (`dmem j = |L:H|·θmem j`, `θmem j = p^(mmem j)`). -/
theorem exists_memberDegreeData (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.S) :
    ∃ mmem : Fin k → ℕ,
      ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = ((H.index * p ^ mmem j : ℕ) : ℂ) := by
  choose mmem hmmem using fun j => hyp.exists_index_primePow_degree_of_mem_S hp hHp (hmemS j)
  exact ⟨mmem, hmmem⟩

/-- **(6.6)/(6.8) central degree bound for an X-member (the redesign linchpin).**  For
`χ = Ind_H^L θ ∈ X(Z) = S − S(Z)` with `H` a `p`-group and `Z` **central in `H`**
(`Z.subgroupOf H ≤ Z(↥H)`), the source `θ` has `θ(1) = p^k` and — crucially — by [Is] Cor 2.30
(`exists_degree_sq_le_index`, which needs `Z` central) `θ(1)² = (p^k)² ≤ |H:Z|`, while
`χ(1) = |L:H|·p^k`.  This is exactly the `θχ`/`hθχ`/`hθsq_le_qtot` data the per-step X-chain producer
needs (with `qtot = |H:Z|`); it is fillable at the central `Z = Z(H)∩H′` but **not** at `Z = ⁅H,H⁆`
(see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`). -/
theorem exists_source_primePow_centralBound_of_mem_Xset (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {Z : Subgroup ↥L} (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset Z) :
    ∃ k : ℕ, χ 1 = ((H.index * p ^ k : ℕ) : ℂ)
      ∧ (p ^ k) ^ 2 ≤ Nat.card (↥H ⧸ Z.subgroupOf H) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hχS : χ ∈ hyp.S := hyp.Xset_subset_S hχ
  rw [hyp.S_eq, Set.mem_setOf_eq] at hχS
  obtain ⟨θ, _hθne, rfl⟩ := hχS
  obtain ⟨k, hk⟩ := exists_primePow_natDegree_of_isPGroup hp hHp θ
  refine ⟨k, ?_, ?_⟩
  · rw [ClassFunction.induce_apply_one, hk]; push_cast; ring
  · obtain ⟨d, hd, hdsq⟩ := θ.isIrreducible.exists_degree_sq_le_index (Z.subgroupOf H) hZcentral
    have hdpk : d = p ^ k := by
      have hcast : (d : ℂ) = ((p ^ k : ℕ) : ℂ) := by rw [← hd, hk]
      exact_mod_cast hcast
    rw [← hdpk, ← Subgroup.index_eq_card]; exact hdsq

open scoped Classical in
/-- **(6.2) core inequality** `|K:A| − 1 ≤ 2ψ(1)` (Frobenius case).

Combines the member-family degree-square bound `sMember_degreeSqReBound_of_not_coherent`
(`∑_{χ∈S₁} χ(1).re² ≤ 2ψ(1).re·χ₁(1).re`) with the real B2 identity `sum_re_sq_induce_kernelFilter_eq`
(`∑_{χ∈S(A)} χ(1).re² = |L:H|·(|H:A| − 1)`).  Since `S(A) ⊆ S₁`, the `S(A)`-sum is bounded by the
`S₁`-sum, and with `χ₁(1) = |W₁| = |L:H|` (cancelling the positive index `|L:H|`) this gives
`|H:A| − 1 ≤ 2ψ(1)`.  This is the (6.2) bound `2ψ(1) ≥ |K:A| − 1` (with `K = H`); composing with the
θ-bound `ψ(1) ≤ |L:C|√|C:D|` yields the full (6.2) `2|L:C|√|C:D| ≥ |K:A| − 1`. -/
theorem sMember_index_le_two_psi (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite) (hSA_S1 : hyp.SsubFiltration A ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    hyp.sMember_degreeSqReBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hB2 := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := A)
  set SA := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) with hSAdef
  -- the `S(A)` Finset is contained in the enumerated `S₁`-range Finset
  have hsub : SA ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    exact hSA_S1 (by rw [hyp.mem_SsubFiltration]; exact ⟨θ, hne, hker, rfl⟩)
  have hchain : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) ≤
      2 * (ψ 1).re * (χ₁ 1).re := by
    rw [← hB2]
    calc ∑ χ ∈ SA, ((χ 1).re) ^ 2
        ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
          sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
      _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound
  have hχ₁re : (χ₁ 1).re = (H.index : ℝ) := by
    rw [hχ₁deg, Complex.natCast_re, hyp.index_H_eq_card_W1]
  rw [hχ₁re] at hchain
  have hidx_pos : (0 : ℝ) < (H.index : ℝ) := by
    rw [hyp.index_H_eq_card_W1]; exact_mod_cast Nat.card_pos
  have key : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) ≤
      (H.index : ℝ) * (2 * (ψ 1).re) := by
    calc (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
        ≤ 2 * (ψ 1).re * (H.index : ℝ) := hchain
      _ = (H.index : ℝ) * (2 * (ψ 1).re) := by ring
  exact le_of_mul_le_mul_left key hidx_pos

open scoped Classical in
/-- **(6.8.3) X-sum break bound.**  The (5.6)/B1 bound applied to the breaking coherent set `S₁ ⊇ X`:
`∑_{χ∈X} χ(1)² ≤ 2ψ(1)·χ₁(1)`.  Since `X ⊆ S₁` and `S₁` enumerates as a member family bounded by
`sMember_degreeSqReBound_of_not_coherent`, the `X`-sum `(H.index)·(|H| − |H:Z|)`
(`sum_re_sq_Xset_eq`) is dominated by the full family sum, which the (5.6) break bounds by
`2ψ(1)χ₁(1)`.  This is the `(6.8.3)` inequality with `χ₁ = η₁ ∈ Y` of degree `|W₁|`. -/
theorem xSum_le_two_psi (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} [Z.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite) (hXS1 : hyp.Xset Z ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ))
      ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    hyp.sMember_degreeSqReBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hXsum := hyp.sum_re_sq_Xset_eq hF (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hsub : Xdiff ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hXdiffdef, Finset.mem_sdiff] at hχ
    obtain ⟨hχbot, hχnotZ⟩ := hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
    obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hθ
    have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hne, rfl⟩
    have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', hne', hker', heq'⟩ := hmem
      exact hχnotZ (Finset.mem_image.mpr
        ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
    exact hXS1 ⟨hχS, hχnotSZ⟩
  rw [← hXsum]
  calc ∑ χ ∈ Xdiff, ((χ 1).re) ^ 2
      ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
        sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
    _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound

open scoped Classical in
/-- **(6.6) X-set nonemptiness from a nontrivial trace.**  If `Z ⊴ L` and `Z.subgroupOf H ≠ ⊥`,
then `X(Z) = S − S(Z)` is nonempty.  The (6.6) degree-square sum
`∑_{χ∈X(Z)} χ(1).re² = |L:H|·(|H| − |H:Z|)` (`sum_re_sq_Xset_eq`) is strictly positive because
`|H:Z| < |H|` whenever `Z.subgroupOf H` is nontrivial, and a positive sum of squares forces its
index Finset — hence `X(Z)` — to be nonempty.  (Note `Xset` is *antitone* in `Z` (`Xset_mono`), so
`X(Zc)` nonemptiness does **not** follow from `X(⁅H,H⁆)` nonemptiness; this degree-sum route is the
honest argument, and it avoids any Clifford-conjugacy reasoning about `Ind`.) -/
theorem Xset_nonempty_of_subgroupOf_ne_bot (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} [Z.Normal] (hZbot : Z.subgroupOf H ≠ ⊥) :
    (hyp.Xset Z).Nonempty := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hXsum := hyp.sum_re_sq_Xset_eq hF (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  -- `|H:Z| < |H|`, since `Z.subgroupOf H` is nontrivial
  have hlt : Nat.card (↥H ⧸ Z.subgroupOf H) < Nat.card ↥H := by
    have h2 : 1 < Nat.card ↥(Z.subgroupOf H) := (Z.subgroupOf H).one_lt_card_iff_ne_bot.mpr hZbot
    have hcard : Nat.card ↥H
        = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
    calc Nat.card (↥H ⧸ Z.subgroupOf H)
        < Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
          lt_mul_of_one_lt_right Nat.card_pos h2
      _ = Nat.card ↥H := hcard.symm
  -- the degree-square sum is strictly positive
  have hidxpos : 0 < H.index := by rw [hyp.index_H_eq_card_W1]; exact Nat.card_pos
  have hpos : (0 : ℝ) < (H.index : ℝ) *
      ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
    refine mul_pos (by exact_mod_cast hidxpos) ?_
    have : (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ) < (Nat.card ↥H : ℝ) := by exact_mod_cast hlt
    linarith
  rw [← hXsum] at hpos
  have hne : Xdiff.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨χ, hχ⟩ := hne
  refine ⟨χ, ?_⟩
  rw [hXdiffdef, Finset.mem_sdiff] at hχ
  obtain ⟨hχbot, hχnotZ⟩ := hχ
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
  obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
  have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
    rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
  have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
    intro hmem
    rw [hyp.mem_SsubFiltration] at hmem
    obtain ⟨θ', hne', hker', heq'⟩ := hmem
    exact hχnotZ (Finset.mem_image.mpr
      ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
  exact hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩

/-- **(6.6)/(6.8) X-set nonemptiness at the central commutator** (the redesign's `hXne`).
`X(Zc)` with `Zc = Z(H) ∩ H′` is nonempty whenever `H` is non-abelian (`commutator ↥H ≠ ⊥`),
since then `Zc ≠ ⊥` (`centralCommutator_ne_bot`), hence `Zc.subgroupOf H ≠ ⊥` (`Zc ≤ H`). -/
theorem Xset_centralCommutator_nonempty (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    (hyp.Xset hyp.centralCommutator).Nonempty := by
  haveI := hyp.centralCommutator_normal
  refine hyp.Xset_nonempty_of_subgroupOf_ne_bot hF ?_
  intro hbot
  apply hyp.centralCommutator_ne_bot hHnonab
  rw [eq_bot_iff]
  intro z hz
  have hzH : z ∈ H := hyp.centralCommutator_le hz
  have hmem : (⟨z, hzH⟩ : ↥H) ∈ hyp.centralCommutator.subgroupOf H :=
    (Subgroup.mem_subgroupOf).mpr hz
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

/-- **(6.8.3) extension, case (A): non-coherence of `S` is impossible.**
If `X ∪ Y` (with `X = S − S(Z)`, `Z = Z(H)∩H′` central) is coherent but `S` is not, the
break-pair `{ψ, ψ̄}` (`exists_coherentBreakPair`) gives a coherent `S₁ ⊇ X∪Y` whose extension by
`{ψ,ψ̄}` fails; the (5.6)/B1 bound (`xSum_le_two_psi`) then forces
`|W₁|·|H:Z|·(|Z|−1) = ∑_X χ(1)² ≤ 2ψ(1)·η₁(1) = 2|W₁|²d` with `d = θ(1)`, `ψ = Ind θ`.  Combined
with Cor 2.30 `d² ≤ |H:Z|` (central `Z`) and the FPF bound `|Z|−1 ≥ 2|W₁|`
(`centralCommutator_card_subgroupOf_lower`), the arithmetic core
`false_of_centralCommutator_break_arith` yields a contradiction.  This is the heart of
Peterfalvi (6.8.3) — the step the old `Xset ⁅H,H⁆ ∪ Yset = S` shortcut elided. -/
theorem false_of_coherentXunionYset_of_not_coherentS (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    (hXYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) : False := by
  classical
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  -- break pair on `Sa = X ∪ Y`, `Sb = S`
  have hSaSb : hyp.Xset hyp.centralCommutator ∪ hyp.Yset ⊆ hyp.S := by
    rintro φ (hX | hY)
    · exact hyp.Xset_subset_S hX
    · exact hyp.Yset_subset_S hY
  have hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset) := by
    intro φ hφ
    rcases hφ with hX | hY
    · exact Or.inl (hyp.Xset_closedUnderConjugate_unconditional hyp.centralCommutator hX)
    · exact Or.inr (hyp.SsubFiltration_closedUnderConjugate ⁅H, H⁆ hY)
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁Sb, hψSb, hψnS₁, hψcnS₁, hS₁cohN, hncN⟩ :=
    exists_coherentBreakPair hyp.tau hSaSb hyp.S_finite hyp.S_closedUnderConjugate
      (hyp.S_hasNoRealCharacters hF)
      (fun χ hχ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχ)
      hSaconj hXYcoh hncoh
  -- anchor `η ∈ Y` of degree `|W₁|`
  obtain ⟨η, hηY⟩ := hyp.Yset_nonempty
  have hηS₁ : η ∈ S₁ := hSaS₁ (Or.inr hηY)
  have hηdeg : η 1 = (Nat.card hyp.W1 : ℂ) := by
    obtain ⟨χ, -, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hηY
    exact hyp.induce_apply_one_eq_card_W1_of_degree_one _
      (OddOrder.RepresentationTheory.linearIrreducibleCharacter_apply_one χ)
  -- `ψ ∈ S` irreducible, `ψ = Ind θ`
  have hψS : ψ ∈ hyp.S := hψSb
  have hψirr : IsIrreducibleCharacter ψ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS
  rw [hyp.S_eq, Set.mem_setOf_eq] at hψS
  obtain ⟨θ, hθne, hψeq⟩ := hψS
  obtain ⟨d, hdpos, hθd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hdsq : d ^ 2 ≤ Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := by
    obtain ⟨d', hθd', hd'sq⟩ := θ.isIrreducible.exists_degree_sq_le_index
      (hyp.centralCommutator.subgroupOf H) hyp.centralCommutator_subgroupOf_le_center
    have hdd' : d = d' := by
      have hcast : (d : ℂ) = (d' : ℂ) := by rw [← hθd, hθd']
      exact_mod_cast hcast
    rw [hdd', ← Subgroup.index_eq_card]; exact hd'sq
  -- the (5.6) X-sum bound
  have hxb := hyp.xSum_le_two_psi hF (Z := hyp.centralCommutator) hS₁Sb hS₁conj
    (hyp.S_finite.subset hS₁Sb) (fun φ hφ => hSaS₁ (Or.inl hφ)) hS₁cohN.some
    hηS₁ hηdeg hψSb hψirr hψnS₁ hψcnS₁ hncN
  have hψre : (ψ 1).re = (H.index : ℝ) * (d : ℝ) := by
    rw [hψeq, ClassFunction.induce_apply_one, hθd]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hηre : (η 1).re = (Nat.card hyp.W1 : ℝ) := by rw [hηdeg, Complex.natCast_re]
  rw [hψre, hηre] at hxb
  -- cast the real inequality to ℕ
  have hZle : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hxbN : H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
      ≤ 2 * (H.index * d) * Nat.card hyp.W1 := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast [Nat.cast_sub hZle]
    nlinarith [hxb]
  rw [hyp.index_mul_card_sub_factor (Z := hyp.centralCommutator), hyp.index_H_eq_card_W1] at hxbN
  -- discharge the arithmetic core
  refine false_of_centralCommutator_break_arith (w1 := Nat.card hyp.W1) (d := d)
    (hZ := Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
    (cZ := Nat.card ↥(hyp.centralCommutator.subgroupOf H))
    Nat.card_pos hdpos hdsq ?_ ?_ ?_
  · -- `2 ≤ |H:Z|`
    have hZcnotle : ¬ H ≤ hyp.centralCommutator := by
      intro h
      exact (ne_of_lt hcommlt)
        (le_antisymm (Subgroup.commutator_le_left H H)
          (le_trans h hyp.centralCommutator_le_commutator))
    have hne : hyp.centralCommutator.subgroupOf H ≠ ⊤ := fun heq =>
      hZcnotle (Subgroup.subgroupOf_eq_top.mp heq)
    have hcard1 : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≠ 1 := by
      rw [← Subgroup.index_eq_card]; exact mt Subgroup.index_eq_one.mp hne
    have hcardpos : 0 < Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := Nat.card_pos
    omega
  · -- `2|W₁| ≤ |Z| − 1`
    have he := hyp.centralCommutator_card_subgroupOf_lower hF hHnonab
    omega
  · -- the break inequality, reassociated
    calc Nat.card hyp.W1 * Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
            * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)
        = Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
            * (Nat.card hyp.W1 * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)) := by ring
      _ ≤ 2 * (Nat.card hyp.W1 * d) * Nat.card hyp.W1 := hxbN
      _ = 2 * Nat.card hyp.W1 ^ 2 * d := by ring

/-- **(6.2) θ-bound for an induced member `ψ = Ind_H^L θ`.**

For `θ ∈ Irr H` and a section `N ◁ C` with `N ≤ D ≤ C ≤ H`, `θ` trivial on `N` (after restriction
to `C`) and `D ⧸ N` central in `C ⧸ N`, the degree of the induced character `ψ = Ind_H^L θ` is
bounded by `ψ(1) = |L:H|·θ(1) ≤ |L:H|·|H:C|·√|C:D|`, combining `induce_apply_one`
(`ψ(1) = |L:H|·θ(1)`) with the §6 `θ`-bound `theta_degree_le_index_mul_sqrt_index`
(`θ(1) ≤ |H:C|·√|C:D|`).  This is the (6.2) step `ψ(1) ≤ |L:C|·√|C:D|`. -/
theorem psi_degree_le_of_source (hyp : SibleyDadeHypothesis G L H)
    (θ : IrreducibleCharacter ↥H) (C : Subgroup ↥H) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] {N : Subgroup ↥C} [N.Normal] (D : Subgroup ↥C) (hND : N ≤ D)
    (hθN : (↑N : Set ↥C) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict C (θ : ClassFunction ↥H ℂ)))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥C ⧸ N)) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re ≤
      (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hind : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re
      = (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hind]
  have hθbound := theta_degree_le_index_mul_sqrt_index (K := ↥H) θ C D hND hθN hcentral
  calc (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re
      ≤ (H.index : ℝ) * ((C.index : ℝ) * Real.sqrt (D.index : ℝ)) :=
        mul_le_mul_of_nonneg_left hθbound (Nat.cast_nonneg _)
    _ = (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

open scoped Classical in
/-- **(6.2) first-obstruction + core wiring** `|K:A| − 1 ≤ 2ψ(1)`.

From `S(A)` coherent and `S(B)` not coherent (with `S(A) ⊆ S(B)`), the first-obstruction
`exists_coherentBreakPair` produces a breaking pair `{ψ, ψ̄}` with `ψ ∈ S(B)` (`ψ, ψ̄ ∉ S₁`), and the
(6.2) core `sMember_index_le_two_psi` — with the degree-`|W₁|` anchor `χ₁ ∈ S(A) ⊆ S₁`
(`exists_mem_SsubFiltration_degree_W1`, valid since `H/(A.subgroupOf H)` has a proper commutator
subgroup) — gives `|H:A| − 1 ≤ 2ψ(1)`.  The structural inputs (`S(B)` finite / conjugation-closed /
real-free / irreducible, `S(A)` conjugation-closed) come from the landed `SsubFiltration_*`
helpers. -/
theorem six_two_index_bound (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ ψ, ψ ∈ hyp.SsubFiltration B ∧
      (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨S₁, ψ, hS₁conj, hAS₁, hS₁B, hψB, hψnotS1, hψcnotS1, hS₁coh, hncoh⟩ :=
    exists_coherentBreakPair hyp.tau hAB (hyp.SsubFiltration_finite B)
      (hyp.SsubFiltration_closedUnderConjugate B) (hyp.SsubFiltration_hasNoRealCharacters hF B)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF
        (hyp.SsubFiltration_subset_S hφ))
      (hyp.SsubFiltration_closedUnderConjugate A) hSAcoh hSBncoh
  obtain ⟨χ₁, hχ₁SA, hχ₁deg⟩ := hyp.exists_mem_SsubFiltration_degree_W1 hAcomm
  have hψS : ψ ∈ hyp.S := hyp.SsubFiltration_subset_S hψB
  exact ⟨ψ, hψB, hyp.sMember_index_le_two_psi hF
    (hS₁B.trans hyp.SsubFiltration_subset_S) hS₁conj
    ((hyp.SsubFiltration_finite B).subset hS₁B) hAS₁ hS₁coh.some
    (hAS₁ hχ₁SA) hχ₁deg hψS (hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS)
    hψnotS1 hψcnotS1 hncoh⟩

/-- **Peterfalvi (6.2)** (Frobenius case, `K = H`).

Under the (6.2) section hypotheses — `B ⊆ D ⊆ C ⊆ H` with `D ⧸ B` central in `C ⧸ B` (here `B`
appears as `N = (B.subgroupOf H).subgroupOf C`), `S(A)` coherent, `S(B)` not — the index bound
`2|L:C|·√|C:D| ≥ |K:A| − 1` holds (with `K = H`, so `|L:C| = |L:H|·|H:C|` and `|C:D| = D.index`).

Proof: `six_two_index_bound` gives a breaking pair `ψ ∈ S(B)` with `|H:A| − 1 ≤ 2ψ(1)`; writing
`ψ = Ind_H^L θ` with `θ` trivial on `B` (`ψ ∈ S(B)`), `characterKernel_restrict_subgroupOf`
discharges the θ-bound's kernel hypothesis, and `psi_degree_le_of_source` gives
`ψ(1) ≤ |L:H|·|H:C|·√|C:D|`. -/
theorem six_two (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal] [B.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (C : Subgroup ↥H) [Fintype ↥C] [Invertible (Nat.card ↥C : ℂ)] (D : Subgroup ↥C)
    (hND : ((B.subgroupOf H).subgroupOf C) ≤ D)
    (hcentral : D.map (QuotientGroup.mk' ((B.subgroupOf H).subgroupOf C)) ≤
      Subgroup.center (↥C ⧸ (B.subgroupOf H).subgroupOf C))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤
      2 * (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨ψ, hψB, hψbound⟩ := hyp.six_two_index_bound hF hAB hAcomm hSAcoh hSBncoh
  rw [hyp.mem_SsubFiltration] at hψB
  obtain ⟨θ, _hθne, hθkerB, hψeq⟩ := hψB
  have hθN := characterKernel_restrict_subgroupOf C hθkerB
  have hψdeg := hyp.psi_degree_le_of_source θ C D hND hθN hcentral
  rw [hψeq] at hψbound
  calc (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re := hψbound
    _ ≤ 2 * ((H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ)) := by linarith [hψdeg]
    _ = 2 * (H.index : ℝ) * (C.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

/-- **(6.2) θ-bound for an induced member, central (`C = H`) case.**

When the section is `N ◁ D ≤ H` with `θ` trivial on `N` and `D ⧸ N` central in `H ⧸ N`, the b-half
`degree_sq_le_index_of_central_quotient` gives `θ(1)² ≤ |H:D|` directly (no Clifford restriction),
so `ψ = Ind_H^L θ` has `ψ(1) = |L:H|·θ(1) ≤ |L:H|·√|H:D|`.  This is the form (6.3) consumes (it
applies (6.2) with `C = H`). -/
theorem psi_degree_le_of_source_central (hyp : SibleyDadeHypothesis G L H)
    (θ : IrreducibleCharacter ↥H) {N : Subgroup ↥H} [N.Normal] (D : Subgroup ↥H) (hND : N ≤ D)
    (hθN : (↑N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥H ⧸ N)) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re ≤
      (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨d, hd1, hd2⟩ :=
    degree_sq_le_index_of_central_quotient N θ D hND hθN hcentral
  have hind : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re
      = (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hind, hd1, Complex.natCast_re]
  exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (by exact_mod_cast hd2))
    (Nat.cast_nonneg _)

/-- **Peterfalvi (6.2), central case `C = H`** (the form consumed by (6.3)).

With the section `B ⊆ D ≤ H` (`B` as `N = B.subgroupOf H`), `D/B` central in `H/B`, `S(A)`
coherent, `S(B)` not: `|K:A| − 1 ≤ 2|L:H|·√|H:D|`.  Specializes `six_two` to `C = H`, where the
θ-bound is the direct b-half (`psi_degree_le_of_source_central`), so the source `θ` of the breaking
pair `ψ ∈ S(B)` is trivial on `N = B.subgroupOf H` (no restriction step needed). -/
theorem six_two_central (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal] [B.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (D : Subgroup ↥H) (hND : B.subgroupOf H ≤ D)
    (hcentral : D.map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  letI : H.Normal := hyp.H_normal
  obtain ⟨ψ, hψB, hψbound⟩ := hyp.six_two_index_bound hF hAB hAcomm hSAcoh hSBncoh
  rw [hyp.mem_SsubFiltration] at hψB
  obtain ⟨θ, _hθne, hθkerB, hψeq⟩ := hψB
  have hψdeg := hyp.psi_degree_le_of_source_central θ D hND hθkerB hcentral
  rw [hψeq] at hψbound
  calc (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re := hψbound
    _ ≤ 2 * ((H.index : ℝ) * Real.sqrt (D.index : ℝ)) := by linarith [hψdeg]
    _ = 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

/-- **(6.3) per-step index bound.**

The per-step of Peterfalvi (6.3): for a section `B ⊆ A ⊆ H₁` with `A/B` central in `H/B`, `S(A)`
coherent and `S(B)` not, the (6.2) central bound `six_two_central` (`|H:A| − 1 ≤ 2|L:H|√|H:A|`)
combines with the arithmetic core `six_three_HH1_le` to give `|H:H₁| ≤ 4|L:K|² + 1` (`K = H`).
The minimal-`A` / maximal-`B` induction of (6.3) repeatedly applies this step. -/
theorem six_three_index_bound (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B H₁ : Subgroup ↥L} [A.Normal] [B.Normal] (hBA : B ≤ A) (hAH₁ : A ≤ H₁)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (hcentral : (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
  letI : H.Normal := hyp.H_normal
  have hsixtwo := hyp.six_two_central hF (hyp.SsubFiltration_antitone hBA) hAcomm
    (A.subgroupOf H) (Subgroup.subgroupOf_mono H hBA) hcentral hSAcoh hSBncoh
  have hHH1le : Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ Nat.card (↥H ⧸ A.subgroupOf H) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono H hAH₁))
  refine six_three_HH1_le (LK := H.index) (KH := 1) (HA := Nat.card (↥H ⧸ A.subgroupOf H))
    (HH1 := Nat.card (↥H ⧸ H₁.subgroupOf H)) (by norm_num) hHH1le ?_
  simpa using hsixtwo

/-- **`hAcomm` from nilpotency of `H`.**

In the Sibley setup `H` is nilpotent, so for a normal `A ⊊ H` the quotient `H/A` is a nontrivial
nilpotent (hence solvable) group, whence its commutator subgroup is proper: `[H/A, H/A] ≠ ⊤`.  This
supplies the `hAcomm` hypothesis of `six_two_index_bound` / `six_three_index_bound` (which need a
degree-`|W₁|` anchor in `S(A)`). -/
theorem commutator_subgroupOf_quotient_ne_top (hyp : SibleyDadeHypothesis G L H)
    {A : Subgroup ↥L} [A.Normal] (hAH : A < H) :
    _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤ := by
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : (A.subgroupOf H).Normal := (‹A.Normal›).subgroupOf H
  haveI : Nontrivial (↥H ⧸ A.subgroupOf H) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hAH.ne (le_antisymm hAH.le htop)
  exact (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H ⧸ A.subgroupOf H)).ne

/-- **Peterfalvi (6.3)** (Frobenius case `K = H`).

With `M ≤ H₁ ⊊ H` normal subgroups of `L`, `S(H₁)` coherent and `|H:H₁| > 4|L:H|² + 1`, the set
`S(M)` is coherent.

Minimal-`A` induction (Peterfalvi's argument): pick a normal `A ∈ [M, H₁]` with `S(A)` coherent that
is minimal for `⊆` (exists since `H₁` qualifies).  If `A ≠ M` then `M < A`; take a maximal normal
`B` with `M ≤ B ⊊ A` (`exists_maximal_normal_between`).  Then `A/B ⊆ Z(H/B)`
(`normal_central_of_maximal_normal_below`, using `H` nilpotent), and `S(B)` is *not* coherent (else
`B ∈ [M, H₁]` would beat the minimality of `A`).  So `six_three_index_bound` gives
`|H:H₁| ≤ 4|L:H|² + 1`, contradicting the hypothesis.  Hence `A = M` and `S(M) = S(A)` is
coherent. -/
theorem six_three (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {M H₁ : Subgroup ↥L} [M.Normal] [H₁.Normal] (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration H₁)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hbound : 4 * H.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration M)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : Finite (Subgroup ↥L) := Finite.of_injective (fun K : Subgroup ↥L => (K : Set ↥L))
    (fun _ _ h => SetLike.coe_injective h)
  set s : Set (Subgroup ↥L) := {A | A.Normal ∧ M ≤ A ∧ A ≤ H₁ ∧
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))} with hs_def
  have hH₁s : H₁ ∈ s := by
    simp only [hs_def, Set.mem_setOf_eq]; exact ⟨‹H₁.Normal›, hMH₁, le_refl _, hcoh⟩
  obtain ⟨A, hAmem, hAmin⟩ :=
    Set.Finite.exists_minimalFor (id : Subgroup ↥L → Subgroup ↥L) s (Set.toFinite _) ⟨H₁, hH₁s⟩
  simp only [hs_def, Set.mem_setOf_eq] at hAmem
  obtain ⟨hAnorm, hMA, hAH₁, hAcoh⟩ := hAmem
  haveI : A.Normal := hAnorm
  have hAeqM : A = M := by
    by_contra hne
    have hMltA : M < A := lt_of_le_of_ne hMA (Ne.symm hne)
    obtain ⟨B, hBnorm, hMB, hBltA, hBmaxl⟩ := exists_maximal_normal_between hMltA
    haveI : B.Normal := hBnorm
    have hAltH : A < H := lt_of_le_of_lt hAH₁ hH₁H
    have hAcomm := hyp.commutator_subgroupOf_quotient_ne_top hAltH
    have hcentral := normal_central_of_maximal_normal_below (H := H) (A := A) (B := B)
      ‹H.Normal› hAltH.le hBltA hBmaxl
    have hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
      intro hBcoh
      have hBs : B ∈ s := by
        simp only [hs_def, Set.mem_setOf_eq]
        exact ⟨hBnorm, hMB, hBltA.le.trans hAH₁, hBcoh⟩
      exact lt_irrefl _ (hBltA.trans_le (hAmin hBs hBltA.le))
    have hbnd := hyp.six_three_index_bound hF hBltA.le hAH₁ hAcomm hcentral hAcoh hSBncoh
    omega
  rw [← hAeqM]
  exact hAcoh

/-- **Peterfalvi (6.5) consequence (Frobenius case): `H` is a `p`-group.**

If the full set `S` is *not* coherent, then `H` is a `p`-group for some prime `p`.  Apply `six_three`
with `M = ⊥`, `H₁ = ⁅H,H⁆`: `S(⁅H,H⁆) = Y` is coherent (`coherentYset`), `⊥ ≤ ⁅H,H⁆` and `⁅H,H⁆ ⊊ H`
(`H` nilpotent nontrivial ⟹ not perfect), so if `|H:⁅H,H⁆| > 4|L:H|²+1` then `S(⊥) = S` would be
coherent — contradiction.  Hence `|Abelianization H| = |H:⁅H,H⁆| ≤ 4|W₁|²+1`
(`commutator_subgroupOf_self`, `index_H_eq_card_W1`), and as everything has odd order
`isPGroup_of_isFrobeniusGroup_of_card_le` produces the prime.  This is the (6.5)/(6.6) reduction
"`H` is a `p`-group" that feeds the (6.8) capstone. -/
theorem isPGroup_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hSncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥H := by
  letI : H.Normal := hyp.H_normal
  letI : Group.IsNilpotent ↥H := hyp.H_nilpotent
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  -- `⁅H,H⁆ ⊊ H` from nilpotency (nontrivial nilpotent is not perfect)
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  -- the index bound, by the contrapositive of `six_three`
  have hidx : Nat.card (↥H ⧸ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have hYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration ⁅H, H⁆)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := ⟨hyp.coherentYset⟩
    have hMcoh := hyp.six_three hF (M := ⊥) (H₁ := ⁅H, H⁆) bot_le hcommlt hYcoh hgt
    rw [hyp.SsubFiltration_bot] at hMcoh
    exact hSncoh hMcoh
  -- convert the index bound to the abelianization-card bound
  have hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card hyp.W1 ^ 2 + 1 := by
    rw [commutator_subgroupOf_self, hyp.index_H_eq_card_W1] at hidx
    exact hidx
  -- odd orders
  have hLodd : Odd (Nat.card ↥L) := hyp.card_L_odd
  have hHodd : Odd (Nat.card (Abelianization ↥H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hLodd H.card_subgroup_dvd_card)
      (Subgroup.card_quotient_dvd_card (_root_.commutator ↥H))
  have hW1odd : Odd (Nat.card hyp.W1) := Odd.of_dvd_nat hLodd hyp.W1.card_subgroup_dvd_card
  exact isPGroup_of_isFrobeniusGroup_of_card_le hF hHodd hW1odd hbound

/-- **(T8 leaf 8) `2 ≤ |S₀|`**, from the abstract input `X ⊆ Irr L`.

If `X` is nonempty, its base block `S₀` (minimal-degree members) contains a minimal-degree `χ`
together with its conjugate `χ̄ ≠ χ` (`Xset_hasNoRealCharacters_of_irreducible_X`,
`xBaseBlock_closedUnderConjugate_of_irreducible_X`), so `2 ≤ |S₀|`. -/
theorem two_le_xBaseBlock_ncard_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard := by
  have hXfin := hyp.xSet_finite_of_irreducible_X hX
  obtain ⟨χ, hχX, hχmin⟩ := Set.exists_min_image (hyp.Xset Z)
    (fun ψ => (OddOrder.Peterfalvi.S03.characterDegree ψ).re) hXfin hXne
  have hχS₀ : χ ∈ hyp.xBaseBlock Z := ⟨hχX, hχmin⟩
  have hconjS₀ : χ.conj ∈ hyp.xBaseBlock Z :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX hχS₀
  have hne : χ.conj ≠ χ := hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX hχX
  have hS₀fin : (hyp.xBaseBlock Z).Finite := hXfin.subset (hyp.xBaseBlock_subset Z)
  have h1 : 1 < (hyp.xBaseBlock Z).ncard :=
    (Set.one_lt_ncard hS₀fin).mpr ⟨χ.conj, hconjS₀, χ, hχS₀, hne⟩
  omega

/-- **(T8 leaf 8) `2 ≤ |S₀|`** (Frobenius case). -/
theorem two_le_xBaseBlock_ncard (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard :=
  hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

/-- **(T8 leaf 9) base coherence `IsCoherent τ S₀`**, from the abstract input
`X ⊆ Irr L`.

The minimal-degree base block `S₀ = xBaseBlock Z` is coherent for the real Dade map `tau`.  It is a
finite, equal-degree family of `≥ 2` irreducible characters of `L`
(`exists_finEnum_irreducible`, `xBaseBlock_degree_re_eq` with the integer degrees
`irreducibleCharacter_apply_one_eq_pos_natCast`, `two_le_xBaseBlock_ncard_of_irreducible_X`) whose
pairwise differences `χⱼ − χ₀` vanish off `H^# = sharpImage H`
(`sMember_diffSupport_of_charValue_eq`), so the §7 base engine `coherentEqualDegree_fromDade`
((6.6) base case, via (1.1)+(1.4)) applies with `A = H^#` — matching
`tau = dadeIntegralCharacterMap hyp.dade …`.

`noncomputable def` (not `theorem`): `IsCoherent` carries the isometric extension map as data
(it lives in `Type`, not `Prop`), exactly like `sibleySetup_is_coherent`/`CoherenceTarget`. -/
noncomputable def xBaseBlock_isCoherent_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  -- Enumerate the finite irreducible base block `S₀` as `χ : Fin k → Irr L`.  The conclusion
  -- `IsCoherent` is `Type`-valued (carries the extension map), so the enumeration data must be
  -- extracted with `choose` (via choice), not `obtain` (which would large-eliminate a `Prop ∃`).
  have hS₀fin : (hyp.xBaseBlock Z).Finite :=
    (hyp.xSet_finite_of_irreducible_X hX).subset (hyp.xBaseBlock_subset Z)
  have hS₀irr : ∀ φ ∈ hyp.xBaseBlock Z, IsIrreducibleCharacter φ :=
    fun φ hφ => hX φ (hyp.xBaseBlock_subset Z hφ)
  choose k χ hχinj hrange using exists_finEnum_irreducible hS₀fin hS₀irr
  have hmemS₀ : ∀ j, (χ j : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z :=
    fun j => hrange ▸ Set.mem_range_self j
  -- `2 ≤ k`: the coerced enumeration is injective, so `|S₀| = k`.
  have hcoeinj : Function.Injective (fun j => (χ j : ClassFunction ↥L ℂ)) := by
    intro i j hij
    exact hχinj (IrreducibleCharacter.ext hij)
  have hk2 : 2 ≤ k := by
    have hcard : (hyp.xBaseBlock Z).ncard = k := by
      rw [← hrange, Set.ncard_range_of_injective hcoeinj, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have h2 := hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH hX hXne
    omega
  haveI : NeZero k := ⟨by omega⟩
  -- `S₀ ⊆ S`.
  have hmemS : ∀ j, (χ j : ClassFunction ↥L ℂ) ∈ hyp.S :=
    fun j => (hyp.mem_Xset.mp (hyp.xBaseBlock_subset Z (hmemS₀ j))).1
  -- Equal degree: real parts equal (base block) and the degrees are positive integers.
  have hdeg : ∀ j, ((χ j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((χ 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    obtain ⟨dj, _, hdj⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ j)
    obtain ⟨d0, _, hd0⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (χ 0)
    have hre := hyp.xBaseBlock_degree_re_eq (hmemS₀ j) (hmemS₀ 0)
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def, hdj, hd0] at hre
    rw [hdj, hd0]
    have hdd : dj = d0 := by exact_mod_cast hre
    rw [hdd]
  -- Difference support: `χⱼ − χ₀` vanishes off `H^#` (equal degree, both supported on `H`).
  have hsuppdiff : ∀ j, (irreducibleCharacterDifference χ j).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    fun j => hyp.sMember_diffSupport_of_charValue_eq (hmemS j) (hmemS 0) (hdeg j)
  -- `1 ∉ A = H^#`.
  have h1notA : (1 : G) ∉ sharpImage H := by simp [sharpImage]
  -- Apply the §7 base engine; its `range χ = S₀` and Dade map `= hyp.tau`.
  have hcoh := OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hyp.hconj
    hk2 χ hχinj hdeg hsuppdiff h1notA
  rw [hrange] at hcoh
  exact hcoh

/-- **(T8 leaf 9) base coherence `IsCoherent τ S₀`** (Frobenius case). -/
noncomputable def xBaseBlock_isCoherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.xBaseBlock_isCoherent_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

/-- **(T8 leaf 9, case A) base coherence `IsCoherent τ S₀`.**

This specializes the abstract `X ⊆ Irr L` base-block engine using the case-A irreducibility bridge
`isIrreducibleCharacter_of_mem_Xset_caseA`. -/
noncomputable def xBaseBlock_isCoherent_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    (hXne : (hyp.Xset Z).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.xBaseBlock Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.xBaseBlock_isCoherent_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_caseA hZH hZcentral hZnorm hZfpf h)
    hXne


/-- **(T8.11b) X-pair step core facts.**

For a pair supplied by `exists_conjugatePairCover`, the first eight fields of
`XAdjoinStepInput` are forced by membership in `X` and the disjoint-prefix property: the new
character is non-real, has the required difference support, is orthonormal to its conjugate, and is
orthogonal to the accumulated prefix. -/
theorem xPair_stepCoreFacts_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N) :
    ¬ ClassFunction.IsReal (χs i : ClassFunction ↥L ℂ) ∧
      (((χs i : ClassFunction ↥L ℂ).conj - (χs i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ) (χs i : ClassFunction ↥L ℂ) = 1 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj
        (χs i : ClassFunction ↥L ℂ).conj = 1 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ)
        (χs i : ClassFunction ↥L ℂ).conj = 0 ∧
      ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj
        (χs i : ClassFunction ↥L ℂ) = 0 ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
        ClassFunction.inner (χs i : ClassFunction ↥L ℂ) x = 0) ∧
      (∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
        ClassFunction.inner (χs i : ClassFunction ↥L ℂ).conj x = 0) := by
  classical
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  rcases hyp.xMember_characterFacts_of_irreducible_X hZH hX hχX with
    ⟨hrealχ, hχχ, hχbarχbar, hχbarχ, hχχbar⟩
  have hdiffsuppχ := hyp.xMember_diffSupport_of_irreducible_X hX hχX
  have hortho := pairCover_orthogonal_to_prefix
    (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z) (pair := pair) (N := N)
    (i := i) (χ := χs i) hX (hyp.xBaseBlock_subset Z) hpairs
    (hpair0 i hi) (hpair1 i hi) (hdisj i hi) hi
  exact ⟨hrealχ, hdiffsuppχ, hχχ, hχbarχbar, hχχbar, hχbarχ, hortho.1, hortho.2⟩

/-- **(T8.11c) Accumulator member-family enumeration.**

Every prefix accumulator `pairUnion (xBaseBlock Z) pair i` in the X-chain is a finite family of
irreducible characters, closed under conjugation.  This packages the `Fin k` enumeration and the
member facts needed by the member-family half of `XAdjoinStepInput`.  The remaining
degree-ratio and lattice-generation fields stay separate. -/
theorem exists_pairUnion_memberFamily_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hi : i < N) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) =
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i ∧
      (∀ j : Fin k, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j : Fin k,
        ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) ∧
      (∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ).conj ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) ∧
      (∀ j : Fin k, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ j l : Fin k,
        ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
          (χmem l : ClassFunction ↥L ℂ) = if j = l then (1 : ℂ) else 0) := by
  classical
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ := fun φ hφ => hX φ (hS₁X hφ)
  have hS₁fin : S₁.Finite := (hyp.xSet_finite_of_irreducible_X hX).subset hS₁X
  have hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  have hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hS₀conj hbase))
    · have hjN : j < N := hji.trans hi
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ | hφ
        · right
          rw [hφ, hpair0 j hjN, hpair1 j hjN]
        · left
          rw [hφ, hpair1 j hjN, hpair0 j hjN]
          simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  obtain ⟨k, χmem, hχinj, hrange⟩ := exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    rw [← hrange]
    exact Set.mem_range_self j
  have hmembarS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁ :=
    fun j => hS₁conj (hmemS1 j)
  have hmemreal : ∀ j : Fin k, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ) := by
    intro j
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).1
  have hmemdiffsupp : ∀ j : Fin k,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    exact hyp.xMember_diffSupport_of_irreducible_X hX (hS₁X (hmemS1 j))
  have hmemconjortho : ∀ j : Fin k, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0 := by
    intro j
    rcases hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j)) with
      ⟨_, _, _, _, hχχbar⟩
    exact hχχbar
  have hmemortho : ∀ j l : Fin k,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem l : ClassFunction ↥L ℂ) = if j = l then (1 : ℂ) else 0 := by
    intro j l
    by_cases hjl : j = l
    · subst j
      simpa using irreducibleCharacter_inner_eq_ite (χmem l) (χmem l)
    · have hχne : χmem j ≠ χmem l := fun h => hjl (hχinj h)
      simpa [hjl, hχne] using irreducibleCharacter_inner_eq_ite (χmem j) (χmem l)
  exact ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1,
    hmemconjortho, hmemortho⟩

open scoped Classical in
/-- **(T8.11l) X-adjoin input from member-family degree ratios.**

Given a conjugate-pair cover step, an explicit finite member-family cover of the current prefix
`S₁ = pairUnion (xBaseBlock Z) pair i`, and degree-ratio data against a chosen anchor `χ₁`, this
assembles the full `XAdjoinStepInput` for adjoining `χᵢ`.  The theorem deliberately leaves the
arithmetical (6.6) payload as inputs: the member and new-character degree ratios, `deg i₁ = 1`, and
the strict inequality `2a < ∑ deg²`.  All non-arithmetical fields are discharged from the X-pair
cover, support bridges, virtual-character bridge, and the §7 anchor-generation lemma. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeRatios
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {deg : ι → ℕ} {i₁ : ι} {a : ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (ha1 : deg i₁ = 1)
    (hdeg_mem : ∀ j ∈ s,
      (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hDeg : 2 * (a : ℝ) < ∑ j ∈ s, ((deg j : ℝ)) ^ 2) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  have hmemX : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := by
    intro j hj
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp (hmemS1 j hj) with hbase | ⟨k, hki, hkpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs k (hki.trans hi) hkpair
  rcases hyp.xPair_stepCoreFacts_of_irreducible_X hZH hX hpair0 hpair1 hpairs hdisj hi with
    ⟨hrealχ, hdiffsuppχ, hχχ, hχbarχbar, hχχbar, hχbarχ, hχ_S1, hχbar_S1⟩
  have hmemdegdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ) - deg j •
          (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.xMember_scaledDiffSupports_of_degreeData hmemX hi₁ hdeg_mem
  have hdiffasuppχ : ((χs i : ClassFunction ↥L ℂ) - a •
        (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.xMember_scaledDiffSupport_of_degreeData hχX (hmemX i₁ hi₁) hdegχ
  have htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
      (hyp.dade.fullDadeIsometryData hyp.hconj)
      ((χs i : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G := by
    simpa [SibleyDadeHypothesis.tau] using hyp.scaledDiff_dadeImage_mem_ZIrr hdiffasuppχ
  have hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          {(χmem i₁ : ClassFunction ↥L ℂ)}) :=
    OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
      (L := ↥L) (S₁ := S₁)
      (A := OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      (χmem := fun j => (χmem j : ClassFunction ↥L ℂ)) (deg := deg) (i₁ := i₁)
      (by simpa [S₁] using hcover) hi₁ (by simpa [S₁] using hmemS1)
      (by simpa using hmemdegdiffsupp)
  exact
    { hrealχ := hrealχ
      hdiffsuppχ := hdiffsuppχ
      hχχ := hχχ
      hχbarχbar := hχbarχbar
      hχχbar := hχχbar
      hχbarχ := hχbarχ
      hχ_S1 := hχ_S1
      hχbar_S1 := hχbar_S1
      ι := ι
      s := s
      χmem := χmem
      deg := deg
      i₁ := i₁
      hi₁ := hi₁
      hmemreal := hmemreal
      hmemdiffsupp := hmemdiffsupp
      hmemdegdiffsupp := hmemdegdiffsupp
      hmemS1 := hmemS1
      hmembarS1 := hmembarS1
      hmemconjortho := hmemconjortho
      hmemortho := hmemortho
      a := a
      hdiffasuppχ := hdiffasuppχ
      htau1_memaχ := htau1_memaχ
      ha1 := ha1
      hDeg := hDeg
      hSgen := hSgen }

/-- **(T8 leaf 10 / T-A4) X-chain assembly from per-pair adjoining data.**

This is the Sibley/Xset wrapper around the abstract `xChainCoherent` fold.  It builds the
conjugate-pair cover of `X = hyp.Xset Z` over the minimal-degree base block
`S0 = hyp.xBaseBlock Z` (`exists_conjugatePairCover`), supplies the base coherence
`xBaseBlock_isCoherent_of_irreducible_X`, and leaves exactly the per-step (5.6)/(6.6) adjoining
payload as `hstep`.

The extra disjoint-prefix and degree-monotonicity facts exposed to `hstep` are produced by the pair
cover but are not consumed by `xChainCoherent` itself; they are the data needed to construct each
`XAdjoinStepInput` without re-enumerating `X`. -/
noncomputable def Xset_isCoherent_from_adjoinSteps_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstep : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)),
        XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hXfin : (hyp.Xset Z).Finite := hyp.xSet_finite_of_irreducible_X hX
  have hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
    hyp.Xset_closedUnderConjugate_of_irreducible_X hZH hX
  have hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
    hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX
  have hS0conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  choose e pair N hpairχ hsurj hpairs hcoverIdx hpair0Raw hpair1Raw hdisj hmono using
    exists_conjugatePairCover (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z)
      hXfin hXconj hXreal hX hS0conj
  let χ0 : IrreducibleCharacter ↥L := ⟨Classical.choose hXne, hX _ (Classical.choose_spec hXne)⟩
  let χs : ℕ → IrreducibleCharacter ↥L := fun i => if hi : i < N then hpairχ i hi else χ0
  have hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ) := by
    intro i hi
    rw [hpair0Raw i hi]
    simp [χs, hi]
  have hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj := by
    intro i hi
    rw [hpair1Raw i hi]
    simp [χs, hi]
  have hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
    intro φ hφ
    obtain ⟨i, hi⟩ := hsurj φ hφ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci
  exact xChainCoherent hyp.dade hyp.hconj pair N χs hpair0 hpair1
    (hyp.xBaseBlock_subset Z) hpairs hcover
    (hyp.xBaseBlock_isCoherent_of_irreducible_X hZH hX hXne)
    (fun i hi hcoh => hstep pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh)

/-- **(T8.10w) X-chain coherence engine, completeness-exposing variant.**  Identical to
`Xset_isCoherent_from_adjoinSteps_of_irreducible_X` but the per-step callback `hstep` additionally
receives the **Xset-cover completeness** witness
`hcover : ∀ φ ∈ X, φ ∈ xBaseBlock Z ∨ ∃ j < N, φ ∈ pairSet pair j`.  The base engine derives this
internally (from `exists_conjugatePairCover`) but does not expose it; the StepData producer needs it
to build the per-step `tailSet = X ∖ accumulator` and discharge `htail_le`/`hsum` (only well-behaved
when the conjugate-pair cover is complete — see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`
finding #6).  Additive: no existing signature changes. -/
noncomputable def Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstep : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      (∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
        ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
      ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
          (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)),
        XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hXfin : (hyp.Xset Z).Finite := hyp.xSet_finite_of_irreducible_X hX
  have hXconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) :=
    hyp.Xset_closedUnderConjugate_of_irreducible_X hZH hX
  have hXreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
    hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX
  have hS0conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  choose e pair N hpairχ hsurj hpairs hcoverIdx hpair0Raw hpair1Raw hdisj hmono using
    exists_conjugatePairCover (X := hyp.Xset Z) (S₀ := hyp.xBaseBlock Z)
      hXfin hXconj hXreal hX hS0conj
  let χ0 : IrreducibleCharacter ↥L := ⟨Classical.choose hXne, hX _ (Classical.choose_spec hXne)⟩
  let χs : ℕ → IrreducibleCharacter ↥L := fun i => if hi : i < N then hpairχ i hi else χ0
  have hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ) := by
    intro i hi
    rw [hpair0Raw i hi]
    simp [χs, hi]
  have hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj := by
    intro i hi
    rw [hpair1Raw i hi]
    simp [χs, hi]
  have hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
    intro φ hφ
    obtain ⟨i, hi⟩ := hsurj φ hφ
    have hci := hcoverIdx i
    rw [hi] at hci
    exact hci
  exact xChainCoherent hyp.dade hyp.hconj pair N χs hpair0 hpair1
    (hyp.xBaseBlock_subset Z) hpairs hcover
    (hyp.xBaseBlock_isCoherent_of_irreducible_X hZH hX hXne)
    (fun i hi hcoh => hstep pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi hcoh)

end SibleyDadeHypothesis

/-- **(T8.11m) normalized degree gap from an absolute degree bound.**

If the new character and the prefix member family have natural degree ratios against the same
anchor `χ₁`, then the absolute §6.6 inequality
`2 * χ(1) * χ₁(1) < ∑ χmem(j)(1)^2` is equivalent, after dividing by the positive square
`χ₁(1)^2`, to the normalized `XAdjoinStepInput.hDeg` inequality
`2 * a < ∑ deg(j)^2`. -/
theorem normalizedDegreeGap_of_realDegreeBound
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a : ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hAbs : 2 *
        ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 := by
  classical
  obtain ⟨d₁, hd₁pos, hχ₁one⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ₁
  have hd₁real_pos : 0 < (d₁ : ℝ) := by exact_mod_cast hd₁pos
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re =
        (a : ℝ) * (d₁ : ℝ) := by
    have h := congrArg Complex.re hχdeg
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hmemre : ∀ i ∈ s,
      (OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re =
        (deg i : ℝ) * (d₁ : ℝ) := by
    intro i hi
    have h := congrArg Complex.re (hmemdeg i hi)
    rw [hχ₁one] at h
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def, Complex.ofReal_mul] using h
  have hleft :
      2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
          (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) =
        (2 * (a : ℝ)) * (d₁ : ℝ) ^ 2 := by
    rw [hχre, hχ₁re]
    ring
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, (((deg i : ℝ) * (d₁ : ℝ)) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmemre i hi]
      _ = ∑ i ∈ s, ((deg i : ℝ) ^ 2 * (d₁ : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (∑ i ∈ s, ((deg i : ℝ)) ^ 2) * (d₁ : ℝ) ^ 2 := by
            rw [← Finset.sum_mul]
  rw [hleft, hright] at hAbs
  have hd₁sq_pos : 0 < (d₁ : ℝ) ^ 2 := sq_pos_of_pos hd₁real_pos
  nlinarith

/-- **(T8.11n) real absolute degree bound from natural prime-power data.**

This is the adapter from the pure §6.6 number-theoretic leaf in §7 to the real-valued
bound used by
`normalizedDegreeGap_of_realDegreeBound`: if natural degree values identify `χ(1)=dχ`,
`χ₁(1)=d₁`, and the member-family square sum is `D`, then the prime-power gap plus
square-divisibility `dχ^2 ∣ D` gives
`2 * χ(1).re * χ₁(1).re < ∑ χmem(j)(1).re^2`. -/
theorem realDegreeBound_of_natDegreeSumPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
        (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2 := by
  classical
  have hNat : 2 * (dχ * d₁) < D :=
    OddOrder.Peterfalvi.S07.two_mul_lt_of_sq_dvd_of_gap
      (OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_primePow_gap hp hpos₁ hq hdiv hlt)
      hdvd hDpos
  have hNatReal : 2 * ((dχ : ℝ) * (d₁ : ℝ)) < (D : ℝ) := by
    exact_mod_cast hNat
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re = (dχ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]
    norm_num
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hsumCast : (∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ)) = (D : ℝ) := by
    exact_mod_cast hDsum
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (D : ℝ) := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, ((dmem i : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [OddOrder.Peterfalvi.S03.characterDegree_def, hmemone i hi]
            norm_num
      _ = ∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            norm_num [pow_two]
      _ = (D : ℝ) := hsumCast
  rw [hχre, hχ₁re, hright]
  exact hNatReal

/-- **(T8.11n1) real absolute degree bound from common-index p-power data.**

This variant of `realDegreeBound_of_natDegreeSumPrimePowerGap` uses the actual §6.6
common-index data instead of asking the caller to name a quotient `q` with
`dχ = q * d₁`.  The strict gap comes from
`two_mul_lt_sq_of_commonIndex_primePower_gap`; square-divisibility then pushes it to
the prefix degree sum. -/
theorem realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * ((OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re *
        (OddOrder.Peterfalvi.S03.characterDegree (χ₁ : ClassFunction G ℂ)).re) <
      ∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2 := by
  classical
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hNat : 2 * (dχ * d₁) < D :=
    OddOrder.Peterfalvi.S07.two_mul_lt_of_sq_dvd_of_gap
      (OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_commonIndex_primePower_gap
        hp hidxpos hd₁ hdχ hθ₁ hθχ hlt)
      hdvd hDpos
  have hNatReal : 2 * ((dχ : ℝ) * (d₁ : ℝ)) < (D : ℝ) := by
    exact_mod_cast hNat
  have hχre :
      (OddOrder.Peterfalvi.S03.characterDegree (χ : ClassFunction G ℂ)).re = (dχ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχone]
    norm_num
  have hχ₁re :
      (OddOrder.Peterfalvi.S03.characterDegree
          (χ₁ : ClassFunction G ℂ)).re = (d₁ : ℝ) := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχ₁one]
    norm_num
  have hsumCast : (∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ)) = (D : ℝ) := by
    exact_mod_cast hDsum
  have hright :
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
        (D : ℝ) := by
    calc
      (∑ i ∈ s,
        ((OddOrder.Peterfalvi.S03.characterDegree (χmem i : ClassFunction G ℂ)).re) ^ 2) =
          ∑ i ∈ s, ((dmem i : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [OddOrder.Peterfalvi.S03.characterDegree_def, hmemone i hi]
            norm_num
      _ = ∑ i ∈ s, ((dmem i * dmem i : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            norm_num [pow_two]
      _ = (D : ℝ) := hsumCast
  rw [hχre, hχ₁re, hright]
  exact hNatReal

/-- **(T8.11o) normalized degree gap from natural prime-power data.**

Combines `realDegreeBound_of_natDegreeSumPrimePowerGap` with
`normalizedDegreeGap_of_realDegreeBound`, so a §6.6 caller with natural degree data and ratio data
can produce the `XAdjoinStepInput.hDeg` field directly. -/
theorem normalizedDegreeGap_of_natDegreeSumPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 :=
  normalizedDegreeGap_of_realDegreeBound hχdeg hmemdeg
    (realDegreeBound_of_natDegreeSumPrimePowerGap hχone hχ₁one hmemone hDsum
      hp hpos₁ hq hdiv hlt hdvd hDpos)

/-- **(T8.11r0) intrinsic degree-divisibility from common-index p-power data.**

`exists_pos_natDegreeRatio_of_dvd` consumes an intrinsic predicate over any natural witnesses for
`χ(1)` and `χ₁(1)`.  This lemma produces that predicate from the (6.6) degree-sort data: both
degrees have the same positive induced index `idx`, their residual factors are powers of the same
base `p`, and the sorted degrees satisfy `d₁ ≤ d`. -/
theorem natDegreeDvd_of_commonIndex_primePowerData
    {G : Type*} [Group G] {χ χ₁ : IrreducibleCharacter G}
    {p idx d d₁ θ θ₁ m n : ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hd : d = idx * θ) (hd₁ : d₁ = idx * θ₁)
    (hθ : θ = p ^ m) (hθ₁ : θ₁ = p ^ n) (hle : d₁ ≤ d) :
    ∀ e e₁ : ℕ, (χ : ClassFunction G ℂ) 1 = (e : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (e₁ : ℂ) → e₁ ∣ e := by
  intro e e₁ he he₁
  have hed : e = d := Nat.cast_injective (he.symm.trans hχone)
  have he₁d₁ : e₁ = d₁ := Nat.cast_injective (he₁.symm.trans hχ₁one)
  subst e
  subst e₁
  exact OddOrder.Peterfalvi.S07.mul_primePow_dvd_mul_primePow_of_le
    hp hidx hd₁ hd hθ₁ hθ hle

/-- **(T8.11o1) normalized degree gap from common-index p-power data.**

Combines `realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap` with
`normalizedDegreeGap_of_realDegreeBound`.  This is the consumer form used by the
common-index step constructors after the quotient `q` has been removed from their input data. -/
theorem normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap
    {G : Type*} [Group G]
    {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {deg : ι → ℕ} {a p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hχdeg : (χ : ClassFunction G ℂ) 1 =
      (a : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hmemdeg : ∀ i ∈ s,
      (χmem i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ₁ : ClassFunction G ℂ) 1)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 :=
  normalizedDegreeGap_of_realDegreeBound hχdeg hmemdeg
    (realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap hχone hχ₁one hmemone hDsum
      hp hlt hdχ hd₁ hθχ hθ₁ hdvd hDpos)

/-- **(T8.11r) degree-divisibility inputs from common-index p-power sorted degrees.**

This packages both divisibility predicates required by
`xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`: the anchor degree divides every
prefix member degree and the new character degree.  The hypotheses are the honest (6.6) data
behind those predicates — common induced index, p-power residual degrees, and sorted natural
degrees — rather than abstract divisibility assumptions. -/
theorem degreeDivisibilityInputs_of_commonIndex_primePowerData
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χ χ₁ : IrreducibleCharacter G} {χmem : ι → IrreducibleCharacter G}
    {p idx d₁ dχ θ₁ θχ m₁ mχ : ℕ}
    {dmem θmem mmem : ι → ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hχone : (χ : ClassFunction G ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction G ℂ) 1 = (dmem j : ℂ))
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j ∈ s, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j ∈ s, θmem j = p ^ mmem j)
    (hleχ : d₁ ≤ dχ) (hlemem : ∀ j ∈ s, d₁ ≤ dmem j) :
    (∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d) ∧
    (∀ d dAnchor : ℕ,
      (χ : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    exact natDegreeDvd_of_commonIndex_primePowerData hp hidx
      (hmemone j hj) hχ₁one (hdmem j hj) hd₁ (hθmem j hj) hθ₁ (hlemem j hj)
  · exact natDegreeDvd_of_commonIndex_primePowerData hp hidx
      hχone hχ₁one hdχ hd₁ hθχ hθ₁ hleχ


namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **(T8.11p) X-adjoin input from natural degree-gap data.**

This combines `xAdjoinStepInput_of_memberFamily_degreeRatios` with
`normalizedDegreeGap_of_natDegreeSumPrimePowerGap`.  A §6.6 caller that already has the finite
member-family data, degree-ratio equations, natural degree witnesses, and the prime-power /
square-divisibility gap can now produce the full `XAdjoinStepInput` without separately supplying
the normalized `hDeg` field. -/
noncomputable def xAdjoinStepInput_of_memberFamily_natDegreeGap
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {deg : ι → ℕ} {i₁ : ι} {a p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (ha1 : deg i₁ = 1)
    (hdeg_mem : ∀ j ∈ s,
      (χmem j : ClassFunction ↥L ℂ) 1 =
        (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) :=
  hyp.xAdjoinStepInput_of_memberFamily_degreeRatios hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho ha1 hdeg_mem hdegχ
    (normalizedDegreeGap_of_natDegreeSumPrimePowerGap hdegχ hdeg_mem
      hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos)

open scoped Classical in
/-- **(T8.11q) X-adjoin input from divisibility and natural degree-gap data.**

This is the same per-step constructor as `xAdjoinStepInput_of_memberFamily_natDegreeGap`,
but it derives the member-family ratios and the new-character ratio from natural degree
divisibility data.  A §6.6 caller can now provide the character-theoretic divisibility
hypotheses together with the prime-power/square-divisibility gap data, without naming the
ratio function `deg` or scalar `a` separately. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p d₁ dχ q m D : ℕ} {dmem : ι → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hdvd_mem : ∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hdvdχ : ∀ d dAnchor : ℕ,
      (χs i : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hpos₁ : 0 < d₁)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let hratioFamily :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatioFamily_of_dvd
      (G := ↥L) (χ := χmem) (s := s) (i₁ := i₁) hdvd_mem
  let deg : ι → ℕ := Classical.choose hratioFamily
  have ha1 : deg i₁ = 1 := (Classical.choose_spec hratioFamily).1
  have hdeg_mem : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 =
      (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 :=
    (Classical.choose_spec hratioFamily).2.2
  let hratioχ :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatio_of_dvd
      (G := ↥L) (χs i) (χmem i₁) hdvdχ
  let a : ℕ := Classical.choose hratioχ
  have hdegχ_char : OddOrder.Peterfalvi.S03.characterDegree (χs i : ClassFunction ↥L ℂ) =
      (a : ℂ) *
        OddOrder.Peterfalvi.S03.characterDegree (χmem i₁ : ClassFunction ↥L ℂ) :=
    (Classical.choose_spec hratioχ).2
  have hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := by
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hdegχ_char
  exact hyp.xAdjoinStepInput_of_memberFamily_natDegreeGap hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho ha1 hdeg_mem hdegχ
    hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos

open scoped Classical in
/-- **(T8.11r1) X-adjoin input from degree divisibility and common-index gap data.**

This is the quotient-free version of
`xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`: the normalized degree inequality is
derived from the common-index p-power factorizations of `d₁` and `dχ`, rather than from a named
quotient `q` with `dχ = q * d₁`. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeDivisibility_commonIndexNatGap
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι : Type} {s : Finset ι} {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p idx d₁ dχ θ₁ θχ m₁ mχ D : ℕ} {dmem : ι → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hdvd_mem : ∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hdvdχ : ∀ d dAnchor : ℕ,
      (χs i : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hdvd : dχ * dχ ∣ D) (hDpos : 0 < D) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  classical
  let hratioFamily :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatioFamily_of_dvd
      (G := ↥L) (χ := χmem) (s := s) (i₁ := i₁) hdvd_mem
  let deg : ι → ℕ := Classical.choose hratioFamily
  have ha1 : deg i₁ = 1 := (Classical.choose_spec hratioFamily).1
  have hdeg_mem : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 =
      (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 :=
    (Classical.choose_spec hratioFamily).2.2
  let hratioχ :=
    OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatio_of_dvd
      (G := ↥L) (χs i) (χmem i₁) hdvdχ
  let a : ℕ := Classical.choose hratioχ
  have hdegχ_char : OddOrder.Peterfalvi.S03.characterDegree (χs i : ClassFunction ↥L ℂ) =
      (a : ℂ) *
        OddOrder.Peterfalvi.S03.characterDegree (χmem i₁ : ClassFunction ↥L ℂ) :=
    (Classical.choose_spec hratioχ).2
  have hdegχ : (χs i : ClassFunction ↥L ℂ) 1 =
      (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := by
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hdegχ_char
  exact hyp.xAdjoinStepInput_of_memberFamily_degreeRatios hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho ha1 hdeg_mem hdegχ
    (normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap hdegχ hdeg_mem
      hχone hχ₁one hmemone hDsum hp hlt hdχ hd₁ hθχ hθ₁ hdvd hDpos)

open scoped Classical in
/-- **(T8.11r) X-adjoin input from degree divisibility and prime-power sum data.**

This is the same constructor as `xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`, but it
no longer asks the caller to provide the square-divisibility `dχ² ∣ D` as an opaque hypothesis.  The
hypothesis is derived internally from the (6.6) mmd L78-80 arithmetic chain: sorted common-index
p-power tail degrees, total-side p-power square divisibility, the additive head/tail identity, and
coprimality of the fixed induction index with the p-power factor. -/
noncomputable def xAdjoinStepInput_of_memberFamily_degreeDivisibility_primePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι κ : Type} {s : Finset ι} {tailSet : Finset κ}
    {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p idx d₁ dχ q qtot c total θχ mχ mq : ℕ}
    {dmem : ι → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hdvd_mem : ∀ j ∈ s, ∀ d dAnchor : ℕ,
      (χmem j : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hdvdχ : ∀ d dAnchor : ℕ,
      (χs i : ClassFunction ↥L ℂ) 1 = (d : ℂ) →
      (χmem i₁ : ClassFunction ↥L ℂ) 1 = (dAnchor : ℂ) → dAnchor ∣ d)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p)
    (hq : q = p ^ m) (hdiv : dχ = q * d₁) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hθχ : θχ = p ^ mχ)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : D + (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_D : idx * idx ∣ D)
    (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hcop : Nat.Coprime idx θχ := coprime_commonIndex_primePower hidx_p hθχ
  have hdvd : dχ * dχ ∣ D :=
    OddOrder.Peterfalvi.S07.sq_dvd_head_of_commonIndex_primePower_sums
      tailSet (by omega) hidxpos hθχ hθtail htail_le hsum hqtot hθsq_le_qtot htotal
      hidx_D hdχ hcop
  have hpos₁ : 0 < d₁ := natDegree_pos_of_irreducibleCharacter_apply_one_eq hχ₁one
  have hDpos : 0 < D := natDegreeSquareSum_pos_of_memberFamily hi₁ hmemone hDsum
  exact hyp.xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho hdvd_mem hdvdχ
    hχone hχ₁one hmemone hDsum hp hpos₁ hq hdiv hlt hdvd hDpos

open scoped Classical in
/-- **(T8.11t) X-adjoin input from common-index p-power degree data.**

This is the `primePowerSums` constructor with the two degree-divisibility predicate inputs
also derived internally from the (6.6) common-index p-power degree data.  The caller supplies the
anchor, new-character, and prefix-member factorizations through the same fixed index `idx`, sorted
natural-degree inequalities, and the tail square-sum divisibility data; no abstract `hdvd_mem`,
`hdvdχ`, or `dχ ^ 2 ∣ D` arithmetic black boxes remain at this interface. -/
noncomputable def xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {ι κ : Type} {s : Finset ι} {tailSet : Finset κ}
    {χmem : ι → IrreducibleCharacter ↥L}
    {i₁ : ι} {p idx d₁ dχ qtot c total θ₁ θχ m₁ mχ mq : ℕ}
    {dmem θmem mmem : ι → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hcover : ∀ x ∈ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i,
      ∃ j, j ∈ s ∧ (χmem j : ClassFunction ↥L ℂ) = x)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ j ∈ s, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ j ∈ s,
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hmemS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmembarS1 : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hmemconjortho : ∀ j ∈ s, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
      (χmem j : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ j ∈ s, ∀ l ∈ s,
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        if j = l then (1 : ℂ) else 0)
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j ∈ s, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hDsum : ∑ j ∈ s, dmem j * dmem j = D)
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j ∈ s, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j ∈ s, θmem j = p ^ mmem j)
    (hlemem : ∀ j ∈ s, d₁ ≤ dmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : D + (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  have hidxpos : 0 < idx := commonIndex_pos_of_natDegree_factor hχone hdχ
  have hdvds :=
    OddOrder.Peterfalvi.S08.degreeDivisibilityInputs_of_commonIndex_primePowerData
      (G := ↥L) (χ := χs i) (χ₁ := χmem i₁) (χmem := χmem) (s := s)
      (p := p) (idx := idx) (d₁ := d₁) (dχ := dχ)
      (θ₁ := θ₁) (θχ := θχ) (m₁ := m₁) (mχ := mχ)
      (dmem := dmem) (θmem := θmem) (mmem := mmem)
      (show 2 ≤ p by omega) hidxpos hχone hχ₁one hmemone hdχ hd₁ hdmem hθχ hθ₁
      hθmem (Nat.le_of_lt hlt) hlemem
  have hidx_D : idx * idx ∣ D :=
    OddOrder.Peterfalvi.S08.sq_dvd_natDegreeSquareSum_of_commonIndex hDsum hdmem
  have hcop : Nat.Coprime idx θχ := coprime_commonIndex_primePower hidx_p hθχ
  have hdvd : dχ * dχ ∣ D :=
    OddOrder.Peterfalvi.S07.sq_dvd_head_of_commonIndex_primePower_sums
      tailSet (by omega) hidxpos hθχ hθtail htail_le hsum hqtot hθsq_le_qtot htotal
      hidx_D hdχ hcop
  have hDpos : 0 < D := natDegreeSquareSum_pos_of_memberFamily hi₁ hmemone hDsum
  exact hyp.xAdjoinStepInput_of_memberFamily_degreeDivisibility_commonIndexNatGap hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover hi₁ hmemreal hmemdiffsupp
    hmemS1 hmembarS1 hmemconjortho hmemortho hdvds.1 hdvds.2
    hχone hχ₁one hmemone hDsum hp hlt hdχ hd₁ hθχ hθ₁ hdvd hDpos

open scoped Classical in
/-- **(T8.11u) X-adjoin input from a pairUnion enumeration and p-power degree data.**

This specializes `xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums` to the actual
running accumulator `pairUnion (xBaseBlock Z) pair i`.  A caller supplies an injective finite
enumeration of that accumulator; this adapter turns it into the member-family cover and all routine
X-member facts (non-real, conjugate support, conjugate membership, and orthonormality).  The
remaining inputs are the genuine (6.6) degree, p-power, sum, and coprimality data indexed by the
same enumeration. -/
noncomputable def xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {κ : Type} {tailSet : Finset κ}
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hχinj : Function.Injective χmem)
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    {i₁ : Fin k} {p idx d₁ dχ qtot c total θ₁ θχ m₁ mχ mq : ℕ}
    {dmem θmem mmem : Fin k → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hp : 3 ≤ p) (hlt : d₁ < dχ)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j, θmem j = p ^ mmem j)
    (hlemem : ∀ j, d₁ ≤ dmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : (∑ j : Fin k, dmem j * dmem j) +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    change (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
    rw [← hrange]
    exact Set.mem_range_self j
  have hS₀conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.xBaseBlock Z) :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX
  have hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl (hS₀conj hbase))
    · have hjN : j < N := hji.trans hi
      have hpair_conj : φ.conj ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j := by
        simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hjpair ⊢
        rcases hjpair with hφ | hφ
        · right
          rw [hφ, hpair0 j hjN, hpair1 j hjN]
        · left
          rw [hφ, hpair1 j hjN, hpair0 j hjN]
          simp
      exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hji, hpair_conj⟩)
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx
    have hxrange : x ∈ Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) := by
      rw [hrange]
      exact hx
    rcases hxrange with ⟨j, rfl⟩
    exact ⟨j, by simp, rfl⟩
  have hmemreal : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ) := by
    intro j _
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).1
  have hmemdiffsupp : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j _
    exact hyp.xMember_diffSupport_of_irreducible_X hX (hS₁X (hmemS1 j))
  have hmemS1' : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := fun j _ => hmemS1 j
  have hmembarS1 : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁ := fun j _ => hS₁conj (hmemS1 j)
  have hmemconjortho : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0 := by
    intro j _
    exact (hyp.xMember_characterFacts_of_irreducible_X hZH hX (hS₁X (hmemS1 j))).2.2.2.2
  have hmemortho : ∀ j ∈ (Finset.univ : Finset (Fin k)), ∀ l ∈ (Finset.univ : Finset (Fin k)),
      ClassFunction.inner (χmem j : ClassFunction ↥L ℂ) (χmem l : ClassFunction ↥L ℂ) =
        @ite ℂ (j = l) (Classical.propDecidable (j = l)) 1 0 := by
    intro j _ l _
    by_cases hjl : j = l
    · subst j
      simpa using irreducibleCharacter_inner_eq_ite (χmem l) (χmem l)
    · have hχne : χmem j ≠ χmem l := fun h => hjl (hχinj h)
      simpa [hjl, hχne] using irreducibleCharacter_inner_eq_ite (χmem j) (χmem l)
  let Dprefix : ℕ := ∑ j : Fin k, dmem j * dmem j
  have hDsum : ∑ j ∈ (Finset.univ : Finset (Fin k)), dmem j * dmem j = Dprefix := by
    simp [Dprefix]
  have hsum' : Dprefix +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total := by
    simpa [Dprefix] using hsum
  exact hyp.xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi hcover (by simp) hmemreal hmemdiffsupp
    hmemS1' hmembarS1 hmemconjortho hmemortho
    hχone hχ₁one (fun j _ => hmemone j) hDsum
    hp hlt hdχ hd₁ (fun j _ => hdmem j) hθχ hθ₁
    (fun j _ => hθmem j) (fun j _ => hlemem j)
    hθtail htail_le hsum' hqtot hθsq_le_qtot htotal hidx_p

/-- **(T8.11v0) X-adjoin input from a pairUnion enumeration with a base-block anchor.**

This variant of `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums` removes two sorted-degree
inputs.  If the chosen anchor `χ₁` lies in the minimal-degree base block, then every member of the
running prefix has degree at least `χ₁(1)`.  The current pair is disjoint from the prefix, hence its
first character is not itself in the base block, so its degree is strictly larger. -/
noncomputable def xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ k, k < N → (pair k).1 = (χs k : ClassFunction ↥L ℂ))
    (hpair1 : ∀ k, k < N → (pair k).2 = (χs k : ClassFunction ↥L ℂ).conj)
    (hpairs : ∀ k, k < N →
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k ⊆ hyp.Xset Z)
    (hdisj : ∀ k, k < N → Disjoint
      (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair k)
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair k))
    (hi : i < N)
    {hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)}
    {κ : Type} {tailSet : Finset κ}
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L}
    (hχinj : Function.Injective χmem)
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    {i₁ : Fin k} {p idx d₁ dχ qtot c total θ₁ θχ m₁ mχ mq : ℕ}
    {dmem θmem mmem : Fin k → ℕ} {θtail : κ → ℕ} {mtail : κ → ℕ}
    (hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ))
    (hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ))
    (hanchor : (χmem i₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z)
    (hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ))
    (hp : 3 ≤ p)
    (hdχ : dχ = idx * θχ) (hd₁ : d₁ = idx * θ₁)
    (hdmem : ∀ j, dmem j = idx * θmem j)
    (hθχ : θχ = p ^ mχ) (hθ₁ : θ₁ = p ^ m₁)
    (hθmem : ∀ j, θmem j = p ^ mmem j)
    (hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j)
    (htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j)
    (hsum : (∑ j : Fin k, dmem j * dmem j) +
      (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total)
    (hqtot : qtot = p ^ mq) (hθsq_le_qtot : θχ * θχ ≤ qtot)
    (htotal : total = qtot * c) (hidx_p : Nat.Coprime idx p) :
    XAdjoinStepInput hyp.dade hyp.hconj hcoh (χs i) := by
  let S₁ : Set (ClassFunction ↥L ℂ) :=
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  have hS₁X : S₁ ⊆ hyp.Xset Z := by
    intro φ hφ
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp hφ with hbase | ⟨j, hji, hjpair⟩
    · exact hyp.xBaseBlock_subset Z hbase
    · exact hpairs j (hji.trans hi) hjpair
  have hmemS1 : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j
    change (χmem j : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
    rw [← hrange]
    exact Set.mem_range_self j
  have hχpair : (χs i : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair i := by
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  have hχX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset Z := hpairs i hi hχpair
  have hχnotbase : (χs i : ClassFunction ↥L ℂ) ∉ hyp.xBaseBlock Z := by
    intro hχbase
    have hχprefix : (χs i : ClassFunction ↥L ℂ) ∈ S₁ :=
      OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hχbase)
    exact (Set.disjoint_left.mp (hdisj i hi)) hχpair hχprefix
  have hlt : d₁ < dχ :=
    hyp.natDegree_lt_of_xBaseBlock_anchor_of_not_mem hanchor hχX hχnotbase hχ₁one hχone
  have hlemem : ∀ j : Fin k, d₁ ≤ dmem j := by
    intro j
    exact hyp.natDegree_le_of_xBaseBlock_anchor hanchor (hS₁X (hmemS1 j))
      hχ₁one (hmemone j)
  exact hyp.xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) hχinj hrange
    hχone hχ₁one hmemone hp hlt
    hdχ hd₁ hdmem hθχ hθ₁ hθmem hlemem
    hθtail htail_le hsum hqtot hθsq_le_qtot htotal hidx_p

/-- **(T8.11v) Common-index p-power data for one X-chain step.**

This is the remaining genuine (6.6) payload for one step after the routine `pairUnion` bookkeeping
has been discharged.  The fields are indexed by the same finite enumeration of the running
accumulator `pairUnion (xBaseBlock Z) pair i`, so downstream callers can supply the character-degree
and p-power data directly without rebuilding the member-family facts or the `XAdjoinStepInput`
record by hand. -/
structure PairUnionCommonIndexPrimePowerStepData
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L} where
  κ : Type
  tailSet : Finset κ
  k : ℕ
  χmem : Fin k → IrreducibleCharacter ↥L
  hχinj : Function.Injective χmem
  hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  i₁ : Fin k
  p : ℕ
  idx : ℕ
  d₁ : ℕ
  dχ : ℕ
  qtot : ℕ
  c : ℕ
  total : ℕ
  θ₁ : ℕ
  θχ : ℕ
  m₁ : ℕ
  mχ : ℕ
  mq : ℕ
  dmem : Fin k → ℕ
  θmem : Fin k → ℕ
  mmem : Fin k → ℕ
  θtail : κ → ℕ
  mtail : κ → ℕ
  hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ)
  hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ)
  hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ)
  hp : 3 ≤ p
  hlt : d₁ < dχ
  hdχ : dχ = idx * θχ
  hd₁ : d₁ = idx * θ₁
  hdmem : ∀ j, dmem j = idx * θmem j
  hθχ : θχ = p ^ mχ
  hθ₁ : θ₁ = p ^ m₁
  hθmem : ∀ j, θmem j = p ^ mmem j
  hlemem : ∀ j, d₁ ≤ dmem j
  hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j
  htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j
  hsum : (∑ j : Fin k, dmem j * dmem j) +
    (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total
  hqtot : qtot = p ^ mq
  hθsq_le_qtot : θχ * θχ ≤ qtot
  htotal : total = qtot * c
  hidx_p : Nat.Coprime idx p

/-- **(T8.11v1) Base-anchor common-index p-power data for one X-chain step.**

This is the chain-step payload matching
`xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums`: the caller supplies the
chosen anchor in `xBaseBlock Z`, and the adapter derives the sorted-degree facts
`d₁ < dχ` and `∀ j, d₁ ≤ dmem j` internally. -/
structure PairUnionBaseAnchorCommonIndexPrimePowerStepData
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L} where
  κ : Type
  tailSet : Finset κ
  k : ℕ
  χmem : Fin k → IrreducibleCharacter ↥L
  hχinj : Function.Injective χmem
  hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
    OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i
  i₁ : Fin k
  p : ℕ
  idx : ℕ
  d₁ : ℕ
  dχ : ℕ
  qtot : ℕ
  c : ℕ
  total : ℕ
  θ₁ : ℕ
  θχ : ℕ
  m₁ : ℕ
  mχ : ℕ
  mq : ℕ
  dmem : Fin k → ℕ
  θmem : Fin k → ℕ
  mmem : Fin k → ℕ
  θtail : κ → ℕ
  mtail : κ → ℕ
  hχone : (χs i : ClassFunction ↥L ℂ) 1 = (dχ : ℂ)
  hχ₁one : (χmem i₁ : ClassFunction ↥L ℂ) 1 = (d₁ : ℂ)
  hanchor : (χmem i₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z
  hmemone : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (dmem j : ℂ)
  hp : 3 ≤ p
  hdχ : dχ = idx * θχ
  hd₁ : d₁ = idx * θ₁
  hdmem : ∀ j, dmem j = idx * θmem j
  hθχ : θχ = p ^ mχ
  hθ₁ : θ₁ = p ^ m₁
  hθmem : ∀ j, θmem j = p ^ mmem j
  hθtail : ∀ j ∈ tailSet, θtail j = p ^ mtail j
  htail_le : ∀ j ∈ tailSet, idx * θχ ≤ idx * θtail j
  hsum : (∑ j : Fin k, dmem j * dmem j) +
    (∑ j ∈ tailSet, (idx * θtail j) * (idx * θtail j)) = total
  hqtot : qtot = p ^ mq
  hθsq_le_qtot : θχ * θχ ≤ qtot
  htotal : total = qtot * c
  hidx_p : Nat.Coprime idx p

open scoped Classical in
/-- **(T8.11w) X-chain coherence from per-step common-index p-power data.**

This is the chain-level consumer of `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums`.
The caller no longer has to construct an `XAdjoinStepInput` at each step: it supplies only a
`PairUnionCommonIndexPrimePowerStepData` package for the actual prefix accumulator chosen by the
conjugate-pair cover.  The adapter folds the chain using
`Xset_isCoherent_from_adjoinSteps_of_irreducible_X` and constructs each step input internally. -/
noncomputable def Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionCommonIndexPrimePowerStepData hyp (Z := Z) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.Xset_isCoherent_from_adjoinSteps_of_irreducible_X hZH hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh
  let data := hstepData pair N χs hpair0 hpair1 hpairs hdisj hmono i hi
  exact hyp.xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) data.hχinj data.hrange
    data.hχone data.hχ₁one data.hmemone
    data.hp data.hlt data.hdχ data.hd₁ data.hdmem
    data.hθχ data.hθ₁ data.hθmem data.hlemem data.hθtail data.htail_le data.hsum
    data.hqtot data.hθsq_le_qtot data.htotal data.hidx_p

open scoped Classical in
/-- **(T8.11w1) X-chain coherence from base-anchor common-index p-power data.**

This is the chain-level consumer of
`xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums`.  Compared with
`Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X`, each step package no
longer includes the sorted-degree fields `d₁ < dχ` and `∀ j, d₁ ≤ dmem j`; the base-block anchor
and pair-cover disjointness provide them internally. -/
noncomputable def Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := Z) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.Xset_isCoherent_from_adjoinSteps_of_irreducible_X hZH hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono i hi hcoh
  let data := hstepData pair N χs hpair0 hpair1 hpairs hdisj hmono i hi
  exact hyp.xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) data.hχinj data.hrange
    data.hχone data.hχ₁one data.hanchor data.hmemone data.hp
    data.hdχ data.hd₁ data.hdmem data.hθχ data.hθ₁ data.hθmem data.hθtail
    data.htail_le data.hsum data.hqtot data.hθsq_le_qtot data.htotal data.hidx_p

/-- **(T8.11w1c) base-anchor X-chain coherence, completeness-exposing variant.**  Like
`Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X` but the per-step
producer `hstepData` additionally receives the Xset-cover completeness witness `hcover` (finding #6)
— required to build the per-step `tailSet`/`htail_le`/`hsum`.  Routes through the `…withCover…`
engine.  Additive (no existing signature changes). -/
noncomputable def
    Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_irreducible_X
    (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ hyp.Xset Z) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      (∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
        ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := Z) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset Z)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X hZH hX hXne ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi hcoh
  let data := hstepData pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi
  exact hyp.xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums hZH hX
    hpair0 hpair1 hpairs hdisj hi (hcoh := hcoh) data.hχinj data.hrange
    data.hχone data.hχ₁one data.hanchor data.hmemone data.hp
    data.hdχ data.hd₁ data.hdmem data.hθχ data.hθ₁ data.hθmem data.hθtail
    data.htail_le data.hsum data.hqtot data.hθsq_le_qtot data.htotal data.hidx_p

/-- **(6.6)/(6.8.1), central-`Zc`, completeness-exposing form (redesign L2 outer shell, withCover).**
Same as `Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
but the `hstepData` producer receives the Xset-cover completeness witness `hcover` (finding #6), which
the monolith needs to build `tailSet`/`htail_le`/`hsum`.  Routes through the `…withCover…` consumer. -/
noncomputable def
    Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_frobenius
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
      (∀ φ ∈ hyp.Xset hyp.centralCommutator, φ ∈ hyp.xBaseBlock hyp.centralCommutator ∨
        ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := hyp.centralCommutator) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  exact hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_irreducible_X
    (Z := hyp.centralCommutator) hyp.centralCommutator_le
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    (hyp.Xset_centralCommutator_nonempty hF hHnonab) hstepData

/-- **Base-anchor index existence** (the StepData `i₁`/`hanchor` data).  If `χmem` enumerates the
running prefix `pairUnion (xBaseBlock Z) pair i` and the minimal-degree base block `xBaseBlock Z`
is nonempty, then some index `i₁` has `χmem i₁ ∈ xBaseBlock Z` (the base block is contained in the
prefix `pairUnion`). -/
theorem exists_xBaseBlock_anchor_index (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {i k : ℕ}
    {χmem : Fin k → IrreducibleCharacter ↥L}
    (hrange : Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) =
      OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i)
    (hne : (hyp.xBaseBlock Z).Nonempty) :
    ∃ i₁ : Fin k, (χmem i₁ : ClassFunction ↥L ℂ) ∈ hyp.xBaseBlock Z := by
  obtain ⟨φ, hφ⟩ := hne
  have hφpair : φ ∈ Set.range (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]
    exact OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hφ)
  obtain ⟨i₁, hi₁⟩ := hφpair
  have hi₁' : (χmem i₁ : ClassFunction ↥L ℂ) = φ := hi₁
  exact ⟨i₁, by rw [hi₁']; exact hφ⟩

/-- **Tail-degree lower bound (finding #6 `htail_le` core).**  An `X`-member `φ` outside the running
prefix `pairUnion (xBaseBlock Z) pair i` has degree at least that of the current pair head
`(pair i).1`.  Proof: by `hcover`, `φ` is in the base block or some pair `j < N`; it is not in the
base (`⊆` prefix), so `φ ∈ pairSet pair j`; and `φ ∉ prefix` forces `j ≥ i` (pairs `< i` lie in the
prefix), so by degree-monotonicity (`hmono`) `(pair i).1(1) ≤ (pair j).1(1) = φ(1)`.  This is the
step where Xset-cover completeness (`hcover`) is genuinely used. -/
theorem characterDegree_re_le_of_not_mem_pairUnion (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L}
    {pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ} {N : ℕ}
    {χs : ℕ → IrreducibleCharacter ↥L}
    (hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ))
    (hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj)
    (hmono : ∀ j, j + 1 < N →
      (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re)
    (hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨
      ∃ j, j < N ∧ φ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
    {i : ℕ} (hi : i < N)
    {φ : ClassFunction ↥L ℂ} (hφX : φ ∈ hyp.Xset Z)
    (hφnot : φ ∉ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock Z) pair i) :
    (OddOrder.Peterfalvi.S03.characterDegree (pair i).1).re ≤
      (OddOrder.Peterfalvi.S03.characterDegree φ).re := by
  -- degree-monotone chaining: `a ≤ b < N ⟹ deg (pair a).1 ≤ deg (pair b).1`
  have hchain : ∀ d a : ℕ, a + d < N →
      (OddOrder.Peterfalvi.S03.characterDegree (pair a).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair (a + d)).1).re := by
    intro d
    induction d with
    | zero => intro a _; simp
    | succ d ih =>
      intro a haN
      have h1 := ih a (by omega)
      have h2 := hmono (a + d) (by omega)
      have : a + (d + 1) = (a + d) + 1 := by omega
      rw [this]
      exact le_trans h1 h2
  -- `φ` is in some pair `j`, and `j ≥ i`
  rcases hcover φ hφX with hbase | ⟨j, hjN, hjpair⟩
  · exact absurd (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inl hbase)) hφnot
  · have hij : i ≤ j := by
      by_contra hlt
      push_neg at hlt  -- j < i
      exact hφnot (OddOrder.Peterfalvi.S07.mem_pairUnion.mpr (Or.inr ⟨j, hlt, hjpair⟩))
    have hdeg_ij : (OddOrder.Peterfalvi.S03.characterDegree (pair i).1).re ≤
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re := by
      have := hchain (j - i) i (by omega)
      rwa [Nat.add_sub_cancel' hij] at this
    -- `φ` equals `(pair j).1` or `(pair j).2`, both of degree `(pair j).1(1)`
    have hφdeg : (OddOrder.Peterfalvi.S03.characterDegree φ).re =
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re := by
      simp only [OddOrder.Peterfalvi.S07.pairSet, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hjpair
      rcases hjpair with h | h
      · rw [h]
      · rw [h, hpair1 j hjN, hpair0 j hjN]; simp
    rw [hφdeg]; exact hdeg_ij

/-- **Degree-square partition (finding #6 `hsum` core).**  For a finite character set `Xfin` whose
real degree-square sum is a natural number `totalN`, and an injective member subfamily `memb`
contained in `Xfin`, the natural degree-square sum splits as members `+` tail (`Xfin ∖ members`)
`= totalN`.  Pure `Finset.sum_image` + `Finset.sum_sdiff` + an ℝ→ℕ cast; no character theory.  The
producer supplies `deg φ = |L:H|·p^(eφ)` and `totalN = |L:H|·(|H|−|H:Z|)` (via `sum_re_sq_Xset_eq`). -/
theorem natSum_partition_of_realSum {α : Type*} [DecidableEq α]
    (Xfin : Finset α) (deg : α → ℕ) (totalN : ℕ)
    (hXsum : (∑ φ ∈ Xfin, ((deg φ : ℝ)) ^ 2) = (totalN : ℝ))
    {k : ℕ} {memb : Fin k → α} (hinj : Function.Injective memb)
    (hsub : ∀ j, memb j ∈ Xfin) :
    (∑ j : Fin k, deg (memb j) * deg (memb j))
      + (∑ φ ∈ Xfin \ Finset.univ.image memb, deg φ * deg φ) = totalN := by
  classical
  have hmembers : Finset.univ.image memb ⊆ Xfin := by
    intro φ hφ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hφ
    exact hsub j
  have hreindex : ∑ φ ∈ Finset.univ.image memb, deg φ * deg φ
      = ∑ j : Fin k, deg (memb j) * deg (memb j) :=
    Finset.sum_image (fun a _ b _ h => hinj h)
  have hXsumN : ∑ φ ∈ Xfin, deg φ * deg φ = totalN := by
    have h : ((∑ φ ∈ Xfin, deg φ * deg φ : ℕ) : ℝ) = (totalN : ℝ) := by
      rw [← hXsum, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun φ _ => by push_cast; ring)
    exact_mod_cast h
  rw [← hreindex, add_comm, Finset.sum_sdiff hmembers]
  exact hXsumN

open scoped Classical in
/-- **(6.6)/(6.8) X = S − S(Zc) coherence at the central commutator — the L2 producer.**
The redesign's L2 deliverable: `X(Zc)` is coherent, with `Zc = Z(H) ∩ H′` central.  Builds the
per-step `PairUnionBaseAnchorCommonIndexPrimePowerStepData` (the first-ever such term) for every
chain step and feeds it to the `…withCover…` Zc shell.  Per step: the current head `χs i` and every
`X`-member `Ind θ` have degree `|L:H|·p^k` (`exists_index_primePow_degree_of_mem_S`), the central
degree bound `θχ² ≤ |H:Zc|` holds ([Is] Cor 2.30 via `exists_source_primePow_centralBound_of_mem_Xset`),
the `htail_le` field is `characterDegree_re_le_of_not_mem_pairUnion` (uses `hcover`), and the `hsum`
partition is `natSum_partition_of_realSum` pinned by `sum_re_sq_Xset_eq`.  `H` is supplied as a
`p`-group (the capstone's ¬-coherent branch gives this via `isPGroup_of_not_coherent`). -/
noncomputable def Xset_centralCommutator_isCoherent_of_frobenius
    (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  haveI : Fact p.Prime := ⟨hp⟩
  -- `|L:H|` coprime to `p`
  have hpdvd : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
    rw [hn]; exact dvd_pow_self p hn0
  have hidxp : Nat.Coprime H.index p := by
    rw [hyp.index_H_eq_card_W1]
    exact (Nat.Coprime.coprime_dvd_left hpdvd hF.coprime_card_kernel_complement).symm
  -- the common-index degree exponent over `X(Zc)`
  have hdegX : ∀ φ ∈ hyp.Xset hyp.centralCommutator,
      ∃ kφ : ℕ, (φ : ClassFunction ↥L ℂ) 1 = ((H.index * p ^ kφ : ℕ) : ℂ) :=
    fun φ hφ => hyp.exists_index_primePow_degree_of_mem_S hp hHp (hyp.Xset_subset_S hφ)
  choose! e he using hdegX
  -- `qtot = |H:Zc| = p^mq`
  haveI : (hyp.centralCommutator.subgroupOf H).Normal :=
    hyp.centralCommutator_normal.subgroupOf H
  choose mq hmq using
    exists_primePow_card_quotient_of_isPGroup hp hHp (hyp.centralCommutator.subgroupOf H)
  have hZle : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  refine hyp.Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover_of_frobenius
    hF hHnonab ?_
  intro pair N χs hpair0 hpair1 hpairs hdisj hmono hcover i hi
  -- `χs i ∈ X(Zc)`
  have hχiX : (χs i : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
    refine hpairs i hi ?_
    simp [OddOrder.Peterfalvi.S07.pairSet, hpair0 i hi]
  -- central degree bound for the head
  choose mχ hχdeg hχsq using hyp.exists_source_primePow_centralBound_of_mem_Xset hp hHp
    hyp.centralCommutator_subgroupOf_le_center hχiX
  -- member-family enumeration
  choose k χmem hconj using
    hyp.exists_pairUnion_memberFamily_of_irreducible_X hyp.centralCommutator_le
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      hpair0 hpair1 hpairs hi
  obtain ⟨hχinj, hrange, -, -, -, -, -, -⟩ := hconj
  -- members lie in `X(Zc)`
  have hmemX : ∀ j : Fin k, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
    intro j
    have : (χmem j : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock hyp.centralCommutator) pair i := by
      rw [← hrange]; exact Set.mem_range_self j
    rcases OddOrder.Peterfalvi.S07.mem_pairUnion.mp this with hbase | ⟨j', hj', hj'pair⟩
    · exact hyp.xBaseBlock_subset _ hbase
    · exact hpairs j' (hj'.trans hi) hj'pair
  -- base-block anchor
  have hbbne : (hyp.xBaseBlock hyp.centralCommutator).Nonempty := by
    rw [← Set.ncard_pos (hyp.xSet_finite_of_irreducible_X
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ) |>.subset
        (hyp.xBaseBlock_subset _))]
    exact lt_of_lt_of_le (by norm_num) (hyp.two_le_xBaseBlock_ncard hF hyp.centralCommutator_le
      (hyp.Xset_centralCommutator_nonempty hF hHnonab))
  choose i₁ hanchor using hyp.exists_xBaseBlock_anchor_index hrange hbbne
  -- the `X(Zc)` index Finset (the `sum_re_sq_Xset_eq` domain) and its coe
  set XF := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(hyp.centralCommutator.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXFdef
  have hmemXF : ∀ φ, φ ∈ XF ↔ φ ∈ hyp.Xset hyp.centralCommutator := by
    intro φ
    rw [hXFdef, Finset.mem_sdiff]
    constructor
    · rintro ⟨hbot, hnotZ⟩
      obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hbot
      obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
      refine hyp.mem_Xset.mpr ⟨by rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩, ?_⟩
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', hne', hker', heq'⟩ := hmem
      exact hnotZ (Finset.mem_image.mpr
        ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
    · intro hφ
      obtain ⟨hφS, hφnotZ⟩ := hyp.mem_Xset.mp hφ
      rw [hyp.S_eq, Set.mem_setOf_eq] at hφS
      obtain ⟨θ, hθne, rfl⟩ := hφS
      refine ⟨Finset.mem_image.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hθne⟩, rfl⟩, ?_⟩
      · intro x hx
        rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
        subst hx; exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
      · intro hmem
        obtain ⟨θ', hθ', hθ'eq⟩ := Finset.mem_image.mp hmem
        obtain ⟨-, hker', hne'⟩ := Finset.mem_filter.mp hθ'
        exact hφnotZ (hyp.mem_SsubFiltration.mpr ⟨θ', hne', hker', hθ'eq.symm⟩)
  -- real degree-square sum over `XF`
  have hrealSum : (∑ φ ∈ XF, ((H.index * p ^ e φ : ℕ) : ℝ) ^ 2)
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ)
          - (Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) : ℝ)) := by
    rw [← hyp.sum_re_sq_Xset_eq hF (Z := hyp.centralCommutator)]
    refine Finset.sum_congr rfl (fun φ hφ => ?_)
    have hφX := (hmemXF φ).mp hφ
    rw [he φ hφX, Complex.natCast_re]
  -- enumerate the tail `XF ∖ members` by `Fin tailF.card` (Type 0, to fit `StepData.κ : Type`)
  set tailF := XF \ Finset.univ.image (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ))
    with htailFdef
  let tElt : Fin tailF.card → ClassFunction ↥L ℂ :=
    fun i => ((tailF.equivFin.symm i : { x // x ∈ tailF }) : ClassFunction ↥L ℂ)
  have htElt_mem : ∀ i, tElt i ∈ tailF := fun i => (tailF.equivFin.symm i).2
  have hreindex : ∀ F : ClassFunction ↥L ℂ → ℕ,
      (∑ i : Fin tailF.card, F (tElt i)) = ∑ x ∈ tailF, F x := by
    intro F
    rw [← Finset.sum_coe_sort tailF F]
    exact Equiv.sum_comp tailF.equivFin.symm (fun y => F (y : ClassFunction ↥L ℂ))
  have hinj : Function.Injective (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hsub : ∀ j : Fin k, (fun j : Fin k => (χmem j : ClassFunction ↥L ℂ)) j ∈ XF :=
    fun j => (hmemXF _).mpr (hmemX j)
  -- assemble the step data
  exact
    { κ := Fin tailF.card
      tailSet := Finset.univ
      k := k
      χmem := χmem
      hχinj := hχinj
      hrange := hrange
      i₁ := i₁
      p := p
      idx := H.index
      d₁ := H.index * p ^ e (χmem i₁ : ClassFunction ↥L ℂ)
      dχ := H.index * p ^ mχ
      qtot := Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
      c := H.index * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)
      total := H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
      θ₁ := p ^ e (χmem i₁ : ClassFunction ↥L ℂ)
      θχ := p ^ mχ
      m₁ := e (χmem i₁ : ClassFunction ↥L ℂ)
      mχ := mχ
      mq := mq
      dmem := fun j => H.index * p ^ e (χmem j : ClassFunction ↥L ℂ)
      θmem := fun j => p ^ e (χmem j : ClassFunction ↥L ℂ)
      mmem := fun j => e (χmem j : ClassFunction ↥L ℂ)
      θtail := fun i => p ^ e (tElt i)
      mtail := fun i => e (tElt i)
      hχone := hχdeg
      hχ₁one := he _ (hyp.xBaseBlock_subset _ hanchor)
      hanchor := hanchor
      hmemone := fun j => he _ (hmemX j)
      hp := hp3
      hdχ := rfl
      hd₁ := rfl
      hdmem := fun _ => rfl
      hθχ := rfl
      hθ₁ := rfl
      hθmem := fun _ => rfl
      hθtail := fun _ _ => rfl
      htail_le := by
        intro t _
        have hφtailF : tElt t ∈ tailF := htElt_mem t
        rw [htailFdef, Finset.mem_sdiff] at hφtailF
        obtain ⟨hφXF, hφnotmem⟩ := hφtailF
        have hφX := (hmemXF (tElt t)).mp hφXF
        have hφnotpair : tElt t ∉ OddOrder.Peterfalvi.S07.pairUnion (L := ↥L)
            (hyp.xBaseBlock hyp.centralCommutator) pair i := by
          intro hmem
          rw [← hrange] at hmem
          obtain ⟨j, hj⟩ := hmem
          exact hφnotmem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
        have hdeg := hyp.characterDegree_re_le_of_not_mem_pairUnion hpair0 hpair1 hmono hcover hi
          hφX hφnotpair
        rw [hpair0 i hi] at hdeg
        have h1 : (OddOrder.Peterfalvi.S03.characterDegree (χs i : ClassFunction ↥L ℂ)).re
            = ((H.index * p ^ mχ : ℕ) : ℝ) := by
          rw [OddOrder.Peterfalvi.S03.characterDegree_def, hχdeg, Complex.natCast_re]
        have h2 : (OddOrder.Peterfalvi.S03.characterDegree (tElt t)).re
            = ((H.index * p ^ e (tElt t) : ℕ) : ℝ) := by
          rw [OddOrder.Peterfalvi.S03.characterDegree_def, he _ hφX, Complex.natCast_re]
        rw [h1, h2] at hdeg
        exact_mod_cast hdeg
      hsum := by
        show (∑ j : Fin k, (H.index * p ^ e (χmem j : ClassFunction ↥L ℂ))
              * (H.index * p ^ e (χmem j : ClassFunction ↥L ℂ)))
            + (∑ i : Fin tailF.card, (H.index * p ^ e (tElt i)) * (H.index * p ^ e (tElt i)))
            = H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
        rw [show (∑ i : Fin tailF.card, (H.index * p ^ e (tElt i)) * (H.index * p ^ e (tElt i)))
              = ∑ x ∈ tailF, (H.index * p ^ e x) * (H.index * p ^ e x) from
            hreindex (fun x => (H.index * p ^ e x) * (H.index * p ^ e x))]
        exact natSum_partition_of_realSum XF (fun φ => H.index * p ^ e φ)
          (H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)))
          (by rw [hrealSum]; push_cast [Nat.cast_sub hZle]; ring) hinj hsub
      hqtot := hmq
      hθsq_le_qtot := by rw [← pow_two]; exact hχsq
      htotal := hyp.index_mul_card_sub_factor (Z := hyp.centralCommutator)
      hidx_p := hidxp }

/-- **(6.8.1)/(6.8), L3 outer shell:** `X(Zc) ∪ Y` is coherent, given the (6.8.1) `τ₃` glue data
`ν`.  Mirrors `coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner` but at
the central `Zc` and **stopping at the union coherence** (`Xset Zc ∪ Yset ⊊ S` in general, so the
final `Xset_union_Yset_eq_S` collapse is unavailable; the gap is closed separately by L4
`false_of_coherentXunionYset_of_not_coherentS`).  The `X`-coherence is the L2 monolith
`Xset_centralCommutator_isCoherent_of_frobenius`; the `Y`-coherence is `coherentYset`;
source-orthogonality is `Xset Zc ⊥ Yset` (`Yset ⊆ S(Zc)` by antitonicity, disjoint from `Xset Zc`).
The remaining input is the genuine **(6.8.1) `ν`/`hmixed` data** — the `τ₃` construction (uses (6.7)
`peterfalvi_67_of_odd`), still to be built; once supplied, `⟨…⟩` feeds L4. -/
noncomputable def coherentXunionYset_centralCommutator_of_glued_of_frobenius
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
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj)
    hmixed hgen

/-- **(6.8.1)/(6.8), L3 outer shell — diagonal-aware form.**  Same as
`coherentXunionYset_centralCommutator_of_glued_of_frobenius`, but routing through the corrected
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`: the plain shell's generation
hypothesis `hgen` (without the cross-diagonals `D`) is **false** in the (6.8.1) situation — the
supported cross-diagonal `χ₁ − a·η₁ ∈ ℤ[X(Zc) ∪ Y]` is not a sum of a supported `X`-combination and
a supported `Y`-combination (see `notes/peterfalvi/s08_6_8_blocker_central_Z.md`, framing correction
#2, and the `coherentUnion_of_glued_withDiagonal` docstring).  Here `D` carries those cross-diagonals
with `hDτ : ∀ d ∈ D, ν d = τ d` (the (6.8.1) `b ≡ 0` conclusion
`(χ₁ − a·η₁)^τ = χ₁^{τ₂} − a·η₁^{τ₁}`), and `hgen` is the satisfiable generation including `D`. -/
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
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset ν hagreeX hagreeY
    (inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj)
    hmixed D hDτ hgen

/-- **Peterfalvi (6.8.1) image orthogonality `himg_ortho` via (4.1)** (Frobenius case, mmd 04.8 L166).
`X(Zc)^{τ₂} ⊥ Y^{τ₁}`: for `χ ∈ X(Zc)`, `η ∈ Y`, the coherent images are orthogonal,
`⟨χ^{τ₂}, η^{τ₁}⟩ = 0`.  This is the "by (4.1)" step, **independent** of the deep `b ≡ 0` argument.

Pick distinct references `χ' ≠ χ` in `X(Zc)` (`2 ≤ |X(Zc)|`, from `two_le_xBaseBlock_ncard` +
`xBaseBlock_subset`) and `η' ≠ η` in `Y` (`2 ≤ |Y|`, `two_le_Yset_ncard`), and apply
`pairwise_inner_eq_zero_of_orthogonal_signedDifference` with `α = η^{τ₁}, β = η'^{τ₁}, γ = χ^{τ₂},
δ = χ'^{τ₂}` and **degree coefficients** `u = χ'(1), v = χ(1)`.  Then `u•γ − v•δ =
(χ'(1)•χ − χ(1)•χ')^{τ₂}` is the τ₂-image of a *supported* (degree-`0`,
`sMember_smulDiffSupport_of_charValue_eq` — no divisibility needed) integer `X`-combination, and
`α − β = (η − η')^{τ₁}` the τ₁-image of a supported (equal-degree, `Yset_apply_one`) `Y`-difference;
the difference-orthogonality `inner_extension_eq_inner_of_supported` (`= 0` by `X ⊥ Y`) and degree-`0`
`extension_apply_one_eq_zero_of_supported` discharge `hdiff`/`hα1`/`hγδ1`.  The conclusion `⟨α,γ⟩ = 0`
gives the claim by conjugate symmetry. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ)
      (hyp.coherentYset.extension η) = 0 := by
  classical
  haveI : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set hXc := hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp with hXc_def
  set hYc := hyp.coherentYset with hYc_def
  -- irreducibility of members
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  -- `if`-formula for inner products of irreducibles (orthonormality)
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  -- distinct references (n, m ≥ 2)
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty :=
    hyp.Xset_centralCommutator_nonempty hF hHnonab
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.xSet_finite_of_irreducible_X hXirr
  have hX2 : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
    le_trans (hyp.two_le_xBaseBlock_ncard hF hyp.centralCommutator_le hXne)
      (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
  obtain ⟨χ', hχ'X, hχ'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by omega : 1 < (hyp.Xset hyp.centralCommutator).ncard) χ
  obtain ⟨η', hη'Y, hη'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega : 1 < hyp.Yset.ncard) η
  -- positive natural degrees of `χ`, `χ'`
  obtain ⟨d, hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'X⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  -- membership in the integral spans (`subset_span`)
  have hχs : χ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ
  have hχ's : χ' ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ'X
  have hηs : η ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη
  have hη's : η' ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη'Y
  -- the two supported difference inputs of (4.1)
  set xdiff : ClassFunction ↥L ℂ := d' • χ - d • χ' with hxdiff_def
  set ydiff : ClassFunction ↥L ℂ := η - η' with hydiff_def
  have hx_supp : xdiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]; exact Submodule.smul_mem _ _ hχs
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']; exact Submodule.smul_mem _ _ hχ's
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ'X) (by rw [hd_eq, hd'_eq]; ring)
  have hy_supp : ydiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ hηs hη's, ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη'Y)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη'Y).symm)
  -- the image of `xdiff` is exactly the degree-weighted `u•γ − v•δ`
  have hXeq : ((d' : ℝ) : ℂ) • hXc.extension χ - ((d : ℝ) : ℂ) • hXc.extension χ'
      = hXc.extension xdiff := by
    rw [hxdiff_def, map_sub, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ d' (hXc.extension χ),
      ← Nat.cast_smul_eq_nsmul ℂ d (hXc.extension χ')]
    push_cast
    ring
  have hYeq : hYc.extension η - hYc.extension η' = hYc.extension ydiff := by
    rw [hydiff_def, map_sub]
  -- disjointness `X(Zc) ⊥ Y` and the source orthogonality `⟨xdiff, ydiff⟩ = 0`
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hsrc0 : ClassFunction.inner xdiff ydiff = 0 :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj xdiff hx_supp.1 ydiff hy_supp.1
  -- discharge the (4.1) hypotheses and read off `⟨α,γ⟩ = 0`
  have hconcl := OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
    (Γ := G) (α := hYc.extension η) (β := hYc.extension η')
    (γ := hXc.extension χ) (δ := hXc.extension χ')
    (u := (d' : ℝ)) (v := (d : ℝ))
    (by exact_mod_cast hd'_pos.ne') (by exact_mod_cast hd_pos.ne')
    (hYc.extension_mem_ZIrr η hηs)
    (by rw [hYc.extension_inner_eq η η hηs hηs, hinner η η (hYirr η hη) (hYirr η hη), if_pos rfl])
    (hYc.extension_mem_ZIrr η' hη's)
    (by rw [hYc.extension_inner_eq η' η' hη's hη's, hinner η' η' (hYirr η' hη'Y) (hYirr η' hη'Y),
        if_pos rfl])
    (hXc.extension_mem_ZIrr χ hχs)
    (by rw [hXc.extension_inner_eq χ χ hχs hχs, hinner χ χ (hXirr χ hχ) (hXirr χ hχ), if_pos rfl])
    (hXc.extension_mem_ZIrr χ' hχ's)
    (by rw [hXc.extension_inner_eq χ' χ' hχ's hχ's, hinner χ' χ' (hXirr χ' hχ'X) (hXirr χ' hχ'X),
        if_pos rfl])
    (by rw [hYc.extension_inner_eq η η' hηs hη's, hinner η η' (hYirr η hη) (hYirr η' hη'Y),
        if_neg (fun h => hη'ne h.symm)])
    (by rw [hXc.extension_inner_eq χ χ' hχs hχ's, hinner χ χ' (hXirr χ hχ) (hXirr χ' hχ'X),
        if_neg (fun h => hχ'ne h.symm)])
    (by -- hdiff
      rw [hXeq, hYeq, inner_conj_symm (hXc.extension xdiff) (hYc.extension ydiff),
        inner_extension_eq_inner_of_supported hyp.dade hyp.hconj hXc hYc hx_supp hy_supp,
        hsrc0, star_zero])
    (by -- hα1
      rw [hYeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hyp.hconj hYc hy_supp)
    (by -- hγδ1
      rw [hXeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hyp.hconj hXc hx_supp)
  rw [inner_conj_symm (hYc.extension η) (hXc.extension χ), hconcl.1, star_zero]

/-- **Span form of `himg_ortho`:** `⟨x^{τ₂}, η^{τ₁}⟩ = 0` for any `x ∈ ℤ[X(Zc)]` and `η ∈ Y`
(by `ℤ`-linearity from the per-member
`inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`). -/
theorem inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {x : ClassFunction ↥L ℂ} (hx : x ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator))
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem χ hχ =>
      exact hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius
        hF hHnonab hp hp3 hHp hχ hη
  | zero => rw [map_zero, ClassFunction.inner_zero_left]
  | add a b _ _ iha ihb => rw [map_add, ClassFunction.inner_add_left, iha, ihb, add_zero]
  | smul c a _ ih =>
      rw [map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ c
          ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension a),
        ClassFunction.inner_smul_left, ih, mul_zero]

/-- **(6.8.1) Res-decomposition orthogonality** (spine steps 1–2): `Res^G_L(η^{τ₁})` is orthogonal
to every *supported* `X(Zc)`-combination.  For `η ∈ Y` and `x ∈ ℤ[X(Zc), H^#]` (supported),
`⟨Res^G_L(η^{τ₁}), x⟩_L = 0`.  By Dade reciprocity (`inner_tau_eq_inner_restrict`,
`⟨x^τ, η^{τ₁}⟩_G = ⟨x, Res_L(η^{τ₁})⟩_L`) and `x^τ = x^{τ₂}` (supported), this reduces to the span
form of `himg_ortho` (`⟨x^{τ₂}, η^{τ₁}⟩_G = 0`).  Hence the `X`-components of `Res^G_L(η^{τ₁})` are
all proportional to `dᵢ`, i.e. `Res^G_L(η^{τ₁}) = c·∑dᵢχᵢ + χ′` with `χ′ ⊥ X(Zc)` (mmd 04.8 L170). -/
theorem inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) x = 0 := by
  classical
  have hrec := hyp.inner_tau_eq_inner_restrict hx.2 (hyp.coherentYset.extension η)
  have hτ : hyp.tau x =
      (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x :=
    ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extends_on_supported
      x hx).symm
  have h0 : ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 :=
    hyp.inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius
      hF hHnonab hp hp3 hHp hx.1 hη
  have hxr : ClassFunction.inner x
      (ClassFunction.restrict L (hyp.coherentYset.extension η)) = 0 := by
    rw [← hrec, hτ, h0]
  rw [inner_conj_symm x (ClassFunction.restrict L (hyp.coherentYset.extension η)), hxr, star_zero]

/-- **(6.8.1) Res `X`-coefficient proportionality** (mmd 04.8 L170).  For `χ, χ' ∈ X(Zc)` and
`R = Res^G_L(η^{τ₁})` (`η ∈ Y`), `χ'(1)·⟨R, χ⟩ = χ(1)·⟨R, χ'⟩` — the `X`-Fourier coefficients of `R`
are proportional to the degrees (`⟨R,χᵢ⟩ ∝ dᵢ`, the `Res^G_L(η₁^{τ₁}) = c∑dᵢχᵢ + χ′` decomposition).
Apply Res-orthogonality (`inner_restrict_extension_Yset_mem_span_Xset_eq_zero`) to the supported
integer combination `χ'(1)•χ − χ(1)•χ'` (degree-`0`, `sMember_smulDiffSupport_of_charValue_eq`). -/
theorem inner_restrict_extension_Yset_mul_degree_eq_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    (hχ' : χ' ∈ hyp.Xset hyp.centralCommutator) :
    (χ' 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ
      = (χ 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ' := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  obtain ⟨d, _hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', _hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  have hx_supp : (d' • χ - d • χ') ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ)
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ')
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ') (by rw [hd_eq, hd'_eq]; ring)
  have hortho := hyp.inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius
    hF hHnonab hp hp3 hHp hη hx_supp
  rw [ClassFunction.inner_sub_right,
    ← Nat.cast_smul_eq_nsmul ℂ d' χ, ← Nat.cast_smul_eq_nsmul ℂ d χ',
    OddOrder.RepresentationTheory.inner_smul_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast, star_natCast, ← hd'_eq, ← hd_eq] at hortho
  exact sub_eq_zero.mp hortho

/-- **(6.8.1) `η^{τ₁}` constancy value on `Zc^#`** (mmd 04.8 L168, the key constant).  For `η ∈ Y`,
`χ₁ ∈ X(Zc)` and `z ∈ Zc^#`, with `R = Res^G_L(η^{τ₁})`,
`χ₁(1)·(R(z) − R(1)) = -⟨R, χ₁⟩·|L|`.  Since the right side is independent of `z`, this shows `R`
(hence `η^{τ₁}`) is **constant on `Zc^#`** (and gives the value `R(z) − R(1) = -c|H|/a` with
`c = ⟨R,χ₁⟩`, `χ₁(1) = a|W₁|`, after clearing the denominator).

Proof: Fourier-expand `R = ∑_{a∈Irr L} ⟨R,a⟩•a` (`classFunction_eq_sum_inner_smul`); split the sum
by `Zc ⊄ ker`.  On `Zc ⊆ ker` (the non-`X` part) `a(z) = a(1)`, so those terms vanish.  On `X(Zc)`
the coefficient relation `χ₁(1)⟨R,a⟩ = a(1)⟨R,χ₁⟩` (`inner_restrict_extension_Yset_mul_degree_eq`)
factors out `⟨R,χ₁⟩`, leaving `⟨R,χ₁⟩·∑_{a∈X} a(1)(a(z)−a(1)) = ⟨R,χ₁⟩·(-|L|)`
(`sum_filter_degree_mul_charValue_sub_eq`). -/
theorem restrict_extension_Yset_degree_value_eq_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (χ₁ 1) * ((ClassFunction.restrict L (hyp.coherentYset.extension η)) z
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1)
      = -(ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁)
          * (Nat.card ↥L : ℂ) := by
  classical
  haveI : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  have hval : R z - R 1 = ∑ a : IrreducibleCharacter ↥L,
      ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
        ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) := by
    conv_lhs => rw [OddOrder.RepresentationTheory.classFunction_eq_sum_inner_smul R]
    rw [ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]; ring
  rw [hval, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : IrreducibleCharacter ↥L => ¬ ((hyp.centralCommutator : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ)))]
  have hnot : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [Finset.mem_filter, not_not] at ha
    have haz : (a : ClassFunction ↥L ℂ) z = (a : ClassFunction ↥L ℂ) 1 := by
      have hmem := ha.2 hz
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hmem
      exact hmem
    rw [haz, sub_self, mul_zero, mul_zero]
  rw [hnot, add_zero]
  have hfilter : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)))
      = (ClassFunction.inner R χ₁) *
        (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
          ¬ ((hyp.centralCommutator : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
          (a : ClassFunction ↥L ℂ) 1 *
            ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have haX : (a : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
      rw [hyp.Xset_eq_irreducible_not_subset_characterKernel hyp.centralCommutator_le
        (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)]
      exact ⟨a.isIrreducible, ha.2⟩
    have hrel := hyp.inner_restrict_extension_Yset_mul_degree_eq_of_frobenius
      hF hHnonab hp hp3 hHp hη haX hχ₁
    rw [← hRdef] at hrel
    linear_combination ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) * hrel
  rw [hfilter, OddOrder.RepresentationTheory.sum_filter_degree_mul_charValue_sub_eq
    (N := hyp.centralCommutator) hz hz1]
  ring

/-- **(6.8.1) `η^{τ₁}` is constant on `Zc^#`** (mmd 04.8 L168 conclusion).  For `η ∈ Y`, the
restriction `Res^G_L(η^{τ₁})` takes the same value at any two points of `Zc^#`.  Immediate from the
value identity `restrict_extension_Yset_degree_value_eq_of_frobenius` (whose right side `-⟨R,χ₁⟩·|L|`
is independent of the point) and `χ₁(1) ≠ 0` (any anchor `χ₁ ∈ X(Zc)`, nonempty).  This is the exact
"character constant on `Z^#`" hypothesis of the (6.7) adapter `peterfalvi_67_centralCommutator`. -/
theorem restrict_extension_Yset_const_on_centralCommutator_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z z' : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1)
    (hz' : z' ∈ hyp.centralCommutator) (hz'1 : z' ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z' := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.Xset_centralCommutator_nonempty hF hHnonab
  have hd : χ₁ 1 ≠ 0 := by
    obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd_eq
    rw [hd_eq]; exact_mod_cast hd_pos.ne'
  have hv := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz hz1
  have hv' := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz' hz'1
  have hcancel : (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z'
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    mul_left_cancel₀ hd (hv.trans hv'.symm)
  linear_combination hcancel

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
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
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
      if_neg (by intro h; exact Set.disjoint_left.mp hdisj hx (h ▸ hy))]
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
`Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X` for the Frobenius
alternative.  The subgroup facts `H' ≤ H`, `H' ⊴ L`, and `X ⊆ Irr L` are discharged internally;
the remaining inputs are the honest (6.6) nonemptiness and per-step degree data. -/
noncomputable def Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
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
        PairUnionCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  exact hyp.Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X
    (Z := ⁅H, H⁆) (Subgroup.commutator_le_left H H)
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hXne hstepData

/-- **(6.8.1), Frobenius case:** chain-level coherence for
`X = S - S(H')`, using the base-anchor common-index p-power step packages.

Compared with
`Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius`, each step data
package only supplies a base-block anchor; the sorted-degree facts are derived by the existing
base-anchor adapter. -/
noncomputable def
    Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
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
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset ⁅H, H⁆)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  exact hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
    (Z := ⁅H, H⁆) (Subgroup.commutator_le_left H H)
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    hXne hstepData

/-- **(6.6)/(6.8.1), central-`Zc` form (redesign L2 outer shell):** chain-level coherence for
`X = S − S(Zc)` with the **central** `Zc = Z(H) ∩ H′`, from base-anchor common-index p-power step
packages.  This replaces `Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
(which instantiated the general (6.6) consumer at `Z = ⁅H,H⁆`, where the per-step degree field
`hθsq_le_qtot : θχ² ≤ qtot ≤ |H:⁅H,H⁆|` is *unsatisfiable* for class ≥ 3 `p`-groups — see
`notes/peterfalvi/s08_6_8_blocker_central_Z.md`).  At the central `Zc` that field is honestly fillable
by [Is] Cor 2.30 (`exists_source_primePow_centralBound_of_mem_Xset`), so the `hstepData` hypothesis
is satisfiable here — the remaining work is to *construct* it (the producer monolith).  `hX` is
discharged Z-generically (`isIrreducibleCharacter_of_mem_Xset_of_frobenius`) and `hXne` from `H`
non-abelian (`Xset_centralCommutator_nonempty`). -/
noncomputable def
    Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
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
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := hyp.centralCommutator) (pair := pair) (i := i) (χs := χs)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  letI : H.Normal := hyp.H_normal
  haveI := hyp.centralCommutator_normal
  exact hyp.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
    (Z := hyp.centralCommutator) hyp.centralCommutator_le
    (fun _ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
    (hyp.Xset_centralCommutator_nonempty hF hHnonab) hstepData

/-- **(6.8.1), Frobenius case:** final glue from common-index p-power X-chain data.

This composes the Frobenius `X = S - S(H')` coherence constructor with the generator-level `τ₃`
glue adapter.  The caller supplies only the genuine (6.6) X-chain step data and generator-level
`τ₃` agreement/mixed-inner facts; the `X` coherence witness is built internally. -/
noncomputable def coherentS_of_frobenius_pairUnionCommonIndexPrimePowerData_generator_mixed_inner
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
        PairUnionCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x = (hyp.Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
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
    (hyp.Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
      hF hXne hstepData)
    ν hagreeX hagreeY hmixed hgen

/-- **(6.8.1), Frobenius case:** final glue from base-anchor common-index p-power X-chain data.

This is the same capstone as
`coherentS_of_frobenius_pairUnionCommonIndexPrimePowerData_generator_mixed_inner`, but using the
base-anchor step package that derives the sorted-degree inequalities internally. -/
noncomputable def
    coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
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
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x =
        (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
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
    (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
      hF hXne hstepData)
    ν hagreeX hagreeY hmixed hgen

/-- **(6.7)-wiring step (b): `N_G(H.map L.subtype) = L`.**  The normalizer (in `G`) of the kernel
realized in the ambient group is exactly `L`: `≤` is the `H^#` TI condition (`H_sharp_ti`; a
nontrivial `a ∈ Ĥ` and its conjugate witness the TI hypothesis), and `≥` holds because `H ◁ L`
(`L = range L.subtype` normalizes the image of the normal `H`, via `le_normalizer_map`). -/
theorem normalizer_map_subtype_eq (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    Subgroup.normalizer (H.map L.subtype) = L := by
  apply le_antisymm
  · haveI : Nontrivial ↥H := H.nontrivial_iff_ne_bot.mpr hyp.H_ne_bot
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

/-- **(6.7)-wiring step (a): the kernel `H`, mapped into `G`, is a Sylow `p`-subgroup of `G`.**

Peterfalvi (6.7) is stated for a Sylow `p`-subgroup `P` of `G` with `L = N_G(P)`; the (6.8.1)
application uses it at `P = H` (modulus `|H|`).  Peterfalvi (6.8)(a) only assumes `H^#` TI with
normalizer `L`, which alone does *not* force `H` Sylow — but in the **Frobenius case** it does:
`H ◁ L` with complement `W₁` of coprime order makes `H` the unique (normal) Sylow `p`-subgroup of
`↥L`, so every `p`-subgroup of `↥L` (in particular `Q ⊓ L` for any Sylow `Q ⊇ Ĥ`) lies in `H`;
combined with `N_G(Ĥ) ≤ L` (from `H^#` TI, `Ĥ := H.map L.subtype`) and the self-normalizing-Sylow
criterion `sylow_coe_eq_of_normalizer_inf_le`, this forces `Ĥ ∈ Syl_p(G)`. -/
theorem sylow_map_subtype_of_frobenius (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H.map L.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
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
    have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1) :=
      hF.coprime_card_kernel_complement
    exact (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_left hpH hcop)
  -- `H` is the unique (normal) Sylow `p`-subgroup of `↥L`.
  set HSyl : Sylow p ↥L := hHp.toSylow hpidx with hHSyl_def
  have hHSyl : (HSyl : Subgroup ↥L) = H := IsPGroup.toSylow_coe hHp hpidx
  haveI hHSylNormal : (HSyl : Subgroup ↥L).Normal := by rw [hHSyl]; exact ‹H.Normal›
  haveI : Unique (Sylow p ↥L) := Sylow.unique_of_normal HSyl hHSylNormal
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
  haveI : Fact p.Prime := ⟨hp⟩
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
  have hsmul : ∀ g : G, (hyp.coherentYset.extension η) g = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  haveI : ρ.IsIrreducible := hρ
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
/-- **(6.8.1) `a ∣ c`** (mmd 04.8 L176, the `c ≡ 0 (mod a)` half of "`b ≡ c ≡ 0 (mod a)`").  For
`η ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` of degree `χ₁(1) = a·|W₁|` (`a > 0`, the degree ratio against
the `Y`-degree `|W₁|`), the multiplicity `c = ⟨Res^G_L(η^{τ₁}), χ₁⟩` is an **integer divisible by
`a`**.

This is the (6.7) divisibility step.  The value identity
`restrict_extension_Yset_degree_value_eq_of_frobenius` gives `χ₁(1)·(R(z)−R(1)) = −c·|L|` for
`z ∈ Zc^#` (`R = Res^G_L(η^{τ₁})`); with `χ₁(1) = a|W₁|` and `|L| = |H|·|W₁|`
(`index_H_eq_card_W1` + `index_mul_card`) it becomes `a·(R(z)−R(1)) = −c·|H|`, i.e.
`(R(z)−R(1))/|H| = −c/a`.  The (6.7)-congruence
`restrict_extension_Yset_charValue_cong_of_frobenius` says `(R(z)−R(1))/|H|` is an algebraic integer;
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

/-- **(6.8.1) `a ∣ b`** (mmd 04.8 L176, the `b ≡ 0 (mod a)` half of "`b ≡ c ≡ 0 (mod a)`").  For
`η = η₁ ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|` (`a > 0`), the `η₁^{τ₁}`-coefficient
of the cross-diagonal image `(χ₁−aη₁)^τ` — namely `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩`, which is `b − a` in the
Peterfalvi decomposition (168) `(χ₁−aη₁)^τ = X − aη₁^{τ₁} + b∑η_j^{τ₁}` — is an **integer divisible
by `a`**.  Since `a ∣ (b − a) ⟺ a ∣ b`, this is exactly Peterfalvi's `b ≡ 0 (mod a)`.

Direct route via Dade reciprocity (no need for the full (168) decomposition): `χ₁−aη₁` is supported
on `H^#` (`sMember_scaledDiffSupport_of_charValue_eq`, `χ₁(1) = a·η₁(1)` from `Yset_apply_one`), so
`⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, Res^G_L(η₁^{τ₁})⟩` (`inner_tau_eq_inner_restrict`)
`= ⟨χ₁, R⟩ − a·⟨η₁, R⟩ = c − a·e` (`R = Res^G_L(η₁^{τ₁})`; conjugate symmetry `inner_conj_symm` +
reality of the integers `c = ⟨R,χ₁⟩`, `e = ⟨R,η₁⟩`, `mem_ZIrr_inner_int`).  Since `a ∣ c`
(`dvd_inner_restrict_extension_Yset_of_frobenius`, step 2) and `a ∣ a·e`, `a ∣ (c − a·e)`. -/
theorem dvd_inner_tau_scaledDiff_extension_Yset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ bb : ℤ,
      ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.coherentYset.extension η) = (bb : ℂ)
        ∧ (a : ℤ) ∣ bb := by
  classical
  -- step 2: `c = ⟨R, χ₁⟩` is an integer with `a ∣ c`.
  obtain ⟨cc, hcc, hacc⟩ :=
    hyp.dvd_inner_restrict_extension_Yset_of_frobenius hF hHnonab hp hp3 hHp hη hχ₁ ha_pos ha
  -- `R ∈ ZIrr L`, `η₁` irreducible ⟹ `e := ⟨R, η₁⟩ ∈ ℤ`.
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : ClassFunction.restrict L (hyp.coherentYset.extension η) ∈ ZIrr (↥L) :=
    OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  obtain ⟨e, he⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨η, hηirr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨η, hηirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η from rfl] at he
  -- `χ₁ − a•η₁` is supported on `H^#`.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  -- reciprocity: `⟨(χ₁−aη₁)^τ, η₁^{τ₁}⟩ = ⟨χ₁−aη₁, R⟩`.
  have hrec := hyp.inner_tau_eq_inner_restrict hsupp (hyp.coherentYset.extension η)
  refine ⟨cc - a * e, ?_, ?_⟩
  · rw [hrec, ClassFunction.inner_sub_left, ← Nat.cast_smul_eq_nsmul ℂ a η,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm _ χ₁, hcc,
      OddOrder.RepresentationTheory.inner_conj_symm _ η, he]
    simp only [star_intCast]
    push_cast; ring
  · exact dvd_sub hacc (dvd_mul_right _ _)

/-- **(6.8.1) cross-diagonal/`Y`-difference isometry** (mmd 04.8 L166, the constancy ingredient of
decomposition (168)).  For `η = η₁`, `η' = η_j ∈ Y` with `η' ≠ η`, and an `X`-anchor `χ₁ ∈ X(Zc)`
with `χ₁(1) = a·|W₁|` (`a > 0`):
`⟨(χ₁−aη₁)^τ, (η_j−η₁)^τ⟩ = a`.

By the Dade isometry on the supported pair `{χ₁−aη₁, η_j−η₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; `χ₁−aη₁` supported by
`sMember_scaledDiffSupport_of_charValue_eq`, `η_j−η₁` by `sMember_diffSupport_of_charValue_eq` at the
common degree `|W₁|`), the inner product equals the source `⟨χ₁−aη₁, η_j−η₁⟩`, which expands by
`X ⊥ Y` (`⟨χ₁,η_j⟩ = ⟨χ₁,η₁⟩ = 0`) and `Y`-orthonormality (`⟨η₁,η_j⟩ = 0`, `⟨η₁,η₁⟩ = 1`) to
`a·⟨η₁,η₁⟩ = a`.  This gives the constancy `β_j − β₁ = a` (j>1) of the `η_j^{τ₁}`-coefficients
`β_j = ⟨(χ₁−aη₁)^τ, η_j^{τ₁}⟩` of decomposition (168). -/
theorem inner_tau_scaledDiff_tau_Yset_diff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (η' - η)) = (a : ℂ) := by
  classical
  -- irreducibility + disjointness `X(Zc) ⊥ Y`.
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- supported difference inputs.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsuppX : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  have hsuppY : (η' - η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη).symm)
  -- Dade isometry on the supported pair.
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η, η' - η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppX
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso]
  -- the source orthogonality computation `⟨χ₁ − a•η, η' − η⟩ = a`.
  have hXY : ∀ ψ ∈ hyp.Yset, ClassFunction.inner χ₁ ψ = 0 := by
    intro ψ hψ
    exact inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hXirr φ hφ) (fun φ hφ => hYirr φ hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      ψ (Submodule.subset_span hψ)
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hXY η' hη', hXY η hη, hYon η η' hη hη', hYon η η hη hη, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.1) norm of the cross-diagonal image** (mmd 04.8 L176: `‖χ₁−aη₁‖² = 1+a²`).  For `η = η₁ ∈ Y`
and an `X`-anchor `χ₁ ∈ X(Zc)` with `χ₁(1) = a·|W₁|`:
`⟨(χ₁−aη₁)^τ, (χ₁−aη₁)^τ⟩ = 1 + a²`.

By the Dade isometry on the supported singleton `{χ₁−aη₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`) this equals the source norm
`⟨χ₁−aη₁, χ₁−aη₁⟩`, which expands by `χ₁`/`η₁`-orthonormality (`⟨χ₁,χ₁⟩ = ⟨η₁,η₁⟩ = 1`) and `X ⊥ Y`
(`⟨χ₁,η₁⟩ = ⟨η₁,χ₁⟩ = 0`) to `1 + a²`.  This is the LHS of Peterfalvi's norm identity
`1+a² = ‖X‖² + (b−a)² + (m−1)b²` for the `b = 0` step. -/
theorem inner_self_tau_scaledDiff_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η)) (hyp.tau (χ₁ - a • η)) = 1 + (a : ℂ) ^ 2 := by
  classical
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  -- orthonormality / orthogonality scalars.
  have hχ₁n : ClassFunction.inner χ₁ χ₁ = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηn : ClassFunction.inner η η = (1 : ℂ) := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hXY : ClassFunction.inner χ₁ η = (0 : ℂ) :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj χ₁ (Submodule.subset_span hχ₁)
      η (Submodule.subset_span hη)
  have hYX : ClassFunction.inner η χ₁ = (0 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm χ₁ η, hXY, star_zero]
  -- supported singleton ⟹ Dade isometry.
  have hdeg : χ₁ 1 = (a : ℂ) * η 1 := by rw [ha, hyp.Yset_apply_one hη]
  have hsupp : (χ₁ - a • η).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ₁) (hyp.Yset_subset_S hη) hdeg
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade hyp.hconj (S := ({χ₁ - a • η} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)
  rw [hiso, ← Nat.cast_smul_eq_nsmul ℂ a η]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hχ₁n, hηn,
    hXY, hYX, star_natCast]
  ring

end SibleyDadeHypothesis

/-- **Peterfalvi (6.8) Theorem** (statement; proof deferred).  Under the faithful Sibley
hypotheses `SibleyDadeHypothesis` (a)/(b)/(c), the set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` is
coherent: there is an integral isometric extension of the §4 Dade map `τ` from `Z[S, H^#]` to
`Z[S]` (`hyp.CoherenceTarget = IsCoherent hyp.tau S H^#`).

The full proof is the central technical content of §8 — the reduction to `H` a non-abelian
`p`-group ((6.5)), the case split (A)/(B) on `Z(H) ∩ W₂` (mmd L150-), and gluing the
`Y = S(H')`-coherence (equal degree `|W₁|`, via [Is] Thm 6.34, now available as
`isIrreducibleCharacter_induce_of_inertia_eq`) with the `X = S − S(Z)`-coherence ((6.6)) through
the §7 engine `coherentUnion_of_glued`. This is one of the two sorries blocking §9 (7.10)
`card_G0_lower_bound`; see `issues/0046-peterfalvi-s08-6-8-coherence.md` and
`notes/peterfalvi/s08_6_8_assembly_plan.md` (task DAG T0–T11).

`noncomputable def` (not `theorem`) because `CoherenceTarget` (an `IsCoherent`) carries the
extension map `ν` as data, living in `Type`, not `Prop`. -/
noncomputable def sibleySetup_is_coherent {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : SibleyDadeHypothesis G L H) : hyp.CoherenceTarget := by
  haveI := hyp.H_normal
  by_cases hXe : hyp.Xset ⁅H, H⁆ = ∅
  · -- `X`-empty (abelian) branch: `S = Y`, discharged by the `Y`-coherence `coherentYset`.
    exact hyp.coherenceTarget_of_Xset_empty hXe
  · -- `X`-nonempty branch: the genuine §8 content — glue the `X = S − S(Z)`-coherence
    -- (`Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`,
    -- per-step (6.6) prime-power degree data) with `Y`-coherence via the §7 engine.  Requires
    -- the case split `hyp.cases` (Frobenius / CertainType) and the per-step `hstepData` +
    -- combined extension `ν` glue data, which remain to be constructed.
    sorry

/-- **Peterfalvi (6.8) → (7.10) consumer interface.**
A degree-scaled `Z`-chain decomposition: given a coherence input `τ` on `(S, A)`
and an orthonormal family `ζ : Fin n → ClassFunction L ℂ` in `S` with explicit
integer degree ratios `d : Fin n → ℤ` (`d 0 = 1`), the family of images
`χ t = ν (ζ t)` under the coherence extension `ν` is orthonormal, and
`τ (ζ t - d t • ζ 0) = χ t - d t • χ 0`.

This packages the orthonormal-subsets-with-Ind-equation language used in the
(7.10) proof (see `references/peterfalvi/04.9_*.mmd` L133-135). -/
structure IndChainDecomposition
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G)
    {n : ℕ} [NeZero n]
    (ζ : Fin n → ClassFunction L ℂ) (d : Fin n → ℤ)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The orthonormal output family `χ_t = ν(ζ_t)` in `ClassFunction G ℂ`. -/
  χ : Fin n → ClassFunction G ℂ
  /-- Each `χ_t` has norm `1`. -/
  norm_one : ∀ t, ClassFunction.inner (χ t) (χ t) = 1
  /-- Distinct indices give orthogonal `χ`. -/
  pairwise_inner_zero :
    ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (χ t) (χ u) = 0
  /-- The reference index has trivial scaling: `d 0 = 1`. -/
  d_zero : d 0 = 1
  /-- The Ind equation: `τ(ζ_t - d_t · ζ_0) = χ_t - d_t · χ_0`. -/
  image_eq :
    ∀ t, τ (ζ t - (d t) • ζ 0) = χ t - (d t) • χ 0

namespace IndChainDecomposition

variable {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
variable {n : ℕ} [NeZero n]

/-- The Ind-chain decomposition vanishes at the reference index: for `t = 0`,
`τ(ζ 0 - d 0 · ζ 0) = 0`. -/
@[simp] theorem image_eq_zero
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ (ζ 0 - (d 0) • ζ 0) = 0 := by
  rw [data.d_zero, one_smul, sub_self, map_zero]

/-- The output family of an `IndChainDecomposition` is orthonormal, packaged as a
single `if` formula. -/
theorem inner_chi_eq_ite
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) (t u : Fin n) :
    ClassFunction.inner (data.χ t) (data.χ u) = if t = u then 1 else 0 := by
  by_cases htu : t = u
  · subst u
    rw [if_pos rfl, data.norm_one]
  · rw [if_neg htu, data.pairwise_inner_zero htu]

/-- The weighted output sum `∑ d_t χ_t` used in Peterfalvi (7.10). -/
noncomputable def weightedOutput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) : ClassFunction G ℂ :=
  ∑ t : Fin n, (d t : ℂ) • data.χ t

/-- The integral weighted source difference `∑ d_t (ζ_t - d_t ζ_0)` used in Peterfalvi (7.10). -/
noncomputable def weightedDifferenceInput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (_data : IndChainDecomposition (L := L) (G := G) τ ζ d) : ClassFunction L ℂ :=
  ∑ t : Fin n, (d t) • (ζ t - (d t) • ζ 0)

/-- Coefficient recovery for the weighted output sum. -/
theorem inner_chi_weightedOutput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) (t : Fin n) :
    ClassFunction.inner (data.χ t) data.weightedOutput = (d t : ℂ) := by
  classical
  rw [weightedOutput, inner_sum_right]
  have hsum :
      (∑ u : Fin n, ClassFunction.inner (data.χ t) ((d u : ℂ) • data.χ u)) =
        ∑ u : Fin n, (if u = t then (d u : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, data.inner_chi_eq_ite t u, star_intCast]
    by_cases hut : u = t
    · subst u
      rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg (Ne.symm hut), if_neg hut, mul_zero]
  rw [hsum, Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) t]
  simp

/-- Parseval for the weighted output: `‖∑ d_tχ_t‖² = ∑ d_t²`. -/
theorem weightedOutput_inner_self_eq_sum_sq
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    ClassFunction.inner data.weightedOutput data.weightedOutput =
      ∑ t : Fin n, (d t : ℂ) ^ 2 := by
  classical
  rw [weightedOutput, inner_sum_left]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ClassFunction.inner_smul_left]
  have hinner := data.inner_chi_weightedOutput t
  rw [weightedOutput] at hinner
  rw [hinner]
  ring

/-- Real Parseval form for the weighted output: the norm is the real sum of
integer squares. -/
theorem weightedOutput_inner_self_re_eq_sum_sq
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    (ClassFunction.inner data.weightedOutput data.weightedOutput).re =
      ∑ t : Fin n, (d t : ℝ) ^ 2 := by
  classical
  rw [data.weightedOutput_inner_self_eq_sum_sq, Complex.re_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show ((d t : ℂ) ^ 2) = (((d t : ℝ) ^ 2 : ℝ) : ℂ) by
    push_cast
    ring, Complex.ofReal_re]

/-- The weighted output has norm at least `1`, because the reference coefficient is
`d 0 = 1`. -/
theorem one_le_weightedOutput_inner_self_re
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    1 ≤ (ClassFunction.inner data.weightedOutput data.weightedOutput).re := by
  classical
  rw [data.weightedOutput_inner_self_re_eq_sum_sq]
  have hterm_nonneg : ∀ t : Fin n, 0 ≤ (d t : ℝ) ^ 2 := fun t => sq_nonneg _
  have hsingle : (d 0 : ℝ) ^ 2 ≤ ∑ t : Fin n, (d t : ℝ) ^ 2 :=
    Finset.single_le_sum (fun t _ => hterm_nonneg t) (by simp)
  have hzero : (d 0 : ℝ) ^ 2 = 1 := by
    rw [data.d_zero]
    norm_num
  rwa [hzero] at hsingle

/-- The Ind equations combine linearly on Peterfalvi's weighted source difference. -/
theorem image_weightedDifferenceInput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ data.weightedDifferenceInput =
      ∑ t : Fin n, (d t) • (data.χ t - (d t) • data.χ 0) := by
  classical
  rw [weightedDifferenceInput, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_zsmul, data.image_eq t]

/-- Normalized form of the weighted Ind equation: the weighted source difference maps to
`∑ d_tχ_t - (∑ d_t²)χ_0`. -/
theorem image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ data.weightedDifferenceInput =
      data.weightedOutput - (∑ t : Fin n, (d t : ℂ) ^ 2) • data.χ 0 := by
  classical
  rw [data.image_weightedDifferenceInput]
  ext g
  have hterm : ∀ t : Fin n,
      (d t • (data.χ t - d t • data.χ 0)) g =
        (d t : ℂ) * data.χ t g - (d t : ℂ) ^ 2 * data.χ 0 g := by
    intro t
    rw [← Int.cast_smul_eq_zsmul ℂ (d t) (data.χ t - (d t) • data.χ 0),
      ClassFunction.smul_apply, ClassFunction.sub_apply,
      ← Int.cast_smul_eq_zsmul ℂ (d t) (data.χ 0), ClassFunction.smul_apply]
    ring
  rw [ClassFunction.sub_apply, ClassFunction.smul_apply, weightedOutput,
    ClassFunction.finset_sum_apply]
  calc
    ∑ t : Fin n, (d t • (data.χ t - d t • data.χ 0)) g
        = ∑ t : Fin n, ((d t : ℂ) * data.χ t g - (d t : ℂ) ^ 2 * data.χ 0 g) := by
          exact Finset.sum_congr rfl fun t _ => hterm t
    _ = (∑ t : Fin n, (d t : ℂ) * data.χ t g) -
          ∑ t : Fin n, (d t : ℂ) ^ 2 * data.χ 0 g := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ t : Fin n, (d t : ℂ) * data.χ t g) -
          (∑ t : Fin n, (d t : ℂ) ^ 2) * data.χ 0 g := by
          rw [← Finset.sum_mul]
    _ = (∑ t : Fin n, ((d t : ℂ) • data.χ t) g) -
          (∑ t : Fin n, (d t : ℂ) ^ 2) * data.χ 0 g := by
          rfl
    _ = (∑ t : Fin n, (d t : ℂ) • data.χ t) g -
          (∑ t : Fin n, (d t : ℂ) ^ 2) * data.χ 0 g := by
          rw [ClassFunction.finset_sum_apply]

/-- The reference character coefficient of the weighted Ind image. -/
theorem inner_chi_zero_image_weightedDifferenceInput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
      1 - ∑ t : Fin n, (d t : ℂ) ^ 2 := by
  classical
  have hstar_sum : star (∑ t : Fin n, (d t : ℂ) ^ 2) =
      ∑ t : Fin n, (d t : ℂ) ^ 2 := by
    rw [show star (∑ t : Fin n, (d t : ℂ) ^ 2) =
        ∑ t : Fin n, star ((d t : ℂ) ^ 2) from by
      simp [star_sum]]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [star_pow, star_intCast]
  rw [data.image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero,
    ClassFunction.inner_sub_right, data.inner_chi_weightedOutput 0,
    OddOrder.RepresentationTheory.inner_smul_right, data.norm_one, hstar_sum, mul_one,
    data.d_zero]
  norm_num

/-- Parseval-normalized reference coefficient of the weighted Ind image. -/
theorem inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput) =
      1 - ClassFunction.inner data.weightedOutput data.weightedOutput := by
  rw [data.inner_chi_zero_image_weightedDifferenceInput,
    data.weightedOutput_inner_self_eq_sum_sq]

/-- Real Parseval form of the reference coefficient of the weighted Ind image. -/
theorem inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re =
      1 - ∑ t : Fin n, (d t : ℝ) ^ 2 := by
  rw [data.inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm,
    Complex.sub_re, Complex.one_re, data.weightedOutput_inner_self_re_eq_sum_sq]

/-- The reference coefficient of the weighted Ind image has nonpositive real part. -/
theorem inner_chi_zero_image_weightedDifferenceInput_re_nonpos
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    (ClassFunction.inner (data.χ 0) (τ data.weightedDifferenceInput)).re ≤ 0 := by
  rw [data.inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq]
  have hsum := data.one_le_weightedOutput_inner_self_re
  rw [data.weightedOutput_inner_self_re_eq_sum_sq] at hsum
  linarith

/-- Parseval-normalized form of the weighted Ind equation. -/
theorem image_weightedDifferenceInput_eq_weightedOutput_sub_norm_smul_chi_zero
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ data.weightedDifferenceInput =
      data.weightedOutput -
        ClassFunction.inner data.weightedOutput data.weightedOutput • data.χ 0 := by
  rw [data.image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero,
    data.weightedOutput_inner_self_eq_sum_sq]

/-- Construct an `IndChainDecomposition` from a coherence input `hτ : IsCoherent τ S A`
together with the membership `ζ_t ∈ S`, the orthonormality of the input family `ζ`,
and the support of each scaled difference `ζ_t - d_t · ζ_0` in `Z[S, A]`.

The orthonormality of the images `χ_t = ν(ζ_t)` uses the **lattice-relative**
isometry `hτ.extension_inner_eq` on the generators `ζ_t ∈ S ⊆ Z[S] = zSpan S`
(`Submodule.subset_span`); this is all the weakened `IsCoherent` interface
supplies, and all it needs to. -/
noncomputable def ofIsCoherent
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hτ : OddOrder.Peterfalvi.S07.IsCoherent (L := L) (G := G) τ S A)
    {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A) :
    IndChainDecomposition (L := L) (G := G) τ ζ d where
  χ t := hτ.extension (ζ t)
  norm_one t := by
    rw [hτ.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem t)), hζ_norm]
  pairwise_inner_zero t u htu := by
    rw [hτ.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem u)), hζ_pairwise htu]
  d_zero := hd_zero
  image_eq t := by
    rw [← hτ.extends_on_supported _ (hsupp t), LinearMap.map_sub, map_zsmul]


end IndChainDecomposition

namespace SibleyDadeHypothesis

/-- **(6.8.1) → (7.10), Frobenius case:** an `IndChainDecomposition` from the
base-anchor common-index p-power X-chain data and generator-level `τ₃` glue.

This is the S09-facing consumer form of the Frobenius/c1 capstone: it first builds the full
`hyp.CoherenceTarget` using the base-anchor X-chain constructor and final generator-level glue, then
turns that coherence witness into the `IndChainDecomposition` package used by the §9 weighted-sum
argument. -/
noncomputable def
    indChainDecomposition_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
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
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x =
        (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
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
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction ↥L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ hyp.S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    IndChainDecomposition (L := ↥L) (G := G) hyp.tau ζ d := by
  exact IndChainDecomposition.ofIsCoherent
    (hyp.coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
      hF hXne hstepData ν hagreeX hagreeY hmixed hgen)
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08
