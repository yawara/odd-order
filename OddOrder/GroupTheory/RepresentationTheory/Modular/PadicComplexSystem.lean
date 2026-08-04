/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.Valuation.LocalSubring
import OddOrder.Algebra.AlgClosedFractionField
import OddOrder.GroupTheory.RepresentationTheory.Modular.SplittingSystem

/-!
# A splitting `p`-modular system: the valuation ring of `ℂ_[p]`

`StandardSystem p = 𝕎(𝔽̄_p)` is a `p`-modular system whose *residue* field is algebraically
closed, which is all that the Brauer-character side needs.  Its fraction field is the completion
of the maximal unramified extension of `ℚ_[p]`, and that is **not** a splitting field for `K[G]`:
it contains every `p'`-th root of unity but no primitive `p`-th root of unity, since
`ℚ_[p](ζ_p)/ℚ_[p]` is totally ramified of degree `p - 1`.  Ordinary character values of a group of
order divisible by `p` generally fall outside it.  Everything indexed by `Irr(G)` — the rows of the
decomposition matrix, the Cartan matrix `C = DᵀD` — therefore has no home over `𝕎(𝔽̄_p)`
(issue 9507).

This file supplies a `p`-modular system that *does* split, by giving up discreteness of the
valuation instead of giving up splitness:

`𝓞_ℂ_[p]`, the valuation ring of the `p`-adic complex numbers.

Its fraction field `ℂ_[p]` is algebraically closed, so it splits `K[G]` for every finite `G` with
no appeal to Brauer's splitting field theorem, and by `AlgClosedFractionField` its residue field is
algebraically closed of characteristic `p`, so it splits `k[G]` too.  The price is that `𝓞_ℂ_[p]`
is not Noetherian and not a discrete valuation ring — its value group is divisible — which is why
`BrauerLinearIndependence` is stated for valuation rings rather than for DVRs.

Being Henselian is free here and needs no completeness argument: the roots of a monic polynomial
are already in `𝓞_ℂ_[p]`, and `exists_isRoot_sub_mem_maximalIdeal` picks out the one in the right
residue class.

## Main results

* `OddOrder.RepresentationTheory.Modular.instIsPModularSystemPadicComplexInt`
* `OddOrder.RepresentationTheory.Modular.instIsAlgClosedResidueFieldPadicComplexInt`
* `OddOrder.RepresentationTheory.Modular.exists_isPrimitiveRoot_padicComplexInt` — every `p'`-th
  root of unity is present, upstairs and downstairs
* `OddOrder.RepresentationTheory.Modular.exists_algEquiv_pi_matrix_padicComplex` — `ℂ_[p]` splits
  `ℂ_[p][G]`, the property `𝕎(𝔽̄_p)` lacks
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### `𝓞_ℂ_[p]` is a `p`-modular system -/

instance : CharZero 𝓞_ℂ_[p] := RingHom.charZero (algebraMap 𝓞_ℂ_[p] ℂ_[p])

/-- `p` is not invertible in `𝓞_ℂ_[p]`: its valuation is `1/p < 1`. -/
theorem natCast_mem_maximalIdeal_padicComplexInt : (p : 𝓞_ℂ_[p]) ∈ maximalIdeal 𝓞_ℂ_[p] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hval := (PadicComplexInt.integers p).one_of_isUnit hu
  rw [map_natCast, PadicComplex.valuation_p] at hval
  have hp0 : (p : NNReal) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hval1 : (p : NNReal) = 1 := by rw [eq_comm, ← div_eq_one_iff_eq hp0]; exact hval
  refine hp.out.ne_one (Nat.cast_injective (R := NNReal) ?_)
  rw [Nat.cast_one]
  exact hval1

instance : CharP (ResidueField 𝓞_ℂ_[p]) p := by
  have h0 : (p : ResidueField 𝓞_ℂ_[p]) = 0 := by
    rw [← map_natCast (residue 𝓞_ℂ_[p]), residue_eq_zero_iff]
    exact natCast_mem_maximalIdeal_padicComplexInt p
  obtain ⟨q, hq⟩ := CharP.exists (ResidueField 𝓞_ℂ_[p])
  haveI := hq
  have hdvd : q ∣ p := (CharP.cast_eq_zero_iff _ q p).mp h0
  have hq1 : q ≠ 1 := by
    rintro rfl
    have h1 : ((1 : ℕ) : ResidueField 𝓞_ℂ_[p]) = 0 :=
      (CharP.cast_eq_zero_iff _ 1 1).mpr dvd_rfl
    rw [Nat.cast_one] at h1
    exact one_ne_zero h1
  rcases hp.out.eq_one_or_self_of_dvd q hdvd with h | h
  · exact absurd h hq1
  · rwa [h] at hq

instance : HenselianLocalRing 𝓞_ℂ_[p] := henselianLocalRing_of_isAlgClosed ℂ_[p]

instance instIsPModularSystemPadicComplexInt : IsPModularSystem p 𝓞_ℂ_[p] where

/-- **The residue field of `𝓞_ℂ_[p]` is algebraically closed** (it is `𝔽̄_p`).  This is what makes
the modular side — Brauer characters, the block decomposition, defect groups — unconditional. -/
instance instIsAlgClosedResidueFieldPadicComplexInt : IsAlgClosed (ResidueField 𝓞_ℂ_[p]) :=
  isAlgClosed_residueField ℂ_[p]

/-! ### Roots of unity

Everything the Brauer-character side asks of the coefficient ring is now available: the residue
field is algebraically closed of characteristic `p`, so it has every `p'`-th root of unity, and
the Henselian lift moves them up into `𝓞_ℂ_[p]`. -/

/-- The residue field of `𝓞_ℂ_[p]` has all `n`-th roots of unity for `p ∤ n`: it is algebraically
closed of characteristic `p`. -/
theorem hasEnoughRootsOfUnity_residueField_padicComplexInt {n : ℕ} (hn : ¬ p ∣ n) (hn0 : n ≠ 0) :
    HasEnoughRootsOfUnity (ResidueField 𝓞_ℂ_[p]) n :=
  hasEnoughRootsOfUnity_of_isAlgClosed p n _ hn hn0

/-- **`𝓞_ℂ_[p]` has all `n`-th roots of unity for `p ∤ n`.** -/
theorem hasEnoughRootsOfUnity_padicComplexInt {n : ℕ} (hn : ¬ p ∣ n) (hn0 : n ≠ 0) :
    HasEnoughRootsOfUnity 𝓞_ℂ_[p] n := by
  haveI : NeZero n := ⟨hn0⟩
  haveI := hasEnoughRootsOfUnity_residueField_padicComplexInt p hn hn0
  exact hasEnoughRootsOfUnity_of_residueField (p := p) hn

/-- A primitive `n`-th root of unity exists in `𝓞_ℂ_[p]` for every `n` prime to `p`.  Together
with the residue-field version this supplies both `ω` and `ω'` of the decomposition matrix. -/
theorem exists_isPrimitiveRoot_padicComplexInt {n : ℕ} (hn : ¬ p ∣ n) (hn0 : n ≠ 0) :
    ∃ ζ : 𝓞_ℂ_[p], IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn0⟩
  haveI := hasEnoughRootsOfUnity_padicComplexInt p hn hn0
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ n

/-- The residue-field companion of `exists_isPrimitiveRoot_padicComplexInt`. -/
theorem exists_isPrimitiveRoot_residueField_padicComplexInt {n : ℕ} (hn : ¬ p ∣ n) (hn0 : n ≠ 0) :
    ∃ ζ : ResidueField 𝓞_ℂ_[p], IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn0⟩
  haveI := hasEnoughRootsOfUnity_residueField_padicComplexInt p hn hn0
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ n

/-! ### `ℂ_[p]` is a splitting field -/

/-- **`ℂ_[p]` splits `ℂ_[p][G]`.**  Maschke makes the group algebra semisimple (the characteristic
is `0`), it is finite-dimensional, and Wedderburn–Artin over an algebraically closed field writes a
finite-dimensional semisimple algebra as a product of *full matrix algebras over the field itself*.

This is the property that `Frac(𝕎(𝔽̄_p))` lacks, and it is what lets `Irr(G)` be indexed by the
Wedderburn components — the row index of the decomposition matrix. -/
theorem exists_algEquiv_pi_matrix_padicComplex (G : Type*) [Group G] [Finite G] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra ℂ_[p] G ≃ₐ[ℂ_[p]] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ_[p]) := by
  haveI : NeZero (Nat.card G : ℂ_[p]) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ_[p] (MonoidAlgebra ℂ_[p] G)

end OddOrder.RepresentationTheory.Modular
