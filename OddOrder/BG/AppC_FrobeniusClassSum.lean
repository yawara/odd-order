/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_NormSet
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra

/-!
# BG Appendix C: Frobenius Class-Sum Bridge

Bender--Glauberman Appendix C, Lemma C.2, pp. 145--152.

This file connects the finite-field pair set in `AppC_NormSet` to the conjugacy
class language used by the class-sum structure constants.  The finite-field leaf
keeps the concrete norm and semidirect-product setup; this file is the first
class-sum dependent layer for the `q >= 5` branch of Lemma C.2.
-/

namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

variable (p q : ℕ)

/-- The conjugacy class in `H = P ⋊ U` of the additive-kernel element attached to
`s ∈ 𝔽_{p^q}`.  BG Lemma C.2 uses the class of a nonzero `s ∈ P`. -/
noncomputable def normOneClassAt [Fact p.Prime] (s : GaloisField p q) :
    ConjClasses (normOneFrobeniusGroup p q) :=
  ConjClasses.mk
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q)

/-- Every `U`-translate `u*s` lies in the conjugacy class of `s` inside
`H = P ⋊ U`.  This is the class-language form of `u s u⁻¹ = u*s`. -/
theorem normOneClassAt_mul_eq [Fact p.Prime] (s : GaloisField p q)
    (u : normOneUnits p q) :
    ConjClasses.mk
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q) = normOneClassAt p q s := by
  unfold normOneClassAt
  apply Eq.symm
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  refine isConj_iff.mpr ⟨SemidirectProduct.inr u, ?_⟩
  simpa using normOneFrobenius_conj_inl p q u s

/-- A pair counted by `normOnePairSetAt s` gives a class-pair counted by the
class-sum structure constants for the class of `s` and the class of `2*s` in
`H = P ⋊ U`.  This is the one-way bridge needed before proving that the
finite-field pair count is exactly the relevant class-sum coefficient. -/
theorem normOnePairSetAt_isClassPair [Fact p.Prime] (s : GaloisField p q)
    {u v : normOneUnits p q} (h : (u, v) ∈ normOnePairSetAt p q s) :
    IsClassPair (normOneClassAt p q s) (normOneClassAt p q s)
      (normOneClassAt p q ((2 : GaloisField p q) * s))
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact normOneClassAt_mul_eq p q s u
  · exact normOneClassAt_mul_eq p q s v
  · have hmul := (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mp h
    rw [hmul]
    rfl

end OddOrder.BG.AppC.NormSet
