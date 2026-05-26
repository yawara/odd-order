/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_Coherence
import Mathlib.GroupTheory.Solvable

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

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

/- 6: Some coherence theorems (pp. 30-37) -/

/-- Peterfalvi (6.1): solvable-normal filtration setup for applying coherence
descent. -/
structure DescentHypothesis (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  coherence : OddOrder.Peterfalvi.S07.Hypothesis (L := L) (G := G) S A
  K : Subgroup L
  K_normal : K.Normal
  K_solvable : IsSolvable K
  filtration : Subgroup L → Set (ClassFunction L ℂ)

/-- Peterfalvi (6.4): the odd-order specialization used before (6.5)-(6.6). -/
structure OddOrderSpecialization (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] : Type _ extends
    DescentHypothesis (L := L) (G := G) S A where
  card_L_odd : Odd (Nat.card L)
  M : Subgroup L
  M_le_K : M ≤ K
  quotient_nilpotent : Prop

/-- Peterfalvi (6.8): the final §8 setup that packages a coherent input and a
TI-subset condition. -/
structure SibleySetup (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] : Type _ extends
    OddOrderSpecialization (L := L) (G := G) S A where
  H : Subgroup L
  W1 : Subgroup L
  H_normal : H.Normal
  H_sharp_ti :
    OddOrder.GroupTheory.IsTISubset ((H : Set L) \ {1})
      (Subgroup.normalizer (H : Set L))
  W1_nontrivial : W1 ≠ ⊥

namespace SibleySetup

variable {S : Set (ClassFunction L ℂ)} {A : Set L}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The coherence target carried by the setup.  Later §8 theorems prove this
under the numerical and class-sum hypotheses. -/
abbrev CoherenceTarget (hyp : SibleySetup (L := L) (G := G) S A) :=
  OddOrder.Peterfalvi.S07.Hypothesis.IsCoherentTarget hyp.coherence

theorem coherence_tau_inner_eq (hyp : SibleySetup (L := L) (G := G) S A)
    (φ ψ : ClassFunction L ℂ) :
    ClassFunction.inner (hyp.coherence.tau φ) (hyp.coherence.tau ψ) =
      ClassFunction.inner φ ψ :=
  hyp.coherence.tau_inner_eq φ ψ

theorem coherence_inner_eq_on_supported
    (hyp : SibleySetup (L := L) (G := G) S A)
    (hcoh : hyp.CoherenceTarget) {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A)
    (hψ : ψ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A) :
    ClassFunction.inner (hyp.coherence.tau φ) (hyp.coherence.tau ψ) =
      ClassFunction.inner φ ψ :=
  hcoh.inner_eq_on_supported hφ hψ

end SibleySetup

end OddOrder.Peterfalvi.S08
