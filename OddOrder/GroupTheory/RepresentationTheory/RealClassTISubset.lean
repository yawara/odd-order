/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutation
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.TISubset

/-!
# Real classes under a TI Sylow setup: the Peterfalvi (6.7.3) real-class atom

This module discharges the **real-class atom** of **Peterfalvi (6.7.3)** (T. Peterfalvi,
*Character Theory for the Odd Order Theorem*, LMS LNS 272, 2000, §4.8, p. 33): in the (6.7) setup —
`P` a Sylow `p`-subgroup of `G`, `L = N_G(P)` of *odd order*, and `P^# = P ∖ {1}` a TI-subset of
`G` with normalizer-bound `L` — a nontrivial element `z ∈ P` is **not** `G`-conjugate to its
inverse.

This is the opening line of Peterfalvi's proof of (6.7.3):

> *Since `|L|` is odd, `z⁻¹` is not conjugate to `z` in `G`.*

(`references/peterfalvi/04.8_pp_30_37_Some_Coherence_Theorems.mmd` L122.)

## Why it lives here (not in `ClassSumAlgebra`)

The statement consumed by (6.7.3) is the structure-constant atom `a_{110} = 0`
(`OddOrder.RepresentationTheory.classSumCoeff_self_one_eq_zero` in `ClassSumAlgebra.lean`), whose
*sole* remaining hypothesis is the real-class atom `⟦z⁻¹⟧ ≠ ⟦z⟧`.  The TI-reduction that proves
that atom calls `ConjClasses.eq_one_of_isConj_inv_of_odd_card` (an element conjugate to its inverse
in a finite group of odd order is trivial), which lives in `BrauerPermutation.lean`.  Importing
`BrauerPermutation` into `ClassSumAlgebra` would close the cycle
`ClassSumAlgebra ← ZIrr ← IrrIndexing ← BrauerPermutation`, so the reduction is placed here, in a
leaf module downstream of both.

## Main results

* `OddOrder.RepresentationTheory.not_isConj_inv_of_isTISubset` — `¬ IsConj z⁻¹ z` for a nontrivial
  `z ∈ P` under the odd-order TI Sylow setup.
* `OddOrder.RepresentationTheory.mk_inv_ne_self_of_isTISubset` — its class-level form
  `⟦z⁻¹⟧ ≠ ⟦z⟧`, the exact hypothesis fed to `classSumCoeff_self_one_eq_zero`.

## References

* Peterfalvi, *Character Theory for the Odd Order Theorem*, (6.7.3) (proof opening line).
* `ConjClasses.eq_one_of_isConj_inv_of_odd_card` (`BrauerPermutation.lean`): the group-theoretic
  core that an element conjugate to its inverse in a finite group of odd order is trivial.
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Peterfalvi (6.7.3), real-class atom (TI-reduction).** In the (6.7) setup — `P ∈ Syl_p(G)`,
`L = N_G(P)` of odd order, and `P^# = P ∖ {1}` a TI-subset of `G` with normalizer-bound `L` — a
nontrivial `z ∈ P` is **not** `G`-conjugate to its inverse.

This is Peterfalvi's "since `|L|` is odd, `z⁻¹` is not conjugate to `z` in `G`".

Proof.  Both `z, z⁻¹ ∈ P^#`.  A `G`-conjugator `c` with `c z⁻¹ c⁻¹ = z` carries `z⁻¹ ∈ P^#` to
`z ∈ P^#`, so by the TI property `c ∈ L`.  As `P ≤ L`, also `z ∈ L`; reading the conjugacy inside
the finite group `L` of odd order, `z` is `L`-conjugate to `z⁻¹`, so
`ConjClasses.eq_one_of_isConj_inv_of_odd_card` forces `z = 1`, contradicting `z ≠ 1`. -/
theorem not_isConj_inv_of_isTISubset {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hodd : Odd (Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G))))
    (hti : IsTISubset ((P : Set G) \ {1}) (Subgroup.normalizer (P : Subgroup G)))
    {z : G} (hzP : z ∈ (P : Subgroup G)) (hz1 : z ≠ 1) :
    ¬ IsConj z⁻¹ z := by
  intro hconj
  -- Bind `L = N_G(P)` once; `hodd`/`hti` fold onto it.
  set L : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G) with hL
  -- `L` is finite: its order is odd, hence nonzero.
  have hcard_ne : Nat.card L ≠ 0 := by rcases hodd with ⟨k, hk⟩; omega
  haveI : Finite L := (Nat.card_ne_zero.mp hcard_ne).2
  -- `z, z⁻¹ ∈ P^# = P ∖ {1}`.
  have hzA : z ∈ (P : Set G) \ {1} := ⟨hzP, by simpa using hz1⟩
  have hzinvA : z⁻¹ ∈ (P : Set G) \ {1} :=
    ⟨inv_mem hzP, by simpa using inv_ne_one.mpr hz1⟩
  -- A `G`-conjugator: `c z⁻¹ c⁻¹ = z`.
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  -- `c` carries `z⁻¹ ∈ P^#` to `z ∈ P^#`, so the TI property puts `c ∈ L`.
  have hcL : c ∈ L := hti c ⟨z⁻¹, hzinvA, by rw [hc]; exact hzA⟩
  -- `P ≤ L`, so `z ∈ L` (and `z⁻¹ ∈ L` as `(⟨z, hzL⟩ : L)⁻¹`).
  have hzL : z ∈ L := by rw [hL]; exact (P : Subgroup G).le_normalizer hzP
  -- Read the conjugacy inside `L`: `IsConj (⟨z, _⟩⁻¹) ⟨z, _⟩`.
  have hconjL : IsConj (⟨z, hzL⟩ : L)⁻¹ ⟨z, hzL⟩ := by
    rw [isConj_iff]
    refine ⟨⟨c, hcL⟩, ?_⟩
    apply Subtype.ext
    change c * z⁻¹ * c⁻¹ = z
    exact hc
  -- Odd order ⇒ `⟨z, _⟩ = 1`, i.e. `z = 1`, contradicting `z ≠ 1`.
  have hz1' : (⟨z, hzL⟩ : L) = 1 :=
    ConjClasses.eq_one_of_isConj_inv_of_odd_card hodd hconjL
  exact hz1 (by simpa using congrArg Subtype.val hz1')

/-- **Peterfalvi (6.7.3), real-class atom (class form).** Under the (6.7) odd-order TI Sylow setup,
the inverse class `⟦z⁻¹⟧` differs from `⟦z⟧` for nontrivial `z ∈ P`.  This is the exact hypothesis
consumed by `classSumCoeff_self_one_eq_zero` (the `a_{110} = 0` structure-constant atom of
(6.7.3)). -/
theorem mk_inv_ne_self_of_isTISubset {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hodd : Odd (Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G))))
    (hti : IsTISubset ((P : Set G) \ {1}) (Subgroup.normalizer (P : Subgroup G)))
    {z : G} (hzP : z ∈ (P : Subgroup G)) (hz1 : z ≠ 1) :
    ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z :=
  fun h => not_isConj_inv_of_isTISubset P hodd hti hzP hz1
    (ConjClasses.mk_eq_mk_iff_isConj.mp h)

end OddOrder.RepresentationTheory
