/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralCharacterTrace
import OddOrder.GroupTheory.RepresentationTheory.SumCharacterInvariants

/-!
# Navarro (4.19): the character formula for `|Ω_{K,L}|`

`Ω_{K,L} = {(u, y) ∈ K × L : u y⁻¹ ∈ P}` counts, after the reindexing `(u,y) ↦ (u y⁻¹, y)`, the
elements of `P` weighted by the structure constants of `K̂ · (L⁻¹)^`:

`|Ω_{K,L}| = ∑_{x ∈ P} (K̂ · L̂')_x`,  `L' = L⁻¹`.

Feeding Burnside's class-multiplication formula
(`sum_centralScalar_mul_character_eq_card_mul_coeff`) into that sum and collapsing
`∑_{x ∈ P} χ(x⁻¹) = |P| · dim V^P` (`sum_character_eq_card_mul_finrank_invariants`) gives the
**division-free** form of Navarro (4.19):

`|G| · ∑_{x ∈ P} (K̂ · L̂')_x = |P| · ∑_χ ω_χ(K̂) ω_χ(L̂') χ(1) · dim V_χ^P`.

Navarro divides by `p^{a-d(K)}` at this point; here both sides are kept integral, so the
statement holds over the splitting field with no valuation bookkeeping.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_pSubgroup_coeff_classSum_mul`
* `OddOrder.RepresentationTheory.Modular.ordCompl_mul_sum_sylow_coeff_classSum_mul` — with the
  `p`-part cancelled
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.GroupTheory.CenterClassSum

variable {K G : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
  [DecidableEq (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι'] [Invertible (Nat.card G : K)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

set_option maxHeartbeats 800000 in
-- Burnside and the invariants count are applied under the same instance chains.
/-- **Navarro (4.19), division-free.**  Summing Burnside's formula over a subgroup `P` replaces
`χ(x⁻¹)` by `|P|` times the dimension of the `P`-invariants. -/
theorem sum_pSubgroup_coeff_classSum_mul (P : Subgroup G) [Fintype ↥P] (C D : ConjClasses G) :
    (Nat.card G : K) * ∑ x : ↥P, (classSum (k := K) C * classSum (k := K) D).coeff (x : G)
      = (Fintype.card ↥P : K) * ∑ i : ι',
          MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)
            * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum D)
            * (wedderburnRepresentation e i).character 1
            * (Module.finrank K (Representation.invariants
                ((wedderburnRepresentation e i).comp P.subtype)) : K) := by
  classical
  have : Invertible (Fintype.card ↥P : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- Burnside, summed over `P`
  have hburn : ∀ x : ↥P, (Nat.card G : K)
      * (classSum (k := K) C * classSum (k := K) D).coeff (x : G)
      = ∑ i : ι', MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)
          * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum D)
          * (wedderburnRepresentation e i).character 1
          * (wedderburnRepresentation e i).character (x : G)⁻¹ := fun x =>
    (sum_centralScalar_mul_character_eq_card_mul_coeff e C D (x : G)).symm
  rw [Finset.mul_sum, Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hburn x,
    Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- collapse the inner sum over `P`
  rw [← Finset.mul_sum]
  have hinv : ∑ x : ↥P, (wedderburnRepresentation e i).character (x : G)⁻¹
      = ∑ x : ↥P, Representation.character
          ((wedderburnRepresentation e i).comp P.subtype) x := by
    rw [← Equiv.sum_comp (Equiv.inv ↥P) (fun x : ↥P => Representation.character
      ((wedderburnRepresentation e i).comp P.subtype) x)]
    exact Finset.sum_congr rfl fun x _ => rfl
  rw [hinv, OddOrder.RepresentationTheory.sum_character_eq_card_mul_finrank_invariants]
  ring

/-! ### Cancelling the `p`-part -/

set_option maxHeartbeats 800000 in
-- The Sylow cardinality and the cancellation are done under the same instance chains.
/-- **Navarro (4.19), with the `p`-part cancelled.**  For a Sylow `p`-subgroup `S` the two `p^a`
factors in `sum_pSubgroup_coeff_classSum_mul` cancel, leaving

`|G|_{p'} · |Ω_{K,L}| = ∑_χ ω_χ(K̂) ω_χ(L̂') χ(1) · dim V_χ^S`,

an identity between elements of the valuation ring with no `p` in sight.  This is the form in
which Navarro's `|Ω_{K,L}|/p^{a-d(K)}` normalisation is used. -/
theorem ordCompl_mul_sum_sylow_coeff_classSum_mul {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    [Fintype ↥(S : Subgroup G)] (C D : ConjClasses G) :
    ((ordCompl[p] (Nat.card G) : ℕ) : K)
        * ∑ x : ↥(S : Subgroup G), (classSum (k := K) C * classSum (k := K) D).coeff (x : G)
      = ∑ i : ι', MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)
          * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum D)
          * (wedderburnRepresentation e i).character 1
          * (Module.finrank K (Representation.invariants
              ((wedderburnRepresentation e i).comp (S : Subgroup G).subtype)) : K) := by
  classical
  have hbase := sum_pSubgroup_coeff_classSum_mul e (S : Subgroup G) C D
  have hcard : Fintype.card ↥(S : Subgroup G) = ordProj[p] (Nat.card G) := by
    rw [← Nat.card_eq_fintype_card]
    exact S.card_eq_multiplicity
  have hsplit : (Nat.card G : K)
      = ((ordProj[p] (Nat.card G) : ℕ) : K) * ((ordCompl[p] (Nat.card G) : ℕ) : K) := by
    rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have hne : ((ordProj[p] (Nat.card G) : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out (p := p.Prime)).pos.ne')
  refine mul_left_cancel₀ hne ?_
  rw [← mul_assoc, ← hsplit, hbase, hcard]

end OddOrder.RepresentationTheory.Modular
