/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import OddOrder.GroupTheory.PRegularElement
import OddOrder.GroupTheory.RepresentationTheory.SumCharacterInvariants

/-!
# A character vanishing off the `p`-regular elements has degree divisible by `|G|_p`

**Navarro (3.18), the implication (b) ⟹ (c).**  If `χ` vanishes on every `p`-singular element of
`G`, then restricting to a Sylow `p`-subgroup `S` leaves only the identity term, so

`χ(1) = ∑_{x ∈ S} χ(x) = |S| · dim V^S`

by `sum_character_eq_card_mul_finrank_invariants`.  Since `χ(1) = dim V` and the coefficient field
has characteristic `0`, this is the divisibility `|G|_p ∣ dim V` in `ℕ` — i.e. the block of `χ`
has defect `0`.

Navarro states it as one link of the chain (3.18)(a)–(e); the direction proved here is the one
Brauer's proof of the Brauer–Suzuki theorem uses, through Theorem (7.2): if a generalised
decomposition number `d^t_{χ 1}` vanished, `χ` would vanish on all involutions, hence on all
`2`-singular elements, and the principal block would have defect `0` — contradicting
`d(B_0) = ν_p(|G|)`.

⚠ Only `Invertible (|S| : K)` is used, so no `p`-modular system is needed: the statement lives
entirely in ordinary character theory over a field of characteristic `0`.

## Main results

* `OddOrder.RepresentationTheory.Modular.ordProj_dvd_finrank_of_character_eq_zero`
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.GroupTheory

variable {K G V : Type*} [Field K] [CharZero K] [Group G] [Finite G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {p : ℕ}

/-- **`|G|_p ∣ χ(1)` for a character vanishing on the `p`-singular elements** (Navarro (3.18),
(b) ⟹ (c)).

Every `x ≠ 1` of a Sylow `p`-subgroup is a nontrivial `p`-element, hence `p`-singular, so the
character sum over `S` collapses to `χ(1)`; on the other hand it is `|S| · dim V^S`. -/
theorem ordProj_dvd_finrank_of_character_eq_zero [Fact p.Prime] (S : Sylow p G)
    (ρ : Representation K G V)
    (hvan : ∀ x : G, ¬ IsPRegular p x → ρ.character x = 0) :
    ordProj[p] (Nat.card G) ∣ Module.finrank K V := by
  classical
  let : Fintype ↥(S : Subgroup G) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(S : Subgroup G) = ordProj[p] (Nat.card G) := by
    rw [← Nat.card_eq_fintype_card]; exact S.card_eq_multiplicity
  have : Invertible ((Fintype.card ↥(S : Subgroup G) : ℕ) : K) := by
    refine invertibleOfNonzero ?_
    rw [hcard]
    exact_mod_cast pow_ne_zero _ (Fact.out (p := p.Prime)).pos.ne'
  -- only the identity term of `∑_{x ∈ S} χ(x)` survives
  have hsum : ∑ x : ↥(S : Subgroup G),
      Representation.character (ρ.comp (S : Subgroup G).subtype) x = ρ.character 1 := by
    refine Finset.sum_eq_single (1 : ↥(S : Subgroup G)) (fun x _ hx => ?_) fun h =>
      absurd (Finset.mem_univ _) h
    refine hvan (x : G) fun hreg => hx (Subtype.ext ?_)
    exact eq_one_of_isPElement_of_isPRegular
      (isPElement_of_mem_of_isPGroup S.isPGroup' x.2) hreg
  have hinv := OddOrder.RepresentationTheory.sum_character_eq_card_mul_finrank_invariants
    (ρ.comp (S : Subgroup G).subtype)
  rw [hsum, Representation.char_one, hcard] at hinv
  refine ⟨Module.finrank K
    (Representation.invariants (ρ.comp (S : Subgroup G).subtype)), ?_⟩
  exact_mod_cast hinv

end OddOrder.RepresentationTheory.Modular
