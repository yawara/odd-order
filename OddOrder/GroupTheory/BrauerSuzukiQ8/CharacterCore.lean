/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiQ8.Reduction

/-!
# Brauer–Suzuki, the `Q₈` case: the character-theoretic core (Navarro pp. 139–146)

`q8_exists_proper_normal` is the whole content of the `Q₈` branch: the involution of a proper
quaternion Sylow `2`-subgroup lies in a proper normal subgroup.  Navarro obtains it as the kernel
of a nontrivial character of the principal block, through the "analysis at `y`" and the "analysis
at `t`" of pp. 140–145.

The character-theoretic engine is `exists_proper_normal_of_columns`; every one of its hypotheses
has a supplier in `GroupTheory/RepresentationTheory/Modular/`, and this file is where they are
instantiated for the `Q₈` configuration (issue 9506).

## Main results

* `OddOrder.GroupTheory.q8_exists_proper_normal`
-/

open OddOrder.Isaacs.Ch03

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- **Navarro pp. 139–146, the character-theoretic core** (issue 9506, `sorry`): when the
quaternion Sylow `2`-subgroup is proper, its involution lies in a proper normal subgroup.

This is Navarro's "our objective is to find a nontrivial character in the principal block of `G`
which contains `t` in its kernel" — the kernel of such a character is the proper normal subgroup.
The proof occupies the eight pages pp. 139–146: a unique `G`-class of elements of order `4`
(fusion control plus `Aut(Q₈) = Sym(4)`), then the "analysis at `y`" and "analysis at `t`" with
the principal-block basic set of Navarro (7.3)/(7.4), for which the integral change-of-basis
matrix `intBasicSetMatrix` (issue 9508, closed) is the prerequisite. -/
theorem q8_exists_proper_normal (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤)
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ z ∈ N := by
  sorry

end OddOrder.GroupTheory
