/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BrauerKernel
import OddOrder.Algebra.DefectGroup
import OddOrder.Algebra.MackeyFormula

/-!
# The Brauer homomorphism sees only the defect group

If `b` is a relative trace from `D` — for a block idempotent, if `D` contains a defect group —
then `Br_P(b) = 0` for every `p`-subgroup `P` that is not contained in a conjugate of `D`.

The proof is Mackey plus the kernel computation.  Restricting `Tr^G_D(a)` to `P` breaks it into
`∑_{g} Tr^P_{P ∩ ᵍD}(g · a)` over the double cosets, and `Br_P` annihilates a relative trace from
any *proper* subgroup of `P`.  A term therefore survives only when `P ∩ ᵍD = P`, i.e. when
`P ≤ ᵍD`.

Read contrapositively: `Br_P(b) ≠ 0` forces `P` into a conjugate of `D` — apply it to a defect
group via `IsDefectGroup.mem`.  This is the half of
Brauer's first main theorem that bounds the `p`-subgroups a block can see; together with the
converse (`Br_D(e_B) ≠ 0`) it characterises the defect group as the largest `P` with
`Br_P(e_B) ≠ 0`.

## Main results

* `OddOrder.GroupAlgebra.exists_le_conj_of_brauerProj_ne_zero`
* `OddOrder.GroupAlgebra.brauerProj_eq_zero_of_forall_not_le`
* `OddOrder.GroupAlgebra.card_le_card_of_brauerProj_ne_zero`
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra

open scoped OddOrder.Conjugation Pointwise

variable {k : Type*} [CommRing k] {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- **`Br_P` kills a relative trace from `D` unless `P` lies inside a conjugate of `D`.**

Mackey writes `Tr^G_D(a)` restricted to `P` as `∑_g Tr^P_{P ∩ ᵍD}(g · a)`, and `Br_P` annihilates
relative traces from proper subgroups of `P` (`brauerProj_relTrace_eq_zero`). -/
theorem brauerProj_eq_zero_of_forall_not_le [Fact p.Prime] (hchar : (p : k) = 0)
    {P D : Subgroup G} (hP : IsPGroup p ↥P) {b : MonoidAlgebra k G}
    (hb : b ∈ GAlgebra.relTraceIdeal D ⊤) (hnle : ∀ g : G, ¬ P ≤ MulAut.conj g • D) :
    brauerProj P b = 0 := by
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨s, hs⟩ := GAlgebra.exists_mackey P ha
  rw [hs, ← brauerProjHom_apply, map_sum]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [brauerProjHom_apply]
  have hlt : P ⊓ MulAut.conj g • D < P :=
    lt_of_le_of_ne inf_le_left fun heq => hnle g (heq ▸ inf_le_right)
  exact brauerProj_relTrace_eq_zero hchar (dvd_relIndex_of_lt_of_isPGroup hP hlt) _

/-- **`Br_P(b) ≠ 0` forces `P` into a conjugate of `D`.**  Contrapositive of
`brauerProj_eq_zero_of_forall_not_le`; for a block idempotent `b` with defect group `D` this says
that the `p`-subgroups the block sees are exactly those subconjugate to `D`. -/
theorem exists_le_conj_of_brauerProj_ne_zero [Fact p.Prime] (hchar : (p : k) = 0)
    {P D : Subgroup G} (hP : IsPGroup p ↥P) {b : MonoidAlgebra k G}
    (hb : b ∈ GAlgebra.relTraceIdeal D ⊤) (hne : brauerProj P b ≠ 0) :
    ∃ g : G, P ≤ MulAut.conj g • D := by
  by_contra hcon
  push Not at hcon
  exact hne (brauerProj_eq_zero_of_forall_not_le hchar hP hb hcon)

omit [Finite G] in
/-- A conjugate subgroup has the same order. -/
theorem card_conj_smul (g : G) (D : Subgroup G) :
    Nat.card ↥(MulAut.conj g • D) = Nat.card ↥D :=
  Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) D).symm.toEquiv

/-- **The defect group bounds every `p`-subgroup the block sees.** -/
theorem card_le_card_of_brauerProj_ne_zero [Fact p.Prime] (hchar : (p : k) = 0)
    {P D : Subgroup G} (hP : IsPGroup p ↥P) {b : MonoidAlgebra k G}
    (hb : b ∈ GAlgebra.relTraceIdeal D ⊤) (hne : brauerProj P b ≠ 0) :
    Nat.card ↥P ≤ Nat.card ↥D := by
  obtain ⟨g, hg⟩ := exists_le_conj_of_brauerProj_ne_zero hchar hP hb hne
  exact (card_conj_smul g D) ▸
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hg)

end OddOrder.GroupAlgebra
