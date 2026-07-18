/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.Simplicity
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesis

/-!
# Peterfalvi Part II, Chapter I §3, Lemma 1 — the `PSU(3,q)` target

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Chapter I §3, p. 105.

This file discharges the target-group inputs to Lemma 1 when the normal
subgroup supplied by Theorem A is the standard projective unitary group
`PSU(3,q)` acting on its Hermitian unital, with `q = 2^n` and `q > 2`
(equivalently, `1 < n`). Peterfalvi cites Huppert, Kapitel II, Sätze 10.12
and 10.13 for the standard-action degree and simplicity; here both come from
the concrete constructed permutation group.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega] [Finite G]

section /- 3: Application of the Induction Hypothesis (pp. 105–107) -/

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

omit [Finite G] in
/-- **Peterfalvi Part II, Chapter I §3, Lemma 1 (`PSU(3,q)` degree input).**
For the standard projective unitary action on its Hermitian unital, with
`q = 2^n`, the degree minus one is the power of two `2^(3*n)`. -/
theorem psu3_degree_twoPower {n : ℕ} (hn : 0 < n) {L : Subgroup G}
    (eL : L ≃* standardPermGroup n)
    (eOmega : Omega →ₑ[eL.toMonoidHom] Unital n)
    (heOmega : Function.Bijective eOmega) :
    ∃ k : ℕ, Nat.card Omega - 1 = 2 ^ k := by
  let e : Omega ≃ Unital n := Equiv.ofBijective eOmega heOmega
  refine ⟨3 * n, ?_⟩
  calc
    Nat.card Omega - 1 = Nat.card (Unital n) - 1 := by
      rw [Nat.card_congr e]
    _ = 2 ^ (3 * n) := by
      rw [Unital.natCard n hn, Nat.add_sub_cancel]

omit [Finite G] in
/-- **Peterfalvi Part II, Chapter I §3, Lemma 1 (`PSU(3,q)` simplicity input).**
For `q = 2^n > 2`, every group concretely isomorphic to the standard
projective unitary permutation group is simple. -/
theorem psu3_target_simple {n : ℕ} (hn : 1 < n) {L : Subgroup G}
    (eL : L ≃* standardPermGroup n) : IsSimpleGroup L := by
  letI : IsSimpleGroup (standardPermGroup n) :=
    standardPermGroup_isSimpleGroup hn
  exact eL.isSimpleGroup

/-- **Peterfalvi Part II, Chapter I §3, Lemma 1, `PSU(3,q)` case.**
Concrete Hermitian-unital coordinates for `L ≅ PSU(3,q)`, with `q = 2^n > 2`,
imply that `Q` is a `2`-group and identify both `O^{2′}(G)` and the join of
the conjugates of `Q` with `L`. -/
theorem Q_and_residual_of_psu3_target (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    {n : ℕ} (hn : 1 < n)
    (eL : L ≃* standardPermGroup n)
    (eOmega : Omega →ₑ[eL.toMonoidHom] Unital n)
    (heOmega : Function.Bijective eOmega) :
    IsPGroup 2 hyp.Q ∧
      hyp.Q ≤ L ∧
      L = Subgroup.primeComplementResidual 2 G ∧
      L = (⨆ g : G, hyp.Q.map (MulAut.conj g).toMonoidHom) := by
  exact hyp.simple_normal_oddIndex_Q_core L hLnormal hLodd
    (psu3_target_simple hn eL)
    (psu3_degree_twoPower (by omega) eL eOmega heOmega)

end

end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
