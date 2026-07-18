/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki.Simplicity
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesis

/-!
# Peterfalvi Part II, Chapter I §3, Lemma 1 — the `Sz(q)` target

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Chapter I §3, p. 105.

This file discharges the target-group inputs to Lemma 1 when the normal
subgroup supplied by Theorem A is the standard Suzuki group `Sz(q)` acting on
its ovoid, with `q = 2^(2m+1)` and `0 < m`.  Peterfalvi cites
Huppert--Blackburn, Chapter XI, Theorems 3.3 and 3.6 for the standard-action
degree and simplicity; here both come from the concrete constructed group.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis

universe u v

variable {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega] [Finite G]

section /- 3: Application of the Induction Hypothesis (pp. 105–107) -/

open OddOrder.GroupTheory.SpecificGroups.Suzuki

omit [Finite G] in
/-- **Peterfalvi Part II, Chapter I §3, Lemma 1 (`Sz(q)` degree input).**
For the standard Suzuki action on its ovoid, the degree minus one is a power
of two. -/
theorem suzuki_degree_twoPower {m : ℕ} {L : Subgroup G}
    (eL : L ≃* standardPermGroup m)
    (eOmega : Omega →ₑ[eL.toMonoidHom] Ovoid m)
    (heOmega : Function.Bijective eOmega) :
    ∃ n : ℕ, Nat.card Omega - 1 = 2 ^ n := by
  let e : Omega ≃ Ovoid m := Equiv.ofBijective eOmega heOmega
  refine ⟨2 * (2 * m + 1), ?_⟩
  calc
    Nat.card Omega - 1 = Nat.card (Ovoid m) - 1 := by
      rw [Nat.card_congr e]
    _ = 2 ^ (2 * (2 * m + 1)) := by
      rw [Ovoid.natCard, Nat.add_sub_cancel]

omit [Finite G] in
/-- **Peterfalvi Part II, Chapter I §3, Lemma 1 (`Sz(q)` simplicity input).**
For `0 < m`, every group concretely isomorphic to the standard Suzuki
permutation group is simple. -/
theorem suzuki_target_simple {m : ℕ} (hm : 0 < m) {L : Subgroup G}
    (eL : L ≃* standardPermGroup m) : IsSimpleGroup L := by
  letI : IsSimpleGroup (standardPermGroup m) :=
    standardPermGroup_isSimpleGroup hm
  exact eL.isSimpleGroup

/-- **Peterfalvi Part II, Chapter I §3, Lemma 1, `Sz(q)` case.**
Concrete standard ovoid coordinates for `L ≅ Sz(q)`, with `q = 2^(2m+1)`
and `0 < m`, imply that `Q` is a `2`-group and identify both `O^{2′}(G)`
and the join of the conjugates of `Q` with `L`. -/
theorem Q_and_residual_of_suzuki_target (hyp : Hypothesis G Omega)
    (L : Subgroup G) (hLnormal : L.Normal) (hLodd : Odd L.index)
    {m : ℕ} (hm : 0 < m)
    (eL : L ≃* standardPermGroup m)
    (eOmega : Omega →ₑ[eL.toMonoidHom] Ovoid m)
    (heOmega : Function.Bijective eOmega) :
    IsPGroup 2 hyp.Q ∧
      hyp.Q ≤ L ∧
      L = Subgroup.primeComplementResidual 2 G ∧
      L = (⨆ g : G, hyp.Q.map (MulAut.conj g).toMonoidHom) := by
  exact hyp.simple_normal_oddIndex_Q_core L hLnormal hLodd
    (suzuki_target_simple hm eL)
    (suzuki_degree_twoPower eL eOmega heOmega)

end

end OddOrder.Peterfalvi.Appendices.Suzuki.Hypothesis
