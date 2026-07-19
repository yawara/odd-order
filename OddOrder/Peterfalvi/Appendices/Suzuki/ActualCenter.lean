/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.ActualKActor
import OddOrder.Higman.Suzuki2Groups.CenterHomocyclic

/-!
# The actual Suzuki center and its Higman filtration

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §2, pp. 102–103, and Appendix III, theorem (a), p. 141;
G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 1, p. 83.

This leaf applies the abstract Higman abelian theorem to the actual
`K`-actor on `Q`. It identifies the concrete `Q₀` with the last nontrivial
Agemo layer of the center. It does not claim the reverse center inclusion:
that remaining statement is isolated exactly as the vanishing of the first
Agemo layer.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open OddOrder.Higman.Suzuki2Groups
open OddOrder.GroupTheory.Suzuki2Group

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

local instance centerCommGroup (P : Type*) [Group P] :
    CommGroup ↥(Subgroup.center P) :=
  { (inferInstance : Group ↥(Subgroup.center P)) with
    mul_comm := fun x y =>
      Subtype.ext ((Subgroup.mem_center_iff.mp x.2 y).symm) }

/-- The concrete `Q₀ ≤ Q` is exactly the subgroup consisting of the identity
and all central involutions of `Q`. -/
theorem Q0_subgroupOf_Q_eq_involutionSubgroup :
    hyp.Q0.subgroupOf hyp.Q = involutionSubgroup ↥hyp.Q := by
  ext x
  rw [involutionSubgroup, mem_omega1OfAbelian]
  change (x : G) ∈ hyp.Q0 ↔
    x ∈ Subgroup.center hyp.Q ∧ x ^ 2 = 1
  constructor
  · intro hx
    refine ⟨?_, Subtype.ext hx.1⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (hyp.Q0_le_centralizer_Q hx) (y : G) y.2)
  · rintro ⟨_, hx2⟩
    exact ⟨congrArg Subtype.val hx2, hyp.Q_le_H x.2⟩

/-- Higman Lemma 1 applied to the actual `K`-actor on `Q`: the center is
homocyclic, every invariant subgroup is an Agemo layer, and the concrete
`Q₀` is the last nontrivial layer. -/
theorem actualQ_center_homocyclic_and_invariant_eq_agemo
    (hQ : IsSuzuki2Group ↥hyp.Q) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ℕ), 0 < e ∧
      Nonempty (↥(Subgroup.center hyp.Q) ≃*
        (ι → Multiplicative (ZMod (2 ^ e)))) ∧
      (∀ U : Subgroup ↥(Subgroup.center hyp.Q),
        IsAInvariant (centerAction hyp.actualKActor) U →
          ∃ s ≤ e, U = Agemo ↥(Subgroup.center hyp.Q) 2 s) ∧
      (hyp.Q0.subgroupOf hyp.Q).subgroupOf (Subgroup.center hyp.Q) =
        Agemo ↥(Subgroup.center hyp.Q) 2 (e - 1) := by
  have htrans : ∀ x ∈ involutions ↥(Subgroup.center hyp.Q),
      ∀ y ∈ involutions ↥(Subgroup.center hyp.Q),
        ∃ k : hyp.actualKActor, centerAction hyp.actualKActor k x = y := by
    intro x hx y hy
    have hxQ : (x : hyp.Q) ∈ involutions ↥hyp.Q := by
      refine ⟨congrArg Subtype.val hx.1, ?_⟩
      intro h
      exact hx.2 (Subtype.ext h)
    have hyQ : (y : hyp.Q) ∈ involutions ↥hyp.Q := by
      refine ⟨congrArg Subtype.val hy.1, ?_⟩
      intro h
      exact hy.2 (Subtype.ext h)
    obtain ⟨k, hk, _⟩ :=
      hyp.actualKActor_actsRegularlyOnInvolutions
        (x : hyp.Q) hxQ (y : hyp.Q) hyQ
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hk
  obtain ⟨ι, hι, e, he, hε, hclass⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      (hQ.1.to_subgroup (Subgroup.center hyp.Q))
      (centerAction hyp.actualKActor) htrans
  obtain ⟨ε⟩ := hε
  refine ⟨ι, hι, e, he, ⟨ε⟩, hclass, ?_⟩
  calc
    (hyp.Q0.subgroupOf hyp.Q).subgroupOf (Subgroup.center hyp.Q) =
        (involutionSubgroup hyp.Q).subgroupOf (Subgroup.center hyp.Q) :=
      congrArg (fun U : Subgroup hyp.Q =>
        U.subgroupOf (Subgroup.center hyp.Q))
        (Q0_subgroupOf_Q_eq_involutionSubgroup hyp)
    _ = Agemo ↥(Subgroup.center hyp.Q) 2 (e - 1) :=
      involutionSubgroup_subgroupOf_center_eq_lastAgemoLayer hQ ε he

/-- For the actual `Q`, proving `Z(Q) = Q₀` is equivalent to the remaining
power-filtration statement that the first Agemo layer of the center vanishes. -/
theorem center_Q_eq_Q0_iff_agemo_one_eq_bot :
    Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q ↔
      Agemo ↥(Subgroup.center hyp.Q) 2 1 = ⊥ := by
  rw [Q0_subgroupOf_Q_eq_involutionSubgroup hyp]
  constructor
  · intro hcenter
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_agemo_iff_of_comm).mp hx
    have hyK : (y : hyp.Q) ∈ involutionSubgroup hyp.Q := by
      rw [← hcenter]
      exact y.2
    rw [involutionSubgroup, mem_omega1OfAbelian] at hyK
    have hy2 : y ^ 2 = 1 := Subtype.ext hyK.2
    simpa using hy2
  · intro hagemo
    apply le_antisymm
    · intro x hxZ
      let z : Subgroup.center hyp.Q := ⟨x, hxZ⟩
      have hzAg : z ^ 2 ∈ Agemo ↥(Subgroup.center hyp.Q) 2 1 := by
        simpa using
          (Agemo.mem_of_eq_pow (G := Subgroup.center hyp.Q)
            (p := 2) (n := 1) z)
      have hz2 : z ^ 2 = 1 := by
        rw [hagemo, Subgroup.mem_bot] at hzAg
        exact hzAg
      rw [involutionSubgroup, mem_omega1OfAbelian]
      exact ⟨hxZ, congrArg Subtype.val hz2⟩
    · intro x hx
      rw [involutionSubgroup, mem_omega1OfAbelian] at hx
      exact hx.1

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
