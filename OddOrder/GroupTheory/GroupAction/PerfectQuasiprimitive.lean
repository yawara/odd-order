/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect quasiprimitive groups with a solvable point stabilizer

A nontrivial perfect group acting faithfully and quasiprimitively is simple when one
point stabilizer is solvable.  The proof sends the stabilizer onto every quotient
by a nontrivial normal subgroup and compares solvability with perfectness.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

open MulAction

/-- A faithful quasiprimitive action of a nontrivial perfect group with a solvable
point stabilizer has simple acting group. -/
theorem isSimpleGroup_of_isPerfect_of_isQuasiPreprimitive_of_isSolvable_stabilizer
    {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
    [IsQuasiPreprimitive G Ω] [Nontrivial G] [Group.IsPerfect G]
    (base : Ω) [IsSolvable (stabilizer G base)] :
    IsSimpleGroup G := by
  apply IsSimpleGroup.mk
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · right
    letI : N.Normal := hN
    have hfixed : fixedPoints N Ω ≠ Set.univ := by
      intro h
      apply hNbot
      rw [Subgroup.eq_bot_iff_forall]
      intro n hn
      apply (inferInstance : FaithfulSMul G Ω).eq_of_smul_eq_smul
      intro x
      rw [one_smul]
      exact Set.eq_univ_iff_forall.mp h x ⟨n, hn⟩
    letI : IsPretransitive N Ω :=
      IsQuasiPreprimitive.isPretransitive_of_normal hfixed
    let f : stabilizer G base →* G ⧸ N :=
      (QuotientGroup.mk' N).comp (stabilizer G base).subtype
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N base (g • base)
      let b : G := (n : G)⁻¹ * g
      have hb : b ∈ stabilizer G base := by
        rw [mem_stabilizer_iff]
        dsimp [b]
        rw [mul_smul, inv_smul_eq_iff]
        exact hn.symm
      refine ⟨⟨b, hb⟩, ?_⟩
      change QuotientGroup.mk' N b = QuotientGroup.mk' N g
      dsimp [b]
      rw [(QuotientGroup.eq_one_iff (n : G)).mpr n.property, inv_one, one_mul]
    letI : IsSolvable (G ⧸ N) := solvable_of_surjective hf
    have hsub : Subsingleton (G ⧸ N) := by
      by_contra h
      letI : Nontrivial (G ⧸ N) := not_subsingleton_iff_nontrivial.mp h
      exact (Group.IsPerfect.not_isSolvable (G ⧸ N)) inferInstance
    exact QuotientGroup.subgroup_eq_top_of_subsingleton N hsub

end OddOrder.GroupTheory
