/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanAbelian

/-!
# Higman Lemma 2: normal abelian invariant subgroups

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 2,
p. 83.

For a nontrivial normal abelian subgroup invariant under an actor transitive
on involutions, Higman proves that an element outside the subgroup cannot
have both its square in the first power layer and all its commutators in the
second power layer. The proof below replaces the original invertibility
sentence by the Agemo--Nakayama lifting established for Lemma 1.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped commutatorElement

/-- A nontrivial invariant subgroup of a finite `2`-group contains every
involution when the actor is transitive on involutions.  This is the
observation used in Higman's proof of Lemma 2. -/
theorem involutions_subset_of_nontrivial_invariant
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (X : Subgroup (MulAut P))
    (htrans : ∀ x ∈ involutions P, ∀ y ∈ involutions P,
      ∃ a : X, (a : MulAut P) x = y)
    {A : Subgroup P} (hAinv : IsAInvariant X.subtype A)
    (hAne : A ≠ ⊥) :
    involutions P ⊆ A := by
  letI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
  have hA2 : IsPGroup 2 A := hP.to_subgroup A
  have hcard_ne : Nat.card A ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  have htwo_dvd : 2 ∣ Nat.card A :=
    hA2.card_eq_or_dvd.resolve_left hcard_ne
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 htwo_dvd
  have hz := orderOf_eq_prime_iff.mp hzorder
  have hzP : (z : P) ∈ involutions P := by
    refine ⟨congrArg Subtype.val hz.1, ?_⟩
    intro h
    exact hz.2 (Subtype.ext h)
  intro x hx
  obtain ⟨a, ha⟩ := htrans (z : P) hzP x hx
  rw [← ha]
  exact hAinv.smul_mem a z.2

/-- **Higman, Suzuki 2-groups, Lemma 2** (p. 83).

Higman assumes globally in §3 that `P` is nonabelian and has more than one
involution. The argument only needs a finite `2`-group and an automorphism
subgroup `X` transitive on its involutions, so we state that generalization.
If `A ≠ 1` is an abelian normal `X`-subgroup, no `u ∉ A` can satisfy both
`u² ∈ A²` and `[u,A] ≤ A⁴`.

Here `A²` and `A⁴` are represented by the first and second Agemo subgroups
of `A`, mapped into the ambient group. -/
theorem no_sq_mem_agemo_one_and_commutator_le_agemo_two
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (X : Subgroup (MulAut P))
    (htrans : ∀ x ∈ involutions P, ∀ y ∈ involutions P,
      ∃ a : X, (a : MulAut P) x = y)
    (A : Subgroup P) [A.Normal]
    (hAcomm : IsMulCommutative A)
    (hAinv : IsAInvariant X.subtype A)
    (hAne : A ≠ ⊥) {u : P} (hu : u ∉ A) :
    ¬ (u ^ 2 ∈ (Agemo A 2 1).map A.subtype ∧
      ⁅Subgroup.zpowers u, A⁆ ≤ (Agemo A 2 2).map A.subtype) := by
  rintro ⟨hu2, hcomm⟩
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := hAcomm.is_comm.comm }
  have hA2 : IsPGroup 2 A := hP.to_subgroup A
  let θ : MulAut A := MulAut.conjNormal (H := A) u⁻¹
  let f : A →* A := MonoidHom.id A * θ.toMonoidHom
  have hdiff (a : A) : θ a * a⁻¹ ∈ Agemo A 2 2 := by
    apply (Subgroup.mem_map_iff_mem A.subtype_injective).mp
    have hgen : ⁅u⁻¹, (a : P)⁆ ∈ ⁅Subgroup.zpowers u, A⁆ :=
      Subgroup.commutator_mem_commutator
        ((Subgroup.zpowers u).inv_mem (Subgroup.mem_zpowers u)) a.2
    have := hcomm hgen
    have hθ : ((θ a : A) : P) = u⁻¹ * (a : P) * u := by
      dsimp [θ]
      simp
    change ((θ a : A) : P) * (a : P)⁻¹ ∈
      (Agemo A 2 2).map A.subtype
    rw [hθ]
    simpa only [commutatorElement_def, inv_inv] using this
  have hf_mem (a : A) : f a ∈ Agemo A 2 1 := by
    have ha2 : a ^ 2 ∈ Agemo A 2 1 := by
      simpa using (Agemo.mem_of_eq_pow (G := A) (p := 2) (n := 1) a)
    have hd : θ a * a⁻¹ ∈ Agemo A 2 1 :=
      Agemo.anti (show 1 ≤ 2 by omega) (hdiff a)
    have hmul := (Agemo A 2 1).mul_mem ha2 hd
    have heq : f a = a ^ 2 * (θ a * a⁻¹) := by
      simp only [f, MonoidHom.mul_apply, MonoidHom.id_apply,
        MulEquiv.coe_toMonoidHom, pow_two]
      rw [mul_comm (θ a) a⁻¹]
      group
    rwa [← heq] at hmul
  have hUle : f.range ≤ Agemo A 2 1 := by
    rintro _ ⟨a, rfl⟩
    exact hf_mem a
  have hsup : f.range ⊔ Agemo A 2 2 = Agemo A 2 1 := by
    apply le_antisymm
    · exact sup_le hUle (Agemo.anti (show 1 ≤ 2 by omega))
    · intro x hx
      obtain ⟨a, rfl⟩ := (mem_agemo_iff_of_comm).mp hx
      have hfU : f a ∈ f.range := ⟨a, rfl⟩
      have hdU : θ a * a⁻¹ ∈ f.range ⊔ Agemo A 2 2 :=
        (le_sup_right : Agemo A 2 2 ≤ f.range ⊔ Agemo A 2 2) (hdiff a)
      have hprod := (f.range ⊔ Agemo A 2 2).mul_mem
        ((le_sup_left : f.range ≤ f.range ⊔ Agemo A 2 2) hfU)
        ((f.range ⊔ Agemo A 2 2).inv_mem hdU)
      have heq : f a * (θ a * a⁻¹)⁻¹ = a ^ 2 := by
        simp only [f, MonoidHom.mul_apply, MonoidHom.id_apply,
        MulEquiv.coe_toMonoidHom, pow_two]
        rw [mul_inv_rev, inv_inv]
        calc
          a * θ a * (a * (θ a)⁻¹) =
              a * (θ a * a) * (θ a)⁻¹ := by group
          _ = a * (a * θ a) * (θ a)⁻¹ := by rw [mul_comm (θ a) a]
          _ = a * a := by group
      simpa only [pow_one, Nat.reducePow] using heq ▸ hprod
  have hUeq : f.range = Agemo A 2 1 :=
    eq_agemo_of_sup_succ_eq (p := 2) (s := 1) hA2 hUle hsup
  obtain ⟨a2, ha2, ha2val⟩ := Subgroup.mem_map.mp hu2
  have ha2U : a2 ∈ f.range := hUeq.symm ▸ ha2
  obtain ⟨b, hb⟩ := ha2U
  have hfb : ((f b : A) : P) = u ^ 2 := by
    rw [hb]
    exact ha2val
  let w : P := (b : P) * u⁻¹
  have hfval : ((f b : A) : P) =
      (b : P) * (u⁻¹ * (b : P) * u) := by
    change (b : P) * ((θ b : A) : P) = _
    congr 1
    simpa only [θ, map_inv] using
      (MulAut.conjNormal_inv_apply (H := A) u b)
  have hw2 : w ^ 2 = 1 := by
    calc
      w ^ 2 = ((b : P) * (u⁻¹ * (b : P) * u)) * (u⁻¹) ^ 2 := by
        dsimp [w]
        rw [pow_two]
        group
      _ = ((f b : A) : P) * (u⁻¹) ^ 2 := by rw [hfval]
      _ = u ^ 2 * (u⁻¹) ^ 2 := by rw [hfb]
      _ = 1 := by group
  have hw1 : w ≠ 1 := by
    intro hw
    apply hu
    have hbu : (b : P) = u := by
      apply mul_inv_eq_one.mp
      exact hw
    rw [← hbu]
    exact b.2
  have hwA : w ∈ A :=
    involutions_subset_of_nontrivial_invariant hP X htrans hAinv hAne
      ⟨hw2, hw1⟩
  apply hu
  have hmem : w⁻¹ * (b : P) ∈ A := A.mul_mem (A.inv_mem hwA) b.2
  have heq : w⁻¹ * (b : P) = u := by
    dsimp [w]
    group
  rwa [heq] at hmem

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
