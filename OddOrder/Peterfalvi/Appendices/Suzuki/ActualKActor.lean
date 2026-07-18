/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowTwo

/-!
# Peterfalvi Part II, Ch. I §2: the actual `K`-actor on `Q`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §2, pp. 102–103.

This file packages the ambient subgroup `K` as the concrete subgroup of
`MulAut Q` induced by conjugation.  Proposition 1(a) makes the action
fixed-point-free, while §1 Proposition 3 makes it faithful and regular on
the nonidentity involutions.  The subgroup `Q₀` is both normal in `Q` and
invariant under this action.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## Faithfulness and fixed-point-freeness -/

/-- Conjugation by `K` on `Q` is faithful.  It suffices to evaluate two
automorphisms at the distinguished involution and use the injectivity clause
of §1 Proposition 3 on the inverse elements of `K`. -/
theorem conjQByK_injective : Function.Injective hyp.conjQByK := by
  intro k l hkl
  let s : ↥hyp.Q := ⟨hyp.distinguishedInvolution,
    hyp.mem_Q_of_sq_eq_one_of_mem_H hyp.distinguishedInvolution_mem_H
      hyp.distinguishedInvolution_sq⟩
  have hact : hyp.conjQByK k s = hyp.conjQByK l s :=
    congrArg (fun a : MulAut ↥hyp.Q => a s) hkl
  have hactG : (k : G) * hyp.distinguishedInvolution * (k : G)⁻¹ =
      (l : G) * hyp.distinguishedInvolution * (l : G)⁻¹ := by
    simpa only [hyp.conjQByK_apply_val] using congrArg Subtype.val hact
  have hkK : (k : G) ∈ hyp.KSet := by
    rw [← hyp.coe_K]
    exact k.2
  have hlK : (l : G) ∈ hyp.KSet := by
    rw [← hyp.coe_K]
    exact l.2
  have hinv : (k : G)⁻¹ = (l : G)⁻¹ :=
    hyp.injOn_conj_KSet hyp.distinguishedInvolution_mem_H
      hyp.distinguishedInvolution_sq hyp.distinguishedInvolution_ne_one
      (hyp.inv_mem_KSet hkK) (hyp.inv_mem_KSet hlK) (by
        simpa only [inv_inv] using hactG)
  exact Subtype.ext (inv_injective hinv)

/-- **Peterfalvi Part II, Ch. I §2 Prop 1(a)** (p. 102), action form:
a nonidentity element of `K` fixes only the identity of `Q`. -/
theorem conjQByK_fixed_eq_one {k : ↥hyp.K} (hk : k ≠ 1) {x : ↥hyp.Q}
    (hx : hyp.conjQByK k x = x) : x = 1 := by
  have hkK : (k : G) ∈ hyp.KSet := by
    rw [← hyp.coe_K]
    exact k.2
  have hk1 : (k : G) ≠ 1 := fun h => hk (Subtype.ext h)
  have hact : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) := by
    simpa only [hyp.conjQByK_apply_val] using congrArg Subtype.val hx
  have hkx : (k : G) * (x : G) = (x : G) * (k : G) := by
    calc
      (k : G) * (x : G) =
          ((k : G) * (x : G) * (k : G)⁻¹) * (k : G) := by group
      _ = (x : G) * (k : G) := by rw [hact]
  have hxmem : (x : G) ∈ hyp.Q ⊓ Subgroup.centralizer {(k : G)} :=
    ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hkx.symm⟩
  rw [hyp.Q_inf_centralizer_eq_bot_of_mem_KSet hkK hk1,
    Subgroup.mem_bot] at hxmem
  exact Subtype.ext hxmem

/-! ## The invariant central subgroup `Q₀` -/

/-- `Q₀`, viewed inside `Q`, is normal.  In fact it lies in the center of
`Q` by Proposition 1(c). -/
instance Q0_subgroupOf_Q_normal : (hyp.Q0.subgroupOf hyp.Q).Normal := by
  constructor
  intro n hn g
  change (n : G) ∈ hyp.Q0 at hn
  change (g : G) * (n : G) * (g : G)⁻¹ ∈ hyp.Q0
  have hcomm : (g : G) * (n : G) = (n : G) * (g : G) :=
    Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hn) (g : G) g.2
  have heq : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
    calc
      (g : G) * (n : G) * (g : G)⁻¹ =
          (n : G) * ((g : G) * (g : G)⁻¹) := by rw [hcomm, mul_assoc]
      _ = (n : G) := by simp
  rwa [heq]

/-- The actual `K`-conjugation action preserves `Q₀ ≤ Q`. -/
theorem Q0_isInvariant :
    OddOrder.Isaacs.Ch03.IsAInvariant hyp.conjQByK
      (hyp.Q0.subgroupOf hyp.Q) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro k x hx
  change (x : G) ∈ hyp.Q0 at hx
  change ((hyp.conjQByK k x : ↥hyp.Q) : G) ∈ hyp.Q0
  rw [hyp.conjQByK_apply_val]
  have hkH : (k : G) ∈ hyp.H :=
    hyp.D_le_H (hyp.K_le_D k.2)
  refine ⟨?_, mul_mem (mul_mem hkH hx.2) (inv_mem hkH)⟩
  rw [sq]
  calc
    ((k : G) * (x : G) * (k : G)⁻¹) *
        ((k : G) * (x : G) * (k : G)⁻¹) =
        (k : G) * ((x : G) * (x : G)) * (k : G)⁻¹ := by group
    _ = 1 := by rw [← sq, hx.1]; simp

/-! ## The actual automorphism subgroup and its regular action -/

/-- The concrete automorphism subgroup induced by the ambient subgroup `K`. -/
def actualKActor : Subgroup (MulAut ↥hyp.Q) := hyp.conjQByK.range

/-- The actual `K`-actor is cyclic. -/
instance actualKActor_isCyclic : IsCyclic ↥hyp.actualKActor :=
  isCyclic_of_surjective hyp.conjQByK.rangeRestrict
    hyp.conjQByK.rangeRestrict_surjective

/-- The actual `K`-actor acts regularly on the nonidentity involutions of
`Q`.  Transitivity and sharpness are precisely the two clauses of §1
Proposition 3, transported from ambient conjugation to `conjQByK`. -/
theorem actualKActor_actsRegularlyOnInvolutions :
    Suzuki2Groups.ActsRegularlyOnInvolutions hyp.actualKActor := by
  intro x hx y hy
  have hx2G : ((x : ↥hyp.Q) : G) ^ 2 = 1 :=
    congrArg Subtype.val hx.1
  have hx1G : ((x : ↥hyp.Q) : G) ≠ 1 :=
    fun h => hx.2 (Subtype.ext h)
  have hy2G : ((y : ↥hyp.Q) : G) ^ 2 = 1 :=
    congrArg Subtype.val hy.1
  have hy1G : ((y : ↥hyp.Q) : G) ≠ 1 :=
    fun h => hy.2 (Subtype.ext h)
  have hxH : ((x : ↥hyp.Q) : G) ∈ hyp.H := hyp.Q_le_H x.2
  have hyH : ((y : ↥hyp.Q) : G) ∈ hyp.H := hyp.Q_le_H y.2
  have himg := hyp.image_conj_KSet_eq_involutions_H hxH hx2G hx1G
  have hymem : ((y : ↥hyp.Q) : G) ∈
      {z : G | z ^ 2 = 1 ∧ z ≠ 1 ∧ z ∈ hyp.H} :=
    ⟨hy2G, hy1G, hyH⟩
  rw [← himg] at hymem
  obtain ⟨k, hkK, hky⟩ := hymem
  have hkiK : k⁻¹ ∈ hyp.K := by
    change k⁻¹ ∈ (hyp.K : Set G)
    rw [hyp.coe_K]
    exact hyp.inv_mem_KSet hkK
  let j : ↥hyp.K := ⟨k⁻¹, hkiK⟩
  let a : ↥hyp.actualKActor :=
    ⟨hyp.conjQByK j, ⟨j, rfl⟩⟩
  refine ⟨a, ?_, ?_⟩
  · apply Subtype.ext
    change k⁻¹ * ((x : ↥hyp.Q) : G) * (k⁻¹)⁻¹ =
      ((y : ↥hyp.Q) : G)
    rw [inv_inv]
    exact hky
  · intro b hb
    obtain ⟨l, hl⟩ := b.2
    have hlaction : hyp.conjQByK l x = y := by
      rw [hl]
      exact hb
    have hlG : (l : G) * ((x : ↥hyp.Q) : G) * (l : G)⁻¹ =
        ((y : ↥hyp.Q) : G) := by
      simpa only [hyp.conjQByK_apply_val] using congrArg Subtype.val hlaction
    have hjG : (j : G) * ((x : ↥hyp.Q) : G) * (j : G)⁻¹ =
        ((y : ↥hyp.Q) : G) := by
      change k⁻¹ * ((x : ↥hyp.Q) : G) * (k⁻¹)⁻¹ = _
      rw [inv_inv]
      exact hky
    have hliK : (l : G)⁻¹ ∈ hyp.KSet := by
      apply hyp.inv_mem_KSet
      rw [← hyp.coe_K]
      exact l.2
    have hjiK : (j : G)⁻¹ ∈ hyp.KSet := by
      apply hyp.inv_mem_KSet
      rw [← hyp.coe_K]
      exact j.2
    have hinv_eq : (l : G)⁻¹ = (j : G)⁻¹ :=
      hyp.injOn_conj_KSet hxH hx2G hx1G hliK hjiK (by
        simpa only [inv_inv] using hlG.trans hjG.symm)
    have hlj : l = j := Subtype.ext (inv_injective hinv_eq)
    apply Subtype.ext
    change (b : MulAut ↥hyp.Q) = hyp.conjQByK j
    rw [← hl, hlj]

/-! ## Orders -/

/-- The order of `K` is one less than the order of `Q₀`: §1 Proposition 3
identifies `K` with the nonidentity involutions, which are exactly
`Q₀ \ {1}`. -/
theorem card_K_eq_card_Q0_sub_one :
    Nat.card ↥hyp.K = Nat.card ↥hyp.Q0 - 1 := by
  have hset : {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} =
      (hyp.Q0 : Set G) \ {1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_sdiff, SetLike.mem_coe,
      hyp.mem_Q0_iff, Set.mem_singleton_iff]
    tauto
  calc
    Nat.card ↥hyp.K = (hyp.K : Set G).ncard := Nat.card_coe_set_eq _
    _ = hyp.KSet.ncard := by rw [hyp.coe_K]
    _ = {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H}.ncard :=
      hyp.ncard_KSet_eq
    _ = ((hyp.Q0 : Set G) \ {1}).ncard := by rw [hset]
    _ = (hyp.Q0 : Set G).ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem hyp.Q0.one_mem
    _ = Nat.card ↥hyp.Q0 - 1 := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]

/-- The subgroup `K` has odd order because `K ≤ D` and `D` has odd order. -/
theorem card_K_odd : Odd (Nat.card ↥hyp.K) :=
  hyp.D_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.K_le_D)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
