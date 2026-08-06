/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiQ8.CharacterCore

/-!
# Brauer–Suzuki, the `Q₈` case: the induction on `|G|` and the final statements

The reduction of `BrauerSuzukiQ8/Reduction.lean` and the character-theoretic core of
`BrauerSuzukiQ8/CharacterCore.lean` are combined by induction on `|G|`, then transported from
`Ḡ = G/O_{2'}(G)` back to `G`.

## Main results

* `OddOrder.GroupTheory.q8_mem_center_of_oPiCore_eq_bot`
* `OddOrder.GroupTheory.q8_mk_mem_center` / `OddOrder.GroupTheory.brauerSuzuki_q8`
-/


open OddOrder.Isaacs.Ch03

open scoped Pointwise

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]
universe u

private theorem q8_mem_center_aux (n : ℕ) : ∀ {H : Type u} [Group H] [Finite H],
    Nat.card H ≤ n → oPiCore {p | p ≠ 2} H = ⊥ → ∀ T : Sylow 2 H,
    Nonempty (↥(T : Subgroup H) ≃* QuaternionGroup 2) → ∀ {z : H}, z ∈ (T : Subgroup H) →
    orderOf z = 2 → z ∈ Subgroup.center H := by
  induction n with
  | zero =>
    intro H _ _ hcard
    have := Nat.card_pos (α := H)
    omega
  | succ n ih =>
    intro H _ _ hcard hO T hq z hzT hz
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e⟩ := hq
    have hz2 : z ^ 2 = 1 := by
      have h := pow_orderOf_eq_one z
      rwa [hz] at h
    have hz1 : z ≠ 1 := fun h => by simp [h] at hz
    by_cases hTop : (T : Subgroup H) = ⊤
    · -- `H` itself is `Q₈`, whose involution is central
      exact mem_center_of_sq_eq_one_of_quaternionTwo
        (Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hTop).symm.trans e)) hz2 hz1
    -- otherwise the character theory gives a proper normal subgroup containing `z`
    obtain ⟨N, hNnorm, hNtop, hzN⟩ := q8_exists_proper_normal hO T e hTop hzT hz
    haveI := hNnorm
    by_cases hTN : (T : Subgroup H) ≤ N
    · -- `P ≤ N`: induct on `N`
      have hidx : 1 < N.index := Subgroup.one_lt_index_of_ne_top hNtop
      have hcardN : Nat.card ↥N ≤ n := by
        have h := Subgroup.card_mul_index N
        have hpos : 0 < Nat.card ↥N := Nat.card_pos
        nlinarith [h, hcard, hidx, hpos]
      have hON : oPiCore {p | p ≠ 2} ↥N = ⊥ := oPiCore_subgroup_eq_bot hO
      -- `T` is a Sylow `2`-subgroup of `N`
      have hinf : (T : Subgroup H) ⊓ N = (T : Subgroup H) := inf_eq_left.mpr hTN
      have hpgT : IsPGroup 2 ↥((T : Subgroup H) ⊓ N) := T.isPGroup'.to_le inf_le_left
      have hpg : IsPGroup 2 ↥(((T : Subgroup H) ⊓ N).subgroupOf N) :=
        hpgT.of_equiv (Subgroup.subgroupOfEquivOfLe (H := (T : Subgroup H) ⊓ N) inf_le_right).symm
      set TN : Sylow 2 ↥N := hpg.toSylow (not_two_dvd_index_inf_subgroupOf T N) with hTNdef
      have hTNcoe : (TN : Subgroup ↥N) = ((T : Subgroup H) ⊓ N).subgroupOf N :=
        hpg.toSylow_coe (not_two_dvd_index_inf_subgroupOf T N)
      have hqN : Nonempty (↥(TN : Subgroup ↥N) ≃* QuaternionGroup 2) :=
        ⟨(MulEquiv.subgroupCongr hTNcoe).trans
          (((Subgroup.subgroupOfEquivOfLe (H := (T : Subgroup H) ⊓ N) inf_le_right).trans
            (MulEquiv.subgroupCongr hinf)).trans e)⟩
      have hzTN : (⟨z, hzN⟩ : ↥N) ∈ (TN : Subgroup ↥N) := by
        rw [hTNcoe, Subgroup.mem_subgroupOf]
        exact ⟨hzT, hzN⟩
      have hzord : orderOf (⟨z, hzN⟩ : ↥N) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
      have hcen := ih hcardN hON TN hqN hzTN hzord
      refine q8_mem_center_of_mem_center_normal T e hz hTN hzN fun x hx => ?_
      have := Subgroup.mem_center_iff.mp hcen ⟨x, hx⟩
      exact congrArg Subtype.val this
    · -- `P ⊄ N`: the cyclic branch
      exact q8_mem_center_of_mem_normal_of_not_le hO T e hz hTN hzN

/-- **Brauer–Suzuki for `Q₈`, the residual statement** (Navarro pp. 139–146; issue 9506): with
`O_{2'}(G) = 1`, the involution of a quaternion Sylow `2`-subgroup of order `8` is central.

The proof is the eight pages pp. 139–146: a unique `G`-class of elements of order `4` (fusion
control plus `Aut(Q₈) = Sym(4)`), then the "analysis at `y`" and "analysis at `t`" with the
principal-block basic set of Navarro (7.3)/(7.4) — for which the integral change-of-basis matrix
`intBasicSetMatrix` (issue 9508, closed) is the prerequisite — producing a nontrivial character of
`B₀` with `t` in its kernel. -/
theorem q8_mem_center_of_oPiCore_eq_bot (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (hq : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup 2))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    z ∈ Subgroup.center G :=
  q8_mem_center_aux (Nat.card G) le_rfl hO T hq hzT hz

/-- **Brauer–Suzuki for `Q₈`, in the form the endgame consumes**: the image of the involution is
central modulo the odd core.

This is `q8_mem_center_of_oPiCore_eq_bot` applied to `Ḡ = G/O_{2'}(G)`, which is legitimate
because `O_{2'}(Ḡ) = 1` (`oPiCore_quotient_self_eq_bot`) and the Sylow `2`-subgroups of `Ḡ` are
again `Q₈`: the odd core meets `T` trivially (`sylowTwo_inf_oPiCore_eq_bot`), so `T → Ḡ` is
injective and its image — a Sylow `2`-subgroup of `Ḡ` by `Sylow.mapSurjective` — is isomorphic
to `T`. -/
theorem q8_mk_mem_center (T : Sylow 2 G)
    (hq : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup 2))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    QuotientGroup.mk' (oPiCore {p | p ≠ 2} G) z
      ∈ Subgroup.center (G ⧸ oPiCore {p | p ≠ 2} G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oPiCore {p | p ≠ 2} G with hK
  set q := QuotientGroup.mk' K with hq'
  -- `T → Ḡ` is injective, since `T ⊓ K = ⊥`
  set f : ↥(T : Subgroup G) →* G ⧸ K := q.comp (T : Subgroup G).subtype with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, ha⟩ hafx
    have haK : a ∈ K := (QuotientGroup.eq_one_iff a).mp hafx
    have : a ∈ (T : Subgroup G) ⊓ K := ⟨ha, haK⟩
    rw [sylowTwo_inf_oPiCore_eq_bot T, Subgroup.mem_bot] at this
    exact Subtype.ext this
  -- the image is a Sylow `2`-subgroup of `Ḡ`, isomorphic to `T`
  have hrange : f.range = (T : Subgroup G).map q := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e⟩ := hq
  refine q8_mem_center_of_oPiCore_eq_bot (oPiCore_quotient_self_eq_bot {p | p ≠ 2})
    (T.mapSurjective (QuotientGroup.mk'_surjective K))
    ⟨((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hfinj).symm).trans e⟩
    (Subgroup.mem_map_of_mem _ hzT) ?_
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, hz2, map_one]
  · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact notMem_oPiCore_of_orderOf_eq_two hz

/-- **Brauer–Suzuki, the `Q₈` case.**  The group-theoretic endgame
(`oPiCore_sup_centralizer_eq_top_of_mk_mem_center`) applied to `q8_mk_mem_center`. -/
theorem brauerSuzuki_q8 (T : Sylow 2 G) (hq : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup 2))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    oPiCore {p | p ≠ 2} G ⊔ Subgroup.centralizer {z} = ⊤ :=
  oPiCore_sup_centralizer_eq_top_of_mk_mem_center hz (q8_mk_mem_center T hq hzT hz)

end OddOrder.GroupTheory
