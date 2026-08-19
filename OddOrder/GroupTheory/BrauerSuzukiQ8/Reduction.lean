/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiEndgame
import OddOrder.GroupTheory.CardSupInf
import OddOrder.GroupTheory.CentralSylowComplement
import OddOrder.GroupTheory.QuaternionTwoFacts
import OddOrder.GroupTheory.SylowContaining
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.Isaacs.Ch05_Transfer.Main
import OddOrder.Mathlib.QuotientGroup
import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Brauer–Suzuki, the `Q₈` case: the group-theoretic reduction (Navarro p. 139)

Navarro's reduction paragraph on p. 139, in full: the fusion of the elements of order `4`, the
two branches of the induction (`N` cyclic / `T ≤ N`), and the structure of `C_G(t)/⟨t⟩` that the
character-theoretic core consumes.  Everything here is group theory; the modular character theory
is `BrauerSuzukiQ8/CharacterCore.lean`.

## Main results

* `OddOrder.GroupTheory.isConj_of_orderFour` — a single class of elements of order `4`
* `OddOrder.GroupTheory.q8_mem_center_of_mem_normal_of_not_le` — the cyclic branch
* `OddOrder.GroupTheory.q8_mem_center_of_mem_center_normal` — the branch `T ≤ N`
* `OddOrder.GroupTheory.isConj_of_sq_eq_one_quotient_centralizer` /
  `OddOrder.GroupTheory.sq_eq_one_of_isPGroup_zpowers_quotient_centralizer` — the `hconjall` of
  Navarro (7.2)/(7.4) for `C_G(t)/⟨t⟩`
* `OddOrder.GroupTheory.card_sylow_quotient_centralizer` — its Sylow `2`-subgroups have order `4`
-/


open OddOrder.Isaacs.Ch03

open scoped Pointwise

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- **The odd core meets a Sylow `2`-subgroup trivially**: the intersection has order dividing
both a power of `2` and an odd number. -/
theorem sylowTwo_inf_oPiCore_eq_bot (T : Sylow 2 G) :
    (T : Subgroup G) ⊓ oPiCore {p | p ≠ 2} G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKodd : ¬ 2 ∣ Nat.card ↥(oPiCore {p | p ≠ 2} G) := fun h2 =>
    (oPiCore.isPiGroup {p | p ≠ 2}) 2
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, Nat.card_pos.ne'⟩) rfl
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hdvdT : Nat.card ↥((T : Subgroup G) ⊓ oPiCore {p | p ≠ 2} G) ∣ 2 ^ n := by
    rw [← hn]; exact card_dvd_card_of_le inf_le_left
  have hdvdK : Nat.card ↥((T : Subgroup G) ⊓ oPiCore {p | p ≠ 2} G)
      ∣ Nat.card ↥(oPiCore {p | p ≠ 2} G) := card_dvd_card_of_le inf_le_right
  refine Subgroup.card_eq_one.mp ?_
  by_contra hne
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdT
  have hj0 : j ≠ 0 := fun h => hne (by rw [hj, h, pow_zero])
  exact hKodd (((hj ▸ dvd_pow_self 2 hj0)).trans hdvdK)

/-- **An involution of a normal cyclic subgroup is central.**  Conjugates of `z` stay in `N` and
are again involutions, and a cyclic group has at most one involution
(`eq_of_sq_eq_one_of_isCyclic`).

This is how *both* branches of Navarro's reduction (p. 139) finish: either `N` itself is a cyclic
`2`-group, or `Z(N) = ⟨t⟩`. -/
theorem mem_center_of_normal_of_isCyclic {N : Subgroup G} [N.Normal] [IsCyclic ↥N] {z : G}
    (hzN : z ∈ N) (hz : orderOf z = 2) : z ∈ Subgroup.center G := by
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hconjN : g * z * g⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹N.Normal› z hzN g
  have hconj_sq : (g * z * g⁻¹) ^ 2 = 1 := by
    rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, ← map_pow, hz2, map_one]
  have hconj_ne : g * z * g⁻¹ ≠ 1 := fun h =>
    hz1 ((MulAut.conj g).injective (h.trans (map_one (MulAut.conj g)).symm))
  have hkey := eq_of_sq_eq_one_of_isCyclic (C := ↥N)
    (a := ⟨g * z * g⁻¹, hconjN⟩) (b := ⟨z, hzN⟩)
    (Subtype.ext (by push_cast; exact hconj_sq)) (by simpa using hconj_ne)
    (Subtype.ext (by push_cast; exact hz2)) (by simpa using hz1)
  have hgz : g * z * g⁻¹ = z := congrArg Subtype.val hkey
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [hgz]

/-- **Once one Sylow `2`-subgroup is `Q₈`, all of them are** — they are conjugate. -/
theorem nonempty_mulEquiv_quaternionTwo_of_sylow (T S : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) :
    Nonempty (↥(S : Subgroup G) ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hcoe : (S : Subgroup G) = MulAut.conj g • (T : Subgroup G) := by rw [← hg]; rfl
  exact ⟨((MulEquiv.subgroupCongr hcoe).trans
    (Subgroup.equivSMul (MulAut.conj g) (T : Subgroup G)).symm).trans e⟩

/-! ### Navarro p. 139: the cyclic branch of the reduction -/

/-- **`T ⊓ N` has odd index in a normal subgroup `N`.**  By the second isomorphism theorem
`|T|·[N : T ⊓ N] = |T ⊔ N|`, which divides `|G| = |T|·[G : T]`, so `[N : T ⊓ N]` divides the odd
number `[G : T]`. -/
theorem not_two_dvd_index_inf_subgroupOf (T : Sylow 2 G) (N : Subgroup G) [N.Normal] :
    ¬ 2 ∣ (((T : Subgroup G) ⊓ N).subgroupOf N).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := ((T : Subgroup G) ⊓ N).subgroupOf N with hS
  have hcard : Nat.card ↥S = Nat.card ↥((T : Subgroup G) ⊓ N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := (T : Subgroup G) ⊓ N) inf_le_right).toEquiv
  have h1 : Nat.card ↥S * S.index = Nat.card ↥N := Subgroup.card_mul_index S
  have h2 := card_sup_mul_card_inf_eq (T : Subgroup G) N
  have hpos : 0 < Nat.card ↥((T : Subgroup G) ⊓ N) := Nat.card_pos
  have h3 : Nat.card ↥(T : Subgroup G) * S.index = Nat.card ↥((T : Subgroup G) ⊔ N) := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc Nat.card ↥(T : Subgroup G) * S.index * Nat.card ↥((T : Subgroup G) ⊓ N)
        = Nat.card ↥(T : Subgroup G) * (Nat.card ↥S * S.index) := by rw [hcard]; ring
      _ = Nat.card ↥(T : Subgroup G) * Nat.card ↥N := by rw [h1]
      _ = Nat.card ↥((T : Subgroup G) ⊔ N) * Nat.card ↥((T : Subgroup G) ⊓ N) := h2.symm
  -- `|T|·index = |T ⊔ N|` divides `|G| = |T|·[G:T]`
  have h4 : Nat.card ↥(T : Subgroup G) * S.index
      ∣ Nat.card ↥(T : Subgroup G) * (T : Subgroup G).index := by
    rw [h3, Subgroup.card_mul_index]
    exact Subgroup.card_subgroup_dvd_card _
  have h5 : S.index ∣ (T : Subgroup G).index :=
    (mul_dvd_mul_iff_left (Nat.card_pos (α := ↥(T : Subgroup G))).ne').mp h4
  exact fun hdvd => T.not_dvd_index (hdvd.trans h5)

/-- **Navarro p. 139, the cyclic branch.**  If the involution `z` lies in a normal subgroup `N`
that does not contain the whole Sylow `2`-subgroup, then `z` is central.

`T ⊓ N` is a Sylow `2`-subgroup of `N` (odd index) and is a *proper* subgroup of `T ≅ Q₈`, hence
cyclic.  Burnside then gives `N` a normal `2`-complement `L`, consisting exactly of the
odd-order elements of `N` — so `L` is normal in `G`, hence inside `O_{2'}(G) = 1`.  Therefore `N`
is its own Sylow `2`-subgroup, a cyclic group, and `mem_center_of_normal_of_isCyclic` applies. -/
theorem q8_mem_center_of_mem_normal_of_not_le (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) {z : G} (hz : orderOf z = 2)
    {N : Subgroup G} [N.Normal] (hTN : ¬ (T : Subgroup G) ≤ N) (hzN : z ∈ N) :
    z ∈ Subgroup.center G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `T ⊓ N` is a Sylow `2`-subgroup of `N`
  have hpgTN : IsPGroup 2 ↥((T : Subgroup G) ⊓ N) := T.isPGroup'.to_le inf_le_left
  have hpg : IsPGroup 2 ↥(((T : Subgroup G) ⊓ N).subgroupOf N) :=
    hpgTN.of_equiv (Subgroup.subgroupOfEquivOfLe (H := (T : Subgroup G) ⊓ N) inf_le_right).symm
  set P : Sylow 2 ↥N := hpg.toSylow (not_two_dvd_index_inf_subgroupOf T N) with hP
  have hPcoe : (P : Subgroup ↥N) = ((T : Subgroup G) ⊓ N).subgroupOf N :=
    hpg.toSylow_coe (not_two_dvd_index_inf_subgroupOf T N)
  -- it is cyclic, being a proper subgroup of `T ≅ Q₈`
  have hne : N.subgroupOf (T : Subgroup G) ≠ ⊤ := fun h =>
    hTN (Subgroup.subgroupOf_eq_top.mp h)
  have hcycT : IsCyclic ↥(N.subgroupOf (T : Subgroup G)) :=
    isCyclic_of_ne_top_of_quaternionTwo e hne
  have hstep : ((T : Subgroup G) ⊓ N).subgroupOf (T : Subgroup G)
      = N.subgroupOf (T : Subgroup G) := by
    rw [show (T : Subgroup G) ⊓ N = N ⊓ (T : Subgroup G) from inf_comm _ _]
    exact Subgroup.inf_subgroupOf_right N (T : Subgroup G)
  have hcycInf : IsCyclic ↥((T : Subgroup G) ⊓ N) := by
    have := hcycT
    exact isCyclic_of_surjective
      ((MulEquiv.subgroupCongr hstep).symm.trans
        (Subgroup.subgroupOfEquivOfLe (H := (T : Subgroup G) ⊓ N) inf_le_left)).toMonoidHom
      (MulEquiv.surjective _)
  have hcyc : IsCyclic ↥(P : Subgroup ↥N) := by
    rw [hPcoe]
    exact isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe (H := (T : Subgroup G) ⊓ N) inf_le_right).symm.toMonoidHom
      (MulEquiv.surjective _)
  -- Burnside: a normal `2`-complement `L`, the odd-order elements
  have hev : 2 ∣ Nat.card ↥N := by
    have hord : orderOf (⟨z, hzN⟩ : ↥N) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
    exact hord ▸ orderOf_dvd_natCard (⟨z, hzN⟩ : ↥N)
  obtain ⟨L, hLnorm, hLodd, hLmem, hLsup⟩ :=
    exists_oddComplement_of_isCyclic_sylowTwo P hcyc hev
  -- `L` maps to a normal odd-order subgroup of `G`, hence into `O_{2'}(G) = ⊥`
  have hLgmem : ∀ x : G, x ∈ L.map N.subtype ↔ ∃ hx : x ∈ N, Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨⟨y, hyN⟩, hyL, rfl⟩
      refine ⟨hyN, ?_⟩
      have := (hLmem ⟨y, hyN⟩).mp hyL
      rwa [Subgroup.orderOf_mk] at this
    · rintro ⟨hxN, hodd⟩
      exact ⟨⟨x, hxN⟩, (hLmem ⟨x, hxN⟩).mpr (by rwa [Subgroup.orderOf_mk]), rfl⟩
  have hLgnorm : (L.map N.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxN, hodd⟩ := (hLgmem x).mp hx
    refine (hLgmem _).mpr ⟨Subgroup.Normal.conj_mem ‹N.Normal› x hxN g, ?_⟩
    rwa [← orderOf_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩)]
  have hLgpi : Subgroup.IsPiGroup {p | p ≠ 2} (L.map N.subtype) := by
    intro p hp
    have hcard : Nat.card ↥(L.map N.subtype) = Nat.card ↥L :=
      Nat.card_congr (Subgroup.equivMapOfInjective L N.subtype N.subtype_injective).symm.toEquiv
    rw [hcard] at hp
    exact fun (h : p = 2) => hLodd (h ▸ Nat.dvd_of_mem_primeFactors hp)
  have hLgbot : L.map N.subtype = ⊥ :=
    le_bot_iff.mp (hO ▸ Subgroup.IsPiGroup.le_oPiCore hLgpi)
  have hLbot : L = ⊥ := by
    refine le_bot_iff.mp fun y hy => ?_
    have : (y : G) ∈ L.map N.subtype := ⟨y, hy, rfl⟩
    rw [hLgbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  -- so `N` is its own Sylow `2`-subgroup: cyclic
  have hPtop : (P : Subgroup ↥N) = ⊤ := by rw [← hLsup, hLbot, bot_sup_eq]
  have : IsCyclic ↥N :=
    isCyclic_of_surjective ((MulEquiv.subgroupCongr hPtop).trans Subgroup.topEquiv).toMonoidHom
      (MulEquiv.surjective _)
  exact mem_center_of_normal_of_isCyclic hzN hz

/-! ### Navarro p. 139: the branch `P ≤ N` -/

/-- **A central involution of a normal subgroup lies in the Sylow `2`-subgroup.**  `⟨u⟩` is a
normal `2`-subgroup of `N`, hence contained in every Sylow `2`-subgroup of `N`
(`IsPGroup.le_sylow_of_normal`), and `T` is one when `T ≤ N`. -/
theorem mem_sylow_of_mem_center_of_orderOf_eq_two (T : Sylow 2 G) {N : Subgroup G} [N.Normal]
    (hTN : (T : Subgroup G) ≤ N) {u : G} (huN : u ∈ N) (hu : orderOf u = 2)
    (huc : ∀ x ∈ N, x * u = u * x) : u ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : (T : Subgroup G) ⊓ N = (T : Subgroup G) := inf_eq_left.mpr hTN
  -- `T.subgroupOf N` is a Sylow `2`-subgroup of `N`
  have hpgT : IsPGroup 2 ↥((T : Subgroup G) ⊓ N) := T.isPGroup'.to_le inf_le_left
  have hpg : IsPGroup 2 ↥(((T : Subgroup G) ⊓ N).subgroupOf N) :=
    hpgT.of_equiv (Subgroup.subgroupOfEquivOfLe (H := (T : Subgroup G) ⊓ N) inf_le_right).symm
  set P : Sylow 2 ↥N := hpg.toSylow (not_two_dvd_index_inf_subgroupOf T N) with hP
  have hPcoe : (P : Subgroup ↥N) = ((T : Subgroup G) ⊓ N).subgroupOf N :=
    hpg.toSylow_coe (not_two_dvd_index_inf_subgroupOf T N)
  -- `⟨u⟩` is a normal `2`-subgroup of `N`
  set v : ↥N := ⟨u, huN⟩ with hv
  have hvord : orderOf v = 2 := by rw [hv, Subgroup.orderOf_mk]; exact hu
  have hvc : v ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    exact fun g => Subtype.ext (huc (g : G) g.2)
  have hnorm : (Subgroup.zpowers v).Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hcomm := Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hvc ha) g
    rw [hcomm, mul_inv_cancel_right]
    exact ha
  have hpgv : IsPGroup 2 ↥(Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hvord, pow_one])
  have hle : Subgroup.zpowers v ≤ (P : Subgroup ↥N) := hpgv.le_sylow_of_normal P
  have hvP : v ∈ ((T : Subgroup G) ⊓ N).subgroupOf N := by
    rw [← hPcoe]; exact hle (Subgroup.mem_zpowers v)
  have := (Subgroup.mem_subgroupOf).mp hvP
  rw [hinf] at this
  exact this

/-- **Navarro p. 139, the branch `P ≤ N`.**  If the involution `z` is *central* in the normal
subgroup `N` containing the Sylow `2`-subgroup — which is what induction on `|G|` supplies — then
it is central in `G`.

Every `G`-conjugate `w` of `z` is again a central involution of `N`, so both `z` and `w` lie in
`T ≅ Q₈` (`mem_sylow_of_mem_center_of_orderOf_eq_two`), whose involution is unique. -/
theorem q8_mem_center_of_mem_center_normal (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) {z : G} (hz : orderOf z = 2)
    {N : Subgroup G} [N.Normal] (hTN : (T : Subgroup G) ≤ N) (hzN : z ∈ N)
    (hzc : ∀ x ∈ N, x * z = z * x) : z ∈ Subgroup.center G := by
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hzT := mem_sylow_of_mem_center_of_orderOf_eq_two T hTN hzN hz hzc
  rw [Subgroup.mem_center_iff]
  intro g
  -- the conjugate is again a central involution of `N`
  set w := g * z * g⁻¹ with hw
  have hwN : w ∈ N := Subgroup.Normal.conj_mem ‹N.Normal› z hzN g
  have hw2 : w ^ 2 = 1 := by
    rw [hw, show g * z * g⁻¹ = MulAut.conj g z from rfl, ← map_pow, hz2, map_one]
  have hw1 : w ≠ 1 := fun h =>
    hz1 ((MulAut.conj g).injective (h.trans (map_one (MulAut.conj g)).symm))
  have hword : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  have hwc : ∀ x ∈ N, x * w = w * x := by
    intro x hxN
    have hgx : g⁻¹ * x * g ∈ N := by
      simpa using Subgroup.Normal.conj_mem ‹N.Normal› x hxN g⁻¹
    have := hzc _ hgx
    calc x * w = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [hw]; group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = w * x := by rw [hw]; group
  have hwT := mem_sylow_of_mem_center_of_orderOf_eq_two T hTN hwN hword hwc
  -- both are involutions of `T ≅ Q₈`
  have hkey : (⟨w, hwT⟩ : ↥(T : Subgroup G)) = ⟨z, hzT⟩ :=
    eq_of_sq_eq_one_of_quaternionTwo e (Subtype.ext (by push_cast; exact hw2))
      (fun h => hw1 (congrArg Subtype.val h)) (Subtype.ext (by push_cast; exact hz2))
      (fun h => hz1 (congrArg Subtype.val h))
  have hgz : w = z := congrArg Subtype.val hkey
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [← hw, hgz]

/-! ### Navarro p. 139: the induction -/

/-- **`O_{2'}(G) = 1` is inherited by normal subgroups.**  `O_{2'}(N)` is characteristic in `N`,
hence normal in `G`, and it is a `2'`-group, so it sits inside `O_{2'}(G)`. -/
theorem oPiCore_subgroup_eq_bot {N : Subgroup G} [N.Normal] (hO : oPiCore {p | p ≠ 2} G = ⊥) :
    oPiCore {p | p ≠ 2} ↥N = ⊥ := by
  set K : Subgroup ↥N := oPiCore {p | p ≠ 2} ↥N with hK
  have : K.Characteristic := oPiCore.characteristic _ _
  have : (K.map N.subtype).Normal := normal_map_subtype_of_characteristic ‹K.Characteristic›
  have hcard : Nat.card ↥(K.map N.subtype) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.equivMapOfInjective K N.subtype N.subtype_injective).symm.toEquiv
  have hpi : Subgroup.IsPiGroup {p | p ≠ 2} (K.map N.subtype) := by
    intro p hp
    rw [hcard] at hp
    exact oPiCore.isPiGroup (G := ↥N) {p | p ≠ 2} p hp
  have hbot : K.map N.subtype = ⊥ := le_bot_iff.mp (hO ▸ Subgroup.IsPiGroup.le_oPiCore hpi)
  refine le_bot_iff.mp fun y hy => ?_
  have hmem : (y : G) ∈ K.map N.subtype := ⟨y, hy, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (Subtype.ext hmem)

/-! ### Navarro p. 139: `T` does not control its own fusion

The first step of the character-theoretic argument: because `O_{2'}(G) = 1` and `T < G`, the group
`G` has no normal `2`-complement, so by Isaacs Thm 5.25 the Sylow `2`-subgroup cannot control its
own fusion — which is what forces two distinct `T`-classes of elements of order `4` to fuse in
`G`. -/

/-- **`G` has no normal `2`-complement** when `O_{2'}(G) = 1` and the Sylow `2`-subgroup is
proper: such a complement is a normal subgroup of odd order, hence trivial, forcing `T = G`. -/
theorem not_hasNormalPComplement_of_oPiCore_eq_bot (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (hTG : (T : Subgroup G) ≠ ⊤) : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨N, hNnorm, hcompl⟩
  have := hNnorm
  have hc := hcompl T
  have hodd : ¬ 2 ∣ Nat.card ↥N := by
    rw [← hc.index_eq_card]; exact T.not_dvd_index
  have hpi : Subgroup.IsPiGroup {p | p ≠ 2} N := fun p hp (h2 : p = 2) =>
    hodd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  have hNbot : N = ⊥ := le_bot_iff.mp (hO ▸ Subgroup.IsPiGroup.le_oPiCore hpi)
  have hsup := hc.sup_eq_top
  rw [hNbot, bot_sup_eq] at hsup
  exact hTG hsup

/-- **`T` does not control its own `G`-fusion** (Navarro p. 139), by Isaacs Thm 5.25. -/
theorem not_controlsOwnFusion_of_oPiCore_eq_bot (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (hTG : (T : Subgroup G) ≠ ⊤) : ¬ T.ControlsOwnFusion := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact fun h => not_hasNormalPComplement_of_oPiCore_eq_bot hO T hTG
    ((OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_controlsOwnFusion T).mpr h)

/-- **`T` has odd index in `N_G(T)`**: it is a Sylow `2`-subgroup there, and its relative index
divides the odd number `[G : T]`.  This is the form the fusion argument uses, `T` being inside the
stabilizer of every inverse pair (`image_eq_self_of_conj`). -/
theorem not_two_dvd_relIndex_normalizer (T : Sylow 2 G) :
    ¬ 2 ∣ (T : Subgroup G).relIndex (Subgroup.normalizer (T : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact fun h =>
    T.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))

/-- **`T·C_G(T)` has odd index in `N_G(T)`**: it contains the Sylow `2`-subgroup `T`, whose index
in `N_G(T)` divides the odd number `[G : T]`.

This is what makes the action of `N_G(T)` on the three cyclic subgroups of order `4` factor
through a group of odd order. -/
theorem not_two_dvd_relIndex_sup_centralizer (T : Sylow 2 G) :
    ¬ 2 ∣ (((T : Subgroup G) ⊔ Subgroup.centralizer (T : Set G)).relIndex
      (Subgroup.normalizer (T : Subgroup G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle1 : (T : Subgroup G) ≤ (T : Subgroup G) ⊔ Subgroup.centralizer (T : Set G) := le_sup_left
  have hcle : Subgroup.centralizer (T : Set G) ≤ Subgroup.normalizer (T : Subgroup G) := by
    intro c hc
    have key : ∀ m : G, m ∈ (T : Subgroup G) → c * m * c⁻¹ = m := by
      intro m hm
      rw [← Subgroup.mem_centralizer_iff.mp hc m hm, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => by rw [key n hn]; exact hn, fun hn => ?_⟩
    have hfix := key _ hn
    have h2 : c * n * c⁻¹ = n := by
      calc c * n * c⁻¹ = c⁻¹ * (c * (c * n * c⁻¹) * c⁻¹) * c := by group
        _ = c⁻¹ * (c * n * c⁻¹) * c := by rw [hfix]
        _ = n := by group
    rwa [h2] at hn
  have hle2 : (T : Subgroup G) ⊔ Subgroup.centralizer (T : Set G)
      ≤ Subgroup.normalizer (T : Subgroup G) := sup_le Subgroup.le_normalizer hcle
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  have hodd : ¬ 2 ∣ (T : Subgroup G).relIndex (Subgroup.normalizer (T : Subgroup G)) := fun h =>
    T.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  exact fun h => hodd (hmul ▸ Dvd.dvd.mul_left h _)

omit [Finite G] in
/-- **`T` normalizes every cyclic subgroup generated by one of its elements** (Navarro p. 139,
"every subgroup of `P` is normal in `P`"), stated in `G`. -/
theorem sylowQ8_le_normalizer_zpowers (T : Sylow 2 G) (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2)
    {w : G} (hwT : w ∈ (T : Subgroup G)) :
    (T : Subgroup G) ≤ Subgroup.normalizer (Subgroup.zpowers w) := by
  have hconj : ∀ s : G, s ∈ (T : Subgroup G) → s * w * s⁻¹ = w ∨ s * w * s⁻¹ = w⁻¹ := by
    intro s hs
    rcases conj_eq_self_or_inv_of_quaternionTwo e ⟨w, hwT⟩ ⟨s, hs⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have key : ∀ s : G, s ∈ (T : Subgroup G) → ∀ k : ℤ,
      s * w ^ k * s⁻¹ ∈ Subgroup.zpowers w := by
    intro s hs k
    have hz : s * w ^ k * s⁻¹ = (s * w * s⁻¹) ^ k := by simp [conj_zpow]
    rcases hconj s hs with h | h
    · rw [hz, h]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) k
    · rw [hz, h]; exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers w)) k
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨k, rfl⟩ := hn
    exact key t ht k
  · obtain ⟨k, hk⟩ := hn
    have hk' : w ^ k = t * n * t⁻¹ := hk
    have hback := key t⁻¹ (inv_mem ht) k
    rw [hk'] at hback
    simpa [mul_assoc] using hback

/-- **Navarro p. 139: the fusing element may be taken in `N_G(T)`.**  If `y, z ∈ T` are
`G`-conjugate then `T` and `T^g` both normalize `⟨z⟩`, so both are Sylow `2`-subgroups of
`N_G(⟨z⟩)`; Sylow conjugacy inside `N_G(⟨z⟩)` corrects `g` to an element of `N_G(T)`, which still
carries `y` into `⟨z⟩`. -/
theorem exists_mem_normalizer_conj_mem_zpowers (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2)
    {y z : G} (hyT : y ∈ (T : Subgroup G)) (hzT : z ∈ (T : Subgroup G))
    {g : G} (hg : g * y * g⁻¹ = z) :
    ∃ u, u ∈ Subgroup.normalizer (T : Subgroup G) ∧ u * y * u⁻¹ ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have hpow : ∀ k : ℤ, z ^ k = g * y ^ k * g⁻¹ := by
    intro k; rw [← hg]; simp [conj_zpow]
  set Hz : Subgroup G := Subgroup.normalizer (Subgroup.zpowers z) with hHz
  have h1 : (T : Subgroup G) ≤ Hz := sylowQ8_le_normalizer_zpowers T e hzT
  have hTy : (T : Subgroup G) ≤ Subgroup.normalizer (Subgroup.zpowers y) :=
    sylowQ8_le_normalizer_zpowers T e hyT
  have hmove : ∀ s : G, s ∈ (T : Subgroup G) →
      ∀ n ∈ Subgroup.zpowers z, g * s * g⁻¹ * n * (g * s * g⁻¹)⁻¹ ∈ Subgroup.zpowers z := by
    intro s hs n hn
    obtain ⟨k, hk⟩ := hn
    have hk' : z ^ k = n := hk
    have hmem : s * y ^ k * s⁻¹ ∈ Subgroup.zpowers y :=
      (Subgroup.mem_normalizer_iff.mp (hTy hs) (y ^ k)).mp
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k)
    obtain ⟨m, hm⟩ := hmem
    have hm' : y ^ m = s * y ^ k * s⁻¹ := hm
    refine ⟨m, ?_⟩
    change z ^ m = _
    rw [hpow m, hm', ← hk', hpow k]
    group
  have h2 : ((g • T : Sylow 2 G) : Subgroup G) ≤ Hz := by
    rintro - ⟨s, hs, rfl⟩
    rw [hHz, Subgroup.mem_normalizer_iff]
    refine fun n => ⟨fun hn => hmove s hs n hn, fun hn => ?_⟩
    have hb := hmove s⁻¹ (inv_mem hs) _ hn
    simpa [mul_assoc] using hb
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥Hz ((g • T).subtype h2) (T.subtype h1)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hh
  refine ⟨(h : G) * g, Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh), ?_⟩
  have hrw : (h : G) * g * y * ((h : G) * g)⁻¹ = (h : G) * z * (h : G)⁻¹ := by
    rw [← hg]; group
  rw [hrw]
  exact (Subgroup.mem_normalizer_iff.mp h.2 z).mp (Subgroup.mem_zpowers z)

/-- **Navarro p. 139: one fusion of inverse pairs fuses all three.**  `N_G(T)` acts on the three
inverse pairs by conjugation (mathlib's `MulDistribMulAction (normalizer H) H`); `T` lies in the
stabilizer of each (`image_eq_self_of_conj`) and has odd index in `N_G(T)`
(`not_two_dvd_relIndex_normalizer`), so the orbit has odd size — hence `1` or `3`.  A single
nontrivial move therefore makes the action transitive.

This is the substitute for Navarro's `Aut(Q₈) = Sym(4)` step.

⚠ `Subgroup.normalizer` takes a **`Set`**, so the sort has to be written with the coercion
`((T : Subgroup G) : Set G)` spelled out; and the induced action on `Finset` lives in the
`Pointwise` scope. -/
theorem exists_smul_eq_of_mem_inversePairs (T : Sylow 2 G)
    [Fintype ↥(T : Subgroup G)] [DecidableEq ↥(T : Subgroup G)]
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2)
    {S : Finset ↥(T : Subgroup G)} (hS : S ∈ inversePairs ↥(T : Subgroup G))
    (hmove : ∃ u : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G)), u • S ≠ S) :
    ∀ S' ∈ inversePairs ↥(T : Subgroup G),
      ∃ u : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G)), u • S = S' := by
  classical
  have hsmul : ∀ u : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G)),
      u • S = S.image (Subgroup.normalizerMonoidHom (T : Subgroup G) u) := fun _ => rfl
  have hsub : ∀ u : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G)),
      u • S ∈ inversePairs ↥(T : Subgroup G) := fun u => by
    rw [hsmul u]; exact image_mem_inversePairs _ hS
  have hstab : ((T : Subgroup G).subgroupOf (Subgroup.normalizer ((T : Subgroup G) : Set G)))
      ≤ MulAction.stabilizer _ S := by
    intro u hu
    change u • S = S
    rw [hsmul u]
    exact image_eq_self_of_conj e (t := ⟨(u : G), hu⟩) (fun s => rfl) hS
  have hodd : ¬ 2 ∣ (MulAction.stabilizer
      ↥(Subgroup.normalizer ((T : Subgroup G) : Set G)) S).index :=
    fun h => not_two_dvd_relIndex_normalizer T (h.trans (Subgroup.index_dvd_of_le hstab))
  exact orbit_eq_of_odd_of_subset_card_three hodd (card_inversePairs_of_quaternionTwo e) hsub hmove

/-- **Navarro p. 139: two elements of order `4` in `T` that fuse in `G` but not in `T`.**
Unfolding the failure of fusion control (`not_controlsOwnFusion_of_oPiCore_eq_bot`); the two
elements must have order `4` because `Q₈` has a *unique* involution, so involutions cannot fuse
nontrivially. -/
theorem exists_orderFour_fused (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤) :
    ∃ x y : G, ∃ _ : x ∈ (T : Subgroup G), ∃ _ : y ∈ (T : Subgroup G), x ^ 2 ≠ 1 ∧
      (∃ g : G, g * x * g⁻¹ = y) ∧ ∀ u ∈ (T : Subgroup G), u * x * u⁻¹ ≠ y := by
  have hnc := not_controlsOwnFusion_of_oPiCore_eq_bot hO T hTG
  rw [Sylow.ControlsOwnFusion, Subgroup.ControlsFusionIn] at hnc
  push Not at hnc
  obtain ⟨x, y, hx, hy, ⟨g, hg⟩, hno⟩ := hnc
  refine ⟨x, y, hx, hy, ?_, ⟨g, hg⟩, fun u hu h => hno u hu h⟩
  intro hx2
  -- an involution (or the identity) of `Q₈` is fixed by every conjugation
  have hy2 : y ^ 2 = 1 := by
    rw [← hg, show g * x * g⁻¹ = MulAut.conj g x from rfl, ← map_pow, hx2, map_one]
  have hxy : x = y := by
    rcases eq_or_ne x 1 with rfl | hx1
    · rw [← hg]; group
    · have hy1 : y ≠ 1 := by
        rw [← hg]
        exact fun h => hx1 ((MulAut.conj g).injective (h.trans (map_one (MulAut.conj g)).symm))
      have := eq_of_sq_eq_one_of_quaternionTwo e (a := (⟨x, hx⟩ : ↥(T : Subgroup G)))
        (b := ⟨y, hy⟩) (Subtype.ext (by push_cast; exact hx2))
        (fun h => hx1 (congrArg Subtype.val h)) (Subtype.ext (by push_cast; exact hy2))
        (fun h => hy1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  exact hno 1 (Subgroup.one_mem _) (by rw [hxy]; group)

/-- **Navarro p. 139: some element of `N_G(T)` genuinely moves an inverse pair.**

Take `x, y ∈ T` of order `4`, `G`-conjugate but not `T`-conjugate
(`exists_orderFour_fused`), and correct the conjugator into `N_G(T)`
(`exists_mem_normalizer_conj_mem_zpowers`).  If the corrected `u` fixed the pair `{x, x⁻¹}` then
`u x u⁻¹ ∈ {x, x⁻¹}`; but it also lies in `⟨y⟩`, hence equals `y` or `y⁻¹`
(`eq_or_eq_inv_of_mem_zpowers_of_quaternionTwo`).  Either way `y ∈ {x, x⁻¹}`, and then `x` and `y`
*are* `T`-conjugate (`T` contains an inverting element) — a contradiction. -/
theorem exists_smul_ne_of_oPiCore_eq_bot (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    [Fintype ↥(T : Subgroup G)] [DecidableEq ↥(T : Subgroup G)]
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤) :
    ∃ S ∈ inversePairs ↥(T : Subgroup G),
      ∃ u : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G)), u • S ≠ S := by
  classical
  obtain ⟨x, y, hx, hy, hx2, ⟨g, hg⟩, hno⟩ := exists_orderFour_fused hO T e hTG
  set X : ↥(T : Subgroup G) := ⟨x, hx⟩ with hX
  set Y : ↥(T : Subgroup G) := ⟨y, hy⟩ with hY
  have hX2 : X ^ 2 ≠ 1 := fun h => hx2 (congrArg Subtype.val h)
  have hY2 : Y ^ 2 ≠ 1 := by
    intro h
    refine hx2 ?_
    have hyc : y ^ 2 = 1 := congrArg Subtype.val h
    rw [← hg, show g * x * g⁻¹ = MulAut.conj g x from rfl, ← map_pow] at hyc
    exact (MulAut.conj g).injective (hyc.trans (map_one (MulAut.conj g)).symm)
  -- `x` and `y` are not `T`-conjugate, so `y ∉ {x, x⁻¹}`
  have hfinal : y = x ∨ y = x⁻¹ → False := by
    rintro (h | h)
    · exact hno 1 (Subgroup.one_mem _) (by rw [h]; group)
    · obtain ⟨V, hV⟩ := exists_conj_eq_inv_of_quaternionTwo e hX2
      refine hno (V : G) V.2 ?_
      rw [h]
      exact congrArg Subtype.val hV
  obtain ⟨u, hu, hmem⟩ := exists_mem_normalizer_conj_mem_zpowers T e hx hy hg
  refine ⟨{X, X⁻¹}, Finset.mem_image.mpr ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX2⟩, rfl⟩,
    ⟨u, hu⟩, fun hcontra => ?_⟩
  -- the conjugate of `X` lies in the pair and in `⟨Y⟩`
  have hUmem : (⟨u, hu⟩ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) • X
      ∈ ({X, X⁻¹} : Finset ↥(T : Subgroup G)) := by
    rw [← hcontra]
    exact Finset.smul_mem_smul_finset (Finset.mem_insert_self _ _)
  have hUzp : (⟨u, hu⟩ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) • X
      ∈ Subgroup.zpowers Y := by
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, Subtype.ext hk⟩
  have hU2 : ((⟨u, hu⟩ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) • X) ^ 2 ≠ 1 := by
    intro h
    refine hX2 (?_ : X ^ 2 = 1)
    have : (u * x * u⁻¹) ^ 2 = 1 := congrArg Subtype.val h
    rw [show u * x * u⁻¹ = MulAut.conj u x from rfl, ← map_pow] at this
    exact Subtype.ext ((MulAut.conj u).injective (this.trans (map_one (MulAut.conj u)).symm))
  rcases eq_or_eq_inv_of_mem_zpowers_of_quaternionTwo e hU2 hY2 hUzp with hUY | hUY <;>
    rw [Finset.mem_insert, Finset.mem_singleton, hUY] at hUmem
  · rcases hUmem with h | h
    · exact hfinal (Or.inl (congrArg Subtype.val h))
    · exact hfinal (Or.inr (congrArg Subtype.val h))
  · rcases hUmem with h | h
    · exact hfinal (Or.inr (congrArg Subtype.val (inv_eq_iff_eq_inv.mp h)))
    · exact hfinal (Or.inl (congrArg Subtype.val (inv_injective h)))

/-- **Navarro p. 139: `G` has a single class of elements of order `4`** ("the claim has been
proven").  All three inverse pairs of `T` fuse under `N_G(T)`
(`exists_smul_eq_of_mem_inversePairs` fed by `exists_smul_ne_of_oPiCore_eq_bot`), and `T` itself
fuses `w` with `w⁻¹`, so any two elements of order `4` of `T` are `G`-conjugate. -/
theorem isConj_of_orderFour (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤)
    {v w : G} (hv : v ∈ (T : Subgroup G)) (hw : w ∈ (T : Subgroup G))
    (hv2 : v ^ 2 ≠ 1) (hw2 : w ^ 2 ≠ 1) :
    ∃ g ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), g * v * g⁻¹ = w := by
  classical
  let : Fintype ↥(T : Subgroup G) := Fintype.ofFinite _
  set V : ↥(T : Subgroup G) := ⟨v, hv⟩ with hVdef
  set W : ↥(T : Subgroup G) := ⟨w, hw⟩ with hWdef
  have hV2 : V ^ 2 ≠ 1 := fun h => hv2 (congrArg Subtype.val h)
  have hW2 : W ^ 2 ≠ 1 := fun h => hw2 (congrArg Subtype.val h)
  have hVmem : ({V, V⁻¹} : Finset ↥(T : Subgroup G)) ∈ inversePairs ↥(T : Subgroup G) :=
    Finset.mem_image.mpr ⟨V, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV2⟩, rfl⟩
  have hWmem : ({W, W⁻¹} : Finset ↥(T : Subgroup G)) ∈ inversePairs ↥(T : Subgroup G) :=
    Finset.mem_image.mpr ⟨W, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW2⟩, rfl⟩
  obtain ⟨S₀, hS₀, u₀, hmove⟩ := exists_smul_ne_of_oPiCore_eq_bot hO T e hTG
  have htrans := exists_smul_eq_of_mem_inversePairs T e hS₀ ⟨u₀, hmove⟩
  obtain ⟨a, ha⟩ := htrans _ hVmem
  obtain ⟨b, hb⟩ := htrans _ hWmem
  have hba : (b * a⁻¹) • ({V, V⁻¹} : Finset ↥(T : Subgroup G)) = {W, W⁻¹} := by
    rw [mul_smul, ← ha, inv_smul_smul, hb]
  have hmem : (b * a⁻¹) • V ∈ ({W, W⁻¹} : Finset ↥(T : Subgroup G)) := by
    rw [← hba]
    exact Finset.smul_mem_smul_finset (Finset.mem_insert_self _ _)
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hcv : ((b * a⁻¹ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) : G) * v
      * ((b * a⁻¹ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) : G)⁻¹
      = ((b * a⁻¹) • V : ↥(T : Subgroup G)) := rfl
  rcases hmem with h | h
  · exact ⟨_, (b * a⁻¹).2, hcv.trans (congrArg Subtype.val h)⟩
  · obtain ⟨d, hd⟩ := exists_conj_eq_inv_of_quaternionTwo e hW2
    have hdG : (d : G) * w * (d : G)⁻¹ = w⁻¹ := congrArg Subtype.val hd
    refine ⟨(d : G)⁻¹ * ((b * a⁻¹ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) : G),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer d.2)) (b * a⁻¹).2, ?_⟩
    have hstep : ((b * a⁻¹ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) : G) * v
        * ((b * a⁻¹ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) : G)⁻¹ = w⁻¹ :=
      hcv.trans (congrArg Subtype.val h)
    calc (d : G)⁻¹ * ((b * a⁻¹ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) : G) * v
          * ((d : G)⁻¹ * ((b * a⁻¹ : ↥(Subgroup.normalizer
            ((T : Subgroup G) : Set G))) : G))⁻¹
        = (d : G)⁻¹ * (((b * a⁻¹ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) : G) * v
          * ((b * a⁻¹ : ↥(Subgroup.normalizer ((T : Subgroup G) : Set G))) : G)⁻¹)
          * (d : G) := by group
      _ = (d : G)⁻¹ * w⁻¹ * (d : G) := by rw [hstep]
      _ = w := by rw [← hdG]; group

omit [Finite G] in
/-- **`N_G(T) ≤ C_G(t)`** for the involution `t` of `T ≅ Q₈` (Navarro p. 139, "since
`{1,t} = Z(P) ⊴ N_G(P)`, it follows that `g ∈ C_G(t)`").  A conjugate of `t` by an element of
`N_G(T)` is again an involution of `T`, and `Q₈` has only one. -/
theorem normalizer_le_centralizer_involution (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) {t : G} (htT : t ∈ (T : Subgroup G))
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ Subgroup.centralizer {t} := by
  intro u hu
  have huT : u * t * u⁻¹ ∈ (T : Subgroup G) := ((Subgroup.mem_normalizer_iff.mp hu) t).mp htT
  have hsq : (u * t * u⁻¹) ^ 2 = 1 := by
    rw [show u * t * u⁻¹ = MulAut.conj u t from rfl, ← map_pow, ht2, map_one]
  have hne : u * t * u⁻¹ ≠ 1 := fun h =>
    ht1 ((MulAut.conj u).injective (h.trans (map_one (MulAut.conj u)).symm))
  have hkey : (⟨u * t * u⁻¹, huT⟩ : ↥(T : Subgroup G)) = ⟨t, htT⟩ :=
    eq_of_sq_eq_one_of_quaternionTwo e (Subtype.ext (by push_cast; exact hsq))
      (fun h => hne (congrArg Subtype.val h)) (Subtype.ext (by push_cast; exact ht2))
      (fun h => ht1 (congrArg Subtype.val h))
  have hut : u * t * u⁻¹ = t := congrArg Subtype.val hkey
  rw [Subgroup.mem_centralizer_iff]
  rintro m hm
  rw [Set.mem_singleton_iff] at hm
  subst hm
  calc m * u = u * m * u⁻¹ * u := by rw [hut]
    _ = u * m := by group

/-! ### Navarro pp. 139–140: the "analysis at `y`"

For an element `y` of order `4` of `T ≅ Q₈`, the cyclic group `⟨y⟩` is a Sylow `2`-subgroup of
`C_G(y)`.  Indeed `y` is central in `C_G(y)`, so `⟨y⟩` is a normal `2`-subgroup and is contained in
some Sylow `2`-subgroup `S` of `C_G(y)`; and `|S| ≠ 8`, for otherwise `S` would be a Sylow
`2`-subgroup of `G` as well, hence isomorphic to `Q₈`, with `y` a *central* element of order `4` —
which `Q₈` does not have (`sq_eq_one_of_mem_center_of_quaternionTwo`).  So `|S| = 4 = |⟨y⟩|`.

Burnside then gives `C_G(y)` a normal `2`-complement
(`hasNormalPComplement_centralizer_of_sylow_zpowers`), which is what makes `IBr(b₀) = {1}` and the
Cartan matrix of the principal block of `C_G(y)` equal to `(4)`. -/

/-- **`⟨y⟩` is a Sylow `2`-subgroup of `C_G(y)`** for `y` of order `4` in a quaternion Sylow
`2`-subgroup `T` of `G` (Navarro p. 139, "analysis at `y`").

The hypothesis `hy : y ∈ C_G(y)` is of course automatic; it is taken as an argument so that the
element `⟨y, hy⟩` matches the one in `hasNormalPComplement_centralizer_of_sylow_zpowers`. -/
theorem sylow_centralizer_eq_zpowers (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) {y : G} (hyT : y ∈ (T : Subgroup G))
    (hy2 : y ^ 2 ≠ 1) (hy : y ∈ Subgroup.centralizer ({y} : Set G))
    (S : Sylow 2 ↥(Subgroup.centralizer ({y} : Set G))) :
    (S : Subgroup ↥(Subgroup.centralizer ({y} : Set G)))
      = Subgroup.zpowers (⟨y, hy⟩ : ↥(Subgroup.centralizer ({y} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `⟨y⟩` is central in `C_G(y)`, hence normal there
  have hcentral : Subgroup.zpowers (⟨y, hy⟩ : ↥(Subgroup.centralizer ({y} : Set G)))
      ≤ Subgroup.center ↥(Subgroup.centralizer ({y} : Set G)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_
    push_cast
    exact ((Subgroup.mem_centralizer_iff.mp h.2) y rfl).symm
  have : (Subgroup.zpowers (⟨y, hy⟩ : ↥(Subgroup.centralizer ({y} : Set G)))).Normal :=
    ⟨fun n hn g => by
      have hc : g * n = n * g := Subgroup.mem_center_iff.mp (hcentral hn) g
      have hrw : g * n * g⁻¹ = n := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      rw [hrw]; exact hn⟩
  -- it has order `4`
  have hy2' : (⟨y, hyT⟩ : ↥(T : Subgroup G)) ^ 2 ≠ 1 := fun h => hy2 (by
    have hval := congrArg (Subtype.val : ↥(T : Subgroup G) → G) h
    push_cast at hval
    exact hval)
  have horder : orderOf (⟨y, hy⟩ : ↥(Subgroup.centralizer ({y} : Set G))) = 4 := by
    rw [Subgroup.orderOf_mk y hy, ← Subgroup.orderOf_mk y hyT]
    exact orderOf_eq_four_of_quaternionTwo e hy2'
  have hcard4 : Nat.card ↥(Subgroup.zpowers
      (⟨y, hy⟩ : ↥(Subgroup.centralizer ({y} : Set G)))) = 4 := by
    rw [Nat.card_zpowers, horder]
  -- so it sits inside `S`
  have hle : Subgroup.zpowers (⟨y, hy⟩ : ↥(Subgroup.centralizer ({y} : Set G)))
      ≤ (S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))) :=
    (IsPGroup.of_card (p := 2) (n := 2) (by rw [hcard4]; norm_num)).le_sylow_of_normal S
  have hdvd4 : 4 ∣ Nat.card ↥(S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))) := by
    rw [← hcard4]; exact card_dvd_card_of_le hle
  -- and `|S|` divides `|G|₂ = 8`
  obtain ⟨Q, hQ⟩ :=
    (S.2.map (Subgroup.subtype (Subgroup.centralizer ({y} : Set G)))).exists_le_sylow
  have hQ8 : Nat.card ↥(Q : Subgroup G) = 8 :=
    card_eq_eight_of_quaternionTwo (nonempty_mulEquiv_quaternionTwo_of_sylow T Q e).some
  have hcardmap : Nat.card ↥((S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))).map
      (Subgroup.subtype (Subgroup.centralizer ({y} : Set G))))
      = Nat.card ↥(S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))) :=
    Subgroup.card_subtype _ _
  have hdvd8 : Nat.card ↥(S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))) ∣ 8 := by
    rw [← hQ8, ← hcardmap]; exact card_dvd_card_of_le hQ
  by_cases h8 : Nat.card ↥(S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))) = 8
  · -- `|S| = 8` would make `S` a Sylow `2`-subgroup of `G` with a central element of order `4`
    exfalso
    have hmapQ : (S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))).map
        (Subgroup.subtype (Subgroup.centralizer ({y} : Set G))) = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hQ (le_of_eq (by rw [hQ8, hcardmap, h8]))
    have hyQ : y ∈ (Q : Subgroup G) := by
      rw [← hmapQ]
      exact ⟨⟨y, hy⟩, hle (Subgroup.mem_zpowers _), rfl⟩
    have hcenter : (⟨y, hyQ⟩ : ↥(Q : Subgroup G)) ∈ Subgroup.center ↥(Q : Subgroup G) := by
      refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
      push_cast
      have hgC : (g : G) ∈ Subgroup.centralizer ({y} : Set G) := by
        have hgmem : (g : G) ∈ (S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))).map
            (Subgroup.subtype (Subgroup.centralizer ({y} : Set G))) := by
          rw [hmapQ]; exact g.2
        obtain ⟨c, -, hc⟩ := hgmem
        rw [← hc]; exact c.2
      exact ((Subgroup.mem_centralizer_iff.mp hgC) y rfl).symm
    refine hy2 ?_
    have hsq := sq_eq_one_of_mem_center_of_quaternionTwo
      (nonempty_mulEquiv_quaternionTwo_of_sylow T Q e).some hcenter
    have hval := congrArg (Subtype.val : ↥(Q : Subgroup G) → G) hsq
    push_cast at hval
    exact hval
  · -- so `|S| = 4 = |⟨y⟩|`
    have h4 : Nat.card ↥(S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))) = 4 := by
      have hpos : 0 < Nat.card ↥(S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))) :=
        Nat.card_pos
      have hle8 : Nat.card ↥(S : Subgroup ↥(Subgroup.centralizer ({y} : Set G))) ≤ 8 :=
        Nat.le_of_dvd (by norm_num) hdvd8
      obtain ⟨k, hk⟩ := hdvd4
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [h4, hcard4]))).symm

/-- **`C_G(y)` has a normal `2`-complement** for `y` of order `4` in a quaternion Sylow
`2`-subgroup `T` of `G` (Navarro p. 139, "analysis at `y`": "`C_G(y)` has a normal `2`-complement,
and therefore `IBr(b₀) = {1_{C_G(y)}}`").

Its Sylow `2`-subgroup is `⟨y⟩` (`sylow_centralizer_eq_zpowers`), which is central there, so
Burnside's transfer theorem applies. -/
theorem hasNormalPComplement_centralizer_orderFour (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) {y : G} (hyT : y ∈ (T : Subgroup G))
    (hy2 : y ^ 2 ≠ 1) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement 2 ↥(Subgroup.centralizer ({y} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy : y ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun m hm => by
      rw [Set.mem_singleton_iff] at hm; subst hm; rfl
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({y} : Set G))) := inferInstance
  exact hasNormalPComplement_centralizer_of_sylow_zpowers y hy S
    (sylow_centralizer_eq_zpowers T e hyT hy2 hy S)

/-! ### Navarro p. 141: the "analysis at `t`"

`T` normalises itself and `N_G(T) ≤ C_G(t)`, so `T ≤ C_G(t)`; being a Sylow `2`-subgroup of `G` it
is one of `C_G(t)` (`Sylow.subtype`).  Hence the Sylow `2`-subgroups of `C_G(t)/⟨t⟩` are
`Q₈/Z(Q₈)`, a Klein four group — `card_quotient_zpowers_of_quaternionTwo` and
`sq_eq_one_quotient_zpowers_of_quaternionTwo`. -/

/-- **Navarro p. 139, sharpened: the elements of order `4` of `T` are `C_G(t)`-conjugate.**
This is the form p. 141 uses ("the elements of order `4` of `P` are `C_G(t)`-conjugate"): the
fusing element of `isConj_of_orderFour` lies in `N_G(T)`, and `N_G(T) ≤ C_G(t)`. -/
theorem isConj_centralizer_of_orderFour (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤)
    {t : G} (htT : t ∈ (T : Subgroup G)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    {v w : G} (hv : v ∈ (T : Subgroup G)) (hw : w ∈ (T : Subgroup G))
    (hv2 : v ^ 2 ≠ 1) (hw2 : w ^ 2 ≠ 1) :
    ∃ g ∈ Subgroup.centralizer ({t} : Set G), g * v * g⁻¹ = w := by
  obtain ⟨g, hgN, hg⟩ := isConj_of_orderFour hO T e hTG hv hw hv2 hw2
  exact ⟨g, normalizer_le_centralizer_involution T e htT ht2 ht1 hgN, hg⟩

omit [Finite G] in
/-- **`T ≤ C_G(t)`** for the involution `t` of `T ≅ Q₈` — Navarro p. 141's "`P` is a Sylow
`2`-subgroup of `C_G(t)`", the form that `Sylow.subtype` consumes. -/
theorem sylowQ8_le_centralizer_involution (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) {t : G} (htT : t ∈ (T : Subgroup G))
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    (T : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) :=
  le_trans Subgroup.le_normalizer (normalizer_le_centralizer_involution T e htT ht2 ht1)

omit [Finite G] in
/-- **`⟨t⟩` is normal in `C_G(t)`** — it is central there. -/
theorem zpowers_self_normal_centralizer (t : G) (htC : t ∈ Subgroup.centralizer ({t} : Set G)) :
    (Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))).Normal :=
  ⟨fun n hn g => by
    have hc : g * n = n * g :=
      Subgroup.mem_center_iff.mp (zpowers_self_le_center_centralizer t htC hn) g
    rw [show g * n * g⁻¹ = n by rw [hc, mul_assoc, mul_inv_cancel, mul_one]]
    exact hn⟩

/-- **Navarro p. 141: two elements of `T` whose images in `C_G(t)/⟨t⟩` are non-trivial have
conjugate images.**  Such an element lies outside `⟨t⟩`, hence has order `4` because the involution
of `Q₈` is unique; and the elements of order `4` of `T` are `C_G(t)`-conjugate
(`isConj_centralizer_of_orderFour`). -/
theorem isConj_quotient_of_mem_sylowQ8 (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤)
    {t : G} (htT : t ∈ (T : Subgroup G)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htC : t ∈ Subgroup.centralizer ({t} : Set G))
    [(Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))).Normal]
    {wa wb : ↥(Subgroup.centralizer ({t} : Set G))}
    (hwa : (wa : G) ∈ (T : Subgroup G)) (hwb : (wb : G) ∈ (T : Subgroup G))
    (ha1 : (QuotientGroup.mk wa :
      ↥(Subgroup.centralizer ({t} : Set G)) ⧸ Subgroup.zpowers ⟨t, htC⟩) ≠ 1)
    (hb1 : (QuotientGroup.mk wb :
      ↥(Subgroup.centralizer ({t} : Set G)) ⧸ Subgroup.zpowers ⟨t, htC⟩) ≠ 1) :
    IsConj (QuotientGroup.mk wa :
        ↥(Subgroup.centralizer ({t} : Set G)) ⧸ Subgroup.zpowers ⟨t, htC⟩)
      (QuotientGroup.mk wb) := by
  classical
  -- an element of `T` whose image is non-trivial has order `4`
  have horder : ∀ w : ↥(Subgroup.centralizer ({t} : Set G)), (w : G) ∈ (T : Subgroup G) →
      (QuotientGroup.mk w :
        ↥(Subgroup.centralizer ({t} : Set G)) ⧸ Subgroup.zpowers ⟨t, htC⟩) ≠ 1 →
      (w : G) ^ 2 ≠ 1 := by
    intro w hw hw1 hsq
    refine hw1 ?_
    rw [QuotientGroup.eq_one_iff]
    by_cases hone : (w : G) = 1
    · rw [show w = 1 from Subtype.ext hone]; exact Subgroup.one_mem _
    · have hwt : (w : G) = t := congrArg Subtype.val
        (eq_of_sq_eq_one_of_quaternionTwo e (a := (⟨(w : G), hw⟩ : ↥(T : Subgroup G)))
          (b := (⟨t, htT⟩ : ↥(T : Subgroup G))) (Subtype.ext (by push_cast; exact hsq))
          (fun h => hone (congrArg Subtype.val h)) (Subtype.ext (by push_cast; exact ht2))
          (fun h => ht1 (congrArg Subtype.val h)))
      rw [show w = (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G))) from Subtype.ext hwt]
      exact Subgroup.mem_zpowers _
  obtain ⟨g, hgC, hg⟩ := isConj_centralizer_of_orderFour hO T e hTG htT ht2 ht1 hwa hwb
    (horder wa hwa ha1) (horder wb hwb hb1)
  refine isConj_iff.mpr ⟨QuotientGroup.mk (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({t} : Set G))), ?_⟩
  have hC : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({t} : Set G))) * wa
      * (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))⁻¹ = wb :=
    Subtype.ext (by push_cast; exact hg)
  calc QuotientGroup.mk (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({t} : Set G))) * QuotientGroup.mk wa
        * (QuotientGroup.mk (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({t} : Set G))))⁻¹
      = QuotientGroup.mk ((⟨g, hgC⟩ : ↥(Subgroup.centralizer ({t} : Set G))) * wa
          * (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))⁻¹) := rfl
    _ = QuotientGroup.mk wb := by rw [hC]

/-- **Navarro p. 141: all involutions of `C_G(t)/⟨t⟩` are conjugate.**  Each is conjugate into the
Sylow `2`-subgroup `T̄` — the image of `T` — (`exists_conj_mem_sylow`), and any two non-identity
elements of `T̄` are conjugate (`isConj_quotient_of_mem_sylowQ8`). -/
theorem isConj_of_sq_eq_one_quotient_centralizer (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤)
    {t : G} (htT : t ∈ (T : Subgroup G)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htC : t ∈ Subgroup.centralizer ({t} : Set G))
    [(Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))).Normal]
    {x y : ↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))}
    (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) (hy1 : y ≠ 1) (hy2 : y ^ 2 = 1) : IsConj x y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tbar : Sylow 2 (↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))) :=
    (T.subtype (sylowQ8_le_centralizer_involution T e htT ht2 ht1)).mapSurjective
      (QuotientGroup.mk'_surjective _) with hTbar
  -- an involution of the quotient is a `2`-element, hence conjugate into `T̄`
  have hpg : ∀ z : ↥(Subgroup.centralizer ({t} : Set G)) ⧸
        Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G))),
      z ≠ 1 → z ^ 2 = 1 → IsPGroup 2 (Subgroup.zpowers z) := by
    intro z hz1 hz2
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact ((Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz2)).resolve_left
      fun h => hz1 (orderOf_eq_one_iff.mp h)
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow (hpg x hx1 hx2) Tbar
  obtain ⟨d, hd⟩ := exists_conj_mem_sylow (hpg y hy1 hy2) Tbar
  -- the conjugates are still non-trivial, and lie in the image of `T`
  have hne : ∀ (u z : ↥(Subgroup.centralizer ({t} : Set G)) ⧸
        Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))),
      z ≠ 1 → u * z * u⁻¹ ≠ 1 := fun u z hz h => hz (by
    calc z = u⁻¹ * (u * z * u⁻¹) * u := by group
      _ = u⁻¹ * 1 * u := by rw [h]
      _ = 1 := by group)
  have hunpack : ∀ z : ↥(Subgroup.centralizer ({t} : Set G)) ⧸
        Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G))),
      z ∈ (Tbar : Subgroup _) →
      ∃ w : ↥(Subgroup.centralizer ({t} : Set G)), (w : G) ∈ (T : Subgroup G) ∧
        QuotientGroup.mk w = z := by
    intro z hz
    rw [hTbar, Sylow.coe_mapSurjective, Subgroup.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hw
    exact ⟨w, hw, hwz⟩
  obtain ⟨wa, hwaT, hwa⟩ := hunpack _ hc
  obtain ⟨wb, hwbT, hwb⟩ := hunpack _ hd
  have hkey := isConj_quotient_of_mem_sylowQ8 hO T e hTG htT ht2 ht1 htC hwaT hwbT
    (by rw [hwa]; exact hne c x hx1) (by rw [hwb]; exact hne d y hy1)
  rw [hwa, hwb] at hkey
  exact ((isConj_iff.mpr ⟨c, rfl⟩).trans hkey).trans (isConj_iff.mpr ⟨d, rfl⟩).symm

/-- **Every `2`-element of `C_G(t)/⟨t⟩` is an involution.**  A `2`-element conjugates into the
Sylow `2`-subgroup `T̄` (the image of `T`), and every square of `T ≅ Q₈` already lies in `⟨t⟩`
(`sq_eq_one_or_eq_of_quaternionTwo`), so `T̄` has exponent `2`.

Together with `isConj_of_sq_eq_one_quotient_centralizer` this is the hypothesis `hconjall` of
Navarro (7.2)/(7.4) for the group `C_G(t)/⟨t⟩`: every nontrivial `2`-element is conjugate to a
fixed involution. -/
theorem sq_eq_one_of_isPGroup_zpowers_quotient_centralizer (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2)
    {t : G} (htT : t ∈ (T : Subgroup G)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htC : t ∈ Subgroup.centralizer ({t} : Set G))
    [(Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))).Normal]
    {v : ↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))}
    (hv : IsPGroup 2 (Subgroup.zpowers v)) : v ^ 2 = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tbar : Sylow 2 (↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))) :=
    (T.subtype (sylowQ8_le_centralizer_involution T e htT ht2 ht1)).mapSurjective
      (QuotientGroup.mk'_surjective _) with hTbar
  -- every element of `T̄` squares to `1`, because every square of `T` lies in `⟨t⟩`
  have hTbar2 : ∀ z ∈ (Tbar : Subgroup (↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G))))), z ^ 2 = 1 := by
    intro z hz
    rw [hTbar, Sylow.coe_mapSurjective, Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hw
    have hwsq : (⟨(w : G), hw⟩ : ↥(T : Subgroup G)) ^ 2 = 1 ∨
        (⟨(w : G), hw⟩ : ↥(T : Subgroup G)) ^ 2 = ⟨t, htT⟩ :=
      sq_eq_one_or_eq_of_quaternionTwo e (Subtype.ext (by push_cast; exact ht2))
        (fun h => ht1 (by simpa using congrArg Subtype.val h)) _
    have hw2G : (w : G) ^ 2 = 1 ∨ (w : G) ^ 2 = t := by
      rcases hwsq with h | h
      · exact Or.inl (by simpa using congrArg Subtype.val h)
      · exact Or.inr (by simpa using congrArg Subtype.val h)
    have hmem : w ^ 2 ∈ Subgroup.zpowers (⟨t, htC⟩ :
        ↥(Subgroup.centralizer ({t} : Set G))) := by
      rcases hw2G with h | h
      · rw [show w ^ 2 = 1 from Subtype.ext (by push_cast; exact h)]
        exact Subgroup.one_mem _
      · rw [show w ^ 2 = (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G))) from
          Subtype.ext (by push_cast; exact h)]
        exact Subgroup.mem_zpowers _
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  -- a `2`-element conjugates into `T̄`
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow hv Tbar
  have hcsq := hTbar2 _ hc
  have hconj : (c * v * c⁻¹) ^ 2 = c * v ^ 2 * c⁻¹ := by
    simp
  rw [hconj] at hcsq
  have h1 : c * v ^ 2 = c := by simpa using congrArg (· * c) hcsq
  exact mul_left_cancel (h1.trans (mul_one c).symm)

/-- **The Sylow `2`-subgroups of `C_G(t)/⟨t⟩` have order `4`** (Navarro p. 141: "`P/⟨t⟩` is a
Klein four Sylow `2`-subgroup of `C_G(t)/⟨t⟩`").

`T ≅ Q₈` has order `8` and `⟨t⟩` has order `2`, so the image `T̄` has order `4`
(`QuotientGroup.card_map_mk'_mul_card`); every Sylow `2`-subgroup of the quotient is conjugate
to `T̄`.

This is what makes `hasNormalPComplement_centralizer_of_card_sylow_four` applicable, hence what
supplies the normal `2`-complement of `C_{C_G(t)/⟨t⟩}(ȳ)` that Navarro (7.2)/(7.4) needs. -/
theorem card_sylow_quotient_centralizer (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2)
    {t : G} (htT : t ∈ (T : Subgroup G)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htC : t ∈ Subgroup.centralizer ({t} : Set G))
    [(Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))).Normal]
    (S : Sylow 2 (↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G))))) :
    Nat.card ↥(S : Subgroup (↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G))))) = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : (T : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) :=
    sylowQ8_le_centralizer_involution T e htT ht2 ht1
  set T' : Sylow 2 ↥(Subgroup.centralizer ({t} : Set G)) := T.subtype hTC with hT'
  set Tbar : Sylow 2 (↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))) :=
    T'.mapSurjective (QuotientGroup.mk'_surjective _) with hTbar
  -- `|T| = 8`
  have hT8 : Nat.card ↥(T' : Subgroup ↥(Subgroup.centralizer ({t} : Set G))) = 8 := by
    rw [hT', Sylow.coe_subtype,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv,
      Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  -- `|⟨t⟩| = 2`
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hNz2 : Nat.card ↥(Subgroup.zpowers
      (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))) = 2 := by
    rw [Nat.card_zpowers,
      ← orderOf_injective (Subgroup.centralizer ({t} : Set G)).subtype
        (Subgroup.subtype_injective _) ⟨t, htC⟩]
    exact hord
  -- `⟨t⟩ ≤ T`
  have hle : Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G)))
      ≤ (T' : Subgroup ↥(Subgroup.centralizer ({t} : Set G))) := by
    rw [hT', Sylow.coe_subtype]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr htT)
  have hkey := QuotientGroup.card_map_mk'_mul_card hle
  rw [hNz2, hT8] at hkey
  have hTbarcard : Nat.card ↥(Tbar : Subgroup (↥(Subgroup.centralizer ({t} : Set G)) ⧸
      Subgroup.zpowers (⟨t, htC⟩ : ↥(Subgroup.centralizer ({t} : Set G))))) = 4 := by
    rw [hTbar, Sylow.coe_mapSurjective]
    omega
  rw [← hTbarcard]
  exact Nat.card_congr (Sylow.equiv S Tbar).toEquiv
end OddOrder.GroupTheory
