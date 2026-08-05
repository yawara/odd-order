/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiEndgame
import OddOrder.GroupTheory.CardSupInf
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.Isaacs.Ch05_Transfer.Main
import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Brauer–Suzuki: the `Q₈` case (Navarro, *Characters and Blocks*, pp. 139–146)

The `|S| ≥ 16` branch of Brauer–Suzuki is `brauerSuzuki_of_quaternionSylow`, proved by ordinary
exceptional characters (Gorenstein Ch. 12).  For `S ≅ Q₈` that argument breaks down and modular
character theory is genuinely required; Navarro's proof (pp. 139–146) is the spine being
formalised in issue 9506, on top of the Brauer-character/block machinery of
`GroupTheory/RepresentationTheory/Modular/`.

This file isolates **what is still missing**.  Two reductions are done here, leaving exactly
Navarro's own statement:

* the group-theoretic endgame is shared with the `|S| ≥ 16` branch and already proved
  (`oPiCore_sup_centralizer_eq_top_of_mk_mem_center`): once the image of the involution is central
  modulo `O_{2'}(G)`, the conclusion `G = O_{2'}(G)·C_G(z)` follows;
* the passage to `Ḡ = G/O_{2'}(G)` (`q8_mk_mem_center`) is legitimate because `O_{2'}(Ḡ) = 1` and
  the Sylow `2`-subgroups of `Ḡ` are again `Q₈` — the odd core meets `T` trivially
  (`sylowTwo_inf_oPiCore_eq_bot`).

The reduction paragraph of p. 139 is then carried out in full, by induction on `|G|`: if the
Sylow `2`-subgroup is all of `G` the involution is central because `Z(Q₈) ≠ 1`; otherwise a
proper normal subgroup `N` containing `z` either misses part of `T` — then `T ⊓ N` is a cyclic
Sylow `2`-subgroup of `N`, Burnside makes `N` a cyclic `2`-group and `z` central — or contains
`T`, and induction on `N` puts `z` in `Z(N)`, whence in `Z(G)`.

So the whole content of the `Q₈` case is `q8_exists_proper_normal`: the existence of that proper
normal subgroup, i.e. Navarro's "find a nontrivial character in the principal block of `G` which
contains `t` in its kernel".

## Main results

* `OddOrder.GroupTheory.q8_exists_proper_normal` — **the remaining mathematics**
  (issue 9506, `sorry`)
* `OddOrder.GroupTheory.mem_center_of_normal_of_isCyclic` — how both branches of Navarro's
  reduction on p. 139 finish
* `OddOrder.GroupTheory.isCyclic_of_ne_top_of_quaternionTwo` — every proper subgroup of `Q₈` is
  cyclic, the dichotomy "`P ∩ N` is cyclic or `P ⊆ N`" that opens that reduction
* `OddOrder.GroupTheory.q8_mem_center_of_mem_normal_of_not_le` — the **cyclic branch** of that
  reduction, proved in full
* `OddOrder.GroupTheory.q8_mem_center_of_mem_center_normal` — the **branch `P ≤ N`**
* `OddOrder.GroupTheory.q8_mem_center_of_oPiCore_eq_bot` — the induction assembled
* `OddOrder.GroupTheory.q8_mk_mem_center` / `OddOrder.GroupTheory.brauerSuzuki_q8`
-/

open OddOrder.Isaacs.Ch03

open scoped Pointwise

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- **The odd core meets a Sylow `2`-subgroup trivially**: the intersection has order dividing
both a power of `2` and an odd number. -/
theorem sylowTwo_inf_oPiCore_eq_bot (T : Sylow 2 G) :
    (T : Subgroup G) ⊓ oPiCore {p | p ≠ 2} G = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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

/-! ### Proper subgroups of `Q₈` are cyclic

Navarro's reduction opens with "`P ∩ N` is cyclic or `P ⊆ N`", which is exactly this. -/

/-- **`Q₈` has a unique involution**, namely `a 2`. -/
theorem quaternionTwo_sq_eq_one : ∀ g : QuaternionGroup 2,
    g ^ 2 = 1 → g = 1 ∨ g = QuaternionGroup.a 2 := by decide

/-- **A group isomorphic to `Q₈` has a unique involution.** -/
theorem eq_of_sq_eq_one_of_quaternionTwo {P : Type*} [Group P]
    (e : P ≃* QuaternionGroup 2) {a b : P} (ha : a ^ 2 = 1) (ha1 : a ≠ 1) (hb : b ^ 2 = 1)
    (hb1 : b ≠ 1) : a = b := by
  have key : ∀ c : P, c ^ 2 = 1 → c ≠ 1 → e c = QuaternionGroup.a 2 := by
    intro c hc hc1
    refine (quaternionTwo_sq_eq_one (e c) (by rw [← map_pow, hc, map_one])).resolve_left ?_
    exact fun h => hc1 (e.injective (h.trans (map_one e).symm))
  exact e.injective ((key a ha ha1).trans (key b hb hb1).symm)

/-- **A finite group of order dividing `4` with at most one involution is cyclic.**  For every
`n > 0` the solutions of `xⁿ = 1` are the elements whose order divides `gcd(n, 4)`, of which there
are at most `gcd(n, 4) ≤ n`; so `isCyclic_of_card_pow_eq_one_le` applies. -/
theorem isCyclic_of_card_dvd_four_of_unique_involution {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H ∣ 4)
    (huniq : ∀ a b : H, a ^ 2 = 1 → a ≠ 1 → b ^ 2 = 1 → b ≠ 1 → a = b) : IsCyclic H := by
  classical
  letI := Fintype.ofFinite H
  refine isCyclic_of_card_pow_eq_one_le fun n hn => ?_
  set d := Nat.gcd n 4 with hd
  have hd4 : d ∣ 4 := Nat.gcd_dvd_right n 4
  have hsub : (Finset.univ.filter fun a : H => a ^ n = 1)
      ⊆ Finset.univ.filter fun a : H => a ^ d = 1 := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ a, orderOf_dvd_iff_pow_eq_one.mp ?_⟩
    exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr ha.2)
      ((orderOf_dvd_natCard a).trans hcard)
  have hdn : d ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left n 4)
  refine le_trans (le_trans (Finset.card_le_card hsub) ?_) hdn
  have hcase : d = 1 ∨ d = 2 ∨ d = 4 := by
    have h1 : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
    have h2 : d ≠ 0 := by rintro h; rw [h] at hd4; simp at hd4
    have h3 : d ≠ 3 := by rintro h; rw [h] at hd4; norm_num at hd4
    omega
  rcases hcase with h | h | h
  · rw [h]
    refine le_trans (Finset.card_le_card (fun a ha => ?_ : _ ⊆ ({1} : Finset H))) (by simp)
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_singleton, ← pow_one a]
    exact ha.2
  · rw [h]
    by_cases hex : ∃ w : H, w ^ 2 = 1 ∧ w ≠ 1
    · obtain ⟨w, hw, hw1⟩ := hex
      refine le_trans (Finset.card_le_card (fun a ha => ?_ : _ ⊆ ({1, w} : Finset H))) ?_
      · rw [Finset.mem_filter] at ha
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases eq_or_ne a 1 with rfl | ha1
        · exact Or.inl rfl
        · exact Or.inr (huniq a w ha.2 ha1 hw hw1)
      · exact le_trans (Finset.card_insert_le _ _) (by simp)
    · push Not at hex
      refine le_trans (Finset.card_le_card (fun a ha => ?_ : _ ⊆ ({1} : Finset H))) (by simp)
      rw [Finset.mem_filter] at ha
      exact Finset.mem_singleton.mpr (hex a ha.2)
  · rw [h]
    refine le_trans (Finset.card_le_univ _) ?_
    rw [← Nat.card_eq_fintype_card]
    exact Nat.le_of_dvd (by norm_num) hcard

/-- **Every proper subgroup of a group isomorphic to `Q₈` is cyclic.**  Its order divides `4`, and
it inherits the unique involution of `Q₈`. -/
theorem isCyclic_of_ne_top_of_quaternionTwo {P : Type*} [Group P] [Finite P]
    (e : P ≃* QuaternionGroup 2) {H : Subgroup P} (hH : H ≠ ⊤) : IsCyclic ↥H := by
  classical
  have hP8 : Nat.card P = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hdvd : Nat.card ↥H ∣ 2 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [hP8, show (8 : ℕ) = 2 ^ 3 from rfl] at this
  have hne : Nat.card ↥H ≠ 8 := fun h =>
    hH (Subgroup.eq_top_of_card_eq H (by rw [h, hP8]))
  refine isCyclic_of_card_dvd_four_of_unique_involution ?_ ?_
  · obtain ⟨j, hjle, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj2 : j ≤ 2 := by
      by_contra hgt
      have hj3 : j = 3 := by omega
      exact hne (by rw [hjc, hj3]; norm_num)
    rw [hjc, show (4 : ℕ) = 2 ^ 2 from rfl]
    exact pow_dvd_pow 2 hj2
  · intro a b ha ha1 hb hb1
    refine Subtype.ext (eq_of_sq_eq_one_of_quaternionTwo e ?_ ?_ ?_ ?_)
    · exact congrArg Subtype.val ha
    · exact fun h => ha1 (Subtype.ext h)
    · exact congrArg Subtype.val hb
    · exact fun h => hb1 (Subtype.ext h)

/-! ### Navarro p. 139: the cyclic branch of the reduction -/

/-- **`T ⊓ N` has odd index in a normal subgroup `N`.**  By the second isomorphism theorem
`|T|·[N : T ⊓ N] = |T ⊔ N|`, which divides `|G| = |T|·[G : T]`, so `[N : T ⊓ N]` divides the odd
number `[G : T]`. -/
theorem not_two_dvd_index_inf_subgroupOf (T : Sylow 2 G) (N : Subgroup G) [N.Normal] :
    ¬ 2 ∣ (((T : Subgroup G) ⊓ N).subgroupOf N).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  haveI hcycInf : IsCyclic ↥((T : Subgroup G) ⊓ N) := by
    haveI := hcycT
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
  haveI hLgnorm : (L.map N.subtype).Normal := by
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
  haveI : IsCyclic ↥N :=
    isCyclic_of_surjective ((MulEquiv.subgroupCongr hPtop).trans Subgroup.topEquiv).toMonoidHom
      (MulEquiv.surjective _)
  exact mem_center_of_normal_of_isCyclic hzN hz

/-! ### Navarro p. 139: the branch `P ≤ N` -/

/-- **The involution of `Q₈` is central.** -/
theorem quaternionTwo_a_two_mem_center :
    ∀ g : QuaternionGroup 2, QuaternionGroup.a 2 * g = g * QuaternionGroup.a 2 := by decide

/-- **The involution of a group isomorphic to `Q₈` is central.** -/
theorem mem_center_of_sq_eq_one_of_quaternionTwo {P : Type*} [Group P]
    (e : P ≃* QuaternionGroup 2) {u : P} (hu : u ^ 2 = 1) (hu1 : u ≠ 1) :
    u ∈ Subgroup.center P := by
  have hval : e u = QuaternionGroup.a 2 := by
    refine (quaternionTwo_sq_eq_one (e u) (by rw [← map_pow, hu, map_one])).resolve_left ?_
    exact fun h => hu1 (e.injective (h.trans (map_one e).symm))
  rw [Subgroup.mem_center_iff]
  intro g
  refine e.injective ?_
  rw [map_mul, map_mul, hval]
  exact (quaternionTwo_a_two_mem_center (e g)).symm

/-- **A central involution of a normal subgroup lies in the Sylow `2`-subgroup.**  `⟨u⟩` is a
normal `2`-subgroup of `N`, hence contained in every Sylow `2`-subgroup of `N`
(`IsPGroup.le_sylow_of_normal`), and `T` is one when `T ≤ N`. -/
theorem mem_sylow_of_mem_center_of_orderOf_eq_two (T : Sylow 2 G) {N : Subgroup G} [N.Normal]
    (hTN : (T : Subgroup G) ≤ N) {u : G} (huN : u ∈ N) (hu : orderOf u = 2)
    (huc : ∀ x ∈ N, x * u = u * x) : u ∈ (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  haveI hnorm : (Subgroup.zpowers v).Normal := by
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
  haveI : K.Characteristic := oPiCore.characteristic _ _
  haveI : (K.map N.subtype).Normal := normal_map_subtype_of_characteristic ‹K.Characteristic›
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
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨N, hNnorm, hcompl⟩
  haveI := hNnorm
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
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact fun h => not_hasNormalPComplement_of_oPiCore_eq_bot hO T hTG
    ((OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_controlsOwnFusion T).mpr h)

/-! ### Navarro p. 139: the fusion of the three cyclic subgroups of order `4`

Two ingredients of the "all elements of order `4` are `G`-conjugate" argument.  `Q₈` is
Hamiltonian, so every subgroup is normal and `T`-conjugacy on elements of order `4` is just
`w ↦ w^{±1}`; and `N_G(T)` acts on the three cyclic subgroups of order `4` through a quotient of
**odd** order, because `T·C_G(T)` already acts trivially and contains a Sylow `2`-subgroup of
`N_G(T)`.  An odd-order subgroup of `Sym(3)` is trivial or transitive — which is why a single
fusion forces all three to fuse. -/

/-- **`Q₈` is Hamiltonian**: conjugation fixes or inverts every element. -/
theorem quaternionTwo_conj_eq_self_or_inv :
    ∀ w g : QuaternionGroup 2, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹ := by decide

/-- The same in a group isomorphic to `Q₈`. -/
theorem conj_eq_self_or_inv_of_quaternionTwo {P : Type*} [Group P]
    (e : P ≃* QuaternionGroup 2) (w g : P) : g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹ := by
  rcases quaternionTwo_conj_eq_self_or_inv (e w) (e g) with h | h
  · exact Or.inl (e.injective (by rw [map_mul, map_mul, map_inv]; exact h))
  · exact Or.inr (e.injective (by rw [map_mul, map_mul, map_inv, map_inv]; exact h))

/-- **Every cyclic subgroup of a group isomorphic to `Q₈` is normal.** -/
theorem zpowers_normal_of_quaternionTwo {P : Type*} [Group P] (e : P ≃* QuaternionGroup 2)
    (w : P) : (Subgroup.zpowers w).Normal := by
  refine ⟨fun a ha g => ?_⟩
  obtain ⟨k, rfl⟩ := ha
  rcases conj_eq_self_or_inv_of_quaternionTwo e w g with h | h
  · refine ⟨k, ?_⟩
    calc (w ^ k : P) = (g * w * g⁻¹) ^ k := by rw [h]
      _ = g * w ^ k * g⁻¹ := by simp [conj_zpow]
  · refine ⟨-k, ?_⟩
    calc (w ^ (-k) : P) = (w⁻¹) ^ k := by rw [zpow_neg, ← inv_zpow]
      _ = (g * w * g⁻¹) ^ k := by rw [h]
      _ = g * w ^ k * g⁻¹ := by simp [conj_zpow]

/-- **In `Q₈` every element of order `4` is inverted by some element.**  (An element has order `4`
exactly when its square is not `1`.) -/
theorem quaternionTwo_exists_conj_eq_inv : ∀ w : QuaternionGroup 2, w ^ 2 ≠ 1 →
    ∃ g : QuaternionGroup 2, g * w * g⁻¹ = w⁻¹ := by decide

/-- The same in a group isomorphic to `Q₈`. -/
theorem exists_conj_eq_inv_of_quaternionTwo {P : Type*} [Group P] (e : P ≃* QuaternionGroup 2)
    {w : P} (hw : w ^ 2 ≠ 1) : ∃ g : P, g * w * g⁻¹ = w⁻¹ := by
  obtain ⟨h, hh⟩ := quaternionTwo_exists_conj_eq_inv (e w) fun hc => hw
    (e.injective (by rw [map_pow, hc, map_one]))
  refine ⟨e.symm h, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply]
  exact hh

/-- **The `P`-class of an element of order `4` in `P ≅ Q₈` is exactly `{w, w⁻¹}`, of size two.**
This is the block structure that the fusion argument on p. 139 runs on: `T` fuses `w` with `w⁻¹`
and nothing else, so the three cyclic subgroups of order `4` are the blocks. -/
theorem conj_eq_iff_of_quaternionTwo {P : Type*} [Group P] (e : P ≃* QuaternionGroup 2)
    {w : P} (hw : w ^ 2 ≠ 1) :
    (∀ g : P, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹) ∧ (∃ g : P, g * w * g⁻¹ = w⁻¹) ∧ w ≠ w⁻¹ :=
  ⟨fun g => conj_eq_self_or_inv_of_quaternionTwo e w g, exists_conj_eq_inv_of_quaternionTwo e hw,
    fun h => hw (by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr h)⟩

/-- **A group of odd order acting with an orbit inside a three-element set is transitive on it.**
Orbits have size dividing the (odd) group order, so an orbit contained in a `3`-element set has
size `1` or `3`; if it is not a fixed point it is the whole set.

This replaces Navarro's appeal to `Aut(Q₈) = Sym(4)`: the three inverse pairs of elements of
order `4` in `T` carry an action of `N_G(T)` through a quotient of odd order
(`not_two_dvd_relIndex_sup_centralizer`), so one fusion forces all three to fuse. -/
theorem orbit_eq_of_odd_of_subset_card_three {H α : Type*} [Group H] [Finite H] [Finite α]
    [MulAction H α] {s : Finset α} {x : α} (hodd : ¬ 2 ∣ (MulAction.stabilizer H x).index)
    (hs : s.card = 3) (hsub : ∀ h : H, h • x ∈ s) (hne : ∃ h : H, h • x ≠ x) :
    ∀ y ∈ s, ∃ h : H, h • x = y := by
  classical
  letI := Fintype.ofFinite H
  letI : Fintype (MulAction.orbit H x) := Fintype.ofFinite _
  have hcard : Fintype.card (MulAction.orbit H x) = (MulAction.stabilizer H x).index := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H x),
      Subgroup.index_eq_card]
  have hle : (MulAction.orbit H x).toFinset ⊆ s := by
    intro y hy
    rw [Set.mem_toFinset] at hy
    obtain ⟨h, rfl⟩ := hy
    exact hsub h
  have hcardeq : (MulAction.orbit H x).toFinset.card = Fintype.card (MulAction.orbit H x) :=
    Set.toFinset_card _
  have hgt : 1 < (MulAction.orbit H x).toFinset.card := by
    obtain ⟨h, hh⟩ := hne
    exact Finset.one_lt_card.mpr ⟨h • x, Set.mem_toFinset.mpr (MulAction.mem_orbit x h), x,
      Set.mem_toFinset.mpr (MulAction.mem_orbit_self x), hh⟩
  have hne2 : (MulAction.orbit H x).toFinset.card ≠ 2 := fun h => hodd (by
    rw [hcardeq, hcard] at h; exact h ▸ dvd_rfl)
  have hleq : (MulAction.orbit H x).toFinset.card ≤ 3 := hs ▸ Finset.card_le_card hle
  have heq : (MulAction.orbit H x).toFinset = s :=
    Finset.eq_of_subset_of_card_le hle (by omega)
  intro y hy
  rw [← heq, Set.mem_toFinset] at hy
  exact hy

/-- **The "inverse pairs" `{w, w⁻¹}` of elements of order `4`.**  For `P ≅ Q₈` these index the
three cyclic subgroups of order `4`; they are the blocks of the fusion argument, because `P` fuses
`w` exactly with `w⁻¹` (`conj_eq_iff_of_quaternionTwo`).

They are represented as a `Finset (Finset P)` rather than as a set of subgroups, because the
former is decidable and the cardinality `3` can then be checked by `decide`. -/
def inversePairs (P : Type*) [Group P] [Fintype P] [DecidableEq P] : Finset (Finset P) :=
  (Finset.univ.filter fun w : P => w ^ 2 ≠ 1).image fun w => ({w, w⁻¹} : Finset P)

/-- Inverse pairs transport along an isomorphism. -/
theorem image_inversePairs {P Q : Type*} [Group P] [Fintype P] [DecidableEq P] [Group Q]
    [Fintype Q] [DecidableEq Q] (e : P ≃* Q) :
    (inversePairs P).image (Finset.image e) = inversePairs Q := by
  ext S
  simp only [inversePairs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨e w, fun hc => hw (e.injective (by rw [map_pow, hc, map_one])), ?_⟩
    simp [Finset.image_insert, Finset.image_singleton]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨{e.symm v, (e.symm v)⁻¹}, ⟨e.symm v, fun hc => hv ?_, rfl⟩, ?_⟩
    · rw [← e.apply_symm_apply v, ← map_pow, hc, map_one]
    · simp [Finset.image_insert, Finset.image_singleton]

/-- **Automorphisms permute the inverse pairs.** -/
theorem image_mem_inversePairs {P : Type*} [Group P] [Fintype P] [DecidableEq P] (σ : P ≃* P)
    {S : Finset P} (hS : S ∈ inversePairs P) : S.image σ ∈ inversePairs P := by
  rw [← image_inversePairs σ]
  exact Finset.mem_image_of_mem _ hS

/-- **`Q₈` has exactly three inverse pairs of elements of order `4`** — equivalently, exactly
three cyclic subgroups of order `4`. -/
theorem quaternionTwo_card_inversePairs : (inversePairs (QuaternionGroup 2)).card = 3 := by
  decide

/-- **`P ≅ Q₈` has exactly three inverse pairs of elements of order `4`.** -/
theorem card_inversePairs_of_quaternionTwo {P : Type*} [Group P] [Fintype P] [DecidableEq P]
    (e : P ≃* QuaternionGroup 2) : (inversePairs P).card = 3 := by
  have hinj : Function.Injective (Finset.image (e : P → QuaternionGroup 2)) :=
    Finset.image_injective e.injective
  rw [← Finset.card_image_of_injective _ hinj, image_inversePairs e]
  exact quaternionTwo_card_inversePairs

/-- **Inner automorphisms of `T ≅ Q₈` fix every inverse pair.**  Conjugation sends `w` to `w` or
to `w⁻¹` (Hamiltonian), and in either case `{w, w⁻¹}` is preserved.

This is why the action of `N_G(T)` on the three pairs has `T` inside the stabilizer, so that the
stabilizer has odd index (`T` being a Sylow `2`-subgroup of `N_G(T)`). -/
theorem image_eq_self_of_conj {P : Type*} [Group P] [Fintype P] [DecidableEq P]
    (e : P ≃* QuaternionGroup 2) {σ : P ≃* P} {t : P} (hσ : ∀ s, σ s = t * s * t⁻¹)
    {S : Finset P} (hS : S ∈ inversePairs P) : S.image σ = S := by
  classical
  rw [inversePairs, Finset.mem_image] at hS
  obtain ⟨w, -, rfl⟩ := hS
  have hconj := conj_eq_self_or_inv_of_quaternionTwo e w t
  rw [← hσ w] at hconj
  rcases hconj with h | h
  · rw [Finset.image_insert, Finset.image_singleton, h, map_inv, h]
  · rw [Finset.image_insert, Finset.image_singleton, h, map_inv, h, inv_inv]
    exact Finset.pair_comm _ _

/-- **`T` has odd index in `N_G(T)`**: it is a Sylow `2`-subgroup there, and its relative index
divides the odd number `[G : T]`.  This is the form the fusion argument uses, `T` being inside the
stabilizer of every inverse pair (`image_eq_self_of_conj`). -/
theorem not_two_dvd_relIndex_normalizer (T : Sylow 2 G) :
    ¬ 2 ∣ (T : Subgroup G).relIndex (Subgroup.normalizer (T : Subgroup G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact fun h =>
    T.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))

/-- **`T·C_G(T)` has odd index in `N_G(T)`**: it contains the Sylow `2`-subgroup `T`, whose index
in `N_G(T)` divides the odd number `[G : T]`.

This is what makes the action of `N_G(T)` on the three cyclic subgroups of order `4` factor
through a group of odd order. -/
theorem not_two_dvd_relIndex_sup_centralizer (T : Sylow 2 G) :
    ¬ 2 ∣ (((T : Subgroup G) ⊔ Subgroup.centralizer (T : Set G)).relIndex
      (Subgroup.normalizer (T : Subgroup G))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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

/-- **In `Q₈`, an element of order `4` inside `⟨y⟩` is `y` or `y⁻¹`** (with `y` of order `4`).
Stated with the powers listed explicitly so that it is decidable; membership in `zpowers y`
reduces to this because `y ^ 4 = 1`. -/
theorem quaternionTwo_eq_or_eq_inv_of_mem_powers : ∀ x y : QuaternionGroup 2, x ^ 2 ≠ 1 →
    y ^ 2 ≠ 1 → (x = 1 ∨ x = y ∨ x = y ^ 2 ∨ x = y ^ 3) → x = y ∨ x = y⁻¹ := by decide

/-- **Every element of `Q₈` has order dividing `4`.** -/
theorem quaternionTwo_pow_four : ∀ w : QuaternionGroup 2, w ^ 4 = 1 := by decide

/-- **In a group isomorphic to `Q₈`, an element of order `4` inside `⟨y⟩` is `y` or `y⁻¹`.**
The bridge from `Subgroup.zpowers` to the decidable list of powers goes through
`mem_powers_iff_mem_zpowers` (so the exponent is a natural number) and `pow_mod_orderOf`. -/
theorem eq_or_eq_inv_of_mem_zpowers_of_quaternionTwo {P : Type*} [Group P] [Finite P]
    (e : P ≃* QuaternionGroup 2) {x y : P} (hx : x ^ 2 ≠ 1) (hy : y ^ 2 ≠ 1)
    (hmem : x ∈ Subgroup.zpowers y) : x = y ∨ x = y⁻¹ := by
  have hy4 : y ^ 4 = 1 := e.injective (by rw [map_pow, quaternionTwo_pow_four (e y), map_one])
  have hy1 : y ≠ 1 := fun h => hy (by rw [h, one_pow])
  have horder : orderOf y = 4 := by
    have hdvd : orderOf y ∣ 4 := orderOf_dvd_of_pow_eq_one hy4
    have hle : orderOf y ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have h0 : orderOf y ≠ 0 := fun h => by rw [h] at hdvd; norm_num at hdvd
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    have h2 : orderOf y ≠ 2 := fun h => hy (by rw [← h]; exact pow_orderOf_eq_one y)
    have h3 : orderOf y ≠ 3 := fun h => by rw [h] at hdvd; norm_num at hdvd
    omega
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff x y |>.mp (mem_powers_iff_mem_zpowers.mpr hmem)
  have hmod : x = y ^ (n % 4) := by rw [← hn, ← horder, pow_mod_orderOf]
  have hlist : x = 1 ∨ x = y ∨ x = y ^ 2 ∨ x = y ^ 3 := by
    have hcase : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hcase with h | h | h | h <;> rw [hmod, h]
    · exact Or.inl (pow_zero y)
    · exact Or.inr (Or.inl (pow_one y))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hex : (e x) = 1 ∨ (e x) = e y ∨ (e x) = (e y) ^ 2 ∨ (e x) = (e y) ^ 3 := by
    rcases hlist with h | h | h | h
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h, map_pow])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, map_pow])))
  rcases quaternionTwo_eq_or_eq_inv_of_mem_powers (e x) (e y)
    (fun hc => hx (e.injective (by rw [map_pow, hc, map_one])))
    (fun hc => hy (e.injective (by rw [map_pow, hc, map_one]))) hex with h | h
  · exact Or.inl (e.injective h)
  · exact Or.inr (e.injective (by rw [h, map_inv]))

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
