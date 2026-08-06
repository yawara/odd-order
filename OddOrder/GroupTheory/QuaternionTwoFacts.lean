/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Push

/-!
# Elementary facts about the quaternion group of order `8`

The group-theoretic input of the `Q₈` branch of Brauer–Suzuki (Navarro,
*Characters and Blocks*, pp. 138–139) that concerns `Q₈` alone: the uniqueness of the involution,
the cyclicity of the proper subgroups, the Hamiltonian property, and the three cyclic subgroups of
order `4`.  All of it is decidable, so each statement is proved for `QuaternionGroup 2` by `decide`
and then transported along an isomorphism `e : P ≃* QuaternionGroup 2` — that transported form is
what `GroupTheory/BrauerSuzukiQ8.lean` uses, `P` being a Sylow `2`-subgroup.

## Main results

* `OddOrder.GroupTheory.eq_of_sq_eq_one_of_quaternionTwo` — the involution is unique
* `OddOrder.GroupTheory.mem_center_of_sq_eq_one_of_quaternionTwo` — and central
* `OddOrder.GroupTheory.sq_eq_one_of_mem_center_of_quaternionTwo` — conversely, `Q₈` has **no**
  central element of order `4` (Navarro p. 139), which is what shrinks the Sylow `2`-subgroups of
  `C_G(y)` for `y` of order `4`
* `OddOrder.GroupTheory.isCyclic_of_ne_top_of_quaternionTwo` — every proper subgroup is cyclic
* `OddOrder.GroupTheory.conj_eq_self_or_inv_of_quaternionTwo` — `Q₈` is Hamiltonian, and
  `OddOrder.GroupTheory.conj_eq_iff_of_quaternionTwo` — so the class of an element of order `4` is
  exactly `{w, w⁻¹}`
* `OddOrder.GroupTheory.inversePairs` / `OddOrder.GroupTheory.card_inversePairs_of_quaternionTwo` —
  the three inverse pairs, the blocks of the fusion argument
* `OddOrder.GroupTheory.orbit_eq_of_odd_of_subset_card_three` — an odd-order group moving a point
  inside a three-element set is transitive on it; this replaces Navarro's appeal to
  `Aut(Q₈) = Sym(4)`
* `OddOrder.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_quaternionTwo` — the elements of order `4`
  of `⟨y⟩` are `y` and `y⁻¹`
-/

namespace OddOrder.GroupTheory


/-! ### The unique involution, and the proper subgroups

Navarro's reduction (p. 139) opens with "`P ∩ N` is cyclic or `P ⊆ N`", which is exactly
`isCyclic_of_ne_top_of_quaternionTwo`; it rests on the uniqueness of the involution. -/

/-- **`Q₈` has a unique involution**, namely `a 2`. -/
theorem quaternionTwo_sq_eq_one : ∀ g : QuaternionGroup 2,
    g ^ 2 = 1 → g = 1 ∨ g = QuaternionGroup.a 2 := by decide

/-- **`Q₈` has no central element of order `4`** (Navarro p. 139: "the quaternion group does not
have a central element of order `4`").  This is what forces the Sylow `2`-subgroups of `C_G(y)`
to be smaller than `T` when `y` has order `4`. -/
theorem quaternionTwo_sq_eq_one_of_central :
    ∀ w : QuaternionGroup 2, (∀ g : QuaternionGroup 2, g * w = w * g) → w ^ 2 = 1 := by decide

/-- The same in a group isomorphic to `Q₈`. -/
theorem sq_eq_one_of_mem_center_of_quaternionTwo {P : Type*} [Group P]
    (e : P ≃* QuaternionGroup 2) {w : P} (hw : w ∈ Subgroup.center P) : w ^ 2 = 1 := by
  refine e.injective ?_
  rw [map_pow, map_one]
  refine quaternionTwo_sq_eq_one_of_central (e w) fun g => ?_
  have := Subgroup.mem_center_iff.mp hw (e.symm g)
  calc g * e w = e (e.symm g * w) := by rw [map_mul, e.apply_symm_apply]
    _ = e (w * e.symm g) := by rw [this]
    _ = e w * g := by rw [map_mul, e.apply_symm_apply]

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

/-! ### The involution is central -/

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

/-! ### `Q₈` is Hamiltonian, and the three cyclic subgroups of order `4`

`Q₈` is Hamiltonian, so every subgroup is normal and conjugacy on elements of order `4` is just
`w ↦ w^{±1}`.  The three cyclic subgroups of order `4` are therefore the blocks of the fusion
argument on p. 139; they are represented by the "inverse pairs" `{w, w⁻¹}`. -/

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

/-! ### Elements of order `4` inside a cyclic subgroup -/

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

end OddOrder.GroupTheory
