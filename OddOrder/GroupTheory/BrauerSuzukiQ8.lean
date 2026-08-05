/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiEndgame
import OddOrder.GroupTheory.CardSupInf

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

So the whole content of the `Q₈` case is `q8_mem_center_of_oPiCore_eq_bot`, which is verbatim
Navarro's "it suffices to prove that `t ∈ Z(G)`" under `O_{2'}(G) = 1`.

## Main results

* `OddOrder.GroupTheory.q8_mem_center_of_oPiCore_eq_bot` — **the remaining mathematics**
  (issue 9506, `sorry`)
* `OddOrder.GroupTheory.mem_center_of_normal_of_isCyclic` — how both branches of Navarro's
  reduction on p. 139 finish
* `OddOrder.GroupTheory.isCyclic_of_ne_top_of_quaternionTwo` — every proper subgroup of `Q₈` is
  cyclic, the dichotomy "`P ∩ N` is cyclic or `P ⊆ N`" that opens that reduction
* `OddOrder.GroupTheory.q8_mk_mem_center` / `OddOrder.GroupTheory.brauerSuzuki_q8`
-/

open OddOrder.Isaacs.Ch03

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
    z ∈ Subgroup.center G := by
  sorry

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
