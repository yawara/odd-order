/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CyclicSubgroupUniqueness
import OddOrder.GroupTheory.PiElementDecomposition
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Elements killed by the order of a cyclic normal subgroup of a `Z`-group

In a finite group `D` all of whose Sylow subgroups are cyclic (`IsZGroup`), a *cyclic
normal* subgroup `W` absorbs every element it could:

  `g ^ |W| = 1  →  g ∈ W`.

This is the group-theoretic content of the argument Peterfalvi runs on p. 129 of Part II
(Ch. IV §2, the proof of the closing Proposition), where `D` is a Frobenius complement of
odd order:

> if `p` is a prime number, then, if `x` is the `p`-component of `h(ω)ζ⁻¹` and `P` is a
> Sylow `p`-subgroup of `D` containing `x`, `x^{m_p} = 1` and `|P ∩ W| = m_p` since
> `W ⊴ D`, whence `x ∈ W`.

The proof here follows that argument, with two simplifications made possible by `W` being
cyclic: the Sylow `p`-subgroup `W_p` of `W` is *normal in `D`* (every subgroup of a cyclic
normal subgroup is), so it lies inside **every** Sylow `p`-subgroup of `D`, and there is no
need to identify `P ∩ W`.  The reduction from `g` to its `p`-components is the two-part
`π`-decomposition of `PiElementDecomposition`, iterated by induction on `orderOf g`.

## Main results

* `OddOrder.GroupTheory.normal_of_le_of_isCyclic_normal` — every subgroup of a cyclic
  normal subgroup is normal.
* `OddOrder.GroupTheory.mem_of_isPGroup_of_orderOf_dvd` — the `p`-element case.
* `OddOrder.GroupTheory.mem_of_pow_card_eq_one_of_isZGroup` — the statement above.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

variable {D : Type*} [Group D] [Finite D]

/-- **Every subgroup of a cyclic normal subgroup is normal.**

Conjugation keeps the subgroup inside `W` and preserves its order, and a finite cyclic
group has only one subgroup of each order (`cyclic_subgroup_eq_of_card_eq`). -/
theorem normal_of_le_of_isCyclic_normal {W : Subgroup D} [hWn : W.Normal]
    (hWcyc : IsCyclic ↥W) {U : Subgroup D} (hUW : U ≤ W) : U.Normal := by
  classical
  have := hWcyc
  refine ⟨fun n hn d => ?_⟩
  set U' : Subgroup D := U.map (MulAut.conj d).toMonoidHom with hU'def
  have hU'W : U' ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hWn.conj_mem x (hUW hx) d
  have hcard : Nat.card ↥U' = Nat.card ↥U :=
    (Nat.card_congr (Subgroup.equivMapOfInjective U (MulAut.conj d).toMonoidHom
      (MulAut.conj d).injective).toEquiv).symm
  have hsub : U'.subgroupOf W = U.subgroupOf W := by
    refine cyclic_subgroup_eq_of_card_eq ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU'W).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv]
    exact hcard
  have hmem : (⟨d * n * d⁻¹, hU'W ⟨n, hn, rfl⟩⟩ : ↥W) ∈ U'.subgroupOf W :=
    Subgroup.mem_subgroupOf.mpr ⟨n, hn, rfl⟩
  rw [hsub] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

/-- **The `p`-element case** (Peterfalvi Part II, p. 129).

`W_p`, the subgroup of `W` of order `|W|_p`, is normal in `D`
(`normal_of_le_of_isCyclic_normal`), hence contained in every Sylow `p`-subgroup of `D`
(`IsPGroup.le_sylow_of_normal`).  Pick one containing `a` as well; inside that cyclic
Sylow, `⟨a⟩` has order dividing `|W_p|`, so it is contained in `W_p`
(`le_of_card_dvd_of_isCyclic`). -/
theorem mem_of_isPGroup_of_orderOf_dvd {W : Subgroup D} [W.Normal] (hWcyc : IsCyclic ↥W)
    [hZ : IsZGroup D] {p : ℕ} (hp : p.Prime) {a : D}
    (hap : IsPGroup p ↥(Subgroup.zpowers a)) (hdvd : orderOf a ∣ Nat.card ↥W) :
    a ∈ W := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hWcyc
  -- `W_p ≤ W` of order `|W|_p`
  obtain ⟨V, hVcard⟩ := exists_subgroup_card_eq_of_isCyclic (C := ↥W)
    (Nat.ordProj_dvd (Nat.card ↥W) p)
  set Wp : Subgroup D := V.map W.subtype with hWpdef
  have hWpW : Wp ≤ W := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hWpcard : Nat.card ↥Wp = p ^ (Nat.card ↥W).factorization p :=
    (Nat.card_congr (Subgroup.equivMapOfInjective V W.subtype
      Subtype.val_injective).toEquiv).symm.trans hVcard
  have : Wp.Normal := normal_of_le_of_isCyclic_normal hWcyc hWpW
  have hWppg : IsPGroup p ↥Wp := IsPGroup.of_card hWpcard
  -- a Sylow `p`-subgroup of `D` containing `a`; `W_p` lies in it too, being normal
  obtain ⟨P, haP⟩ := hap.exists_le_sylow
  have hWpP : Wp ≤ (P : Subgroup D) := hWppg.le_sylow_of_normal P
  have : IsCyclic ↥(P : Subgroup D) := hZ.isZGroup p hp P
  -- `|⟨a⟩| = p^k` divides `|W| `, hence divides `|W_p| = |W|_p`
  obtain ⟨k, hk⟩ := hap.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hordvd : orderOf a ∣ Nat.card ↥Wp := by
    rw [hWpcard, hk]
    refine pow_dvd_pow p ?_
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp (hk ▸ hdvd)
  -- inside the cyclic Sylow, divisibility of orders is containment
  have hle : (Subgroup.zpowers a).subgroupOf (P : Subgroup D)
      ≤ Wp.subgroupOf (P : Subgroup D) := by
    refine le_of_card_dvd_of_isCyclic ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe haP).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWpP).toEquiv, Nat.card_zpowers]
    exact hordvd
  refine hWpW (Subgroup.mem_subgroupOf.mp
    (hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a) :
      (⟨a, haP (Subgroup.mem_zpowers a)⟩ : ↥(P : Subgroup D)) ∈ _)))

/-- **A cyclic normal subgroup of a `Z`-group absorbs everything it kills** (Peterfalvi
Part II, Ch. IV §2, p. 129).

Induction on `orderOf g`: split off the `p`-part for a prime `p` dividing it
(`exists_isPiElement_mul`), place it in `W` by `mem_of_isPGroup_of_orderOf_dvd`, and apply
the induction hypothesis to the `p′`-part, whose order is strictly smaller. -/
theorem mem_of_pow_card_eq_one_of_isZGroup {W : Subgroup D} [W.Normal]
    (hWcyc : IsCyclic ↥W) [IsZGroup D] {g : D} (hg : g ^ Nat.card ↥W = 1) : g ∈ W := by
  classical
  suffices H : ∀ n : ℕ, ∀ x : D, orderOf x = n → x ^ Nat.card ↥W = 1 → x ∈ W from
    H (orderOf g) g rfl hg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hxord hx
    have hdvd : orderOf x ∣ Nat.card ↥W := orderOf_dvd_of_pow_eq_one hx
    rcases eq_or_ne (orderOf x) 1 with h1 | h1
    · rw [orderOf_eq_one_iff.mp h1]
      exact W.one_mem
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨a, b, hab, hcomm, hapi, hbpi, hazp, hbzp⟩ :=
      exists_isPiElement_mul ({p} : Set ℕ) x
    have haord : orderOf a ∣ orderOf x := orderOf_dvd_of_mem_zpowers hazp
    have hbord : orderOf b ∣ orderOf x := orderOf_dvd_of_mem_zpowers hbzp
    -- the `p`-part lies in `W`
    have haW : a ∈ W := by
      rcases eq_or_ne (orderOf a) 1 with ha1 | ha1
      · rw [orderOf_eq_one_iff.mp ha1]; exact W.one_mem
      have hapow : orderOf a = p ^ (orderOf a).primeFactorsList.length :=
        Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos a).ne' fun {q} hq hqd =>
          hapi q (Nat.mem_primeFactors.mpr ⟨hq, hqd, (orderOf_pos a).ne'⟩)
      refine mem_of_isPGroup_of_orderOf_dvd hWcyc hp ?_ (haord.trans hdvd)
      exact IsPGroup.of_card (by rw [Nat.card_zpowers]; exact hapow)
    -- the `p′`-part has strictly smaller order, so the induction hypothesis applies
    have hbW : b ∈ W := by
      have hpb : ¬ p ∣ orderOf b := by
        intro hcon
        have : p ∈ ({p} : Set ℕ)ᶜ :=
          hbpi p (Nat.mem_primeFactors.mpr ⟨hp, hcon, (orderOf_pos b).ne'⟩)
        exact this rfl
      have hlt : orderOf b < n := by
        have hne : orderOf b ≠ orderOf x := fun hcon => hpb (hcon ▸ hpdvd)
        have hle : orderOf b ≤ orderOf x := Nat.le_of_dvd (orderOf_pos x) hbord
        omega
      exact ih (orderOf b) hlt b rfl (orderOf_dvd_iff_pow_eq_one.mp (hbord.trans hdvd))
    rw [← hab]
    exact W.mul_mem haW hbW

end OddOrder.GroupTheory
