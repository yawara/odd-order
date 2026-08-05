/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import OddOrder.GroupTheory.KleinFourAutomorphism

/-!
# A single class of involutions for a Klein four Sylow `2`-subgroup

Navarro (7.2), first part: if the Sylow `2`-subgroup `P` of `G` is a Klein four group and
`N_G(P) ≠ C_G(P)`, then `G` has a single class of involutions.

Every involution of `G` is conjugate into `P` (Sylow), and an element of `N_G(P)` of odd order not
centralising `P` conjugates the three involutions of `P` cyclically
(`eq_or_eq_or_eq_iterate_of_odd_of_klein`).

The hypothesis is stated as "there is an odd-order `g ∈ N_G(P)` not centralising `P`" rather than
"`N_G(P) ≠ C_G(P)`"; the two are equivalent because `|N_G(P) : C_G(P)|` is odd, which is a
separate piece of Sylow bookkeeping.

## Main results

* `OddOrder.GroupTheory.exists_conj_mem_sylow_of_mul_self_eq_one` — an involution is conjugate
  into any Sylow `2`-subgroup
* `OddOrder.GroupTheory.isConj_of_klein_sylow` — all involutions of `G` are conjugate
-/

namespace OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- **An involution is conjugate into any Sylow `2`-subgroup.** -/
theorem exists_conj_mem_sylow_of_mul_self_eq_one (P : Sylow 2 G) {u : G} (hu : u ≠ 1)
    (hu2 : u * u = 1) : ∃ c : G, c * u * c⁻¹ ∈ (P : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u = 2 := by
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu
    · exact h
  have hzp : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨Q, hzQ⟩ := hzp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q P
  have hQP : (P : Subgroup G) = MulAut.conj c • (Q : Subgroup G) := by
    rw [← hc, Sylow.coe_subgroup_smul]
  refine ⟨c, ?_⟩
  rw [hQP, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hsimp : (MulAut.conj c)⁻¹ • (c * u * c⁻¹) = u := by
    simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    group
  rw [hsimp]
  exact hzQ (Subgroup.mem_zpowers u)

/-- **All involutions of `G` are conjugate** when the Sylow `2`-subgroup `P` is a Klein four group
and some odd-order `g ∈ N_G(P)` does not centralise `P`. -/
theorem isConj_of_klein_sylow (P : Sylow 2 G) (hcard : Nat.card ↥(P : Subgroup G) = 4)
    (hexp : ∀ x : ↥(P : Subgroup G), x * x = 1)
    {g : G} (hgN : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G)) (hgodd : Odd (orderOf g))
    (hgnc : ∃ x ∈ (P : Subgroup G), g * x * g⁻¹ ≠ x)
    {u v : G} (hu : u ≠ 1) (hu2 : u * u = 1) (hv : v ≠ 1) (hv2 : v * v = 1) :
    IsConj u v := by
  have hconj : ∀ x ∈ (P : Subgroup G), g * x * g⁻¹ ∈ (P : Subgroup G) := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
  -- conjugation by `g`, as an endomorphism of `P`
  let f : ↥(P : Subgroup G) →* ↥(P : Subgroup G) :=
    { toFun := fun x => ⟨g * (x : G) * g⁻¹, hconj (x : G) x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; push_cast; group }
  have hfval : ∀ x : ↥(P : Subgroup G), ((f x : ↥(P : Subgroup G)) : G) = g * (x : G) * g⁻¹ :=
    fun _ => rfl
  have hiter : ∀ (n : ℕ) (x : ↥(P : Subgroup G)),
      (((⇑f)^[n] x : ↥(P : Subgroup G)) : G) = g ^ n * (x : G) * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply, ih (f x), hfval x, pow_succ]
        group
  have hfm : ∀ x : ↥(P : Subgroup G), (⇑f)^[orderOf g] x = x := fun x => by
    refine Subtype.ext ?_
    rw [hiter, pow_orderOf_eq_one]
    group
  have hfne : ∃ x : ↥(P : Subgroup G), f x ≠ x := by
    obtain ⟨x, hxP, hxne⟩ := hgnc
    exact ⟨⟨x, hxP⟩, fun h => hxne (congrArg Subtype.val h)⟩
  -- the involutions of `P` are pairwise conjugate in `G`
  have key : ∀ a b : ↥(P : Subgroup G), a ≠ 1 → b ≠ 1 → IsConj (a : G) (b : G) := by
    intro a b ha hb
    rcases eq_or_eq_or_eq_iterate_of_odd_of_klein hcard hexp f hgodd hfm hfne ha hb with
      h | h | h
    · exact h ▸ IsConj.refl _
    · exact isConj_iff.mpr ⟨g, by rw [h, hfval]⟩
    · exact isConj_iff.mpr ⟨g * g, by
        rw [h, hfval, hfval]
        group⟩
  -- move both involutions into `P`
  obtain ⟨c, hcP⟩ := exists_conj_mem_sylow_of_mul_self_eq_one P hu hu2
  obtain ⟨d, hdP⟩ := exists_conj_mem_sylow_of_mul_self_eq_one P hv hv2
  have hcu : (⟨c * u * c⁻¹, hcP⟩ : ↥(P : Subgroup G)) ≠ 1 := fun h => hu (by
    have h' : c * u * c⁻¹ = 1 := congrArg Subtype.val h
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = 1 := by rw [h']; group)
  have hdv : (⟨d * v * d⁻¹, hdP⟩ : ↥(P : Subgroup G)) ≠ 1 := fun h => hv (by
    have h' : d * v * d⁻¹ = 1 := congrArg Subtype.val h
    calc v = d⁻¹ * (d * v * d⁻¹) * d := by group
      _ = 1 := by rw [h']; group)
  have hcc : IsConj u (c * u * c⁻¹) := isConj_iff.mpr ⟨c, rfl⟩
  have hdd : IsConj v (d * v * d⁻¹) := isConj_iff.mpr ⟨d, rfl⟩
  exact hcc.trans ((key _ _ hcu hdv).trans hdd.symm)

end OddOrder.GroupTheory
