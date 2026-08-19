/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.PClassIndicator

/-!
# Gorenstein Lemma 7.7: class functions whose values are divisible by `|G|`

If `θ` is a class function on `G` all of whose values are rational integers divisible by `|G|`,
then `θ ∈ v_R(G)`.

The proof applies Lemma 7.6 (`exists_pClassIndicator`) with a prime `p` *not* dividing `|G|`.
Two things collapse at once:

* every element of `G` is `p`-regular, so `p`-classes are ordinary conjugacy classes and the
  support condition of Lemma 7.6 becomes "vanishes off the conjugacy class of `u`";
* `P = ⊥` is an admissible `p`-subgroup of `C_G(u)`, so the value at `u` is `|C_G(u)|`.

So for every conjugacy class `C` we get `χ_C ∈ v_R(G)` supported on `C` with `χ_C(C.out)`
`= |C_G(C.out)|`, and

`θ = ∑_C (θ(C.out) / |G|) · [G : C_G(C.out)] · χ_C`

with integer coefficients, because `|G| / |C_G(C.out)| = [G : C_G(C.out)]` is the size of `C`.

## Main results

* `OddOrder.RepresentationTheory.mem_adjoinSpan_inducedVirtualCharacters_of_card_dvd` —
  **Lemma 7.7**

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.7 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G K : Type*} [Group G] [Fintype G] [Field K] [CharZero K]
  {N : ℕ} {ω : K} {𝒳 : Set (Subgroup G)}

set_option backward.isDefEq.respectTransparency false in
/-- **Gorenstein Lemma 7.7.**  A class function on `G` whose values are integers divisible by
`|G|` lies in `v_R(G)`. -/
theorem mem_adjoinSpan_inducedVirtualCharacters_of_card_dvd (h𝒳 : IsElementaryFamily 𝒳)
    (hN : N ≠ 0) (hgN : ∀ g : G, g ^ N = 1) (hω : IsPrimitiveRoot ω N) {θ : G → K}
    (hclass : ∀ y z : G, IsConj y z → θ y = θ z)
    (hdvd : ∀ y : G, ∃ d : ℤ, θ y = (d : K) * (Nat.card G : K)) :
    θ ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) := by
  classical
  -- a prime larger than `|G|`: then every element of `G` is `p`-regular and `⊥` is a `p`-group
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (Nat.card G + 1)
  have hreg : ∀ g : G, IsPRegular p g := by
    intro g hdg
    have h1 : p ∣ Nat.card G := hdg.trans (orderOf_dvd_natCard g)
    have h2 := Nat.le_of_dvd Nat.card_pos h1
    omega
  have hPp : IsPGroup p ↥(⊥ : Subgroup G) := IsPGroup.of_bot
  have hcomm : ∀ u : G, ∀ v ∈ (⊥ : Subgroup G), Commute u v := fun u v hv => by
    rw [Subgroup.mem_bot.mp hv]; exact Commute.one_right u
  -- one indicator per conjugacy class
  have hex : ∀ C : ConjClasses G, ∃ χ : G → K,
      χ ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) ∧
      (∀ y : G, χ y = ((conjugateCount (leftCosetOf C.out (⊥ : Subgroup G)) y /
        Nat.card ↥(⊥ : Subgroup G) : ℕ) : K)) ∧
      (∀ y z : G, IsConj y z → χ y = χ z) ∧
      (∀ y : G, ¬ IsConj (pRegularPart p y) C.out → χ y = 0) ∧
      χ C.out = ((Nat.card ↥(Subgroup.centralizer ({C.out} : Set G)) /
        Nat.card ↥(⊥ : Subgroup G) : ℕ) : K) :=
    fun C => exists_pClassIndicator h𝒳 hN hgN hω hp (hreg C.out) hPp (hcomm C.out)
  choose χ hmem _hval hcf hsupp hself using hex
  choose d hd using hdvd
  have hmkout : ∀ C : ConjClasses G, ConjClasses.mk C.out = C := fun C => by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  -- the coefficients: `θ(C.out) / |G|` times the size `[G : C_G(C.out)]` of the class
  set c : ConjClasses G → ℤ := fun C =>
    d C.out * ((Subgroup.centralizer ({C.out} : Set G)).index : ℤ) with hc
  have hpt : ∀ y : G, θ y = ∑ C : ConjClasses G, (c C • χ C) y := by
    intro y
    obtain ⟨C₀, hC₀⟩ : ∃ C : ConjClasses G, ConjClasses.mk y = C := ⟨_, rfl⟩
    have hIsConj : IsConj y C₀.out :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [hC₀, hmkout])
    -- every other class contributes nothing
    have hzero : ∀ C : ConjClasses G, C ≠ C₀ → (c C • χ C) y = 0 := by
      intro C hC
      have hne : ¬ IsConj (pRegularPart p y) C.out := by
        rw [pRegularPart_eq_self_of_isPRegular hp (hreg y)]
        intro h
        have h1 : ConjClasses.mk y = ConjClasses.mk C.out := ConjClasses.mk_eq_mk_iff_isConj.mpr h
        rw [hC₀, hmkout] at h1
        exact hC h1.symm
      rw [Pi.smul_apply, hsupp C y hne, smul_zero]
    have hcollapse : (∑ C : ConjClasses G, (c C • χ C) y) = (c C₀ • χ C₀) y :=
      Finset.sum_eq_single C₀ (fun C _ hC => hzero C hC) fun h => absurd (Finset.mem_univ C₀) h
    -- and the surviving one contributes `|C_G(C₀.out)|`
    have hχ : χ C₀ y = (Nat.card ↥(Subgroup.centralizer ({C₀.out} : Set G)) : K) := by
      rw [hcf C₀ y C₀.out hIsConj, hself C₀, Subgroup.card_bot, Nat.div_one]
    have hθ : θ y = (d C₀.out : K) * (Nat.card G : K) := by
      rw [hclass y C₀.out hIsConj, hd C₀.out]
    rw [hcollapse, Pi.smul_apply, hχ, zsmul_eq_mul, hθ, hc,
      ← Subgroup.card_mul_index (Subgroup.centralizer ({C₀.out} : Set G))]
    push_cast
    ring
  have hfun : θ = ∑ C : ConjClasses G, c C • χ C :=
    funext fun y => (hpt y).trans (Finset.sum_apply _ _ _).symm
  rw [hfun]
  exact AddSubgroup.sum_mem _ fun C _ => AddSubgroup.zsmul_mem _ (hmem C) (c C)

end OddOrder.RepresentationTheory
