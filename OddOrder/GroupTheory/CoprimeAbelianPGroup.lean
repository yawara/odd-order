/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.GroupTheory.OmegaSubgroup

/-!
# Gorenstein "Finite Groups" Chapter 3 §2: p′-automorphisms of abelian p-groups

`OddOrder.GroupTheory.CoprimeAbelianPGroup`: coprime (`p′`-)automorphism action on a finite
abelian `p`-group, following Gorenstein _Finite Groups_ (1968), Chapter 3 §2.

This is **precursor 2** material for **BG §4 Lemma 4.13** (= **G** Theorem 4.15(ii)): the
structure of a minimal `A`-invariant subgroup on which a `p′`-automorphism acts nontrivially
(special of exponent `p`) rests on Gorenstein Theorem 3.7, which in turn cites Theorems 2.2
(indecomposable ⇒ homocyclic) and 2.4 (the `Ω₁`-extension) of this section. See
`notes/bg/s04_precursor2_special_expP_design.md`.

The repo's coprime-action API lives in `OddOrder.Isaacs.Ch04` (`actionCommutator φ = [G, A]`,
`Subgroup.fixedPointsOfMulAut φ = C_G(A)` for `φ : A →* MulAut G`); Gorenstein's
**Theorem 2.3** (`G = C_G(A) × [G, A]` for abelian `G`) is exactly the pair
`fixedPoints_sup_actionCommutator_eq_top` / `fixedPoints_inf_actionCommutator_eq_bot_of_abelian`.

## Main results

* `actionCommutator_eq_bot_of_omega1_le_fixedPoints` — **Gorenstein Theorem 2.4**: a
  `p′`-automorphism group of a finite abelian `p`-group acting trivially on `Ω₁` acts
  trivially everywhere.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch04

variable {A G : Type*} [Group A]

/-- **Gorenstein "Finite Groups" Theorem 2.4** (Chapter 3 §2). Let `A` be a `p′`-group of
automorphisms of a finite abelian `p`-group `G` (`φ : A →* MulAut G`, `(|A|, |G|) = 1`). If
`A` acts trivially on `Ω₁(G)` (every element of order dividing `p` is fixed), then `A` acts
trivially on all of `G`, i.e. `[G, A] = ⊥`.

Proof (Gorenstein, via Theorem 2.3): `G = C_G(A) × [G, A]`, so `C_G(A) ⊓ [G, A] = ⊥`. If
`[G, A] ≠ ⊥` it is a nontrivial `p`-group, hence (Cauchy) contains an element `x` of order
`p`; then `x ∈ Ω₁(G) ⊆ C_G(A)`, so `x ∈ C_G(A) ⊓ [G, A] = ⊥`, contradicting `x ≠ 1`.

This is the abelian special case of Gorenstein Theorem 3.10 and the `Ω₁`-extension feeding
Theorem 3.7 (precursor 2 of BG Lemma 4.13). -/
theorem actionCommutator_eq_bot_of_omega1_le_fixedPoints
    [CommGroup G] [Finite A] [Finite G] {p : ℕ} [Fact p.Prime]
    (φ : A →* MulAut G) (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hG : IsPGroup p G)
    (htriv : Omega G p 1 ≤ Subgroup.fixedPointsOfMulAut φ) :
    actionCommutator φ = ⊥ := by
  classical
  have hinf : Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥ :=
    fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hCop
  by_contra hH
  -- `H := [G, A]` is a nontrivial `p`-group; extract an order-`p` element (Cauchy).
  haveI hHne : Nontrivial (actionCommutator φ) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hH
  have hHp : IsPGroup p (actionCommutator φ) := hG.to_subgroup _
  haveI : Fintype (actionCommutator φ) := Fintype.ofFinite _
  have hpH : p ∣ Nat.card (actionCommutator φ) := by
    rcases hHp.card_eq_or_dvd with h1 | hd
    · exact absurd h1 (by simpa using (Finite.one_lt_card (α := actionCommutator φ)).ne')
    · exact hd
  have hpH' : p ∣ Fintype.card (actionCommutator φ) := by rwa [Nat.card_eq_fintype_card] at hpH
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := actionCommutator φ) p hpH'
  have hxp : (x : G) ^ p = 1 := by
    have hxp1 : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    exact_mod_cast hxp1
  have hx_ne : (x : G) ≠ 1 := by
    rw [Ne, OneMemClass.coe_eq_one]
    intro h; rw [h, orderOf_one] at hx; exact (Fact.out : p.Prime).ne_one hx.symm
  have hx_omega : (x : G) ∈ Omega G p 1 :=
    Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hxp)
  have hx_inf : (x : G) ∈ Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ :=
    Subgroup.mem_inf.mpr ⟨htriv hx_omega, x.2⟩
  rw [hinf, Subgroup.mem_bot] at hx_inf
  exact hx_ne hx_inf

end OddOrder.GroupTheory
