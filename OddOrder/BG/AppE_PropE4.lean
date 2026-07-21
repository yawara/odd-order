/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_BetaSupply

/-!
# BG Proposition E.4, corrected: `C_S(Z₂(S))` is abelian of index `p`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 162–164.

> **Proposition E.4** *(as printed)*.  Assume the situation of Theorem E.3 and let
> `S = Ω₁(R)`.  Suppose `|S| ≥ p⁴`, `B` acts regularly on `R`, and `B` does not fix `R₀`.
> Then `C_S(Z₂(S))` is abelian and has index `p` in `S`.

**As printed the proposition is false**: its unproved display `(E.23)` (*"Similarly one can
show"*) needs the 2-step centralizer relations `⁅Hₐ, T⁆ ≤ Hₐ₊₂` (in the language of
maximal-class theory: `S` *non-exceptional*, equivalently of positive degree of
commutativity), which the printed hypotheses do not force.  The Lazard group of the
exceptional filiform Lie ring `Q₆` (`p = 197`, `B = C₄₉`) satisfies every printed
hypothesis while `T = C_S(Z₂(S))` is non-abelian; the machine-checked refutation is
`printed_propE4_false` in `OddOrder/BG/AppE_FiliformRefutation.lean`, and the master note
is `notes/bg/appE_e4_counterexample_2026_07_21.md` (issues 3021/9402).

This leaf proves the **corrected** proposition: the same statement with the missing
non-exceptionality supplied as the explicit hypothesis `hdc` (the 2-step centralizer
relations for the chain `Hₙ = iterCommutator T ⊤ n` out of `T`).  The index clause never
needed `hdc` — it is Step 2's `|S : T| = p`, proved unconditionally in
`AppE_AbelianCentralizer.lean`.

## Assembly

The abelian clause is BG's `(E.28)` contradiction, run by the engine
`RegularOperatorSetup.commutator_centralizer_eq_bot_of_beta_supply`
(`AppE_EigenvalueCombinatorics.lean`).  This file's work is discharging the engine's
inputs from the proved pieces:

* `α`-side data (`(E.9)`/`(E.11)`/`(E.22)`): `exists_zpow_eq_act_of_mem_A`,
  `zpow_exponent_ne_one`, `exists_zpow_eq_mod_chain`, and `r₀ ≡ r` from
  `dvd_sub_eigenvalues` (which needs `(E.20)` `B` abelian, from `commutator_eq_bot`).
* `β`-side data (`(E.19)`/`(E.21)`): the `B`-invariant complement `Q/S'` from
  `exists_aInvariant_complement_of_centralizer`, eigenvalues `t, t₀` by
  `exists_zpow_of_map_eq_of_isCyclic`, and `t ≠ t₀` from
  `not_dvd_sub_eigenvalues_of_not_fixes`.
* the corrected `(E.23)` supply: `scale_iterCommutator_of_two_step`
  (`AppE_BetaSupply.lean`) applied to a lift `q` of a generator of `Q/S'`, with `hdc`.

Throughout, `S' = H₁` (BG `(E.7)`, here `commutator_eq_and_card_quotient`) converts
between the mod-`S'` eigenvalue statements on `S/S'` and the mod-`H₁` chain statements.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch04
open scoped commutatorElement Pointwise

variable {R B : Type*} [Group R] [Group B] {p q : ℕ}

/-! ## Two small generic helpers -/

/-- The map-equality form of `IsAInvariant` at a single operator — the shape
`exists_zpow_of_map_eq_of_isCyclic` consumes. -/
theorem IsAInvariant.map_coe_eq {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : IsAInvariant φ H) (a : A) :
    H.map ((φ a : MulAut G) : G →* G) = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hH.smul_mem a hx
  · intro x hx
    refine ⟨(φ a)⁻¹ x, ?_, ?_⟩
    · have h := hH.smul_mem a⁻¹ hx
      rwa [map_inv] at h
    · exact MulAut.apply_inv_self G (φ a) x

/-- An automorphism scaling a nontrivial element of order dividing a prime `p` by `t` has
`t` a unit mod `p` — BG's tacit *"the eigenvalues are nonzero"* for the lines of `S/S'`. -/
theorem isUnit_intCast_of_mulAut_zpow {E : Type*} [Group E] {p : ℕ} (hp : p.Prime)
    {g : E} (hgne : g ≠ 1) (hgp : g ^ p = 1) (f : MulAut E) {t : ℤ} (ht : f g = g ^ t) :
    IsUnit (t : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨c, rfl⟩ : (p : ℤ) ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp h0
  have h1 : f g = 1 := by rw [ht, zpow_mul, zpow_natCast, hgp, one_zpow]
  exact hgne (f.injective (by rw [h1, map_one]))

/-! ## The corrected Proposition E.4 -/

/-- **BG Proposition E.4, corrected** (BG pp. 162–164 + the missing non-exceptionality
hypothesis; issues 3021/9402): in the situation of Theorem E.3, with `S = Ω₁(R)`, if
`|S| ≥ p⁴`, `B` acts regularly on `R`, `B` does not fix `R₀`, **and** the 2-step
centralizer relations `hdc` hold for the chain out of `T = C_S(Z₂(S))`, then `T` is
abelian of index `p` in `S`.

⚠ **As printed (without `hdc`) the proposition is false** — refuted by the Lazard group
of the exceptional filiform `Q₆` in `AppE_FiliformRefutation.lean`
(`printed_propE4_false`); BG's display `(E.23)` silently uses `⁅Hₐ, T⁆ ≤ Hₐ₊₂`, which the
printed hypotheses do not force.  `hdc` is exactly that missing assumption (equivalently:
`S` is non-exceptional / has positive degree of commutativity, in the sense of
Leedham-Green–McKay), stated with BG's `Z₂(S)`.  Master note:
`notes/bg/appE_e4_counterexample_2026_07_21.md`.

The index clause does not consume `hdc` (nor regularity, nor `B ⊄ N(R₀)`); it is Step 2's
`|S : T| = p`. -/
theorem RegularOperatorSetup.centralizer_upperCentralSeries_abelian_index_p
    [Finite R] [Finite B] (hyp : RegularOperatorSetup R B p q)
    (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1))
    (hB_regular : ∀ b : B, b ≠ 1 → ∀ x : R, hyp.act b x = x → x = 1)
    (hB_not_fixes : ¬ ∀ b : B, (hyp.act b) • hyp.R₀ = hyp.R₀)
    (hdc : ∀ n : ℕ,
      ⁅OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer
            ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
              Set ↥(Omega R p 1)))
          (⊤ : Subgroup ↥(Omega R p 1)) n,
        Subgroup.centralizer
          ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
            Set ↥(Omega R p 1))⁆ ≤
        OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer
            ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
              Set ↥(Omega R p 1)))
          (⊤ : Subgroup ↥(Omega R p 1)) (n + 2)) :
    IsMulCommutative
        ↥(Subgroup.centralizer
          ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
            Set ↥(Omega R p 1))) ∧
      (Subgroup.centralizer
          ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
            Set ↥(Omega R p 1))).index = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hTeq := centralizer_upperCentralSeries_eq_centralizer_omega1 (p := p)
    hyp.omega_pow_eq_one'
  rw [hTeq] at hdc ⊢
  have hR₀S : hyp.R₀ ≤ Omega R p 1 := hyp.R₀_le_omega
  have hexp : ∀ x : ↥(Omega R p 1), x ^ p = 1 := hyp.omega_pow_eq_one'
  have hS3 : 3 ≤ pRank ↥(Omega R p 1) p := hyp.three_le_pRank_omega hcard
  refine ⟨?_, (hyp.card_omega1Center_and_index_centralizer hR₀S hS3).2⟩
  set S' : Subgroup ↥(Omega R p 1) := _root_.commutator ↥(Omega R p 1) with hS'def
  set T : Subgroup ↥(Omega R p 1) :=
    Subgroup.centralizer
      (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)) with hTdef
  haveI : S'.Normal := by rw [hS'def]; infer_instance
  haveI : S'.Characteristic := by rw [hS'def]; infer_instance
  -- Invariances: `S`, `S'`, `T` are all characteristic.
  haveI : (Omega R p 1).Characteristic := Omega.characteristic
  have hSinvB : IsAInvariant hyp.act (Omega R p 1) := IsAInvariant.of_characteristic hyp.act
  have hSinvA : IsAInvariant (hyp.act.comp hyp.A.subtype) (Omega R p 1) :=
    IsAInvariant.of_characteristic _
  have hNinv : IsAInvariant hSinvB.restrict S' := IsAInvariant.of_characteristic _
  have hTinvB : IsAInvariant hSinvB.restrict T := IsAInvariant.of_characteristic _
  -- `S' = H₁` — BG `(E.7)`, the bridge between mod-`S'` and mod-`H₁` statements.
  have hH₁ : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥(Omega R p 1)) 1 = S' :=
    (hyp.commutator_eq_and_card_quotient hR₀S hexp hS3).1
  have hS'T : S' ≤ T := hyp.commutator_le_centralizer hcard
  -- BG's `α ∈ A^#`.
  obtain ⟨a, ha, hane⟩ : ∃ a, ∃ h : a ∈ hyp.A, (⟨a, h⟩ : ↥hyp.A) ≠ 1 := by
    haveI : Nontrivial ↥hyp.A := by
      have hcardA := hyp.A_card
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro h
      rw [h, Subgroup.card_bot] at hcardA
      exact hyp.q_prime.one_lt.ne hcardA
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥hyp.A)
    exact ⟨x.1, x.2, by simpa using hx⟩
  have hane' : a ≠ 1 := fun h => hane (Subtype.ext (by simpa using h))
  -- BG's `v` generating `R₀`, and `(E.9)`/`(E.11)`: `vᵃ = vʳ`, `r^q ≡ 1`, `r ≢ 1`.
  obtain ⟨v, hv⟩ := hyp.exists_zpowers_eq_R₀_subgroupOf hR₀S
  have hvR₀ : (v : R) ∈ hyp.R₀ := by
    have hvmem : v ∈ hyp.R₀.subgroupOf (Omega R p 1) := by
      rw [← hv]; exact Subgroup.mem_zpowers v
    exact Subgroup.mem_subgroupOf.mp hvmem
  obtain ⟨r, hrall, hrq⟩ := hyp.exists_zpow_eq_act_of_mem_A ha
  have hr1 : (r : ZMod p) ≠ 1 := hyp.zpow_exponent_ne_one ha hane' hrall
  have hr : (hSinvA.restrict ⟨a, ha⟩) v = v ^ r := by
    refine Subtype.ext ?_
    rw [IsAInvariant.restrict_apply_val]
    push_cast
    exact hrall _ hvR₀
  -- BG's `w ∈ H₀ − H₁`; liveness `T ≠ ⊥` from `|S| ≥ p⁴` and `|S : T| = p`.
  have hTidx : T.index = p := (hyp.card_omega1Center_and_index_centralizer hR₀S hS3).2
  have h0live : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥(Omega R p 1)) 0 ≠ ⊥ := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_zero]
    intro hbot
    have hmul := T.card_mul_index
    rw [hTidx, hbot, Subgroup.card_bot, one_mul] at hmul
    have hcard' := hcard
    rw [← hmul] at hcard'
    have hlt : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hyp.p_prime.one_lt (by omega)
    rw [pow_one] at hlt
    omega
  obtain ⟨w, hwmem, hw1⟩ := SetLike.exists_of_lt (hyp.iterCommutator_lt hR₀S hexp hS3 h0live)
  rw [OddOrder.Isaacs.Ch04.iterCommutator_zero] at hwmem
  -- `r₀`, the eigenvalue of `α` on the top section `H₀/H₁`.
  obtain ⟨r₀, hr₀q, hr₀⟩ := hyp.exists_zpow_eq_mod_chain hR₀S hexp hS3 hSinvA h0live ha
  -- The `B`-restriction and the `A`-restriction of `α` agree on `S`.
  have hAB : ∀ y : ↥(Omega R p 1), hSinvB.restrict a y = hSinvA.restrict ⟨a, ha⟩ y := fun y =>
    Subtype.ext (by rw [IsAInvariant.restrict_apply_val, IsAInvariant.restrict_apply_val]; rfl)
  -- `(E.20)`: `B` is abelian.
  have habel : ∀ x y : B, x * y = y * x := by
    have hcommB := hyp.commutator_eq_bot hcard hB_regular
    intro x y
    have hmem : ⁅x, y⁆ ∈ _root_.commutator B :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hcommB, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_commute.mp hmem).eq
  -- `(E.22)`: `r₀ ≡ r (mod p)`, through the eigenvalue statements on `S/S'`.
  have hrquot : ∀ x ∈ (hyp.R₀.subgroupOf (Omega R p 1)).map (QuotientGroup.mk' S'),
      hNinv.quotientMulAutHom a x = x ^ r := by
    rintro x ⟨y, hy, rfl⟩
    rw [IsAInvariant.quotientMulAutHom_apply_mk']
    have hres : hSinvB.restrict a y = y ^ r := by
      refine Subtype.ext ?_
      rw [IsAInvariant.restrict_apply_val]
      push_cast
      exact hrall _ (Subgroup.mem_subgroupOf.mp hy)
    rw [hres, map_zpow]
  have hr₀quot : ∀ x ∈ T.map (QuotientGroup.mk' S'),
      hNinv.quotientMulAutHom a x = x ^ r₀ := by
    rintro x ⟨y, hy, rfl⟩
    rw [IsAInvariant.quotientMulAutHom_apply_mk']
    have hmem := hr₀ y (by rw [OddOrder.Isaacs.Ch04.iterCommutator_zero]; exact hy)
    rw [hH₁] at hmem
    rw [hAB y, ← map_zpow]
    exact (QuotientGroup.eq.mpr hmem).symm
  have hdvdr := hyp.dvd_sub_eigenvalues hcard hB_not_fixes habel hSinvB hNinv hrquot hr₀quot
  have hr0r : (r₀ : ZMod p) = (r : ZMod p) := by
    have h0 : ((r - r₀ : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvdr
    push_cast at h0
    exact (sub_eq_zero.mp h0).symm
  -- BG's `β`: an operator not fixing the line `R₀S'/S'` — `(E.18)`.
  have hnotall := hyp.not_fixes_sup_frattini_of_not_fixes_R₀ hB_not_fixes
  push Not at hnotall
  obtain ⟨b, hbfix'⟩ := hnotall
  have hbfix : (hyp.act b) • (hyp.R₀ ⊔ derivedInG (Omega R p 1)) ≠
      hyp.R₀ ⊔ derivedInG (Omega R p 1) := by
    rwa [hyp.frattiniInG_omega_eq_derivedInG] at hbfix'
  -- The `B`-invariant complement `Q/S'` of `T/S'` in `S/S'`.
  obtain ⟨W, hWinv, hWinf, hWsup⟩ :=
    hyp.exists_aInvariant_complement_of_centralizer hcard hSinvB hNinv
  set Tbar : Subgroup (↥(Omega R p 1) ⧸ S') := T.map (QuotientGroup.mk' S') with hTbardef
  have hEA := hyp.isElementaryAbelian_quotient_commutator
  have hcardTbar : Nat.card ↥Tbar = p := hyp.card_map_centralizer hcard
  have hcardQuot : Nat.card (↥(Omega R p 1) ⧸ S') = p ^ 2 := hyp.card_omega_abelianization
  -- `|Q/S'| = p`, via the injection `Q/S' → (S/S')/(T/S')`.
  have hWne : W ≠ ⊥ := by
    intro hb
    rw [hb, sup_bot_eq] at hWsup
    rw [hWsup, Subgroup.card_top, hcardQuot] at hcardTbar
    have hlt : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hyp.p_prime.one_lt (by omega)
    rw [pow_one] at hlt
    omega
  haveI hTbarNormal : Tbar.Normal := ⟨fun n hn g => by
    rw [hEA.comm g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have hTbarIdx : Tbar.index = p := by
    have hmul := Tbar.card_mul_index
    rw [hcardTbar, hcardQuot] at hmul
    exact Nat.eq_of_mul_eq_mul_left hyp.p_prime.pos (by rw [hmul]; ring)
  have hcardW : Nat.card ↥W = p := by
    have hinj : Function.Injective ((QuotientGroup.mk' Tbar).comp W.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hx
      have hxT : ((x : ↥W) : ↥(Omega R p 1) ⧸ S') ∈ Tbar :=
        (QuotientGroup.eq_one_iff _).mp hx
      have hxbot : ((x : ↥W) : ↥(Omega R p 1) ⧸ S') ∈ Tbar ⊓ W := ⟨hxT, x.2⟩
      rw [hWinf] at hxbot
      exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
    have hdvd : Nat.card ↥W ∣ p := by
      have h1 : Nat.card ↥W =
          Nat.card ↥((QuotientGroup.mk' Tbar).comp W.subtype).range :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      have h2 := Subgroup.card_subgroup_dvd_card ((QuotientGroup.mk' Tbar).comp W.subtype).range
      rw [← Subgroup.index_eq_card, hTbarIdx] at h2
      rw [h1]
      exact h2
    rcases hyp.p_prime.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hWne
    · exact h1
  haveI : IsCyclic ↥W := isCyclic_of_prime_card hcardW
  haveI : IsCyclic ↥Tbar := isCyclic_of_prime_card hcardTbar
  -- `(E.19)`: the eigenvalues `t`, `t₀` of `β` on `Q/S'` and `T/S'`.
  have hTbarInv : IsAInvariant hNinv.quotientMulAutHom Tbar :=
    OddOrder.BG.Ch1_Preliminary.isAInvariant_map_mk' hNinv hTinvB
  obtain ⟨t, htW⟩ := exists_zpow_of_map_eq_of_isCyclic
    (hNinv.quotientMulAutHom b) (IsAInvariant.map_coe_eq hWinv b)
  obtain ⟨t₀, ht₀T⟩ := exists_zpow_of_map_eq_of_isCyclic
    (hNinv.quotientMulAutHom b) (IsAInvariant.map_coe_eq hTbarInv b)
  -- `(E.21)`: `t ≠ t₀`.
  have hQsup : W ⊔ Tbar = ⊤ := by rw [sup_comm]; exact hWsup
  have hnotdvd := hyp.not_dvd_sub_eigenvalues_of_not_fixes hSinvB hNinv hbfix hQsup htW ht₀T
  have htne : (t₀ : ZMod p) ≠ (t : ZMod p) := by
    intro h
    refine hnotdvd ?_
    have h0 : ((t - t₀ : ℤ) : ZMod p) = 0 := by push_cast; rw [h, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  -- The eigenvalues are units mod `p`.
  haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
  obtain ⟨xW, hxWne⟩ := exists_ne (1 : ↥W)
  have htu : IsUnit (t : ZMod p) :=
    isUnit_intCast_of_mulAut_zpow hyp.p_prime (fun h => hxWne (Subtype.ext h))
      (hEA.pow_eq_one _) (hNinv.quotientMulAutHom b) (htW _ xW.2)
  haveI : Nontrivial ↥Tbar := (Subgroup.nontrivial_iff_ne_bot Tbar).mpr fun hb => by
    rw [hb, Subgroup.card_bot] at hcardTbar
    exact hyp.p_prime.one_lt.ne hcardTbar
  obtain ⟨yT, hyTne⟩ := exists_ne (1 : ↥Tbar)
  have ht₀u : IsUnit (t₀ : ZMod p) :=
    isUnit_intCast_of_mulAut_zpow hyp.p_prime (fun h => hyTne (Subtype.ext h))
      (hEA.pow_eq_one _) (hNinv.quotientMulAutHom b) (ht₀T _ yT.2)
  -- A lift `q` of a generator of `Q/S'`, and `⊤ = ⟨q⟩ ⊔ T`.
  obtain ⟨gW, hgW⟩ := IsCyclic.exists_generator (α := ↥W)
  obtain ⟨qe, hqe⟩ := QuotientGroup.mk'_surjective S' ((gW : ↥W) : ↥(Omega R p 1) ⧸ S')
  have hzpW : Subgroup.zpowers ((gW : ↥W) : ↥(Omega R p 1) ⧸ S') = W := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      exact gW.2
    · intro x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgW ⟨x, hx⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h2 := congrArg (fun z : ↥W => (z : ↥(Omega R p 1) ⧸ S')) hn
      simpa using h2
  have hmapsup : (Subgroup.zpowers qe ⊔ T).map (QuotientGroup.mk' S') = ⊤ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hqe, hzpW, sup_comm]
    exact hWsup
  have hsup : (⊤ : Subgroup ↥(Omega R p 1)) = Subgroup.zpowers qe ⊔ T := by
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' S') (Subgroup.zpowers qe ⊔ T)
    rw [hmapsup, Subgroup.comap_top, QuotientGroup.ker_mk', sup_assoc,
      sup_of_le_left hS'T] at h2
    exact h2
  -- `β` as an endomorphism of `S`, with its scaling data mod `H₁ = S'`.
  set σβ : ↥(Omega R p 1) →* ↥(Omega R p 1) :=
    ((hSinvB.restrict b : MulAut ↥(Omega R p 1)) : ↥(Omega R p 1) →* ↥(Omega R p 1))
    with hσβdef
  have hσT : ∀ y ∈ T, σβ y ∈ T := fun y hy => hTinvB.smul_mem b hy
  have hσq : (qe ^ t)⁻¹ * σβ qe ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥(Omega R p 1)) 1 := by
    rw [hH₁]
    have hqW : (QuotientGroup.mk' S') qe ∈ W := by rw [hqe]; exact gW.2
    have h := htW _ hqW
    rw [IsAInvariant.quotientMulAutHom_apply_mk', ← map_zpow] at h
    exact QuotientGroup.eq.mp h.symm
  have hbase : ∀ y ∈ T, (y ^ t₀)⁻¹ * σβ y ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥(Omega R p 1)) 1 := by
    intro y hy
    rw [hH₁]
    have h := ht₀T ((QuotientGroup.mk' S') y) ⟨y, hy, rfl⟩
    rw [IsAInvariant.quotientMulAutHom_apply_mk', ← map_zpow] at h
    exact QuotientGroup.eq.mp h.symm
  -- The corrected `(E.23)` supply, from `hdc`.
  have hscale := scale_iterCommutator_of_two_step (T := T) σβ hsup hσT hσq hbase hdc
  have hβsupply : ∀ n : ℕ,
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥(Omega R p 1)) n ≠ ⊥ →
      ∃ s : ℤ, (s : ZMod p) = (t₀ : ZMod p) * (t : ZMod p) ^ n ∧
        ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥(Omega R p 1)) n,
          (y ^ s)⁻¹ * σβ y ∈
            OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥(Omega R p 1)) (n + 1) :=
    fun n _ => ⟨t₀ * t ^ n, by push_cast; ring, fun y hy => hscale n y hy⟩
  -- Fire the `(E.28)` engine, and unfold `⁅T, T⁆ = ⊥` into commutativity.
  have hbot := hyp.commutator_centralizer_eq_bot_of_beta_supply hcard hSinvA ha hv hwmem hw1
    hr hr₀ hr0r hrq hr1 σβ hβsupply htu ht₀u htne
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hxy : ⁅(x : ↥(Omega R p 1)), (y : ↥(Omega R p 1))⁆ ∈
      (⊥ : Subgroup ↥(Omega R p 1)) := by
    rw [← hbot]
    exact Subgroup.commutator_mem_commutator x.2 y.2
  have hcomm : (x : ↥(Omega R p 1)) * y = y * x :=
    (commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hxy)).eq
  simpa using hcomm

end OddOrder.BG.AppE
