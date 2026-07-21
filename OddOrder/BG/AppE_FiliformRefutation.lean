/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_FiliformGroup
import OddOrder.BG.AppE_FurtherResults

/-!
# BG Proposition E.4, as printed, is false: the assembled refutation

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, Proposition E.4 (p. 162).

This leaf is **Tier 2, WP5** of the counterexample programme (issue 3027; master
note `notes/bg/appE_e4_counterexample_2026_07_21.md`): it instantiates the repo's
own `RegularOperatorSetup` with the Lazard group `S = Exp(Q₆)` of
`OddOrder/BG/AppE_FiliformGroup.lean` and derives the **negation of the printed
Proposition E.4**, refuted at universe `0`.

* `q6Setup` — `S`, `B = C₄₉`, `A = ⟨β⁷⟩`, `R₀ = ⟨v⟩`, `R₁ = ⟨e₅⟩` satisfy **every**
  field of `RegularOperatorSetup Q6 (Multiplicative (ZMod 49)) 197 7` (Theorem E.3's
  standing hypotheses, checked against the PDF page image — see the master note);
* `omega_q6_eq_top` — `S` has exponent `197`, so `Ω₁(S) = S` and `|Ω₁(S)| = 197⁶ ≥ 197⁴`;
* `act_regular` / `act_not_fixes_zpowers_vg` (imported) — `B` acts regularly and does
  not fix `R₀`: Proposition E.4's two extra hypotheses;
* `q6_centralizer_not_mulCommutative` — yet `C_S(Z₂(S))` is **not** abelian;
* `printed_propE4_false` — the headline: the printed Proposition E.4 is false.

The missing hypothesis is that `S` be **non-exceptional** (equivalently
`dc(S) ≥ 1`, equivalently the 2-step centralizers all agree); `Q₆` is exceptional,
and BG's unproved display `(E.23)` fails on it at level `i = 2`.  The corrected
E.4 — the same statement with that hypothesis added as `hdc` — is **proved** as
`RegularOperatorSetup.centralizer_upperCentralSeries_abelian_index_p` in
`OddOrder/BG/AppE_PropE4.lean` (issue 9402).

This leaf deliberately isolates the heavy `AppE_FurtherResults` import away from
`AppE_FiliformGroup.lean`.
-/

namespace OddOrder.BG.AppE.Filiform

open OddOrder.GroupTheory
open scoped Pointwise

/-! ## The setup instance: every hypothesis of Theorem E.3 holds for `Q₆` -/

/-- **The Lazard group of `Q₆` satisfies every standing hypothesis of BG
Theorem E.3** with `p = 197`, `q = 7`, `B = C₄₉`, `A = ⟨β⁷⟩ ≅ C₇`, `R₀ = ⟨v⟩`,
`R₁ = ⟨e₅⟩`.  All fields are supplied by the machine-checked layers of
`AppE_FiliformGroup.lean`; none is `sorry`d or opaque. -/
def q6Setup : RegularOperatorSetup Q6 (Multiplicative (ZMod 49)) 197 7 where
  p_prime := by norm_num
  p_odd := by decide
  q_prime := by norm_num
  q_odd := by decide
  p_ne_q := by norm_num
  R_pGroup := isPGroup_q6
  act := act
  p_not_dvd_card_B := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide
  A := Subgroup.zpowers (Multiplicative.ofAdd (7 : ZMod 49))
  A_card := card_zpowers_ofAdd_seven
  R₀ := Subgroup.zpowers vg
  R₀_card := card_zpowers_vg
  R₁ := Subgroup.zpowers e5g
  R₁_ne_bot := fun h => e5g_ne_one (Subgroup.zpowers_eq_bot.mp h)
  R₁_cyclic := isCyclic_of_prime_card card_zpowers_e5g
  centralizer_eq := centralizer_zpowers_vg
  R₀_disjoint_R₁ := disjoint_zpowers_vg_e5g
  A_fixes_R₀ := act_A_fixes_zpowers_vg
  A_regular := fun a _ ha x hx => act_regular a ha x hx

/-! ## `Ω₁(S) = S` and the size hypothesis -/

/-- `S` has exponent `197`, so `Ω₁(S) = S`. -/
theorem omega_q6_eq_top : Omega Q6 197 1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact pow_card_eq_one x)

/-- `|Ω₁(S)| = 197⁶ ≥ 197⁴`: Proposition E.4's size hypothesis. -/
theorem card_omega_ge : 197 ^ 4 ≤ Nat.card ↥(Omega Q6 197 1) := by
  rw [omega_q6_eq_top, Subgroup.card_top, card_q6]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-! ## Transporting `T = C_S(Z₂(S))` into the subtype `↥Ω₁(S)` -/

/-- `↥Ω₁(S) ≃* S`, since `Ω₁(S) = ⊤`. -/
def omegaEquiv : ↥(Omega Q6 197 1) ≃* Q6 :=
  (MulEquiv.subgroupCongr omega_q6_eq_top).trans Subgroup.topEquiv

/-- Membership in `Z₂(↥Ω₁(S))` is membership of the underlying element in
`Z₂(S)` (upper central series transports along `omegaEquiv`, which is `Subtype.val`). -/
theorem mem_upperCentralSeries_omega_two_iff (z : ↥(Omega Q6 197 1)) :
    z ∈ Subgroup.upperCentralSeries ↥(Omega Q6 197 1) 2 ↔
      (z : Q6) ∈ Subgroup.upperCentralSeries Q6 2 := by
  rw [← Subgroup.comap_upperCentralSeries omegaEquiv 2]
  exact Iff.rfl

/-- **The abelian clause of Proposition E.4 fails for `Q₆`**: `b` and `e₂` lie in
`C_{Ω₁(S)}(Z₂(Ω₁(S)))` (they centralize the `e₄`–`e₅` plane, having `x₀ = 0`),
but they do not commute. -/
theorem q6_centralizer_not_mulCommutative :
    ¬ IsMulCommutative
        ↥(Subgroup.centralizer
          ((Subgroup.upperCentralSeries ↥(Omega Q6 197 1) 2 :
            Subgroup ↥(Omega Q6 197 1)) : Set ↥(Omega Q6 197 1))) := by
  intro habel
  have hbgΩ : bg ∈ Omega Q6 197 1 := by rw [omega_q6_eq_top]; trivial
  have he2Ω : e2g ∈ Omega Q6 197 1 := by rw [omega_q6_eq_top]; trivial
  have hmemT : ∀ (g : Q6) (hg : g ∈ Omega Q6 197 1), g.co 0 = 0 →
      (⟨g, hg⟩ : ↥(Omega Q6 197 1)) ∈ Subgroup.centralizer
        ((Subgroup.upperCentralSeries ↥(Omega Q6 197 1) 2 :
          Subgroup ↥(Omega Q6 197 1)) : Set ↥(Omega Q6 197 1)) := by
    intro g hg h0
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : (z : Q6) ∈ Subgroup.upperCentralSeries Q6 2 :=
      (mem_upperCentralSeries_omega_two_iff z).mp hz
    have hcomm : (z : Q6) * g = g * (z : Q6) :=
      Subgroup.mem_centralizer_iff.mp
        (mem_centralizer_upperCentralSeries_two_iff.mpr h0) _ hz'
    exact Subtype.ext hcomm
  have hcomm := habel.is_comm.comm
    ⟨⟨bg, hbgΩ⟩, hmemT bg hbgΩ (by decide)⟩
    ⟨⟨e2g, he2Ω⟩, hmemT e2g he2Ω (by decide)⟩
  exact bg_e2g_not_commute (congrArg Subtype.val (congrArg Subtype.val hcomm))

/-! ## Headline -/

/-- **BG Proposition E.4, as printed, is FALSE.**

The statement below is the exact universally-quantified form of BG's Proposition E.4
as printed (without the corrective `hdc` hypothesis of
`RegularOperatorSetup.centralizer_upperCentralSeries_abelian_index_p`,
`OddOrder/BG/AppE_PropE4.lean`), quantified at universe `0` — and it is
refuted by `S = Exp(Q₆)`, `B = C₄₉`: the setup `q6Setup` satisfies every hypothesis
of Theorem E.3, `|Ω₁(S)| = 197⁶ ≥ 197⁴`, `B` acts regularly and does not fix `R₀`,
yet `T = C_S(Z₂(S))` is not abelian (`⁅b, e₂⁆ ≡ e₃ ≠ 1`).

The missing hypothesis is non-exceptionality (`dc(S) ≥ 1`); BG's unproved display
`(E.23)` fails on `Q₆` at level `i = 2`.  Master note:
`notes/bg/appE_e4_counterexample_2026_07_21.md`; the corrected E.4 (issue 9402) is
proved in `OddOrder/BG/AppE_PropE4.lean`.
Since App.E is Feit–Thompson's unpublished 1991 work with no published erratum,
this is, to our knowledge, a new finding. -/
theorem printed_propE4_false :
    ¬ ∀ (R B : Type) [Group R] [Group B] (p q : ℕ) [Finite R] [Finite B]
        (hyp : RegularOperatorSetup R B p q),
        p ^ 4 ≤ Nat.card ↥(Omega R p 1) →
        (∀ b : B, b ≠ 1 → ∀ x : R, hyp.act b x = x → x = 1) →
        (¬ ∀ b : B, (hyp.act b) • hyp.R₀ = hyp.R₀) →
        IsMulCommutative
            ↥(Subgroup.centralizer
              ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 :
                Subgroup ↥(Omega R p 1)) : Set ↥(Omega R p 1))) ∧
          (Subgroup.centralizer
              ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 :
                Subgroup ↥(Omega R p 1)) : Set ↥(Omega R p 1))).index = p := by
  intro h
  exact q6_centralizer_not_mulCommutative
    (h Q6 (Multiplicative (ZMod 49)) 197 7 q6Setup card_omega_ge
      act_regular act_not_fixes_zpowers_vg).1

end OddOrder.BG.AppE.Filiform
