/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.FieldAction

/-!
# Peterfalvi Part II, Ch. II, step (1): fixed points on `Q₀`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (1), p. 108.

The fixed points of `P` on `Q₀` number exactly two: at most two by (B1),
and the orbit count of the `p`-group `P` acting on the `2^p` elements of
`Q₀` gives `|C_{Q₀}(P)| ≡ 2^p ≡ 2 (mod p)` by Fermat's little theorem.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch01 (fitting)

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. II, step (1), fixed-point count** (p. 108):
`|C_{Q₀}(P)| = 2`. -/
theorem card_Q0_inf_centralizer_eq_two :
    Nat.card ↥(fc.toHypothesis.Q0 ⊓
      Subgroup.centralizer (fc.P : Set G)) = 2 := by
  classical
  -- the action of `P` on `Q₀` by conjugation
  set actP : ↥fc.P →* MulAut ↥fc.toHypothesis.Q0 :=
    fc.toHypothesis.conjQ0.comp
      (Subgroup.inclusion (fc.P_le_V.trans fc.toHypothesis.V_le_D))
    with hactdef
  letI : MulAction ↥fc.P ↥fc.toHypothesis.Q0 := MulAction.compHom _ actP
  haveI : Fintype ↥fc.toHypothesis.Q0 := Fintype.ofFinite _
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  have hP : IsPGroup fc.p ↥fc.P :=
    IsPGroup.of_card (by rw [fc.card_P, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints ↥fc.toHypothesis.Q0
  -- the fixed points are exactly the centralized elements
  have hmem : ∀ x : ↥fc.toHypothesis.Q0,
      x ∈ MulAction.fixedPoints ↥fc.P ↥fc.toHypothesis.Q0 ↔
        (x : G) ∈ Subgroup.centralizer (fc.P : Set G) := by
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have happ : actP ⟨g, hg⟩ x = x := hx ⟨g, hg⟩
      have hval := congrArg
        (fun y : ↥fc.toHypothesis.Q0 => (y : G)) happ
      have hconj : g * (x : G) * g⁻¹ = (x : G) := hval
      calc g * (x : G) = (g * (x : G) * g⁻¹) * g := by group
        _ = (x : G) * g := by rw [hconj]
    · intro hx g
      show actP g x = x
      apply Subtype.ext
      have hcomm := Subgroup.mem_centralizer_iff.mp hx (g : G) g.2
      show (g : G) * (x : G) * (g : G)⁻¹ = (x : G)
      calc (g : G) * (x : G) * (g : G)⁻¹
          = ((x : G) * (g : G)) * (g : G)⁻¹ := by rw [← hcomm]
        _ = (x : G) := by group
  -- transfer the count to the centralizer subgroup
  have hcardfix :
      Nat.card (MulAction.fixedPoints ↥fc.P ↥fc.toHypothesis.Q0) =
        Nat.card ↥(fc.toHypothesis.Q0 ⊓
          Subgroup.centralizer (fc.P : Set G)) := by
    apply Nat.card_congr
    exact
      { toFun := fun x =>
          ⟨((x : ↥fc.toHypothesis.Q0) : G),
            (x : ↥fc.toHypothesis.Q0).2, (hmem _).mp x.2⟩
        invFun := fun y =>
          ⟨⟨(y : G), y.2.1⟩, (hmem _).mpr y.2.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => rfl }
  -- Fermat: `2^p ≡ 2 (mod p)`
  have h2p : (2 : ℕ) ^ fc.p ≡ 2 [MOD fc.p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact ZMod.pow_card (2 : ZMod fc.p)
  -- assemble
  set c := Nat.card ↥(fc.toHypothesis.Q0 ⊓
    Subgroup.centralizer (fc.P : Set G)) with hcdef
  have hcmod : (2 : ℕ) ≡ c [MOD fc.p] := by
    have h1 : (2 : ℕ) ^ fc.p ≡ c [MOD fc.p] := by
      rw [← fc.card_Q0_eq_two_pow, ← hcardfix]
      exact hmod
    exact h2p.symm.trans h1
  have hle : c ≤ 2 := fc.card_Q0_inf_centralizer_le_two
  have hp3 : 3 ≤ fc.p := by
    have h2 := fc.p_prime.two_le
    have hne := fc.p_ne_two
    omega
  have hmodeq : 2 % fc.p = c % fc.p := hcmod
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmodeq
  omega

/-- **Peterfalvi Part II, Ch. II, step (1), trivial `K`-fixed points**
(p. 108): `C_K(P) = 1`.  A `P`-centralized element of `K` maps to a
`P`-fixed unit of the field model, hence to a unit of the two-element
fixed subfield, so its image in `D̄` is trivial and it lies in
`K ∩ W ≤ K ∩ V = 1`. -/
theorem K_inf_centralizer_eq_bot :
    fc.toHypothesis.K ⊓ Subgroup.centralizer (fc.P : Set G) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨hkK, hkC⟩ := hk
  rw [Subgroup.mem_bot]
  have hkD : k ∈ fc.toHypothesis.D := fc.toHypothesis.K_le_D hkK
  set kbar : fc.toHypothesis.Dbar :=
    QuotientGroup.mk ⟨k, hkD⟩ with hkbar
  have hkfit : kbar ∈ fitting fc.toHypothesis.Dbar := by
    rw [← fc.toHypothesis.Kbar_eq_fitting]
    exact ⟨⟨k, hkD⟩, hkK, rfl⟩
  set t : ↥(fitting fc.toHypothesis.Dbar) := ⟨kbar, hkfit⟩ with htdef
  -- `P` fixes `t` under the conjugation action on the Fitting subgroup
  have hfixt : ∀ g : ↥fc.P,
      fc.toHypothesis.fittingConjAction (fc.toVbar g) t = t := by
    intro g
    apply Subtype.ext
    simp only [Hypothesis.fittingConjAction, MonoidHom.comp_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    show ((fc.toVbar g : ↥fc.toHypothesis.Vbar) : fc.toHypothesis.Dbar) *
        kbar *
        (((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
          fc.toHypothesis.Dbar))⁻¹ = kbar
    rw [toVbar_coe, hkbar, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have hcomm := Subgroup.mem_centralizer_iff.mp hkC (g : G) g.2
    show (g : G) * k * (g : G)⁻¹ = k
    calc (g : G) * k * (g : G)⁻¹ = (k * (g : G)) * (g : G)⁻¹ := by
          rw [← hcomm]
      _ = k := by group
  -- consume the adapted field model
  obtain ⟨F, hField, hFinite, eQ, μ, σhom, hcardF, hσinj, hbridge,
      hunits, hfixmem⟩ := fc.exists_adapted_field_model
  letI : Field F := hField
  letI : Finite F := hFinite
  have hμfix : ∀ g : ↥fc.P,
      σhom g ((μ t : Fˣ) : F) = ((μ t : Fˣ) : F) := by
    intro g
    have hu := hunits g t
    rw [hfixt g] at hu
    have hval := congrArg (fun u : Fˣ => (u : F)) hu
    rw [fieldRingAutOnUnits_apply_val] at hval
    exact hval.symm
  rcases hfixmem _ hμfix with h0 | h1
  · exact absurd h0 (Units.ne_zero (μ t))
  · have hμt1 : μ t = 1 := Units.ext h1
    have ht1 : t = 1 := μ.injective (by rw [hμt1, map_one])
    have hkbar1 : kbar = 1 := congrArg Subtype.val ht1
    rw [hkbar, QuotientGroup.eq_one_iff] at hkbar1
    have hkW : k ∈ fc.toHypothesis.W := hkbar1
    have hVK : k ∈ fc.toHypothesis.V ⊓ fc.toHypothesis.K :=
      ⟨fc.toHypothesis.W_le_V hkW, hkK⟩
    rw [fc.toHypothesis.V_inf_K_eq_bot] at hVK
    exact Subgroup.mem_bot.mp hVK

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
