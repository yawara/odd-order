/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.Basic
import Mathlib.FieldTheory.Fixed

/-!
# Peterfalvi Part II, Ch. II, step (1): the field model adapted to `P`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (1), p. 108.

Since `P ∩ W = 1`, the subgroup `P` embeds into `V̄ ≤ D̄ = D/W`, hence, by
the semilinear model of §2 Proposition 3, into the automorphism group of
the field `F ≅ Q₀`.  The adapted model records the coordinates `eQ` on
`Q₀` and `μ` on `K̄ = F(D̄)` together with the `P`-equivariances, and the
key consequence of (B1): the only elements of `F` fixed by all of `P` are
`0` and `1`.  Artin's lemma then gives `[F : F₂] = p`, so `|Q₀| = 2^p`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch01 (fitting)

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- The embedding of `P` into `V̄ = VW/W ≤ D̄`. -/
noncomputable def toVbar : ↥fc.P →* ↥fc.toHypothesis.Vbar where
  toFun g :=
    ⟨QuotientGroup.mk (⟨(g : G),
        fc.toHypothesis.V_le_D (fc.P_le_V g.2)⟩ : ↥fc.toHypothesis.D),
      ⟨⟨(g : G), fc.toHypothesis.V_le_D (fc.P_le_V g.2)⟩,
        fc.P_le_V g.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    change QuotientGroup.mk _ = (1 : fc.toHypothesis.Dbar)
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.one_mem _
  map_mul' g h := by
    apply Subtype.ext
    change QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul]
    rfl

@[simp] lemma toVbar_coe (g : ↥fc.P) :
    ((fc.toVbar g : ↥fc.toHypothesis.Vbar) : fc.toHypothesis.Dbar) =
      QuotientGroup.mk (⟨(g : G),
        fc.toHypothesis.V_le_D (fc.P_le_V g.2)⟩ : ↥fc.toHypothesis.D) := rfl

theorem toVbar_injective : Function.Injective fc.toVbar := by
  intro g h hgh
  have hval := congrArg
    (fun z : ↥fc.toHypothesis.Vbar => (z : fc.toHypothesis.Dbar)) hgh
  simp only [toVbar_coe] at hval
  rw [QuotientGroup.eq] at hval
  have hmemW : (g : G)⁻¹ * (h : G) ∈ fc.toHypothesis.W := hval
  have hmemP : (g : G)⁻¹ * (h : G) ∈ fc.P :=
    fc.P.mul_mem (fc.P.inv_mem g.2) h.2
  have hbot : (g : G)⁻¹ * (h : G) ∈ fc.P ⊓ fc.toHypothesis.W :=
    ⟨hmemP, hmemW⟩
  rw [fc.P_inf_W_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hbot
  exact Subtype.ext hbot

/-- **The field model adapted to `P`** (Peterfalvi Part II, Ch. II, (1),
p. 108): coordinates `eQ : Q₀ ≃ F` and `μ : K̄ ≃ Fˣ` under which `P` acts
by field automorphisms `σhom`, together with the (B1) consequence that the
only `P`-fixed elements of `F` are `0` and `1`. -/
theorem exists_adapted_field_model :
    ∃ (F : Type uG) (_ : Field F) (_ : Finite F)
      (eQ : ↥fc.toHypothesis.Q0 ≃* Multiplicative F)
      (μ : ↥(fitting fc.toHypothesis.Dbar) ≃* Fˣ)
      (σhom : ↥fc.P →* RingAut F),
      Nat.card F = Nat.card ↥fc.toHypothesis.Q0 ∧
      Function.Injective σhom ∧
      (∀ (g : ↥fc.P) (x : ↥fc.toHypothesis.Q0),
        eQ (fc.toHypothesis.conjQ0bar
          ((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
            fc.toHypothesis.Dbar) x) =
          fieldRingAutOnAdditive F (σhom g) (eQ x)) ∧
      (∀ (g : ↥fc.P) (t : ↥(fitting fc.toHypothesis.Dbar)),
        μ (fc.toHypothesis.fittingConjAction (fc.toVbar g) t) =
          fieldRingAutOnUnits F (σhom g) (μ t)) ∧
      ∀ a : F, (∀ g : ↥fc.P, σhom g a = a) → a = 0 ∨ a = 1 := by
  classical
  obtain ⟨F, hField, hFinite, A, hcardF, hVcyc, eQ, μ, νe,
      hT, hE, hκ, eL, hL1, hL2, hL3⟩ := fc.toHypothesis.exists_semilinear_equiv
  letI : Field F := hField
  letI : Finite F := hFinite
  set σhom : ↥fc.P →* RingAut F :=
    A.subtype.comp (νe.toMonoidHom.comp fc.toVbar) with hσdef
  have hσinj : Function.Injective σhom := by
    intro a b hab
    exact fc.toVbar_injective (νe.injective (Subtype.val_injective hab))
  -- the additive bridge
  have hbridge : ∀ (g : ↥fc.P) (x : ↥fc.toHypothesis.Q0),
      eQ (fc.toHypothesis.conjQ0bar
        ((fc.toVbar g : ↥fc.toHypothesis.Vbar) : fc.toHypothesis.Dbar) x) =
        fieldRingAutOnAdditive F (σhom g) (eQ x) := by
    intro g x
    have happ := congrArg
      (fun e : ↥fc.toHypothesis.Q0 ≃* Multiplicative F => e x)
      (hE (fc.toVbar g))
    simp only [MulEquiv.trans_apply] at happ
    have hinr : fc.toHypothesis.fittingSemidirectEquiv
        (SemidirectProduct.inr (fc.toVbar g)) =
        ((fc.toVbar g : ↥fc.toHypothesis.Vbar) : fc.toHypothesis.Dbar) := by
      show SemidirectProduct.mulEquivSubgroup _
        (SemidirectProduct.inr (fc.toVbar g)) = _
      simp [SemidirectProduct.mulEquivSubgroup]
    have hract : SemidirectProduct.rightFactorAction
        fc.toHypothesis.fittingConjAction
        (fc.toHypothesis.conjQ0bar.comp
          fc.toHypothesis.fittingSemidirectEquiv.toMonoidHom)
        (fc.toVbar g) =
        fc.toHypothesis.conjQ0bar
          ((fc.toVbar g : ↥fc.toHypothesis.Vbar) :
            fc.toHypothesis.Dbar) := by
      show fc.toHypothesis.conjQ0bar
        (fc.toHypothesis.fittingSemidirectEquiv
          (SemidirectProduct.inr (fc.toVbar g))) = _
      rw [hinr]
    rwa [hract] at happ
  -- the multiplicative bridge
  have hunits : ∀ (g : ↥fc.P) (t : ↥(fitting fc.toHypothesis.Dbar)),
      μ (fc.toHypothesis.fittingConjAction (fc.toVbar g) t) =
        fieldRingAutOnUnits F (σhom g) (μ t) := by
    intro g t
    have happ := congrArg
      (fun e : ↥(fitting fc.toHypothesis.Dbar) ≃* Fˣ => e t)
      (hκ (fc.toVbar g))
    simp only [MulEquiv.trans_apply] at happ
    exact happ
  -- the (B1) fixed-element dichotomy
  have hfixmem : ∀ a : F, (∀ g : ↥fc.P, σhom g a = a) → a = 0 ∨ a = 1 := by
    intro a ha
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨ha0, ha1⟩ := hcon
    -- three distinct fixed elements `0, 1, a` inject into `C_{Q₀}(P)`
    have hmapmem : ∀ b : F, (∀ g : ↥fc.P, σhom g b = b) →
        ((eQ.symm (Multiplicative.ofAdd b) : ↥fc.toHypothesis.Q0) : G) ∈
          fc.toHypothesis.Q0 ⊓ Subgroup.centralizer (fc.P : Set G) := by
      intro b hb
      refine ⟨(eQ.symm (Multiplicative.ofAdd b)).2, ?_⟩
      show ((eQ.symm (Multiplicative.ofAdd b) : ↥fc.toHypothesis.Q0) : G) ∈
        Subgroup.centralizer (fc.P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      set x := eQ.symm (Multiplicative.ofAdd b) with hxdef
      have heq : eQ (fc.toHypothesis.conjQ0bar
          ((fc.toVbar ⟨g, hg⟩ : ↥fc.toHypothesis.Vbar) :
            fc.toHypothesis.Dbar) x) = eQ x := by
        rw [hbridge]
        apply Multiplicative.toAdd.injective
        rw [fieldRingAutOnAdditive_apply]
        have hxb : Multiplicative.toAdd (eQ x) = b := by
          rw [hxdef, eQ.apply_symm_apply]
          rfl
        rw [hxb]
        exact hb ⟨g, hg⟩
      have hconj := eQ.injective heq
      rw [toVbar_coe, fc.toHypothesis.conjQ0bar_mk] at hconj
      have hval := congrArg
        (fun y : ↥fc.toHypothesis.Q0 => (y : G)) hconj
      have hgx : g * (x : G) * g⁻¹ = (x : G) := hval
      calc g * (x : G) = (g * (x : G) * g⁻¹) * g := by group
        _ = (x : G) * g := by rw [hgx]
    have h0 : ∀ g : ↥fc.P, σhom g 0 = 0 := fun g => map_zero _
    have h1 : ∀ g : ↥fc.P, σhom g 1 = 1 := fun g => map_one _
    set y₀ : ↥(fc.toHypothesis.Q0 ⊓
        Subgroup.centralizer (fc.P : Set G)) :=
      ⟨_, hmapmem 0 h0⟩ with hy₀
    set y₁ : ↥(fc.toHypothesis.Q0 ⊓
        Subgroup.centralizer (fc.P : Set G)) :=
      ⟨_, hmapmem 1 h1⟩ with hy₁
    set ya : ↥(fc.toHypothesis.Q0 ⊓
        Subgroup.centralizer (fc.P : Set G)) :=
      ⟨_, hmapmem a ha⟩ with hya
    have hinjQ : ∀ b c : F,
        ((eQ.symm (Multiplicative.ofAdd b) : ↥fc.toHypothesis.Q0) : G) =
        ((eQ.symm (Multiplicative.ofAdd c) : ↥fc.toHypothesis.Q0) : G) →
        b = c := by
      intro b c hbc
      have := eQ.symm.injective (Subtype.ext hbc)
      exact Multiplicative.ofAdd.injective this
    have hne01 : y₀ ≠ y₁ := by
      intro h
      have hv : (y₀ : G) = (y₁ : G) := Subtype.ext_iff.mp h
      exact zero_ne_one (hinjQ 0 1 hv)
    have hne0a : y₀ ≠ ya := by
      intro h
      have hv : (y₀ : G) = (ya : G) := Subtype.ext_iff.mp h
      exact ha0 (hinjQ 0 a hv).symm
    have hne1a : y₁ ≠ ya := by
      intro h
      have hv : (y₁ : G) = (ya : G) := Subtype.ext_iff.mp h
      exact ha1 (hinjQ 1 a hv).symm
    have hcard3 : 3 ≤ Nat.card ↥(fc.toHypothesis.Q0 ⊓
        Subgroup.centralizer (fc.P : Set G)) := by
      haveI : Fintype ↥(fc.toHypothesis.Q0 ⊓
        Subgroup.centralizer (fc.P : Set G)) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      calc 3 = ({y₀, y₁, ya} : Finset _).card := by
            rw [Finset.card_insert_of_notMem (by simp [hne01, hne0a]),
              Finset.card_insert_of_notMem (by simp [hne1a]),
              Finset.card_singleton]
        _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    have := fc.card_Q0_inf_centralizer_le_two
    omega
  exact ⟨F, hField, hFinite, eQ, μ, σhom, hcardF, hσinj, hbridge,
    hunits, hfixmem⟩

/-- **Peterfalvi Part II, Ch. II, step (1), order of `Q₀`** (p. 108):
`|Q₀| = 2^p`.  The fixed subfield of the `P`-action is `{0, 1}` and
Artin's lemma gives `[F : F₂] = p`. -/
theorem card_Q0_eq_two_pow : Nat.card ↥fc.toHypothesis.Q0 = 2 ^ fc.p := by
  classical
  obtain ⟨F, hField, hFinite, eQ, μ, σhom, hcardF, hσinj, hbridge,
      hunits, hfixmem⟩ := fc.exists_adapted_field_model
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : MulSemiringAction ↥fc.P F := MulSemiringAction.compHom F σhom
  haveI hfaith : FaithfulSMul ↥fc.P F :=
    ⟨fun {σ τ} h => hσinj (RingEquiv.ext fun a => h a)⟩
  haveI : Fintype ↥fc.P := Fintype.ofFinite _
  haveI : Fintype F := Fintype.ofFinite F
  set F₀ := FixedPoints.subfield ↥fc.P F with hF₀def
  have hartin : Module.finrank ↥F₀ F = Fintype.card ↥fc.P :=
    FixedPoints.finrank_eq_card ↥fc.P F
  have hcardF₀_le : Fintype.card ↥F₀ ≤ 2 := by
    have hsub : (F₀ : Set F) ⊆ {0, 1} := by
      intro a haF₀
      have hfa : ∀ g : ↥fc.P, σhom g a = a := fun g => haF₀ g
      rcases hfixmem a hfa with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc Fintype.card ↥F₀ = Nat.card ↥(F₀ : Set F) := by
          rw [Nat.card_eq_fintype_card]
          rfl
      _ ≤ Nat.card ↥({0, 1} : Set F) := by
          apply Nat.card_le_card_of_injective
            (fun a => ⟨(a : F), hsub a.2⟩)
          intro a b hab
          have hv : ((a : F)) = ((b : F)) :=
            congrArg (fun y : ↥({0, 1} : Set F) => (y : F)) hab
          exact Subtype.ext hv
      _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          have := Set.ncard_insert_le (0 : F) ({1} : Set F)
          simpa [Set.ncard_singleton] using this
  have hcardF₀_ge : 2 ≤ Fintype.card ↥F₀ := Fintype.one_lt_card
  have hcardF₀ : Fintype.card ↥F₀ = 2 := le_antisymm hcardF₀_le hcardF₀_ge
  have hcards : Fintype.card F = Fintype.card ↥F₀ ^ Module.finrank ↥F₀ F :=
    Module.card_eq_pow_finrank
  rw [← hcardF, Nat.card_eq_fintype_card, hcards, hcardF₀, hartin,
    ← Nat.card_eq_fintype_card, fc.card_P]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
