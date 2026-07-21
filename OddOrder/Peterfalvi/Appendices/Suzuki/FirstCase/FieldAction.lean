/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.Basic
import Mathlib.FieldTheory.Fixed

/-!
# Peterfalvi Part II, Ch. II, step (1): `|Q₀| = 2^p`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (1), p. 108.

Since `P ∩ W = 1`, the subgroup `P` embeds into `V̄ ≤ D̄ = D/W`, hence, by
the semilinear model of §2 Proposition 3, into the automorphism group of
the field `F ≅ Q₀`.  Its fixed subfield corresponds to `C_{Q₀}(P)`, which
has order at most `2` by (B1) and at least `2` because it contains the
prime field.  Artin's lemma then gives `[F : F^P] = p`, so
`|Q₀| = |F| = 2^p`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

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

/-- **Peterfalvi Part II, Ch. II, step (1), order of `Q₀`** (p. 108):
`|Q₀| = 2^p`.  `P` acts on the field `F ≅ Q₀` as a group of field
automorphisms of order `p`; by (B1) its fixed subfield has exactly two
elements, and Artin's lemma gives `[F : F₂] = p`. -/
theorem card_Q0_eq_two_pow : Nat.card ↥fc.toHypothesis.Q0 = 2 ^ fc.p := by
  classical
  obtain ⟨F, hField, hFinite, A, hcardF, hVcyc, eQ, μ, νe,
      hT, hE, hκ, eL, hL1, hL2, hL3⟩ := fc.toHypothesis.exists_semilinear_equiv
  letI : Field F := hField
  letI : Finite F := hFinite
  -- the action of `P` on `F` by field automorphisms
  set σhom : ↥fc.P →* RingAut F :=
    A.subtype.comp (νe.toMonoidHom.comp fc.toVbar) with hσdef
  have hσinj : Function.Injective σhom := by
    intro a b hab
    exact fc.toVbar_injective (νe.injective (Subtype.val_injective hab))
  -- the bridge: `eQ` intertwines conjugation by `V̄` with field automorphisms
  have hbridge : ∀ (z : ↥fc.toHypothesis.Vbar) (x : ↥fc.toHypothesis.Q0),
      eQ (fc.toHypothesis.conjQ0bar (z : fc.toHypothesis.Dbar) x) =
        fieldRingAutOnAdditive F ((νe z : A) : RingAut F) (eQ x) := by
    intro z x
    have happ := congrArg
      (fun e : ↥fc.toHypothesis.Q0 ≃* Multiplicative F => e x) (hE z)
    simp only [MulEquiv.trans_apply] at happ
    have hinr : fc.toHypothesis.fittingSemidirectEquiv
        (SemidirectProduct.inr z) = (z : fc.toHypothesis.Dbar) := by
      show SemidirectProduct.mulEquivSubgroup _ (SemidirectProduct.inr z) = _
      simp [SemidirectProduct.mulEquivSubgroup]
    have hract : SemidirectProduct.rightFactorAction
        fc.toHypothesis.fittingConjAction
        (fc.toHypothesis.conjQ0bar.comp
          fc.toHypothesis.fittingSemidirectEquiv.toMonoidHom) z =
        fc.toHypothesis.conjQ0bar (z : fc.toHypothesis.Dbar) := by
      show fc.toHypothesis.conjQ0bar
        (fc.toHypothesis.fittingSemidirectEquiv (SemidirectProduct.inr z)) = _
      rw [hinr]
    rwa [hract] at happ
  -- the fixed-point dictionary
  have hfix : ∀ (g : ↥fc.P) (x : ↥fc.toHypothesis.Q0),
      fc.toHypothesis.conjQ0
        ⟨(g : G), fc.toHypothesis.V_le_D (fc.P_le_V g.2)⟩ x = x ↔
      σhom g (Multiplicative.toAdd (eQ x)) = Multiplicative.toAdd (eQ x) := by
    intro g x
    constructor
    · intro h
      have := hbridge (fc.toVbar g) x
      rw [toVbar_coe, fc.toHypothesis.conjQ0bar_mk, h] at this
      have htoAdd := congrArg Multiplicative.toAdd this
      rw [fieldRingAutOnAdditive_apply] at htoAdd
      exact htoAdd.symm
    · intro h
      have hb := hbridge (fc.toVbar g) x
      rw [toVbar_coe, fc.toHypothesis.conjQ0bar_mk] at hb
      apply eQ.injective
      rw [hb]
      apply Multiplicative.toAdd.injective
      rw [fieldRingAutOnAdditive_apply]
      exact h
  -- the `P`-action on `F` by field automorphisms, and its fixed subfield
  letI : MulSemiringAction ↥fc.P F := MulSemiringAction.compHom F σhom
  haveI hfaith : FaithfulSMul ↥fc.P F :=
    ⟨fun {σ τ} h => hσinj (RingEquiv.ext fun a => h a)⟩
  haveI : Fintype ↥fc.P := Fintype.ofFinite _
  haveI : Fintype F := Fintype.ofFinite F
  set F₀ := FixedPoints.subfield ↥fc.P F with hF₀def
  have hartin : Module.finrank ↥F₀ F = Fintype.card ↥fc.P :=
    FixedPoints.finrank_eq_card ↥fc.P F
  -- fixed elements inject into `C_{Q₀}(P)`
  have hmapinj : ∀ a : F, (∀ σ : ↥fc.P, σhom σ a = a) →
      ((eQ.symm (Multiplicative.ofAdd a) : ↥fc.toHypothesis.Q0) : G) ∈
        fc.toHypothesis.Q0 ⊓ Subgroup.centralizer (fc.P : Set G) := by
    intro a ha
    refine ⟨(eQ.symm (Multiplicative.ofAdd a)).2, ?_⟩
    show ((eQ.symm (Multiplicative.ofAdd a) : ↥fc.toHypothesis.Q0) : G) ∈
      Subgroup.centralizer (fc.P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    set x := eQ.symm (Multiplicative.ofAdd a) with hxdef
    have hafix : σhom ⟨g, hg⟩ (Multiplicative.toAdd (eQ x)) =
        Multiplicative.toAdd (eQ x) := by
      have : eQ x = Multiplicative.ofAdd a := by
        rw [hxdef, eQ.apply_symm_apply]
      rw [this]
      exact ha ⟨g, hg⟩
    have hconj := (hfix ⟨g, hg⟩ x).mpr hafix
    have hval := congrArg
      (fun y : ↥fc.toHypothesis.Q0 => (y : G)) hconj
    have hgx : g * (x : G) * g⁻¹ = (x : G) := hval
    calc g * (x : G) = (g * (x : G) * g⁻¹) * g := by group
      _ = (x : G) * g := by rw [hgx]
  have hcardF₀_le : Fintype.card ↥F₀ ≤ 2 := by
    have hinj : Function.Injective
        (fun a : ↥F₀ =>
          (⟨((eQ.symm (Multiplicative.ofAdd (a : F)) :
              ↥fc.toHypothesis.Q0) : G),
            hmapinj (a : F) a.2⟩ :
          ↥(fc.toHypothesis.Q0 ⊓
            Subgroup.centralizer (fc.P : Set G)))) := by
      intro a b hab
      have h1 := congrArg
        (fun y : ↥(fc.toHypothesis.Q0 ⊓
          Subgroup.centralizer (fc.P : Set G)) =>
            eQ (⟨(y : G), y.2.1⟩ : ↥fc.toHypothesis.Q0)) hab
      simp only at h1
      apply Subtype.ext
      have h2 : eQ (eQ.symm (Multiplicative.ofAdd (a : F))) =
          eQ (eQ.symm (Multiplicative.ofAdd (b : F))) := h1
      rw [eQ.apply_symm_apply, eQ.apply_symm_apply] at h2
      exact Multiplicative.ofAdd.injective h2
    calc Fintype.card ↥F₀ = Nat.card ↥F₀ := Nat.card_eq_fintype_card.symm
      _ ≤ Nat.card ↥(fc.toHypothesis.Q0 ⊓
            Subgroup.centralizer (fc.P : Set G)) :=
          Nat.card_le_card_of_injective _ hinj
      _ ≤ 2 := fc.card_Q0_inf_centralizer_le_two
  have hcardF₀_ge : 2 ≤ Fintype.card ↥F₀ := Fintype.one_lt_card
  have hcardF₀ : Fintype.card ↥F₀ = 2 := le_antisymm hcardF₀_le hcardF₀_ge
  -- assemble
  have hcards : Fintype.card F = Fintype.card ↥F₀ ^ Module.finrank ↥F₀ F :=
    Module.card_eq_pow_finrank
  rw [← hcardF, Nat.card_eq_fintype_card, hcards, hcardF₀, hartin,
    ← Nat.card_eq_fintype_card, fc.card_P]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
