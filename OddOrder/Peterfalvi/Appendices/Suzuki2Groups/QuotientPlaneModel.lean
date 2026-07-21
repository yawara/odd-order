/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.HigmanDE
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.InvariantSummands
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.SplitUniqueness
import OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabBridge

/-!
# Peterfalvi Part II, Ch. I §3, Lemma 5: the plane model of `Q ⧸ Q₀`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, Lemma 5, p. 107, final paragraph.

An isomorphic order-`q` two-summand split of `P ⧸ Z` under a cyclic
fixed-point-free actor `K` of order `q - 1` identifies `P ⧸ Z` with a
two-dimensional vector space over `F_q` on which `K` acts as the group of
nonzero scalar multiplications: each summand is a faithful irreducible
`F₂[K]`-module, its Singer model provides the field coordinate, and the
equivariant isomorphism between the summands aligns the two coordinates into
the diagonal scalar action.  This is the identification used in the last
paragraph of Lemma 5 to place `W` inside `GL(2, q)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

universe u

variable {P : Type u} [Group P] [Finite P]
variable {K : Type u} [Group K] [Finite K] [IsCyclic K]
variable {Z : Subgroup P} [Z.Normal]
variable {rho : K →* MulAut P} {hZinv : IsAInvariant rho Z}

/-- **The plane model of the central quotient** (Peterfalvi Part II, Ch. I
§3, Lemma 5, p. 107).  Given an isomorphic order-`q` two-summand split of
`P ⧸ Z` under a cyclic fixed-point-free actor of order `q - 1 = 2^n - 1`,
the quotient `P ⧸ Z` carries coordinates in `F_q × F_q` under which the
`K`-action is the diagonal action by nonzero scalars, and every nonzero
scalar arises this way. -/
theorem exists_planeCoordinates_of_isomorphicSplit
    (isplit : IsomorphicOrderQModuleSplit rho Z hZinv)
    (hfree : ∀ k : K, k ≠ 1 → ∀ q : P ⧸ Z,
      quotientMulAutHom hZinv k q = q → q = 1)
    {n : ℕ} (hn : n ≠ 0)
    (hKcard : Nat.card K = 2 ^ n - 1)
    (hZcard : Nat.card ↥Z = 2 ^ n) :
    ∃ (ψ : P ⧸ Z ≃ GaloisField 2 n × GaloisField 2 n)
      (mu : K →* (GaloisField 2 n)ˣ),
      Function.Surjective mu ∧
      (∀ x y : P ⧸ Z, ψ (x * y) = ψ x + ψ y) ∧
      ∀ (k : K) (x : P ⧸ Z),
        ψ (quotientMulAutHom hZinv k x) = (mu k : GaloisField 2 n) • ψ x := by
  classical
  set Xbar := isplit.split.left with hXdef
  set Ybar := isplit.split.right with hYdef
  have hcomm := isplit.split.quotientEA.comm
  have hsq := isplit.split.quotientEA.pow_eq_one
  letI : CommGroup (P ⧸ Z) :=
    { (inferInstance : Group (P ⧸ Z)) with mul_comm := hcomm }
  letI : CommGroup K := IsCyclic.commGroup
  -- the additive `F₂`-structure on the left summand
  letI : Module (ZMod 2) (Additive ↥Xbar) := AddCommGroup.zmodModule (by
    intro q
    apply Additive.toMul.injective
    change (Additive.toMul q : ↥Xbar) ^ 2 = 1
    apply Subtype.ext
    change ((Additive.toMul q : ↥Xbar) : P ⧸ Z) ^ 2 = 1
    exact hsq _)
  set rhoX : Representation (ZMod 2) K (Additive ↥Xbar) :=
    OddOrder.GroupTheory.elabRepresentation 2
      isplit.split.leftInvariant.restrict with hrhoX
  have hrhoXapply : ∀ (k : K) (x : ↥Xbar),
      rhoX k (Additive.ofMul x) =
        Additive.ofMul (isplit.split.leftInvariant.restrict k x) := fun k x =>
    OddOrder.GroupTheory.elabRepresentation_apply 2 _ k x
  -- cardinalities
  have hcardX : Nat.card ↥Xbar = 2 ^ n := isplit.split.leftCard.trans hZcard
  have hcardK' : Nat.card K = Nat.card ↥Xbar - 1 := by
    rw [hcardX, hKcard]
  have hXnontriv : Nontrivial ↥Xbar := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hcardX]
    exact Nat.one_lt_two_pow_iff.mpr hn
  -- fixed-point-freeness of the restricted action
  have hfreeX : ∀ k : K, k ≠ 1 → ∀ x : ↥Xbar,
      isplit.split.leftInvariant.restrict k x = x → x = 1 := by
    intro k hk x hx
    apply Subtype.ext
    apply hfree k hk
    have := congrArg Subtype.val hx
    rwa [IsAInvariant.restrict_apply_val] at this
  -- the subgroup ↔ submodule dictionary on the summand
  let Φ : Submodule (ZMod 2) (Additive ↥Xbar) ≃o Subgroup ↥Xbar :=
    (AddSubgroup.toZModSubmodule (n := 2)).symm.trans AddSubgroup.toSubgroup'
  have hmemΦ : ∀ (M : Submodule (ZMod 2) (Additive ↥Xbar)) (x : ↥Xbar),
      x ∈ Φ M ↔ Additive.ofMul x ∈ M := by
    intro M x
    simp only [Φ, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
      AddSubgroup.mem_toZModSubmodule]
    rfl
  -- irreducibility of the linearized summand
  have hirr : Representation.IsIrreducible rhoX := by
    have hbot_ne_top : (⊥ : Subrepresentation rhoX) ≠ ⊤ := by
      intro h
      have hbt : (⊥ : Submodule (ZMod 2) (Additive ↥Xbar)) = ⊤ :=
        congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top hbt
    letI : Nontrivial (Subrepresentation rhoX) := ⟨⊥, ⊤, hbot_ne_top⟩
    apply IsSimpleOrder.of_forall_eq_top
    intro W hWbot
    set V : Subgroup ↥Xbar := Φ W.toSubmodule with hV
    have hVmem : ∀ x : ↥Xbar, x ∈ V ↔ Additive.ofMul x ∈ W.toSubmodule :=
      hmemΦ W.toSubmodule
    have hVinv : IsAInvariant isplit.split.leftInvariant.restrict V := by
      intro k
      ext y
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      change (isplit.split.leftInvariant.restrict k)⁻¹ y ∈ V ↔ y ∈ V
      rw [hVmem, hVmem]
      constructor
      · intro h
        have hstep := W.apply_mem_toSubmodule k h
        rw [hrhoXapply] at hstep
        have hcancel : isplit.split.leftInvariant.restrict k
            ((isplit.split.leftInvariant.restrict k)⁻¹ y) = y := by
          rw [← map_inv]
          change isplit.split.leftInvariant.restrict k
            (isplit.split.leftInvariant.restrict k⁻¹ y) = y
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            MulAut.one_apply]
        rwa [hcancel] at hstep
      · intro h
        have hstep := W.apply_mem_toSubmodule k⁻¹ h
        rw [hrhoXapply] at hstep
        rwa [map_inv] at hstep
    have hdich := invariant_eq_bot_or_top_of_fixedPointFree_card
      (quotientMulAutHom hZinv) hfree isplit.split.leftInvariant hcardK' hVinv
    rcases hdich with hbot | htop
    · exfalso
      apply hWbot
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊥
      apply Φ.injective
      rw [Φ.map_bot, ← hV]
      exact hbot
    · apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊤
      apply Φ.injective
      rw [Φ.map_top, ← hV]
      exact htop
  -- faithfulness of the linearized summand
  have hfaith : Function.Injective rhoX := by
    have hker : ∀ k : K, rhoX k = 1 → k = 1 := by
      intro k hk
      by_contra hkne
      obtain ⟨x, hxne⟩ := exists_ne (1 : ↥Xbar)
      apply hxne
      apply hfreeX k hkne
      have happ : rhoX k (Additive.ofMul x) = Additive.ofMul x := by
        rw [hk]
        rfl
      rw [hrhoXapply] at happ
      exact Additive.ofMul.injective happ
    intro k l hkl
    have hmul : rhoX (k⁻¹ * l) = 1 := by
      rw [map_mul, ← hkl, ← map_mul, inv_mul_cancel, map_one]
    have := hker _ hmul
    rwa [inv_mul_eq_one] at this
  -- dimension of the summand
  have hfinrank : Module.finrank (ZMod 2) (Additive ↥Xbar) = n := by
    have hpow : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive ↥Xbar) = 2 ^ n := by
      haveI : Fintype (Additive ↥Xbar) := Fintype.ofFinite _
      calc (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive ↥Xbar)
          = Fintype.card (ZMod 2) ^
              Module.finrank (ZMod 2) (Additive ↥Xbar) := by
            rw [ZMod.card]
        _ = Fintype.card (Additive ↥Xbar) := Module.card_eq_pow_finrank.symm
        _ = Nat.card (Additive ↥Xbar) := Nat.card_eq_fintype_card.symm
        _ = 2 ^ n := hcardX
    exact Nat.pow_right_injective (le_refl 2) hpow
  -- the Singer field coordinate on the left summand
  obtain ⟨e₁, mu, hmuinj, hmueq⟩ :=
    OddOrder.RepresentationTheory.exists_galoisFieldLinearModel_of_faithful_irreducible
      rhoX n hn hfinrank hirr hfaith
  -- `mu` is surjective by cardinality
  have hmusurj : Function.Surjective mu := by
    have hcardF : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
      haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_units,
        ← Nat.card_eq_fintype_card, GaloisField.card 2 n hn]
    have hbij : Function.Bijective mu :=
      (Nat.bijective_iff_injective_and_card mu).mpr
        ⟨hmuinj, by rw [hKcard, hcardF]⟩
    exact hbij.surjective
  -- the product decomposition of the quotient
  set φhom : ↥Xbar × ↥Ybar →* P ⧸ Z := Xbar.subtype.coprod Ybar.subtype
    with hφdef
  have hφapply : ∀ p : ↥Xbar × ↥Ybar,
      φhom p = (p.1 : P ⧸ Z) * (p.2 : P ⧸ Z) := fun p => rfl
  have hφinj : Function.Injective φhom := by
    intro a b hab
    rw [hφapply, hφapply] at hab
    have hkey : (b.1 : P ⧸ Z)⁻¹ * (a.1 : P ⧸ Z) =
        (b.2 : P ⧸ Z) * (a.2 : P ⧸ Z)⁻¹ := by
      calc (b.1 : P ⧸ Z)⁻¹ * (a.1 : P ⧸ Z)
          = (b.1 : P ⧸ Z)⁻¹ * (((a.1 : P ⧸ Z) * a.2) * (a.2 : P ⧸ Z)⁻¹) := by
            group
        _ = (b.1 : P ⧸ Z)⁻¹ * (((b.1 : P ⧸ Z) * b.2) * (a.2 : P ⧸ Z)⁻¹) := by
            rw [hab]
        _ = (b.2 : P ⧸ Z) * (a.2 : P ⧸ Z)⁻¹ := by group
    have hmemX : (b.1 : P ⧸ Z)⁻¹ * (a.1 : P ⧸ Z) ∈ Xbar :=
      Xbar.mul_mem (Xbar.inv_mem b.1.2) a.1.2
    have hmemY : (b.1 : P ⧸ Z)⁻¹ * (a.1 : P ⧸ Z) ∈ Ybar := by
      rw [hkey]
      exact Ybar.mul_mem b.2.2 (Ybar.inv_mem a.2.2)
    have hbot : (b.1 : P ⧸ Z)⁻¹ * (a.1 : P ⧸ Z) ∈ (⊥ : Subgroup (P ⧸ Z)) := by
      rw [← isplit.split.complementary.inf_eq_bot]
      exact ⟨hmemX, hmemY⟩
    rw [Subgroup.mem_bot] at hbot
    have h1 : (b.1 : P ⧸ Z) = (a.1 : P ⧸ Z) := by
      rwa [inv_mul_eq_one] at hbot
    have h2 : (b.2 : P ⧸ Z) = (a.2 : P ⧸ Z) := by
      have h2' : (b.2 : P ⧸ Z) * (a.2 : P ⧸ Z)⁻¹ = 1 := hkey.symm.trans hbot
      rwa [mul_inv_eq_one] at h2'
    exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)
  have hcardprod : Nat.card (↥Xbar × ↥Ybar) = Nat.card (P ⧸ Z) := by
    haveI hXnormal : Xbar.Normal := normal_of_mul_comm hcomm _
    rw [Nat.card_prod]
    calc Nat.card ↥Xbar * Nat.card ↥Ybar
        = Nat.card ((P ⧸ Z) ⧸ Xbar) * Nat.card ↥Xbar := by
          rw [card_quotient_of_isCompl isplit.split.complementary,
            isplit.split.rightCard, isplit.split.leftCard, Nat.mul_comm]
      _ = Nat.card (P ⧸ Z) :=
          (Subgroup.card_eq_card_quotient_mul_card_subgroup Xbar).symm
  have hφbij : Function.Bijective φhom :=
    (Nat.bijective_iff_injective_and_card φhom).mpr ⟨hφinj, hcardprod⟩
  set φ : (↥Xbar × ↥Ybar) ≃* (P ⧸ Z) := MulEquiv.ofBijective φhom hφbij
    with hφequivdef
  have hφeq : ∀ p : ↥Xbar × ↥Ybar,
      φ p = (p.1 : P ⧸ Z) * (p.2 : P ⧸ Z) := fun p => rfl
  -- the coordinate equivalences on the two summands
  set eX : ↥Xbar ≃ GaloisField 2 n :=
    Additive.ofMul.trans e₁.toEquiv with heXdef
  have heXapply : ∀ x : ↥Xbar, eX x = e₁ (Additive.ofMul x) := fun _ => rfl
  set eY : ↥Ybar ≃ GaloisField 2 n :=
    isplit.summandEquiv.toMulEquiv.symm.toEquiv.trans eX with heYdef
  have heYapply : ∀ y : ↥Ybar,
      eY y = eX (isplit.summandEquiv.toMulEquiv.symm y) := fun _ => rfl
  -- additivity of the coordinates
  have heXadd : ∀ a b : ↥Xbar, eX (a * b) = eX a + eX b := by
    intro a b
    rw [heXapply, heXapply, heXapply]
    have hofmul : Additive.ofMul (a * b) =
        Additive.ofMul a + Additive.ofMul b := rfl
    rw [hofmul, map_add]
  have heYadd : ∀ a b : ↥Ybar, eY (a * b) = eY a + eY b := by
    intro a b
    rw [heYapply, heYapply, heYapply, map_mul, heXadd]
  -- equivariance of the coordinates
  have heXeq : ∀ (k : K) (x : ↥Xbar),
      eX (isplit.split.leftInvariant.restrict k x) =
        (mu k : GaloisField 2 n) * eX x := by
    intro k x
    rw [heXapply, heXapply, ← hrhoXapply, hmueq]
  have heYeq : ∀ (k : K) (y : ↥Ybar),
      eY (isplit.split.rightInvariant.restrict k y) =
        (mu k : GaloisField 2 n) * eY y := by
    intro k y
    rw [heYapply, heYapply]
    have hsymm : isplit.summandEquiv.toMulEquiv.symm
        (isplit.split.rightInvariant.restrict k y) =
        isplit.split.leftInvariant.restrict k
          (isplit.summandEquiv.toMulEquiv.symm y) := by
      apply isplit.summandEquiv.toMulEquiv.injective
      rw [MulEquiv.apply_symm_apply, isplit.summandEquiv.equivariant,
        MulEquiv.apply_symm_apply]
    rw [hsymm, heXeq]
  -- assemble the plane coordinates
  set ψ : P ⧸ Z ≃ GaloisField 2 n × GaloisField 2 n :=
    φ.toEquiv.symm.trans (Equiv.prodCongr eX eY) with hψdef
  have hψapply : ∀ x : P ⧸ Z,
      ψ x = (eX (φ.symm x).1, eY (φ.symm x).2) := fun _ => rfl
  refine ⟨ψ, mu, hmusurj, ?_, ?_⟩
  · -- additivity
    intro x y
    rw [hψapply, hψapply, hψapply]
    have hsymm_mul : φ.symm (x * y) = φ.symm x * φ.symm y := map_mul φ.symm x y
    rw [hsymm_mul]
    have h1 : (φ.symm x * φ.symm y).1 = (φ.symm x).1 * (φ.symm y).1 := rfl
    have h2 : (φ.symm x * φ.symm y).2 = (φ.symm x).2 * (φ.symm y).2 := rfl
    rw [h1, h2, heXadd, heYadd]
    rfl
  · -- scalar equivariance
    intro k x
    obtain ⟨p, rfl⟩ := φ.surjective x
    have hact : quotientMulAutHom hZinv k (φ p) =
        φ (isplit.split.leftInvariant.restrict k p.1,
           isplit.split.rightInvariant.restrict k p.2) := by
      rw [hφeq, hφeq, map_mul,
        IsAInvariant.restrict_apply_val isplit.split.leftInvariant,
        IsAInvariant.restrict_apply_val isplit.split.rightInvariant]
    rw [hact, hψapply, hψapply, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]
    show (eX (isplit.split.leftInvariant.restrict k p.1),
        eY (isplit.split.rightInvariant.restrict k p.2)) =
      (mu k : GaloisField 2 n) • (eX p.1, eY p.2)
    rw [heXeq, heYeq, Prod.smul_mk, smul_eq_mul, smul_eq_mul]

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
