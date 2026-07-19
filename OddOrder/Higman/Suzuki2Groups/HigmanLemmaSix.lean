/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanSquareMap
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralDegreeThree

/-!
# Higman's Lemma 6

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), section 4,
pp. 85--86, Lemma 6.

Higman's first step is a kernel comparison.  If a power of the cyclic actor
is the identity on `L₂` and `L₃`, then it is already the identity on `L₁`.
Indeed the image of `1 - η` on `L₁` is invariant.  Equivariance makes the
actual bracket `L₂ × L₁ → L₃` vanish on that image.  Irreducibility says the
image is zero or all of `L₁`; the latter would make the full-span bracket
zero and hence force `L₃ = 0`.

The later sections of this file will add the odd-dimension reduction and the
pair/triple Frobenius-weight argument from the rest of Higman's proof.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open scoped IsMulCommutative

universe uH uC

local instance instLemmaSixLowerCentralLayerIsMulCommutative
    (H : Type uH) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  ⟨⟨(lowerCentralLayer_isElementaryAbelian H i).1⟩⟩

noncomputable local instance instLemmaSixLowerCentralLayerZModTwoModule
    (H : Type uH) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-! ## Equality of the three actor kernels -/

/-- **Higman Lemma 6, first paragraph (p. 85).**

For a commutative actor, an element acting trivially on `L₂` and `L₃` also
acts trivially on an irreducible `L₁`, provided `L₃` is nonzero.  The proof
uses the actual mixed commutator and its full-span theorem. -/
theorem lowerCentralLayerZero_action_eq_one_of_second_third_action_eq_one
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 2))]
    (c : C)
    (hsecond : lowerCentralLayerRepresentation phi 1 c = 1)
    (hthird : lowerCentralLayerRepresentation phi 2 c = 1) :
    lowerCentralLayerRepresentation phi 0 c = 1 := by
  let rho₀ := lowerCentralLayerRepresentation phi 0
  let rho₁ := lowerCentralLayerRepresentation phi 1
  let rho₂ := lowerCentralLayerRepresentation phi 2
  let gamma := lowerCentralDegreeThreeCommutatorBilinear H
  change Representation.IsIrreducible rho₀ at hirr
  change rho₁ c = 1 at hsecond
  change rho₂ c = 1 at hthird
  change rho₀ c = 1
  have hcomm : ∀ (g : C) (v : Additive (lowerCentralLayer H 0)),
      rho₀ c (rho₀ g v) = rho₀ g (rho₀ c v) := by
    intro g v
    rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      ← map_mul, ← map_mul, mul_comm]
  let d : Additive (lowerCentralLayer H 0) →ₗ[ZMod 2]
      Additive (lowerCentralLayer H 0) :=
    LinearMap.id - rho₀ c
  let dInter : Representation.IntertwiningMap rho₀ rho₀ :=
    d.intertwiningMap_of_isIntertwiningMap rho₀ rho₀ (by
      intro g v
      dsimp only [d]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
      rw [hcomm])
  let S : Subrepresentation rho₀ := dInter.range
  letI : Representation.IsIrreducible rho₀ := hirr
  rcases eq_bot_or_eq_top S with hS | hS
  · have hdRange : LinearMap.range d = ⊥ := by
      have h := congrArg Subrepresentation.toSubmodule hS
      change LinearMap.range d = ⊥ at h
      exact h
    have hd : d = 0 := LinearMap.range_eq_bot.mp hdRange
    ext v
    have hv := LinearMap.congr_fun hd v
    change v - rho₀ c v = 0 at hv
    simpa using (sub_eq_zero.mp hv).symm
  · have hdRange : LinearMap.range d = ⊤ := by
      have h := congrArg Subrepresentation.toSubmodule hS
      change LinearMap.range d = ⊤ at h
      exact h
    have hzero : ∀ (y : Additive (lowerCentralLayer H 1))
        (x : Additive (lowerCentralLayer H 0)), gamma y x = 0 := by
      intro y x
      have hx : x ∈ LinearMap.range d := by
        rw [hdRange]
        exact Submodule.mem_top
      obtain ⟨w, rfl⟩ := hx
      have heq :=
        lowerCentralDegreeThreeCommutatorBilinear_equivariant_representation
          phi c y w
      change rho₂ c (gamma y w) =
        gamma (rho₁ c y) (rho₀ c w) at heq
      rw [hsecond, hthird] at heq
      simp only [Module.End.one_apply] at heq
      change gamma y (w - rho₀ c w) = 0
      rw [map_sub, heq, sub_self]
    have hspan := lowerCentralDegreeThreeCommutatorBilinear_span_eq_top H
    change Submodule.span (ZMod 2)
        (Set.range fun z :
          Additive (lowerCentralLayer H 1) ×
            Additive (lowerCentralLayer H 0) => gamma z.1 z.2) = ⊤ at hspan
    have hle : Submodule.span (ZMod 2)
        (Set.range fun z :
          Additive (lowerCentralLayer H 1) ×
            Additive (lowerCentralLayer H 0) => gamma z.1 z.2) ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨y, x⟩, rfl⟩
      change gamma y x ∈
        (⊥ : Submodule (ZMod 2) (Additive (lowerCentralLayer H 2)))
      rw [hzero]
      exact Submodule.zero_mem _
    have htopbot :
        (⊤ : Submodule (ZMod 2) (Additive (lowerCentralLayer H 2))) = ⊥ :=
      le_bot_iff.mp (hspan ▸ hle)
    exact (bot_ne_top htopbot.symm).elim

/-- **Higman Lemma 6, first paragraph (p. 85), kernel form.**

The common kernel of the actions on `L₂` and `L₃` is contained in the
kernel of the action on `L₁`. -/
theorem lowerCentralLayerRepresentation_ker_inf_le_ker_zero
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 2))] :
    (lowerCentralLayerRepresentation phi 1).ker ⊓
        (lowerCentralLayerRepresentation phi 2).ker ≤
      (lowerCentralLayerRepresentation phi 0).ker := by
  intro c hc
  exact lowerCentralLayerZero_action_eq_one_of_second_third_action_eq_one
    phi hirr c hc.1 hc.2

/-- Under an equivariant isomorphism `L₂ ≃ L₃`, faithfulness on `L₁`
forces faithfulness on `L₂`.  This is the kernel consequence used immediately
after the first paragraph of Higman's Lemma 6. -/
theorem lowerCentralLayerOneRepresentation_injective_of_equivariant_linearEquiv
    {H : Type uH} {C : Type uC} [Group H] [CommGroup C]
    (phi : C →* MulAut H)
    (hirr : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    [Nontrivial (Additive (lowerCentralLayer H 1))]
    (e : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2]
      Additive (lowerCentralLayer H 2))
    (hequiv : ∀ c v,
      e (lowerCentralLayerRepresentation phi 1 c v) =
        lowerCentralLayerRepresentation phi 2 c (e v)) :
    Function.Injective (lowerCentralLayerRepresentation phi 1) := by
  let rho₀ := lowerCentralLayerRepresentation phi 0
  let rho₁ := lowerCentralLayerRepresentation phi 1
  let rho₂ := lowerCentralLayerRepresentation phi 2
  change Representation.IsIrreducible rho₀ at hirr
  change Function.Injective rho₀ at hfaith
  change ∀ c v, e (rho₁ c v) = rho₂ c (e v) at hequiv
  change Function.Injective rho₁
  letI : Nontrivial (Additive (lowerCentralLayer H 2)) :=
    e.symm.toEquiv.nontrivial
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro c hc
  change rho₁ c = 1 at hc
  have hc₂ : rho₂ c = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    have h := hequiv c v
    rw [hc] at h
    simpa only [Module.End.one_apply] using h.symm
  have hc₀ : rho₀ c = 1 :=
    lowerCentralLayerZero_action_eq_one_of_second_third_action_eq_one
      phi hirr c hc hc₂
  apply hfaith
  simpa only [map_one] using hc₀

end OddOrder.Higman.Suzuki2Groups
