/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialKeystone
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialThm25

/-!
# BG Theorem 2.5 at the group level (divisibility part)

`OddOrder.GroupTheory.RepresentationTheory` shared module: wires the BG (2.11) keystone
(`finrank_cyclicEndConjEigenspaceFin_succ`) and the Prop 2.4 counting
(`sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace`) into the **group-level** divisibility
conclusion of Bender–Glauberman Theorem 2.5: for a class-`≤ 2` `p`-group `P ⊴ G` with a faithful
irreducible representation and an element `x` of order `h` acting fixed-point-freely on `P/Z(P)`,
`h ∣ (dim V) ± 1`.

This file supplies the group-theoretic *setup wiring* (the conjugation automorphism `φ` of `P`
induced by `x`, the intertwiner `T = ρ x`, the intertwining relation, `φ^h = 1`, and the eigenspace
decomposition `hV`).  Two inputs are taken as hypotheses, to be discharged separately:

* `hVP : Representation.IsIrreducible (ρ.comp P.subtype)` — **BG Prop 2.2(a)** (`V_P` irreducible,
  the alg-closed Clifford step), still to be formalised;
* `hcent` — **BG Prop 1.5** (`C_{P/Z}(xᵏ) = 1`, i.e. `x` is fixed-point-free on `P/Z`), from the
  hypothesis `C_P(xᵏ) = Z(P)` via coprime action.
-/

namespace OddOrder.RepresentationTheory

open Representation Module EigenspaceUnderCyclicAction

variable {G : Type*} [Group G]

/-- The automorphism of a normal subgroup `P` induced by conjugation by `x ∈ G`. -/
noncomputable def conjAutOfNormal (P : Subgroup G) [P.Normal] (x : G) : P ≃* P :=
  (MulEquiv.subgroupMap (MulAut.conj x) P).trans
    (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self x P))

@[simp]
theorem conjAutOfNormal_apply_coe (P : Subgroup G) [P.Normal] (x : G) (p : P) :
    (conjAutOfNormal P x p : G) = x * (p : G) * x⁻¹ := rfl

/-- Iterating: `(φ^k p : G) = x^k · p · x^{-k}`. -/
theorem conjAutOfNormal_pow_apply_coe (P : Subgroup G) [P.Normal] (x : G) (k : ℕ) (p : P) :
    (((conjAutOfNormal P x) ^ k) p : G) = x ^ k * (p : G) * (x ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, conjAutOfNormal_apply_coe, ih]
    group

/-- If `x^h = 1` then `φ^h = 1`. -/
theorem conjAutOfNormal_pow_eq_one (P : Subgroup G) [P.Normal] {x : G} {h : ℕ} (hx : x ^ h = 1) :
    (conjAutOfNormal P x) ^ h = 1 := by
  ext p
  rw [conjAutOfNormal_pow_apply_coe, hx]
  simp

/-- **BG Theorem 2.5, divisibility part (group level).** Let `P ⊴ G` be a finite group of
nilpotency class `≤ 2` (`commutator P ≤ Z(P)`) with a faithful representation `ρ` over an
algebraically closed field (`char ∤ |P|`), `x ∈ G` of order `h ≥ 2` with `char ∤ h`, `ε` a
primitive `h`-th root of unity.  If the restriction `V_P` is irreducible (BG Prop 2.2(a)) and `x`
acts fixed-point-freely on `P/Z(P)` (`hcent`, BG Prop 1.5), then `dim V ≡ ±1 (mod h)`. -/
theorem finrank_modEq_of_faithful_irreducible
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite G]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1) (hh2 : 2 ≤ h)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hVP : Representation.IsIrreducible (ρ.comp P.subtype))
    (hcent : ∀ k : ZMod h, k ≠ 0 → ∀ c : P ⧸ Subgroup.center P,
        ((quotientCenterCongr (conjAutOfNormal P x) ^ k.val) c) = c → c = 1) :
    ∃ (v₀ δ : ℤ), (δ = 1 ∨ δ = -1) ∧ (Module.finrank F V : ℤ) = (h : ℤ) * v₀ + δ := by
  classical
  set ρP : Representation F P V := ρ.comp P.subtype with hρP
  haveI : Representation.IsIrreducible ρP := hVP
  set φ : P ≃* P := conjAutOfNormal P x with hφ
  set T : LinearMap.GeneralLinearGroup F V := ρ.asGroupHom x with hT
  -- `↑T = ρ x`
  have hTcoe : (T : Module.End F V) = ρ x := by rw [hT]; exact MonoidHom.coe_toHomUnits ρ x
  -- restriction is faithful
  have hfP : Function.Injective ρP := fun a b hab => Subtype.ext (hf hab)
  -- intertwining relation
  have hint : ∀ p : P, (T : Module.End F V) * ρP p = ρP (φ p) * (T : Module.End F V) := by
    intro p
    rw [hTcoe]
    change ρ x * ρ (p : G) = ρ ((φ p : P) : G) * ρ x
    rw [conjAutOfNormal_apply_coe, ← map_mul, ← map_mul]
    congr 1
    group
  -- `φ^h = 1`, `T^h = 1`
  have hφh : φ ^ h = 1 := conjAutOfNormal_pow_eq_one P hxh
  have hTEnd_h : (T : Module.End F V) ^ h = 1 := by
    rw [hTcoe, ← map_pow, hxh, map_one]
  -- eigenspace decomposition of `V` under `T`
  have hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily ε (T : Module.End F V) h) :=
    cyclicEigenspaceFin_isInternal_of_pow_eq_one hprim hTEnd_h
  -- the keystone supplies `hEdim`
  have hEdim := finrank_cyclicEndConjEigenspaceFin_succ ρP hfP hcl φ T hint hφh hprim hh hcent
  -- the Prop 2.4 counting gives `∑ dim Vᵢ ≡ ±1`
  obtain ⟨v₀, δ, hδ, hsum⟩ :=
    sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace hprim hV hh2 hEdim
  -- `∑ dim Vᵢ = dim V`
  have hsumV : ∑ i : Fin h, cyclicEigenspaceFinDim ε (T : Module.End F V) i
      = Module.finrank F V := by
    rw [← (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily ε (T : Module.End F V) h)) hV).finrank_eq,
      Module.finrank_directSum]
  refine ⟨v₀, δ, hδ, ?_⟩
  rw [← hsum, ← Nat.cast_sum, hsumV]

end OddOrder.RepresentationTheory
