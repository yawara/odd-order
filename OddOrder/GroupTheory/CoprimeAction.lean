/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SemidirectProduct
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.Mathlib.SchurZassenhausConj

/-!
# Coprime Actions and Glauberman's Lemma (setup)

`OddOrder.GroupTheory.CoprimeAction`: 互素作用 (coprime action) 関連の基本道具.

## Main definitions

* `OddOrder.GroupTheory.IsCompatibleAction φ`: A, G の Ω への作用が `φ : A →* MulAut G`
  と整合するという述語. `a • (g • ω) = (φ a g) • (a • ω)` の形.
* `OddOrder.GroupTheory.gammaMulAction`: compatibility が成り立つ時, 半直積 `G ⋊[φ] A`
  の Ω への作用. `(g, a) • ω := g • (a • ω)`.
* `OddOrder.GroupTheory.CoprimeFrobeniusAction`: the carrier for Wielandt's
  fixed-point formula used in Peterfalvi (9.1).

## Main results (future)

* `OddOrder.GroupTheory.glaubermanFixedPoint`: **Isaacs Lemma 3.24(a) — Glauberman's Lemma**.
  互素作用 + G transitive + compatibility + (A or G) solvable ⇒ A-fixed 点存在.
  実装は別 commit で. 本 commit は setup のみ.

## 構造

Isaacs PDF p.98 (mmd L1880-1906) の Γ = G ⋊ A 構成を Lean 4 で実装. 主な依存:
mathlib `SemidirectProduct` + `MulAction.stabilizer` + SZ existence + SZ conjugacy
(`OddOrder.Mathlib.SchurZassenhausConj` axiom).
-/

namespace OddOrder.GroupTheory

section CompatibleAction

variable {A G Ω : Type*} [Group A] [Group G]
variable [MulAction G Ω] [MulAction A Ω]

/-- **Compatibility** between A and G actions on Ω via `φ : A → Aut(G)`:
`a • (g • ω) = (φ a g) • (a • ω)` for all `a ∈ A, g ∈ G, ω ∈ Ω`.

Isaacs PDF p.97 の (★) 条件 (right-action 表記での `(α·g)·a = (α·a)·g^a` の left-action 翻訳). -/
def IsCompatibleAction (φ : A →* MulAut G) : Prop :=
  ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (φ a g) • (a • ω)

end CompatibleAction

section GammaAction

variable {A G Ω : Type*} [Group A] [Group G]
variable [MulAction G Ω] [MulAction A Ω]
variable {φ : A →* MulAut G}

/-- The action of the semidirect product `G ⋊[φ] A` on `Ω`, built from compatible
G- and A-actions. `(g, a) • ω := g • (a • ω)`.

これは `def` であって `instance` ではない (compatibility は `Prop` で typeclass で
推論不能). 使用側は `letI := gammaMulAction hCompat` で局所 instance 化. -/
@[reducible] def gammaMulAction (hCompat : @IsCompatibleAction A G Ω _ _ _ _ φ) :
    MulAction (G ⋊[φ] A) Ω where
  smul x ω := x.left • (x.right • ω)
  one_smul ω := by
    change (1 : G ⋊[φ] A).left • ((1 : G ⋊[φ] A).right • ω) = ω
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, one_smul, one_smul]
  mul_smul x y ω := by
    rcases x with ⟨gx, ax⟩
    rcases y with ⟨gy, ay⟩
    change (gx * φ ax gy) • ((ax * ay) • ω) = gx • (ax • (gy • (ay • ω)))
    rw [mul_smul (gx) (φ ax gy), mul_smul ax ay, ← hCompat ax gy (ay • ω)]

variable (hCompat : @IsCompatibleAction A G Ω _ _ _ _ φ)

/-- `inl g ∈ G ⋊[φ] A` acts on `Ω` as `g` does (via the original G-action). -/
theorem gammaMulAction_inl_smul (g : G) (ω : Ω) :
    (gammaMulAction hCompat).toSMul.smul (SemidirectProduct.inl g) ω = g • ω := by
  change (SemidirectProduct.inl g : G ⋊[φ] A).left • ((SemidirectProduct.inl g).right • ω) = g • ω
  rw [SemidirectProduct.left_inl, SemidirectProduct.right_inl, one_smul]

/-- `inr a ∈ G ⋊[φ] A` acts on `Ω` as `a` does (via the original A-action). -/
theorem gammaMulAction_inr_smul (a : A) (ω : Ω) :
    (gammaMulAction hCompat).toSMul.smul (SemidirectProduct.inr a) ω = a • ω := by
  change (SemidirectProduct.inr a : G ⋊[φ] A).left • ((SemidirectProduct.inr a).right • ω) = a • ω
  rw [SemidirectProduct.left_inr, SemidirectProduct.right_inr, one_smul]
end GammaAction

section WielandtFixedPoint

/-- A carrier for **Peterfalvi (9.1)**: a coprime action of a Frobenius group
`U E` on a finite solvable group `H`.

The subgroups `fixedByUE`, `fixedByE`, and `fixedByU` are the three fixed-point
subgroups appearing in Wielandt's formula.  They are stored explicitly because
the action itself will later be supplied by the semidirect-product construction
attached to `H/H_0`. -/
structure CoprimeFrobeniusAction (L H : Type*) [Group L] [Group H] where
  U : Subgroup L
  E : Subgroup L
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup L U E
  H_solvable : IsSolvable H
  coprime_order : Nat.Coprime (Nat.card H) (Nat.card L)
  fixedByUE : Subgroup H
  fixedByE : Subgroup H
  fixedByU : Subgroup H

/-- **Peterfalvi (9.1)**: Wielandt's fixed-point formula for a coprime
Frobenius action. -/
theorem wielandt_fixedPoint_frobenius {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H) :
    Nat.card ↥act.fixedByUE ^ Nat.card ↥act.E * Nat.card H =
      Nat.card ↥act.fixedByE ^ Nat.card ↥act.E * Nat.card ↥act.fixedByU := by
  sorry

/-- **Peterfalvi (9.1), first corollary**: if the `E`-fixed subgroup is trivial,
then the Frobenius kernel centralizes the acted-on group. -/
theorem wielandt_fixedPoint_trivial_E_fixed {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hE : act.fixedByE = ⊥) :
    act.fixedByU = ⊤ := by
  sorry

/-- **Peterfalvi (9.1), second corollary**: if the `U`-fixed subgroup is
trivial, then `|H| = |C_H(E)|^|E|`. -/
theorem wielandt_fixedPoint_trivial_U_fixed {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hU : act.fixedByU = ⊥) :
    Nat.card H = Nat.card ↥act.fixedByE ^ Nat.card ↥act.E := by
  sorry

end WielandtFixedPoint


end OddOrder.GroupTheory
