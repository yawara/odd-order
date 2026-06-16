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

variable {L H : Type*} [Group L] [Group H]

/-- The subgroup `C_H(K)` of points of `H` fixed by every element of a subgroup `K ≤ L`,
under an action `φ : L →* MulAut H`.  This is a subgroup of `H` because each `φ l` is a
group automorphism. -/
def fixedSubgroup (φ : L →* MulAut H) (K : Subgroup L) : Subgroup H where
  carrier := {h | ∀ l ∈ K, φ l h = h}
  one_mem' l _ := map_one (φ l)
  mul_mem' ha hb l hl := by rw [map_mul, ha l hl, hb l hl]
  inv_mem' ha l hl := by rw [map_inv, ha l hl]

@[simp] theorem mem_fixedSubgroup {φ : L →* MulAut H} {K : Subgroup L} {x : H} :
    x ∈ fixedSubgroup φ K ↔ ∀ l ∈ K, φ l x = x := Iff.rfl

/-- Fixing the elements of a *larger* subgroup yields a *smaller* fixed subgroup. -/
theorem fixedSubgroup_antitone (φ : L →* MulAut H) {K K' : Subgroup L} (h : K ≤ K') :
    fixedSubgroup φ K' ≤ fixedSubgroup φ K :=
  fun _ hx l hl => hx l (h hl)

/-- A carrier for **Peterfalvi (9.1)**: a coprime action `φ` of a Frobenius group
`L = U ⋊ E` (kernel `U`, complement `E`) on a finite solvable group `H`.

The three fixed-point subgroups `C_H(UE)`, `C_H(E)`, `C_H(U)` of Wielandt's formula are
*derived* from the action (see `fixedByUE`, `fixedByE`, `fixedByU`), not stored, so the
formula below is a genuine statement about the action. -/
structure CoprimeFrobeniusAction (L H : Type*) [Group L] [Group H] where
  U : Subgroup L
  E : Subgroup L
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup L U E
  H_solvable : IsSolvable H
  /-- The action of the Frobenius group `L = U ⋊ E` on `H` by automorphisms. -/
  φ : L →* MulAut H
  coprime_order : Nat.Coprime (Nat.card H) (Nat.card L)

namespace CoprimeFrobeniusAction

/-- `C_H(UE) = C_H(L)`: the points of `H` fixed by the whole Frobenius group `L = UE`. -/
def fixedByUE (act : CoprimeFrobeniusAction L H) : Subgroup H := fixedSubgroup act.φ ⊤
/-- `C_H(E)`: the points of `H` fixed by the Frobenius complement `E`. -/
def fixedByE (act : CoprimeFrobeniusAction L H) : Subgroup H := fixedSubgroup act.φ act.E
/-- `C_H(U)`: the points of `H` fixed by the Frobenius kernel `U`. -/
def fixedByU (act : CoprimeFrobeniusAction L H) : Subgroup H := fixedSubgroup act.φ act.U

theorem fixedByUE_le_fixedByE (act : CoprimeFrobeniusAction L H) :
    act.fixedByUE ≤ act.fixedByE := fixedSubgroup_antitone act.φ le_top
theorem fixedByUE_le_fixedByU (act : CoprimeFrobeniusAction L H) :
    act.fixedByUE ≤ act.fixedByU := fixedSubgroup_antitone act.φ le_top

end CoprimeFrobeniusAction

/-- **Peterfalvi (9.1)**: Wielandt's fixed-point formula for a coprime Frobenius action.
For `L = U ⋊ E` Frobenius with kernel `U` acting on a finite solvable `H` of order prime
to `|L|`,
`|C_H(UE)|^{|E|} · |H| = |C_H(E)|^{|E|} · |C_H(U)|`.

The proof rests on **Wielandt's fixed-point theorem** ([HB], Ch. XI, Thm 12.4): the
group-ring identity `U·E + |U|·1 = ∑_{u∈U} E^u + U` in `ℤ[L]` transforms, via the
solvability of `H` and the coprimality, into the multiplicative fixed-point identity
`|C_H(UE)|^{|L|} · |H|^{|U|} = (∏_{u∈U} |C_H(E^u)|^{|E|}) · |C_H(U)|^{|U|}`, whence the
claim by taking `|U|`-th roots.  Wielandt's theorem is not yet available in mathlib: its
core reduces to a characteristic-0 / Brauer-character trace argument on the
elementary-abelian chief factors of the solvable group `H`. -/
theorem wielandt_fixedPoint_frobenius {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H) :
    Nat.card ↥act.fixedByUE ^ Nat.card ↥act.E * Nat.card H =
      Nat.card ↥act.fixedByE ^ Nat.card ↥act.E * Nat.card ↥act.fixedByU := by
  sorry

/-- **Peterfalvi (9.1), first corollary**: if `C_H(E) = 1` then the Frobenius kernel `U`
centralizes `H`, i.e. `C_H(U) = H`. -/
theorem wielandt_fixedPoint_trivial_E_fixed {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hE : act.fixedByE = ⊥) :
    act.fixedByU = ⊤ := by
  have key := wielandt_fixedPoint_frobenius act
  have hUE : act.fixedByUE = ⊥ := le_bot_iff.mp (hE ▸ act.fixedByUE_le_fixedByE)
  simp only [hUE, hE, Subgroup.card_bot, one_pow, one_mul] at key
  exact Subgroup.eq_top_of_card_eq _ key.symm

/-- **Peterfalvi (9.1), second corollary**: if `C_H(U) = 1` then `|H| = |C_H(E)|^{|E|}`. -/
theorem wielandt_fixedPoint_trivial_U_fixed {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hU : act.fixedByU = ⊥) :
    Nat.card H = Nat.card ↥act.fixedByE ^ Nat.card ↥act.E := by
  have key := wielandt_fixedPoint_frobenius act
  have hUE : act.fixedByUE = ⊥ := le_bot_iff.mp (hU ▸ act.fixedByUE_le_fixedByU)
  simp only [hUE, hU, Subgroup.card_bot, one_pow, one_mul, mul_one] at key
  exact key

end WielandtFixedPoint


end OddOrder.GroupTheory
