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

/-! The group-level Wielandt formula `wielandt_fixedPoint_frobenius` and its corollaries are proved
from the chief-series assembly in `OddOrder.GroupTheory.WielandtFixedPoint` (downstream of this
file, which holds only the shared carrier and fixed-point subgroups). -/

end WielandtFixedPoint

section FrobeniusCentralizer

open OddOrder.Isaacs

variable {L : Type*} [Group L] [Finite L] {N A : Subgroup L}

/-- **A non-kernel element centralizes nothing nontrivial in the Frobenius kernel.**  In a finite
Frobenius group with kernel `N`, if `g ∉ N` then `C_L(g) ⊓ N = 1`: any `x ∈ N` commuting with `g`
would put `g ∈ C_L(x) ≤ N` (`centralizer_kernel_le`).  Reusable; the engine of the fixed-point-free
action in Peterfalvi (9.1)/(13.17.b). -/
theorem IsFrobeniusGroup.centralizer_inf_kernel_eq_bot_of_not_mem
    (h : Ch06.IsFrobeniusGroup L N A) {g : L} (hg : g ∉ N) :
    Subgroup.centralizer ({g} : Set L) ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxc, hxN⟩ := Subgroup.mem_inf.mp hx
  by_contra hxne
  rw [Subgroup.mem_bot] at hxne
  refine hg (h.centralizer_kernel_le x hxN hxne ?_)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm

/-- **A subgroup meeting the Frobenius kernel trivially is coprime to it.**  In a finite Frobenius
group with kernel `N` and complement `A`, if `K ⊓ N = ⊥` then `|K| ⟂ |N|`: `K` injects into the
quotient `L / N`, so `|K| ∣ [L : N] = |A|`, which is prime to `|N|`
(`coprime_card_kernel_complement`).  Reusable; supplies the `coprime_order` of the (9.1) action. -/
theorem IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot
    (h : Ch06.IsFrobeniusGroup L N A) {K : Subgroup L} (hKN : K ⊓ N = ⊥) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥N) := by
  haveI := h.isNormal
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    exact Subtype.ext (Subgroup.disjoint_def.mp (disjoint_iff.mpr hKN) a.2 ha)
  have hdvd : Nat.card ↥K ∣ N.index := by
    rw [Subgroup.index_eq_card]; exact Subgroup.card_dvd_of_injective _ hinj
  rw [h.isComplement.symm.index_eq_card] at hdvd
  exact Nat.Coprime.coprime_dvd_left hdvd h.coprime_card_kernel_complement.symm

/-- The ambient-`G` form of `coprime_card_of_inf_kernel_eq_bot`: for a Frobenius group `Lsub ≤ G`
with kernel `N` (`N ≤ Lsub`), a subgroup `K ≤ Lsub` meeting `N` trivially is coprime to `N`. -/
theorem IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le {G : Type*} [Group G] [Finite G]
    {Lsub N K : Subgroup G} {A : Subgroup ↥Lsub} (hNL : N ≤ Lsub) (hKL : K ≤ Lsub)
    (h : Ch06.IsFrobeniusGroup ↥Lsub (N.subgroupOf Lsub) A) (hKN : K ⊓ N = ⊥) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥N) := by
  have hsub : (K.subgroupOf Lsub) ⊓ (N.subgroupOf Lsub) = ⊥ := by
    rw [show K.subgroupOf Lsub ⊓ N.subgroupOf Lsub = (K ⊓ N).subgroupOf Lsub from
      (Subgroup.comap_inf K N Lsub.subtype).symm, hKN, Subgroup.bot_subgroupOf]
  have hcop := IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot h hsub
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv] at hcop

/-! The fixed-point-free engine `isFrobenius_kernel_eq_bot_of_frobenius_subgroup` (Peterfalvi
(13.17.b)), which combines `centralizer_inf_kernel_eq_bot_of_not_mem` with Wielandt's formula
`coprimeFrobeniusAction_card_eq_one`, lives in `OddOrder.GroupTheory.WielandtFixedPoint`
(downstream, since it depends on the assembled Wielandt formula). -/

end FrobeniusCentralizer


end OddOrder.GroupTheory
