/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions
import OddOrder.Mathlib.SchurZassenhausConj
import OddOrder.Mathlib.SemidirectProduct

/-!
# Ch.4 → Ch.3 forward dependencies (coprime action machinery)

このファイルは **Isaacs FGT Ch.3 §3E (Coprime action)** の定理群を実装する.
owner chapter は本来 Ch.4 (`[G,A]` 構造 + coprime action machinery) だが,
**Tier 1 の結果 (Lem 3.24 Glauberman 経由)** は Ch.4 §4C-§4D を待たずに
Schur-Zassenhaus + Sylow + Frattini のみで実装可能 (2026-05-23 audit).

## 主要結果 (実装順)

| Isaacs # | Lean | 状態 |
|---|---|---|
| Lem 3.24(a) Glauberman | `glauberman_fixed_point_exists` | 進行中 |
| Lem 3.24(b) Glauberman | `glauberman_fixed_points_conj` | 予定 |
| Thm 3.23(a) A-inv Sylow | `exists_aInvariant_sylow` | 予定 |
| Thm 3.23(b) A-inv Sylow conj | `aInvariant_sylow_conj` | 予定 |
| Cor 3.25 A-inv p-subgroup | `aInvariant_pSubgroup_le_aInvariant_sylow` | 予定 |
| Thm 3.27 A-inv coset | `aInvariant_coset_mem_centralizer` | 予定 |
| Cor 3.28 商の固定点 | `coprime_fixedPoints_quotient` | 予定 |
| Cor 3.29 A trivial on G/Φ | `aFixed_quotient_frattini` | 予定 |
| Cor 3.30 A faithful on G/Φ | `aFaithful_quotient_frattini` | 予定 |

## namespace 設計

書籍上は Ch.3 の定理だが, Lean 上は物理的に Ch.4 dir にいるため
`OddOrder.Isaacs.Ch04` namespace を使う. docstring に book 番号を明示.

## 関連ノート

- [`notes/isaacs/ch03_split.md`](../../../notes/isaacs/ch03_split.md) §3E セクション.
- [`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md).
-/

namespace OddOrder.Isaacs.Ch04

open scoped Pointwise
open OddOrder.Isaacs.Ch03 (IsAInvariant)
open Subgroup

variable {G : Type*} [Group G]

/-! ## §3E.0 基盤: `IsCompatibleMulAction` + SDP 作用

Glauberman lemma (3.24) は `Γ = G ⋊ A` の `Ω` への自然な作用を経由する.
このための **compatible action** を抽象化する.
-/

section CompatibleAction

variable {A : Type*} [Group A] (φ : A →* MulAut G) (Ω : Type*)

/-- **Compatible action**: `A` が `G` に自己同型で作用 (`φ`), `A` と `G` が共通の
集合 `Ω` に作用しているとき, `a • (g • ω) = (φ a g) • (a • ω)` (`g` の `a` による
twist と作用が可換) を満たす条件. これは `G ⋊[φ] A` が `Ω` に自然に作用する
ための同値条件. -/
def IsCompatibleMulAction [MulAction G Ω] [MulAction A Ω] : Prop :=
  ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (φ a g) • (a • ω)

variable {φ Ω}

/-- Compatible action から `SemidirectProduct G A φ →* Equiv.Perm Ω` を構成.
`SemidirectProduct.lift` を `(MulAction.toPermHom G Ω, MulAction.toPermHom A Ω)`
で呼ぶ. -/
noncomputable def IsCompatibleMulAction.toPermHom
    [MulAction G Ω] [MulAction A Ω] (h : IsCompatibleMulAction φ Ω) :
    SemidirectProduct G A φ →* Equiv.Perm Ω :=
  SemidirectProduct.lift (MulAction.toPermHom G Ω) (MulAction.toPermHom A Ω) (fun a => by
    ext g ω
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAut.conj_apply,
      Equiv.Perm.mul_apply]
    -- Goal: (φ a g) • ω = a • g • (a⁻¹ • ω) (RHS uses MulAut.conj which inverts).
    -- Use compatibility: a • (g • α) = (φ a g) • (a • α) with α = a⁻¹ • ω.
    have heq := h a g (a⁻¹ • ω)
    rw [smul_smul, mul_inv_cancel, one_smul] at heq
    exact heq.symm)

/-- Compatible action から `MulAction (G ⋊[φ] A) Ω` を構成 (非 instance).
`Equiv.Perm Ω` の自明作用と `compHom` の合成. -/
noncomputable def IsCompatibleMulAction.toMulAction
    [MulAction G Ω] [MulAction A Ω] (h : IsCompatibleMulAction φ Ω) :
    MulAction (SemidirectProduct G A φ) Ω :=
  MulAction.compHom Ω h.toPermHom

@[simp] lemma IsCompatibleMulAction.toMulAction_inl_smul
    [MulAction G Ω] [MulAction A Ω] (h : IsCompatibleMulAction φ Ω) (g : G) (ω : Ω) :
    letI := h.toMulAction
    (SemidirectProduct.inl g : SemidirectProduct G A φ) • ω = g • ω := by
  letI := h.toMulAction
  show h.toPermHom (SemidirectProduct.inl g) ω = g • ω
  simp [IsCompatibleMulAction.toPermHom, SemidirectProduct.lift_inl]

@[simp] lemma IsCompatibleMulAction.toMulAction_inr_smul
    [MulAction G Ω] [MulAction A Ω] (h : IsCompatibleMulAction φ Ω) (a : A) (ω : Ω) :
    letI := h.toMulAction
    (SemidirectProduct.inr a : SemidirectProduct G A φ) • ω = a • ω := by
  letI := h.toMulAction
  show h.toPermHom (SemidirectProduct.inr a) ω = a • ω
  simp [IsCompatibleMulAction.toPermHom, SemidirectProduct.lift_inr]

end CompatibleAction

/-! ## §3E.1 Lemma 3.24 Glauberman fixed-point lemma -/

section Glauberman

variable {A : Type*} [Group A] [Finite A] [Finite G]

/-! ### Glauberman の補助補題群 -/

/-- `IsSolvable G ⇒ IsSolvable inl.range` (inl の rangeRestrict 経由). -/
private lemma isSolvable_inlRange_of_isSolvable {φ : A →* MulAut G} [IsSolvable G] :
    IsSolvable (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range :=
  solvable_of_surjective (MonoidHom.rangeRestrict_surjective
    (SemidirectProduct.inl : G →* SemidirectProduct G A φ))

/-- `IsSolvable A ⇒ IsSolvable (Γ ⧸ inl.range)`.
`rightHom` の核が `inl.range` で `rightHom` は全射, 第一同型定理 + 同型による IsSolvable
の移送. -/
private lemma isSolvable_quotient_inlRange_of_isSolvable
    {φ : A →* MulAut G} [IsSolvable A] :
    IsSolvable (SemidirectProduct G A φ ⧸
      (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range) := by
  -- Compose two isos: Γ⧸inl.range ≃ Γ⧸rightHom.ker ≃ A.
  have h_ker_eq : (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range =
      (SemidirectProduct.rightHom : SemidirectProduct G A φ →* A).ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  have h_iso1 : SemidirectProduct G A φ ⧸
      (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range ≃*
      SemidirectProduct G A φ ⧸
      (SemidirectProduct.rightHom : SemidirectProduct G A φ →* A).ker :=
    QuotientGroup.quotientMulEquivOfEq h_ker_eq
  have h_iso2 :
      SemidirectProduct G A φ ⧸
        (SemidirectProduct.rightHom : SemidirectProduct G A φ →* A).ker ≃* A :=
    QuotientGroup.quotientKerEquivOfSurjective _ SemidirectProduct.rightHom_surjective
  let h_iso : A ≃* SemidirectProduct G A φ ⧸
      (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range :=
    (h_iso1.trans h_iso2).symm
  exact solvable_of_surjective (f := h_iso.toMonoidHom) h_iso.surjective

/-- `inl.range` の `Γ = G ⋊ A` における index は `Nat.card A`. -/
private lemma inlRange_index_eq_card_A {φ : A →* MulAut G} :
    (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range.index = Nat.card A := by
  have h_card_Gamma : Nat.card (SemidirectProduct G A φ) = Nat.card G * Nat.card A :=
    SemidirectProduct.card
  have h_card_inlG : Nat.card
      (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range = Nat.card G :=
    Nat.card_range_of_injective SemidirectProduct.inl_injective
  have key := Subgroup.card_mul_index
    (H := (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range)
  rw [h_card_inlG, h_card_Gamma] at key
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos key

/-- **Isaacs Lemma 3.24(a) Glauberman fixed-point lemma**:
Let `A` act via automorphisms on `G`, where `A`, `G` are finite groups with `(|A|, |G|) = 1`,
and at least one of `A` or `G` is solvable.
Suppose `A` and `G` both act on a nonempty set `Ω`, where `G` acts transitively, and the
compatibility condition `a • (g • ω) = (φ a g) • (a • ω)` holds.
Then there exists an `A`-invariant element `α ∈ Ω`.

**証明** (Isaacs p.98): `Γ := G ⋊[φ] A`, choose `α ∈ Ω`, `U := stabilizer Γ α`.
`UG = Γ` (since `G` transitive). `U ∩ G ⊴ U`, `|U:U∩G| = |Γ:G| = |A|` coprime to `|U∩G|`.
Schur-Zassenhaus existence in `U` gives complement `H` of `U ∩ G` in `U`. `H` is also
complement of `G` in `Γ`. `inr(A)` is too. SZ conjugacy: `H = (inr A)^x` for `x ∈ inl(G)`.
Then `x⁻¹ • α` is `A`-invariant. -/
theorem glauberman_fixed_point_exists
    {φ : A →* MulAut G} (_hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (_hSolv : IsSolvable A ∨ IsSolvable G)
    {Ω : Type*} [MulAction G Ω] [MulAction A Ω] [Nonempty Ω]
    (_h : IsCompatibleMulAction φ Ω) (_hG_trans : MulAction.IsPretransitive G Ω) :
    ∃ α : Ω, ∀ a : A, a • α = α := by
  sorry  -- TODO: SDP + SZ existence + conjugacy.

end Glauberman

end OddOrder.Isaacs.Ch04
