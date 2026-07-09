/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Order.OrderIsoNat
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.BG.Ch1_Preliminary.S02_Representations
import OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector
import OddOrder.GroupTheory.RepresentationTheory.CoprimeActionTrivial
import OddOrder.GroupTheory.ChiefFactor
import OddOrder.Isaacs.Ch02_Subnormality.Main

/-!
# AppA_PStabilityBasic

Prefix-split from `OddOrder.BG.AppA_PStability` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# BG Appendix A: p-Stability — Theorems A.1 and A.2

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Appendix A (pp. 135-138), mmd L4450-4513.

本ファイルは **A.1 と A.2 (+ A.2 の dim reduction lemma)** のみ.
A.3, A.4, A.5 は別ファイルで実装予定. 詳細 mini-roadmap:
[`notes/bg/appA_pstability.md`](../../notes/bg/appA_pstability.md).
issue: [`issues/0041-bg-appa-a2-dim-reduction.md`](../../issues/0041-bg-appa-a2-dim-reduction.md).

## Main results

* `OddOrder.BG.AppA.thmA1` — **BG Theorem A.1** (L4460-4464):
  V 2-dim faithful irreducible over F (char p), |G| odd ⇒ `p ∤ |G|`.
  Proof: BG Thm 2.6 (Sylow-p abelian + G' ≤ P) + commutator≤H → Normal +
  `PGroupFixedVector` で C_V(P) ≠ ⊥, G-invariant → 既約 → P 自明 → 矛盾.

* `OddOrder.BG.AppA.quadratic_two_generated_irreducible_finrank_eq_two` —
  **BG Thm A.2 の dim reduction part** (= Gorenstein Ch.3 §8 Thm 8.1 weakening,
  mmd L2204-L2240): V faithful irreducible alg-closed F (char p), G = ⟨x, y⟩
  with quadratic min poly p-elements ⇒ `dim V = 2`.

  **Step 4 精密化** (issue #0041): Jordan canonical form は不要、
  `T := (x₂-1)∘(x₁-1) : V₂ → V₂` の eigenvector 1 個で完結.
  (`Module.End.exists_eigenvalue` 利用)

* `OddOrder.BG.AppA.thmA2` — **BG Theorem A.2** (L4468-4472):
  上記 dim reduction + A.1 で `|G|` 偶を結論. Dickson 不要.

## Proof strategy (Gorenstein 8.1 / issue #0041 / notes/bg/appA_pstability.md)

A.1: BG Thm 2.6 (`odd_two_dim_sylow_abelian`) + `Subgroup.Normal.of_commutator_le`
+ `IsPGroup.invariants_ne_bot` (= `PGroupFixedVector`) + 既約 + 忠実 → 矛盾.

A.2 dim reduction (= Gorenstein 8.1 mmd L2210-L2240 翻訳):
- Step 1: `(ρ xᵢ - 1)² = 0` ⇒ `Wᵢ := range(ρ xᵢ - 1) ⊆ ker(ρ xᵢ - 1) =: Vᵢ`,
  rank-nullity で `dim V ≤ 2 dim Vᵢ`.
- Step 2: `dᵢ > d/2` 仮定 ⇒ `V₁ ∩ V₂ ≠ ⊥`, 両 `xᵢ` 自明 → `G = ⟨x,y⟩` 自明 →
  既約より `V = V₁ ∩ V₂` → 忠実 + `xᵢ ≠ 1` で矛盾. ∴ `d₁ = d₂ = d/2`,
  `V = V₁ ⊕ V₂`.
- Step 3: `(x₁-1)|_{V₂}: V₂ → V₁` iso, `(x₂-1)|_{V₁}: V₁ → V₂` iso.
- Step 4 (精密化): `T := (x₂-1)∘(x₁-1) : V₂ → V₂` iso, F alg-closed +
  V₂ nontrivial で `∃ v ∈ V₂\0, ∃ λ ≠ 0, T(v) = λv`.
- Step 5: `u₁ := v`, `u₂ := (x₁-1)(v) ∈ V₁`, `U := span {u₁, u₂}` が
  x₁, x₂ で不変 (直接計算 4 行) ⇒ G-不変 ⇒ 既約 + `u₁ ≠ 0` で `U = ⊤` ⇒
  `dim V = 2`.

A.2 closure: `dim V = 2` + A.1 + x (or y) が `p`-element で `≠ 1` ⇒
`p ∣ |G|`, A.1 と矛盾 ⇒ `|G|` 偶.
-/

namespace OddOrder.BG.AppA

open Representation Module Function LinearMap Submodule

universe uF uG uV

variable {p : ℕ} [Fact p.Prime]
variable {F : Type uF} [Field F] [CharP F p]
variable {V : Type uV} [AddCommGroup V] [Module F V] [Module.Finite F V]
variable {G : Type uG} [Group G]

/-! ## A.1: 2-dim faithful irreducible odd-order ⇒ p ∤ |G| -/

section ThmA1

/-- **BG Theorem A.1** (mmd L4460-4464): `V` 2-dim faithful irreducible over
`F` (char `p`), `|G|` odd ⇒ `p ∤ |G|`.

証明: BG Thm 2.6 で Sylow-`p` `P` が abelian かつ `G' ≤ P` を得, 後者から
`P ⊴ G` (`Subgroup.Normal.of_commutator_le`). `P` 正規 `p`-群なので
`PGroupFixedVector` の固定点 `C_V(P) ≠ ⊥` は `G`-不変. 既約で `C_V(P) = ⊤`,
すなわち `P` 全要素が `V` 上自明作用. 忠実より `P = ⊥`. しかし `p ∣ |G|`
なら `Sylow.ne_bot_of_dvd_card` で `P ≠ ⊥`, 矛盾. -/
theorem thmA1
    [Finite G] (hodd : Odd (Nat.card G))
    (hdim : Module.finrank F V = 2)
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hirr : ∀ U : Submodule F V,
      (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) :
    ¬ p ∣ Nat.card G := by
  intro hp_dvd
  -- 1. Get a Sylow p subgroup
  obtain ⟨P⟩ : Nonempty (Sylow p G) := Sylow.nonempty
  -- 2. BG Thm 2.6: P abelian + commutator G ≤ P
  obtain ⟨_hP_comm, hG'_le_P⟩ :=
    OddOrder.BG.Ch1.S02.odd_two_dim_sylow_abelian hodd hdim ρ hfaithful hp_dvd ‹CharP F p› P
  -- 3. P normal in G (commutator G ≤ P)
  haveI hP_normal : (P : Subgroup G).Normal := by
    apply Subgroup.Normal.of_commutator_le (H := (P : Subgroup G))
    exact hG'_le_P
  -- 4. P is a p-group
  have hP_pgroup : IsPGroup p (↥(P : Subgroup G)) := P.isPGroup'
  -- 5. V is nontrivial (dim = 2)
  haveI hV_nontriv : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := F) (M := V) (by rw [hdim]; norm_num)
  -- 6. ⊤ ≠ ⊥ in Submodule F V
  have hV_ne_bot : (⊤ : Submodule F V) ≠ ⊥ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have hv_top : v ∈ (⊤ : Submodule F V) := Submodule.mem_top
    rw [h] at hv_top
    exact (Submodule.mem_bot _).mp hv_top
  -- 7. ρ restricted to P is a representation of P
  let ρ_P : Representation F (↥(P : Subgroup G)) V := ρ.comp (P : Subgroup G).subtype
  -- 8. C_V(P) := ρ_P.invariants ≠ ⊥ (PGroupFixedVector)
  have hC_ne_bot : ρ_P.invariants ≠ ⊥ := hP_pgroup.invariants_ne_bot ρ_P hV_ne_bot
  -- 9. C_V(P) is G-invariant (since P is normal)
  have hC_inv : ∀ g : G, ∀ v ∈ ρ_P.invariants, ρ g v ∈ ρ_P.invariants := by
    intro g v hv
    rw [Representation.mem_invariants] at hv ⊢
    rintro ⟨q, hq⟩
    -- want ρ_P ⟨q, hq⟩ (ρ g v) = ρ g v, i.e., ρ q (ρ g v) = ρ g v
    change ρ q (ρ g v) = ρ g v
    have hconj : g⁻¹ * q * g ∈ (P : Subgroup G) := hP_normal.conj_mem' q hq g
    have h_fix : ρ (g⁻¹ * q * g) v = v := by
      have := hv ⟨g⁻¹ * q * g, hconj⟩
      simpa [ρ_P] using this
    calc ρ q (ρ g v)
        = (ρ q * ρ g) v := by rw [Module.End.mul_apply]
      _ = ρ (q * g) v := by rw [← map_mul]
      _ = ρ (g * (g⁻¹ * q * g)) v := by congr 1; group
      _ = (ρ g * ρ (g⁻¹ * q * g)) v := by rw [map_mul]
      _ = ρ g (ρ (g⁻¹ * q * g) v) := by rw [Module.End.mul_apply]
      _ = ρ g v := by rw [h_fix]
  -- 10. C_V(P) = ⊤ by irreducibility
  have hC_top : ρ_P.invariants = ⊤ :=
    (hirr ρ_P.invariants hC_inv).resolve_left hC_ne_bot
  -- 11. ρ q = 1 for all q ∈ P
  have h_triv : ∀ q ∈ (P : Subgroup G), ρ q = (1 : Module.End F V) := by
    intro q hq
    ext v
    have hv_inv : v ∈ ρ_P.invariants := by rw [hC_top]; exact Submodule.mem_top
    have hv_fix := (Representation.mem_invariants ρ_P v).mp hv_inv ⟨q, hq⟩
    -- hv_fix : ρ_P ⟨q, hq⟩ v = v; ρ_P ⟨q, hq⟩ = ρ q definitionally
    rw [Module.End.one_apply]
    simpa [ρ_P] using hv_fix
  -- 12. P = ⊥ (by faithful)
  have hP_bot : (P : Subgroup G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    apply hfaithful
    rw [h_triv q hq, map_one]
  -- 13. Contradiction: P ≠ ⊥ (Sylow + p ∣ |G|)
  exact P.ne_bot_of_dvd_card hp_dvd hP_bot

end ThmA1

/-! ## A.2 dim reduction: 二次既約 ⇒ dim V = 2 -/

section DimReduction

/-- **BG Thm A.2 の dim reduction lemma** (= Gorenstein Ch.3 §8 Thm 8.1
weakening, mmd L2204-L2240). `F` alg-closed char `p` 上, `V` finite-dim
nontrivial, `G = ⟨x, y⟩` 忠実既約作用, `x, y` が二次最小多項式の `p`-元
⇒ `dim V = 2`.

証明: 5 step (Gorenstein 8.1 翻訳, Step 4 を eigenvector 1 個に精密化).
詳細 [`notes/bg/appA_pstability.md`](../../notes/bg/appA_pstability.md)
「★ 2026-05-28 (late PM) 追補」, issue #0041. -/
theorem quadratic_two_generated_irreducible_finrank_eq_two
    [IsAlgClosed F] [Nontrivial V]
    (ρ : Representation F G V) (_hfaithful : Function.Injective ρ)
    (hirr : ∀ U : Submodule F V,
      (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (x y : G) (hgen : Subgroup.closure ({x, y} : Set G) = ⊤)
    (hx : ((ρ x : Module.End F V) - 1) ^ 2 = 0) (hxne : ρ x ≠ 1)
    (hy : ((ρ y : Module.End F V) - 1) ^ 2 = 0) (hyne : ρ y ≠ 1) :
    Module.finrank F V = 2 := by
  -- Setup: V_i = ker(ρ x_i - 1), W_i = range(ρ x_i - 1)
  set Tx : Module.End F V := (ρ x : Module.End F V) - 1 with hTx_def
  set Ty : Module.End F V := (ρ y : Module.End F V) - 1 with hTy_def
  set V_1 : Submodule F V := LinearMap.ker Tx with hV1_def
  set V_2 : Submodule F V := LinearMap.ker Ty with hV2_def
  set W_1 : Submodule F V := LinearMap.range Tx with hW1_def
  set W_2 : Submodule F V := LinearMap.range Ty with hW2_def
  -- Step 1: W_i ⊆ V_i (since (ρ x_i - 1)^2 = 0)
  have hW1_le_V1 : W_1 ≤ V_1 := by
    rw [hW1_def, hV1_def, LinearMap.range_le_ker_iff]
    -- Goal: Tx ∘ₗ Tx = 0, equivalently Tx * Tx = 0, equivalently Tx^2 = 0
    have : Tx * Tx = 0 := by
      have : Tx ^ 2 = 0 := hx
      simpa [pow_two] using this
    exact this
  have hW2_le_V2 : W_2 ≤ V_2 := by
    rw [hW2_def, hV2_def, LinearMap.range_le_ker_iff]
    have : Ty * Ty = 0 := by
      have : Ty ^ 2 = 0 := hy
      simpa [pow_two] using this
    exact this
  -- Step 1: rank-nullity ⇒ d = dim V ≤ 2 dim V_i
  have h_rn_x : Module.finrank F W_1 + Module.finrank F V_1 = Module.finrank F V :=
    LinearMap.finrank_range_add_finrank_ker Tx
  have h_rn_y : Module.finrank F W_2 + Module.finrank F V_2 = Module.finrank F V :=
    LinearMap.finrank_range_add_finrank_ker Ty
  have hd_le_2d1 : Module.finrank F V ≤ 2 * Module.finrank F V_1 := by
    have hW1_le := Submodule.finrank_mono hW1_le_V1
    omega
  have hd_le_2d2 : Module.finrank F V ≤ 2 * Module.finrank F V_2 := by
    have hW2_le := Submodule.finrank_mono hW2_le_V2
    omega
  -- Helpers: x acts trivially on V_1 = ker(ρx - 1), y on V_2 = ker(ρy - 1)
  have hx_triv_V1 : ∀ v ∈ V_1, ρ x v = v := by
    intro v hv
    have h : Tx v = 0 := hv
    have e : Tx v = ρ x v - v := by
      simp [hTx_def, LinearMap.sub_apply, Module.End.one_apply]
    rw [e] at h
    exact sub_eq_zero.mp h
  have hy_triv_V2 : ∀ v ∈ V_2, ρ y v = v := by
    intro v hv
    have h : Ty v = 0 := hv
    have e : Ty v = ρ y v - v := by
      simp [hTy_def, LinearMap.sub_apply, Module.End.one_apply]
    rw [e] at h
    exact sub_eq_zero.mp h
  -- Step 2: V_1 ∩ V_2 = ⊥
  -- (Otherwise both x, y act trivially on W := V_1 ∩ V_2 ⇒ G acts trivially on W
  -- ⇒ W = ⊤ by irreducibility ⇒ ρ x = 1, contradicts hxne)
  have hV12_inter_bot : V_1 ⊓ V_2 = ⊥ := by
    by_contra hne
    -- ∀ g ∈ G, ρ g v = v for v ∈ V_1 ⊓ V_2 (via closure_induction)
    have h_triv_all : ∀ g : G, ∀ v ∈ V_1 ⊓ V_2, ρ g v = v := by
      intro g v hv
      have hg_mem : g ∈ Subgroup.closure ({x, y} : Set G) := by rw [hgen]; trivial
      induction hg_mem using Subgroup.closure_induction with
      | mem h hh =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
        rcases hh with h_eq | h_eq
        · subst h_eq
          exact hx_triv_V1 v (Submodule.mem_inf.mp hv).1
        · subst h_eq
          exact hy_triv_V2 v (Submodule.mem_inf.mp hv).2
      | one => rw [map_one, Module.End.one_apply]
      | mul a b _ _ ihA ihB =>
        rw [map_mul, Module.End.mul_apply, ihB, ihA]
      | inv a _ ihA =>
        -- ρ a v = v ⇒ ρ a⁻¹ v = v via ρ (a⁻¹ * a) = ρ 1 = 1
        have : ρ a⁻¹ (ρ a v) = ρ a⁻¹ v := by rw [ihA]
        rw [← this, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
    -- W := V_1 ⊓ V_2 is G-invariant
    have hW_inv : ∀ g : G, ∀ v ∈ V_1 ⊓ V_2, ρ g v ∈ V_1 ⊓ V_2 := by
      intro g v hv
      rw [h_triv_all g v hv]; exact hv
    -- Apply hirr ⇒ W = ⊥ or ⊤; ≠ ⊥, so = ⊤
    rcases hirr (V_1 ⊓ V_2) hW_inv with h_bot | h_top
    · exact hne h_bot
    · -- W = ⊤ ⇒ every v ∈ V is in V_1 ⊓ V_2 ⊆ V_1 ⇒ ρ x = 1, contradicts hxne
      apply hxne
      ext v
      rw [Module.End.one_apply]
      have hv1 : v ∈ V_1 := by
        have : v ∈ V_1 ⊓ V_2 := by rw [h_top]; exact Submodule.mem_top
        exact (Submodule.mem_inf.mp this).1
      exact hx_triv_V1 v hv1
  -- Step 4 prep: V_2 ≠ ⊥ (else (ρ y - 1) injective ⇒ surjective ⇒ W_2 = ⊤,
  -- but W_2 ⊆ V_2 = ⊥, ⊥ ≠ ⊤ since V Nontrivial)
  have hV2_ne_bot : V_2 ≠ ⊥ := by
    intro h
    have hW2_le : W_2 ≤ ⊥ := hW2_le_V2.trans h.le
    have hW2_bot : W_2 = ⊥ := le_bot_iff.mp hW2_le
    have hTy_zero : Ty = 0 := LinearMap.range_eq_bot.mp hW2_bot
    apply hyne
    have : (ρ y : Module.End F V) - 1 = 0 := hTy_zero
    exact sub_eq_zero.mp this
  -- Step 4: T := (Ty * Tx) : V_2 → V_2 well-defined (well-typed restriction)
  have hT_maps : ∀ v ∈ V_2, ((Ty * Tx : Module.End F V)) v ∈ V_2 := by
    intro v _
    change Ty (Tx v) ∈ V_2
    exact hW2_le_V2 ⟨Tx v, rfl⟩
  haveI hV2_fd : FiniteDimensional F V_2 := inferInstance
  haveI hV2_nontriv : Nontrivial (V_2 : Submodule F V) :=
    Submodule.nontrivial_iff_ne_bot.mpr hV2_ne_bot
  let T : V_2 →ₗ[F] V_2 := (Ty * Tx : Module.End F V).restrict hT_maps
  -- T has eigenvalue μ
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v_sub, hv_sub_mem, hv_sub_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  -- T v_sub = μ • v_sub
  have hT_eq : T v_sub = μ • v_sub := by
    rwa [Module.End.mem_eigenspace_iff] at hv_sub_mem
  -- v := v_sub.val ∈ V is the eigenvector lifted to V; u_1 := v, u_2 := Tx v
  set v : V := v_sub.val with hv_def
  -- u_1 = v ≠ 0
  have hu_1_ne : v ≠ 0 := by
    intro h
    apply hv_sub_ne
    ext
    exact h
  -- u_2 := Tx v ∈ V_1 (since Tx v ∈ W_1 ⊆ V_1)
  have hu_2_V1 : Tx v ∈ V_1 := hW1_le_V1 ⟨v, rfl⟩
  -- T injectivity argument: T v_sub = 0 ⇒ Ty (Tx v) = 0 ⇒ Tx v ∈ V_1 ∩ V_2 = ⊥ ⇒ Tx v = 0
  have hT_inj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w_sub hw_ker
    have h_val_zero : (Ty * Tx : Module.End F V) w_sub.val = 0 := by
      have h := congr_arg Subtype.val (hw_ker : T w_sub = 0)
      simpa [T] using h
    have hTyTx : Ty (Tx w_sub.val) = 0 := by
      rw [Module.End.mul_apply] at h_val_zero; exact h_val_zero
    -- Tx w_sub.val ∈ V_2 (from Ty (Tx w_sub.val) = 0 = kernel of Ty)
    have hTxw_V2 : Tx w_sub.val ∈ V_2 := hTyTx
    have hTxw_V1 : Tx w_sub.val ∈ V_1 := hW1_le_V1 ⟨w_sub.val, rfl⟩
    have hTxw_zero : Tx w_sub.val = 0 := by
      have : Tx w_sub.val ∈ V_1 ⊓ V_2 := Submodule.mem_inf.mpr ⟨hTxw_V1, hTxw_V2⟩
      rw [hV12_inter_bot] at this
      exact (Submodule.mem_bot _).mp this
    -- w_sub.val ∈ V_1 (from Tx w_sub.val = 0)
    have hw_V1 : w_sub.val ∈ V_1 := hTxw_zero
    have : w_sub.val ∈ V_1 ⊓ V_2 := Submodule.mem_inf.mpr ⟨hw_V1, w_sub.prop⟩
    rw [hV12_inter_bot] at this
    exact Subtype.ext ((Submodule.mem_bot _).mp this)
  -- μ ≠ 0 (else T v_sub = 0 ⇒ v_sub = 0 by T injective)
  have hμ_ne : μ ≠ 0 := by
    intro hμ_zero
    apply hv_sub_ne
    apply hT_inj
    rw [hT_eq, hμ_zero, zero_smul, LinearMap.map_zero]
  -- u_2 = Tx v ≠ 0 (else v ∈ V_1 ∩ V_2 = ⊥)
  have hu_2_ne : Tx v ≠ 0 := by
    intro hu_2_zero
    have hv_V1 : v ∈ V_1 := hu_2_zero
    have : v ∈ V_1 ⊓ V_2 := Submodule.mem_inf.mpr ⟨hv_V1, v_sub.prop⟩
    rw [hV12_inter_bot] at this
    exact hu_1_ne ((Submodule.mem_bot _).mp this)
  -- Step 5: U := span {v, Tx v}; show U is x,y-invariant, hence G-invariant, hence = ⊤
  -- ρ x v = v + Tx v, ρ x (Tx v) = Tx v, ρ y v = v, ρ y (Tx v) = Tx v + μ • v
  have hxv : ρ x v = v + Tx v := by
    have h : Tx v = ρ x v - v := by
      simp [hTx_def, LinearMap.sub_apply, Module.End.one_apply]
    rw [h]; abel
  have hxTxv : ρ x (Tx v) = Tx v := hx_triv_V1 (Tx v) hu_2_V1
  have hyv : ρ y v = v := hy_triv_V2 v v_sub.prop
  have hyTxv : ρ y (Tx v) = Tx v + μ • v := by
    have hTyTxv : Ty (Tx v) = μ • v := by
      -- (Ty * Tx) v = (T v_sub).val; T v_sub = μ • v_sub; (μ • v_sub).val = μ • v
      have h1 : (Ty * Tx : Module.End F V) v = (T v_sub).val := by
        change (Ty * Tx : Module.End F V) v_sub.val = (T v_sub).val
        simp [T]
      rw [Module.End.mul_apply] at h1
      rw [h1, hT_eq]
      rfl
    have h_diff : ρ y (Tx v) - Tx v = μ • v := by
      have e : Ty (Tx v) = ρ y (Tx v) - Tx v := by
        simp [hTy_def, LinearMap.sub_apply, Module.End.one_apply]
      rw [e] at hTyTxv; exact hTyTxv
    rw [← h_diff]; abel
  -- U := span F {v, Tx v}
  set U : Submodule F V := Submodule.span F {v, Tx v} with hU_def
  -- v ∈ U, Tx v ∈ U
  have hv_in_U : v ∈ U := Submodule.subset_span (Set.mem_insert _ _)
  have hTxv_in_U : Tx v ∈ U := Submodule.subset_span (by simp)
  -- "g preserves U" forms a subgroup; contains x, y; ⟨x, y⟩ = ⊤ ⇒ all g preserve U
  haveI hU_fd : FiniteDimensional F U := inferInstance
  -- Build the "stabilizer" subgroup
  let stab : Subgroup G :=
    { carrier := { g | ∀ u ∈ U, ρ g u ∈ U }
      one_mem' := by intro u hu; rw [map_one, Module.End.one_apply]; exact hu
      mul_mem' := by
        intro a b ha hb u hu
        rw [map_mul, Module.End.mul_apply]; exact ha _ (hb _ hu)
      inv_mem' := by
        intro a ha u hu
        -- Restrict ρ a to U → U, then it's injective (ρ a inj on V) + finite-dim ⇒ surjective
        let f : U →ₗ[F] U := LinearMap.restrict (ρ a) (fun w hw => ha w hw)
        have hρa_inj : Function.Injective ((ρ a) : V → V) := by
          intro p q hpq
          have : ρ a⁻¹ (ρ a p) = ρ a⁻¹ (ρ a q) := congr_arg _ hpq
          have heq : (ρ a⁻¹ * ρ a : Module.End F V) = 1 := by
            rw [← map_mul, inv_mul_cancel, map_one]
          rwa [show (ρ a⁻¹ : V → V) (ρ a p) = (ρ a⁻¹ * ρ a : Module.End F V) p
            from rfl,
            show (ρ a⁻¹ : V → V) (ρ a q) = (ρ a⁻¹ * ρ a : Module.End F V) q
            from rfl,
            heq, Module.End.one_apply, Module.End.one_apply] at this
        have hf_inj : Function.Injective f := by
          intro p q hpq
          apply Subtype.ext
          have := congr_arg Subtype.val hpq
          simpa [f] using hρa_inj this
        have hf_surj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf_inj
        obtain ⟨w, hw⟩ := hf_surj ⟨u, hu⟩
        have h_val : ρ a w.val = u := by
          have := congr_arg Subtype.val hw
          simpa [f] using this
        have : ρ a⁻¹ u = w.val := by
          rw [← h_val]
          have heq : (ρ a⁻¹ * ρ a : Module.End F V) = 1 := by
            rw [← map_mul, inv_mul_cancel, map_one]
          change (ρ a⁻¹ * ρ a : Module.End F V) w.val = w.val
          rw [heq, Module.End.one_apply]
        rw [this]; exact w.prop }
  -- stab = ⊤ (since x, y ∈ stab and ⟨x, y⟩ = ⊤)
  have hStab_top : stab = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    change ∀ u ∈ U, ρ g u ∈ U
    -- Use span_induction
    rcases hg with rfl | rfl
    · -- g = x
      intro u hu
      induction hu using Submodule.span_induction with
      | mem w hw =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · rw [hxv]
          exact U.add_mem hv_in_U hTxv_in_U
        · rw [hxTxv]; exact hTxv_in_U
      | zero => rw [map_zero]; exact U.zero_mem
      | add a b _ _ iha ihb => rw [map_add]; exact U.add_mem iha ihb
      | smul s a _ iha => rw [map_smul]; exact U.smul_mem s iha
    · -- g = y
      intro u hu
      induction hu using Submodule.span_induction with
      | mem w hw =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · rw [hyv]; exact hv_in_U
        · rw [hyTxv]
          exact U.add_mem hTxv_in_U (U.smul_mem μ hv_in_U)
      | zero => rw [map_zero]; exact U.zero_mem
      | add a b _ _ iha ihb => rw [map_add]; exact U.add_mem iha ihb
      | smul s a _ iha => rw [map_smul]; exact U.smul_mem s iha
  -- U is G-invariant: every g ∈ G is in stab = ⊤
  have hU_G_inv : ∀ g : G, ∀ u ∈ U, ρ g u ∈ U := fun g => by
    have : g ∈ stab := by rw [hStab_top]; trivial
    exact this
  -- U ≠ ⊥ (v ∈ U, v ≠ 0)
  have hU_ne_bot : U ≠ ⊥ := by
    intro h
    apply hu_1_ne
    have : v ∈ (⊥ : Submodule F V) := h ▸ hv_in_U
    exact (Submodule.mem_bot _).mp this
  -- By irreducibility, U = ⊤
  have hU_top : U = ⊤ := (hirr U hU_G_inv).resolve_left hU_ne_bot
  -- u_1 = v, u_2 = Tx v are linearly independent
  have h_lin_ind : LinearIndependent F ![v, Tx v] := by
    rw [LinearIndependent.pair_iff' hu_1_ne]
    intro a heq
    -- heq : a • v = Tx v; we show contradiction with hu_2_ne (or get Tx v = 0)
    -- a • v ∈ V_2 (V_2 contains v); Tx v ∈ V_1; so Tx v ∈ V_1 ∩ V_2 = ⊥ ⇒ Tx v = 0
    have hav_V2 : a • v ∈ V_2 := V_2.smul_mem a v_sub.prop
    have hTxv_V2 : Tx v ∈ V_2 := heq ▸ hav_V2
    have : Tx v ∈ V_1 ⊓ V_2 := Submodule.mem_inf.mpr ⟨hu_2_V1, hTxv_V2⟩
    rw [hV12_inter_bot] at this
    exact hu_2_ne ((Submodule.mem_bot _).mp this)
  -- {v, Tx v} is a basis of V (lin ind + spans top)
  have h_setrange : Set.range ![v, Tx v] = ({v, Tx v} : Set V) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
    · rintro h
      rcases h with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hSpan_top : Submodule.span F (Set.range ![v, Tx v]) = ⊤ := by
    rw [h_setrange]; exact hU_top
  let B : Module.Basis (Fin 2) F V := Basis.mk h_lin_ind hSpan_top.ge
  -- dim V = card (Fin 2) = 2
  rw [Module.finrank_eq_card_basis B]
  simp

end DimReduction

/-! ## A.2: 二次既約 ⇒ |G| 偶 -/

section ThmA2

/-- **BG Theorem A.2** (mmd L4468-4472): `F` alg-closed char `p` (odd) 上,
`V` finite-dim nontrivial, `G = ⟨x, y⟩` 忠実既約作用, `x, y` が二次最小
多項式の `p`-元 ⇒ `|G|` 偶 (i.e., `¬ Odd |G|`).

証明: dim reduction で `dim V = 2`. `x` (or `y`) は `p`-element で `≠ 1` ⇒
`p ∣ |G|`. もし `|G|` 奇なら A.1 で `p ∤ |G|`, 矛盾. -/
theorem thmA2
    [Finite G] [IsAlgClosed F] [Nontrivial V]
    (_hp_odd : p ≠ 2)
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hirr : ∀ U : Submodule F V,
      (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (x y : G) (hgen : Subgroup.closure ({x, y} : Set G) = ⊤)
    (hx : ((ρ x : Module.End F V) - 1) ^ 2 = 0) (hxne : ρ x ≠ 1)
    (hy : ((ρ y : Module.End F V) - 1) ^ 2 = 0) (hyne : ρ y ≠ 1) :
    ¬ Odd (Nat.card G) := by
  intro hodd
  -- Step 1: dim V = 2 (from dim reduction lemma)
  have hdim : Module.finrank F V = 2 :=
    quadratic_two_generated_irreducible_finrank_eq_two ρ hfaithful hirr
      x y hgen hx hxne hy hyne
  -- Step 2: (ρ x)^p = 1 via Frobenius
  haveI : CharP (Module.End F V) p := IsPGroup.charP_End_of_field
  have hp_prime : p.Prime := Fact.out
  -- (ρ x - 1)^p = (ρ x - 1)^(p-2) * (ρ x - 1)^2 = (ρ x - 1)^(p-2) * 0 = 0
  have hN_p_zero : ((ρ x : Module.End F V) - 1) ^ p = 0 := by
    have hp_two : 2 ≤ p := hp_prime.two_le
    calc ((ρ x : Module.End F V) - 1) ^ p
        = ((ρ x : Module.End F V) - 1) ^ (p - 2) * ((ρ x : Module.End F V) - 1) ^ 2 := by
          rw [← pow_add]; congr 1; omega
      _ = ((ρ x : Module.End F V) - 1) ^ (p - 2) * 0 := by rw [hx]
      _ = 0 := mul_zero _
  -- (ρ x - 1)^p = (ρ x)^p - 1^p (Frobenius); = 0 ⇒ (ρ x)^p = 1
  have hρx_p : (ρ x : Module.End F V) ^ p = 1 := by
    have h1 : ((ρ x : Module.End F V) - 1) ^ p =
        (ρ x : Module.End F V) ^ p - (1 : Module.End F V) ^ p :=
      sub_pow_char_of_commute p (Commute.one_right _)
    rw [hN_p_zero, one_pow, eq_comm, sub_eq_zero] at h1
    exact h1
  -- Step 3: x has order dividing p; ≠ 1 ⇒ order = p (p prime); so p ∣ |G|
  have hxp_one : x ^ p = 1 := by
    apply hfaithful
    rw [map_pow, map_one]; exact hρx_p
  have hox_dvd_p : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp_one
  have hx_ne_one : x ≠ 1 := fun h => hxne (by rw [h, map_one])
  have hox_ne_one : orderOf x ≠ 1 := fun h => hx_ne_one (orderOf_eq_one_iff.mp h)
  have hox_eq_p : orderOf x = p := by
    rcases hp_prime.eq_one_or_self_of_dvd (orderOf x) hox_dvd_p with h | h
    · exact absurd h hox_ne_one
    · exact h
  have hp_dvd : p ∣ Nat.card G := hox_eq_p ▸ orderOf_dvd_natCard x
  -- Step 4: A.1 (|G| odd ⇒ p ∤ |G|) で矛盾
  exact thmA1 hodd hdim ρ hfaithful hirr hp_dvd

end ThmA2

/-! ## p-stability: 定義 + A.3 (no normal p-subgroup + not p-stable ⇒ |G| even) -/

section PStability

end PStability
end OddOrder.BG.AppA
