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
import OddOrder.BG.Ch1_Preliminary.S02_Representations
import OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector

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
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hirr : ∀ U : Submodule F V,
      (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (x y : G) (hgen : Subgroup.closure ({x, y} : Set G) = ⊤)
    (hx : ((ρ x : Module.End F V) - 1) ^ 2 = 0) (_hxne : ρ x ≠ 1)
    (hy : ((ρ y : Module.End F V) - 1) ^ 2 = 0) (_hyne : ρ y ≠ 1) :
    Module.finrank F V = 2 := by
  sorry

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
  sorry

end ThmA2

end OddOrder.BG.AppA
