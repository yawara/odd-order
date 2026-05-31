/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.BG.Ch1_Preliminary.S04c_Prop411
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.SCN
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.GroupTheory.FrattiniPGroup

/-!
# Gorenstein "Finite Groups" Lemma 4.14 — the engine of `dₙ(P) ≤ 2 ⇒ d(P) ≤ 2`

> **本** D. Gorenstein, *Finite Groups* (2nd ed.), Lemma 4.14 (mmd L4203–4215),
> referenced by Bender–Glauberman §4 (`local-analysis.mmd` L1624, Lem 4.13 が依存).
> CLAUDE.md の方針に従い, BG が省略する行間を Gorenstein 原典で埋める.

**Lemma 4.14**: `P` 有限 `p`-群, `p` odd, `A` を正規 abelian で **rank 最大**
(`m(A) = dₙ(P)`) なる maximal abelian normal subgroup とする. このとき
`Ω₁(C_P(Ω₁(A))) = Ω₁(A)`.

§4 Thm 4.16 (Blackburn apex) の最終ゲート chain の engine. ロードマップ =
`notes/bg/s04_lem413_gorenstein_precursors.md`.

証明は 3 part:
* **PART 1** (stabilization): 位数 `p` で `Ω₁(A)` を中心化する `x` は `A/Ω₁(A)` も
  中心化する (= `x⁻¹ a x a⁻¹ ∈ Ω₁(A)`).
* **PART 2** (`D` exp `p`): `D = Ω₁(C_P(Ω₁(A)))` は exponent `p` (minimal
  counterexample + Lem 4.12 / 4.13 / 3.9(i) / 3.12).
* **PART 3** (`Ω₁(A) = D`): rank squeeze (`dₙ(P)` 最大性 + Lem 1.3.4).
-/

open scoped commutatorElement

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

/-! ## INLINE-1: Gorenstein Lemma 4.12 -/

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

/-- **Gorenstein "Finite Groups" Lemma 4.12.** If `x, y` are elements of a `p`-group
with `⟨x, y⟩` noncyclic, then `⟨y, ˣy⟩ ⊊ ⟨x, y⟩` (here `ˣy = x y x⁻¹`).

Proof (Gorenstein, mmd L4185): set `Q = ⟨y, x y x⁻¹⟩`, `P₀ = ⟨x, y⟩`. Clearly `Q ≤ P₀`.
If `Q = P₀`, then since `⁅x, y⁆ = (x y x⁻¹) · y⁻¹ ∈ Q` the coset `Φ(Q) y` generates
`Q/Φ(Q)` (because `x y x⁻¹ = ⁅x, y⁆ · y` and `⁅x, y⁆ ∈ Q' ≤ Φ(Q)`); so `Q/Φ(Q)` is
cyclic and hence `Q` is cyclic (Frattini non-generating), contradicting noncyclicity
of `P₀ = Q`. -/
private theorem lt_closure_conj_of_noncyclic (hP : IsPGroup p P) {x y : P}
    (hncyc : ¬ IsCyclic ↥(Subgroup.closure ({x, y} : Set P))) :
    Subgroup.closure ({y, x * y * x⁻¹} : Set P) < Subgroup.closure ({x, y} : Set P) := by
  set Q := Subgroup.closure ({y, x * y * x⁻¹} : Set P) with hQ
  set P₀ := Subgroup.closure ({x, y} : Set P) with hP₀
  -- `y, x y x⁻¹ ∈ P₀`.
  have hyP₀ : y ∈ P₀ := Subgroup.subset_closure (by simp)
  have hxP₀ : x ∈ P₀ := Subgroup.subset_closure (by simp)
  have hcyP₀ : x * y * x⁻¹ ∈ P₀ :=
    P₀.mul_mem (P₀.mul_mem hxP₀ hyP₀) (P₀.inv_mem hxP₀)
  -- `Q ≤ P₀`.
  have hQle : Q ≤ P₀ := by
    rw [hQ, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hyP₀
    · exact hcyP₀
  refine lt_of_le_of_ne hQle (fun hQeq => hncyc ?_)
  -- Suppose `Q = P₀`; show `P₀` is cyclic. Generators `y, x y x⁻¹ ∈ Q`, and `x ∈ Q` (as `Q = P₀`).
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hcyQ : x * y * x⁻¹ ∈ Q := Subgroup.subset_closure (by simp)
  have hxQ : x ∈ Q := hQeq ▸ hxP₀
  -- Subtype lifts.
  set y₀ : Q := ⟨y, hyQ⟩ with hy₀
  set x₀ : Q := ⟨x, hxQ⟩ with hx₀
  set c₀ : Q := ⟨x * y * x⁻¹, hcyQ⟩ with hc₀
  -- `Q` is a `p`-group (subgroup of the `p`-group `P`).
  have hQpg : IsPGroup p Q := hP.to_subgroup Q
  -- **Frattini argument in `Q`**: `zpowers y₀ ⊔ Φ(Q) = ⊤`, hence `zpowers y₀ = ⊤`.
  -- `c₀ = ⁅x₀, y₀⁆ * y₀ ∈ Φ(Q) ⊔ zpowers y₀`.
  have hc₀_mem : c₀ ∈ Subgroup.zpowers y₀ ⊔ frattini Q := by
    have hcomm : ⁅x₀, y₀⁆ ∈ frattini Q := hQpg.commutator_mem_frattini x₀ y₀
    have heq : c₀ = ⁅x₀, y₀⁆ * y₀ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, commutatorElement_def]
      push_cast [hc₀, hx₀, hy₀]
      group
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left (Subgroup.mem_zpowers y₀))
  have hsup_top : Subgroup.zpowers y₀ ⊔ frattini Q = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_subtype_le_map_subtype, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    -- `Q = closure {y, x y x⁻¹} ≤ (zpowers y₀ ⊔ Φ(Q)).map Q.subtype`.
    refine le_trans (le_of_eq hQ) ?_
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨y₀, Subgroup.mem_sup_left (Subgroup.mem_zpowers y₀), rfl⟩
    · exact ⟨c₀, hc₀_mem, rfl⟩
  have hzeq : Subgroup.zpowers y₀ = ⊤ := frattini_nongenerating hsup_top
  haveI : IsCyclic Q := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨y₀, hzeq⟩
  exact isCyclic_of_surjective (MulEquiv.subgroupCongr hQeq).toMonoidHom
    (MulEquiv.subgroupCongr hQeq).surjective

end OddOrder.BG.Ch1.S04
