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

/-! ## INLINE-2: Gorenstein Lemma 4.13 (element / commutator form) -/

/-- **Gorenstein "Finite Groups" Lemma 4.13** (element form). Let `A` be a normal
subgroup of `P` and `H ≤ A` an abelian subgroup. If two elements `g₁, g₂` each
"stabilize" the series `A ⊇ H ⊇ 1` — i.e. their conjugation displaces every `a ∈ A`
into `H` (`g⁻¹ a g a⁻¹ ∈ H`) and they centralize `H` — then their commutator
`⁅g₂, g₁⁆` centralizes `A`.

This is the element-level version of Gorenstein's stability-group lemma (the
stabilizer of a two-step normal series with abelian top is abelian, mmd L4195,
eq. (4.11)). Concretely, with `s = g₁⁻¹ a g₁ a⁻¹`, `t = g₂⁻¹ a g₂ a⁻¹ ∈ H`, one
computes `⁅g₂, g₁⁆ a ⁅g₂, g₁⁆⁻¹ = (s t s⁻¹ t⁻¹) a = a`, the last step because
`s, t ∈ H` commute. -/
private theorem commutator_centralizes_of_stabilize {A H : Subgroup P} [A.Normal]
    (hH_le : H ≤ A) (hH_comm : ∀ s ∈ H, ∀ t ∈ H, s * t = t * s) {g₁ g₂ : P}
    (hdisp₁ : ∀ a ∈ A, g₁⁻¹ * a * g₁ * a⁻¹ ∈ H)
    (hdisp₂ : ∀ a ∈ A, g₂⁻¹ * a * g₂ * a⁻¹ ∈ H)
    (hfix₁ : ∀ w ∈ H, g₁ * w = w * g₁) (hfix₂ : ∀ w ∈ H, g₂ * w = w * g₂) :
    ∀ a ∈ A, ⁅g₂, g₁⁆ * a = a * ⁅g₂, g₁⁆ := by
  intro a ha
  -- Displacement elements `s, t ∈ H`.
  set s := g₁⁻¹ * a * g₁ * a⁻¹ with hs_def
  set t := g₂⁻¹ * a * g₂ * a⁻¹ with ht_def
  have hsH : s ∈ H := hdisp₁ a ha
  have htH : t ∈ H := hdisp₂ a ha
  -- `s, t ∈ A`.
  have hsA : s ∈ A := hH_le hsH
  have htA : t ∈ A := hH_le htH
  -- `g₁⁻¹ a g₁ = s * a` and `g₂⁻¹ a g₂ = t * a`.
  have hconj₁ : g₁⁻¹ * a * g₁ = s * a := by rw [hs_def]; group
  have hconj₂ : g₂⁻¹ * a * g₂ = t * a := by rw [ht_def]; group
  -- `g₁ a g₁⁻¹ = s⁻¹ * a`: from `g₁` fixing `s ∈ H`, `g₁ s g₁⁻¹ = s`, hence
  -- `a g₁ a⁻¹ g₁⁻¹ = s`, so `g₁ a g₁⁻¹ = s⁻¹ a` (using `A` abelian via `H`-fix? no — direct).
  have hg1s : g₁ * s = s * g₁ := hfix₁ s hsH
  have hg2t : g₂ * t = t * g₂ := hfix₂ t htH
  -- `s⁻¹ = g₁ a g₁⁻¹ a⁻¹`: conjugate `hconj₁` by `g₁`.
  -- Conjugation-fix helpers: if `g` commutes with `w`, then `g w g⁻¹ = w` and `g⁻¹ w g = w`.
  have fixR : ∀ (g w : P), g * w = w * g → g * w * g⁻¹ = w := fun g w hgw => by
    rw [hgw]; group
  have fixL : ∀ (g w : P), g * w = w * g → g⁻¹ * w * g = w := fun g w hgw => by
    rw [mul_assoc, ← hgw]; group
  have hconj₁' : g₁ * a * g₁⁻¹ = s⁻¹ * a := by
    -- From `g₁⁻¹ a g₁ = s a` we get `a = (g₁ s g₁⁻¹)(g₁ a g₁⁻¹) = s (g₁ a g₁⁻¹)`.
    have h1 : a = s * (g₁ * a * g₁⁻¹) := by
      have h := congrArg (fun z => g₁ * z * g₁⁻¹) hconj₁
      simp only at h
      rw [show g₁ * (g₁⁻¹ * a * g₁) * g₁⁻¹ = a by group,
        show g₁ * (s * a) * g₁⁻¹ = (g₁ * s * g₁⁻¹) * (g₁ * a * g₁⁻¹) by group,
        fixR g₁ s hg1s] at h
      exact h
    refine mul_left_cancel (a := s) ?_
    rw [← h1]; group
  -- Similarly `g₂ a g₂⁻¹ = t⁻¹ * a`.
  have hconj₂' : g₂ * a * g₂⁻¹ = t⁻¹ * a := by
    have h1 : a = t * (g₂ * a * g₂⁻¹) := by
      have h := congrArg (fun z => g₂ * z * g₂⁻¹) hconj₂
      simp only at h
      rw [show g₂ * (g₂⁻¹ * a * g₂) * g₂⁻¹ = a by group,
        show g₂ * (t * a) * g₂⁻¹ = (g₂ * t * g₂⁻¹) * (g₂ * a * g₂⁻¹) by group,
        fixR g₂ t hg2t] at h
      exact h
    refine mul_left_cancel (a := t) ?_
    rw [← h1]; group
  -- `s, t` commute (both in abelian `H`); also `s⁻¹ ∈ H`, fixed by `g₂`.
  have hst : s * t = t * s := hH_comm s hsH t htH
  -- Auxiliary fixings.
  have hg2s : g₂ * s = s * g₂ := hfix₂ s hsH
  have hg1t : g₁ * t = t * g₁ := hfix₁ t htH
  have hg2si : g₂ * s⁻¹ = s⁻¹ * g₂ := hfix₂ s⁻¹ (H.inv_mem hsH)
  -- Conjugation of `a` by `⁅g₂, g₁⁆` is trivial.
  have hconj : ⁅g₂, g₁⁆ * a * (⁅g₂, g₁⁆)⁻¹ = a := by
    rw [commutatorElement_def]
    calc g₂ * g₁ * g₂⁻¹ * g₁⁻¹ * a * (g₂ * g₁ * g₂⁻¹ * g₁⁻¹)⁻¹
        = g₂ * g₁ * g₂⁻¹ * (g₁⁻¹ * a * g₁) * g₂ * g₁⁻¹ * g₂⁻¹ := by group
      _ = g₂ * g₁ * g₂⁻¹ * (s * a) * g₂ * g₁⁻¹ * g₂⁻¹ := by rw [hconj₁]
      _ = g₂ * g₁ * (g₂⁻¹ * s * g₂) * (g₂⁻¹ * a * g₂) * g₁⁻¹ * g₂⁻¹ := by group
      _ = g₂ * g₁ * s * (t * a) * g₁⁻¹ * g₂⁻¹ := by
            rw [hconj₂, fixL g₂ s hg2s]
      _ = g₂ * ((g₁ * s * g₁⁻¹) * (g₁ * t * g₁⁻¹) * (g₁ * a * g₁⁻¹)) * g₂⁻¹ := by group
      _ = g₂ * (s * t * (s⁻¹ * a)) * g₂⁻¹ := by
            rw [hconj₁', fixR g₁ s hg1s, fixR g₁ t hg1t]
      _ = (g₂ * s * g₂⁻¹) * (g₂ * t * g₂⁻¹) * (g₂ * s⁻¹ * g₂⁻¹) * (g₂ * a * g₂⁻¹) := by group
      _ = s * t * s⁻¹ * (t⁻¹ * a) := by
            rw [hconj₂', fixR g₂ s hg2s, fixR g₂ t hg2t, fixR g₂ s⁻¹ hg2si]
      _ = (s * t * s⁻¹ * t⁻¹) * a := by group
      _ = a := by
            rw [show s * t * s⁻¹ * t⁻¹ = 1 by
              rw [hst]; group]
            group
  -- Convert conjugation-trivial to commuting.
  have := hconj
  rw [mul_inv_eq_iff_eq_mul] at this
  rw [this]

end OddOrder.BG.Ch1.S04
