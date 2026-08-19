/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-!
# GL(2,p) transvection: transitivity on lines (BG Lemma 10.13(c) core)

Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994), §10,
Lemma 10.13(c) (PDF p.79-80).

The pure linear-algebra core of BG Lemma 10.13(c): an order-`p` automorphism `φ` of a
2-dimensional `𝔽_p`-vector space `V` that fixes a line `L` pointwise is a *transvection*, and the
cyclic group `⟨φ⟩` acts transitively (via its powers) on the remaining `p` lines of `V`.

In `V ≅ 𝔽_p²` with `L = ⟨e₁⟩` and a complementary `e₂`, the hypotheses force `φ` to be the
transvection `e₁ ↦ e₁`, `e₂ ↦ a·e₁ + e₂` with `a ≠ 0`: the `e₂`-coordinate `b` of `φ e₂`
satisfies `bᵖ = 1`, and Fermat (`bᵖ = b` over `𝔽_p`) gives `b = 1`. Then `φᵏ` sends the line
`⟨u·e₁ + e₂⟩` to `⟨(u + k·a)·e₁ + e₂⟩`, and `u ↦ u + k·a` is transitive on `𝔽_p` since `a ≠ 0`.

BG uses this in Lemma 10.13(c): for `A ∈ ℰ_p²(G)`, `Z₀ = Ω₁(Z(P))` a line of `A`, and
`x ∈ N_P(A) − C_P(A)` of order `p`, conjugation by `x` is exactly such a transvection (it
centralises `Z₀ ≤ Z(P)`), so `⟨x⟩` permutes the lines of `A` other than `Z₀` transitively.
The group-level wiring (`A` elementary abelian rank 2 ↔ `Additive A` a 2-dim `𝔽_p`-space,
`MulAut.conj x` ↔ `φ`) is supplied where Lemma 10.13(c) is assembled (which additionally needs
Cor 10.7(b)).
-/

namespace OddOrder.BG.Ch3.S10

open Module Submodule

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- **BG Lemma 10.13(c) — transvection transitivity (linear-algebra core)**: let `V` be a
2-dimensional `𝔽_p`-vector space, `φ` a linear automorphism with `φ ^ p = 1` and `φ ≠ 1` that
fixes a line `L` pointwise. Then for any two lines `W₁, W₂ ≠ L` there is a power `φ ^ k` mapping
`W₁` onto `W₂`. -/
theorem exists_pow_map_line_eq
    (hdim : finrank (ZMod p) V = 2) (φ : V ≃ₗ[ZMod p] V) (hord : φ ^ p = 1) (hne : φ ≠ 1)
    {L : Submodule (ZMod p) V} (hLdim : finrank (ZMod p) L = 1)
    (hfix : ∀ v ∈ L, φ v = v)
    {W₁ W₂ : Submodule (ZMod p) V}
    (hW₁ : finrank (ZMod p) W₁ = 1) (hW₁L : W₁ ≠ L)
    (hW₂ : finrank (ZMod p) W₂ = 1) (hW₂L : W₂ ≠ L) :
    ∃ k : ℕ, W₁.map (φ ^ k).toLinearMap = W₂ := by
  classical
  have : FiniteDimensional (ZMod p) V := .of_finrank_eq_succ hdim
  -- A generator `e₁` of the fixed line `L`.
  have hLne : L ≠ ⊥ := by rintro rfl; rw [finrank_bot] at hLdim; omega
  obtain ⟨e₁, he₁L, he₁0⟩ := (Submodule.ne_bot_iff L).mp hLne
  have hLspan : span (ZMod p) {e₁} = L :=
    eq_of_le_of_finrank_eq ((span_singleton_le_iff_mem _ _).mpr he₁L)
      (by rw [finrank_span_singleton he₁0, hLdim])
  have hφe₁ : φ e₁ = e₁ := hfix e₁ he₁L
  -- A vector `e₂ ∉ L`.
  obtain ⟨e₂, he₂L⟩ : ∃ e₂, e₂ ∉ L := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : L = ⊤ := eq_top_iff.mpr fun v _ => h v
    rw [this, finrank_top] at hLdim; omega
  have he₂0 : e₂ ≠ 0 := fun h => he₂L (h ▸ L.zero_mem)
  -- `{e₁, e₂}` is linearly independent and spans `V`.
  have hli : LinearIndependent (ZMod p) ![e₁, e₂] := by
    rw [LinearIndependent.pair_iff' he₁0]
    intro c hc
    exact he₂L (hc ▸ hLspan ▸ Submodule.smul_mem _ c (mem_span_singleton_self e₁))
  have hrange : Set.range ![e₁, e₂] = {e₁, e₂} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan : span (ZMod p) {e₁, e₂} = ⊤ := by
    have hsp := (basisOfLinearIndependentOfCardEqFinrank hli
      (show Fintype.card (Fin 2) = finrank (ZMod p) V by simp [hdim])).span_eq
    rwa [coe_basisOfLinearIndependentOfCardEqFinrank, hrange] at hsp
  -- Coordinate uniqueness on `{e₁, e₂}`.
  have hpair := LinearIndependent.pair_iff.mp hli
  -- `φ e₂ = a • e₁ + b • e₂`.
  obtain ⟨a, b, hφe₂⟩ : ∃ a b : ZMod p, a • e₁ + b • e₂ = φ e₂ :=
    mem_span_pair.mp (by rw [hspan]; exact Submodule.mem_top)
  -- `φ ^ k e₁ = e₁` for all `k`.
  have hiter_e₁ : ∀ k : ℕ, φ^[k] e₁ = e₁ := by
    intro k; induction k with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hφe₁]
  -- `φ ^ k e₂ = c • e₁ + b ^ k • e₂` for some `c`.
  have hiter_e₂ : ∀ k : ℕ, ∃ c : ZMod p, φ^[k] e₂ = c • e₁ + b ^ k • e₂ := by
    intro k; induction k with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
        obtain ⟨c, hc⟩ := ih
        refine ⟨c + b ^ n * a, ?_⟩
        rw [Function.iterate_succ_apply', hc, map_add, map_smul, map_smul, hφe₁, ← hφe₂,
          pow_succ]
        module
  -- `b = 1` (from `φ ^ p = 1` and Fermat `bᵖ = b`).
  have hb1 : b = 1 := by
    obtain ⟨c, hc⟩ := hiter_e₂ p
    have hφp : φ^[p] e₂ = e₂ := by
      rw [← LinearEquiv.pow_apply, hord]; rfl
    rw [hφp] at hc
    have hzero : c • e₁ + (b ^ p - 1) • e₂ = 0 := by
      have hmod : c • e₁ + (b ^ p - 1) • e₂ = (c • e₁ + b ^ p • e₂) - e₂ := by module
      rw [hmod, ← hc, sub_self]
    have hbp : b ^ p = 1 := sub_eq_zero.mp (hpair c (b ^ p - 1) hzero).2
    rwa [ZMod.pow_card] at hbp
  -- With `b = 1`: `φ ^ k e₂ = (k • a) • e₁ + e₂`.
  have hiter_e₂' : ∀ k : ℕ, φ^[k] e₂ = ((k : ZMod p) * a) • e₁ + e₂ := by
    intro k; induction k with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, map_add, map_smul, hφe₁, ← hφe₂, hb1, one_smul]
        push_cast; module
  -- `a ≠ 0` (else `φ` fixes the spanning pair, so `φ = 1`).
  have ha0 : a ≠ 0 := by
    intro ha
    apply hne
    apply LinearEquiv.toLinearMap_injective
    refine LinearMap.ext_on hspan (fun x hx => ?_)
    simp only [LinearEquiv.coe_coe, LinearEquiv.coe_one, id_eq]
    rcases hx with rfl | hx
    · exact hφe₁
    · rw [Set.mem_singleton_iff] at hx; subst hx
      rw [← hφe₂, ha, hb1]; simp
  -- Each line `≠ L` is `⟨u • e₁ + e₂⟩` for a unique `u`.
  have hline : ∀ W : Submodule (ZMod p) V, finrank (ZMod p) W = 1 → W ≠ L →
      ∃ u : ZMod p, W = span (ZMod p) {u • e₁ + e₂} := by
    intro W hWdim hWL
    have hWne : W ≠ ⊥ := by rintro rfl; rw [finrank_bot] at hWdim; omega
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hWne
    have hWspan : W = span (ZMod p) {w} :=
      (eq_of_le_of_finrank_eq ((span_singleton_le_iff_mem _ _).mpr hwW)
        (by rw [finrank_span_singleton hw0, hWdim])).symm
    have hwL : w ∉ L := by
      intro hw
      exact hWL (hWspan.trans (eq_of_le_of_finrank_eq
        ((span_singleton_le_iff_mem _ _).mpr hw)
        (by rw [finrank_span_singleton hw0, hLdim])))
    obtain ⟨s, t, hst⟩ : ∃ s t : ZMod p, s • e₁ + t • e₂ = w :=
      mem_span_pair.mp (by rw [hspan]; exact Submodule.mem_top)
    have ht0 : t ≠ 0 := by
      intro ht; apply hwL
      rw [← hst, ht, zero_smul, add_zero, ← hLspan]
      exact Submodule.smul_mem _ s (mem_span_singleton_self e₁)
    refine ⟨s * t⁻¹, ?_⟩
    rw [hWspan]
    have hsmul : t⁻¹ • w = (s * t⁻¹) • e₁ + e₂ := by
      rw [← hst, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht0, one_smul, mul_comm]
    rw [← hsmul, span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero ht0)) w]
  -- Parametrise `W₁, W₂` and solve `u₁ + k * a = u₂`.
  obtain ⟨u₁, hu₁⟩ := hline W₁ hW₁ hW₁L
  obtain ⟨u₂, hu₂⟩ := hline W₂ hW₂ hW₂L
  refine ⟨((u₂ - u₁) * a⁻¹).val, ?_⟩
  have hk : (((u₂ - u₁) * a⁻¹).val : ZMod p) = (u₂ - u₁) * a⁻¹ := by
    simp [ZMod.natCast_val, ZMod.cast_id]
  -- `(φ ^ k) (u₁ • e₁ + e₂) = u₂ • e₁ + e₂`.
  have happ : (φ ^ ((u₂ - u₁) * a⁻¹).val).toLinearMap (u₁ • e₁ + e₂) = u₂ • e₁ + e₂ := by
    rw [LinearEquiv.coe_coe, map_add, map_smul, LinearEquiv.pow_apply, LinearEquiv.pow_apply,
      hiter_e₁, hiter_e₂', hk, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    module
  rw [hu₁, hu₂, Submodule.map_span, Set.image_singleton, happ]

end OddOrder.BG.Ch3.S10
