/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Character

/-!
# Character values at involutions are rational integers

If `t² = 1` then `ρ t` is an involution of `V`, so `(1 + ρ t)/2` is a projection onto its
`+1`-eigenspace and

`χ_ρ(t) = 2 · dim V₊ − dim V`.

In particular `χ_ρ(t)` lies in the image of `ℤ`, whatever the ground field (of characteristic
`≠ 2`) — no theory of algebraic integers or of roots of unity is involved.

Navarro's remark after (5.1) says more, that the generalized decomposition numbers `d^x_{χφ}` lie
in `ℤ[ζ]` for `ζ` a primitive `o(x)`-th root of unity.  For an involution `ζ = -1`, so the numbers
are *rational* integers, and the same projection gives that too: inserting `σ y` for `y` a element
commuting with `t`,

`χ(t y) = 2 · χ_{V₊}(y) − χ(y)`,

where `V₊ = range (1 + σ t)/2` is a subrepresentation of the centraliser.  Both terms on the right
are ordinary characters of `C_G(t)`, so on the `p`-regular classes both are `ℕ`-combinations of
`IBr(C_G(t))` and `d^t_{χφ}` is the difference of two natural numbers.  That is the content of
`Modular/InvolutionDecompositionIntegral`; this file supplies the linear algebra.

## Main results

* `OddOrder.RepresentationTheory.trace_comp_eq_trace_restrict_range` — `tr(P f) = tr(f|_{im P})`
* `OddOrder.RepresentationTheory.character_eq_of_mul_self_eq_one` — `χ(t) = 2 dim V₊ − dim V`
* `OddOrder.RepresentationTheory.exists_intCast_character_of_mul_self_eq_one`
* `OddOrder.RepresentationTheory.character_involution_mul_eq` — `χ(t y) = 2 χ_{V₊}(y) − χ(y)`
-/

namespace OddOrder.RepresentationTheory

open Module

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Group G]

/-- The projection onto the `+1`-eigenspace of an involution, `(1 + ρ t)/2`. -/
noncomputable def involutionProj (σ : Representation K G V) (t : G) : Module.End K V :=
  (2 : K)⁻¹ • (1 + σ t)

omit [FiniteDimensional K V] in
theorem isIdempotentElem_involutionProj (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {t : G}
    (ht : t * t = 1) : IsIdempotentElem (involutionProj σ t) := by
  have hA : (σ t) * (σ t) = 1 := by rw [← map_mul, ht, map_one]
  have hsq : ((1 : Module.End K V) + σ t) * (1 + σ t) = (2 : K) • (1 + σ t) := by
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, hA]
    module
  rw [IsIdempotentElem, involutionProj, smul_mul_smul_comm, hsq, smul_smul]
  congr 1
  field_simp

/-- **`χ(t) = 2 · dim V₊ − dim V`** for `t² = 1`: the trace of the projection `(1 + ρ t)/2` is the
dimension of its image. -/
theorem character_eq_of_mul_self_eq_one (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {t : G}
    (ht : t * t = 1) :
    σ.character t
      = 2 * (finrank K (LinearMap.range (involutionProj σ t)) : K) - (finrank K V : K) := by
  have htr : LinearMap.trace K V (involutionProj σ t)
      = (finrank K (LinearMap.range (involutionProj σ t)) : K) :=
    ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr
      (isIdempotentElem_involutionProj σ h2 ht)).trace
  have htrP : LinearMap.trace K V (involutionProj σ t)
      = (2 : K)⁻¹ * ((finrank K V : K) + σ.character t) := by
    rw [involutionProj, map_smul, map_add, LinearMap.trace_one, smul_eq_mul]
    rfl
  rw [← htr, htrP]
  field_simp
  ring

/-- **Character values at involutions are rational integers.** -/
theorem exists_intCast_character_of_mul_self_eq_one (σ : Representation K G V) (h2 : (2 : K) ≠ 0)
    {t : G} (ht : t * t = 1) : ∃ n : ℤ, σ.character t = (n : K) := by
  refine ⟨2 * (finrank K (LinearMap.range (involutionProj σ t)) : ℤ) - (finrank K V : ℤ), ?_⟩
  push_cast
  exact character_eq_of_mul_self_eq_one σ h2 ht

/-- **An involution with `χ(t) = χ(1)` acts trivially.**  From `χ(t) = 2 dim V₊ − dim V` and
`χ(1) = dim V` one gets `dim V₊ = dim V` (the cast is injective in characteristic zero), so the
projection `(1 + ρ t)/2` is the identity and `ρ t = 1`.

Over `ℂ` this is `rep_eq_id_of_character_eq_one`, proved by the equality case of the triangle
inequality; for an involution the eigenvalues are just `±1`, so no archimedean input is needed and
the statement holds over any field of characteristic zero. -/
theorem rep_eq_one_of_character_eq_of_mul_self_eq_one [CharZero K] (σ : Representation K G V)
    {t : G} (ht : t * t = 1) (h : σ.character t = σ.character 1) : σ t = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hchar := character_eq_of_mul_self_eq_one σ h2 ht
  rw [Representation.char_one] at h
  rw [h] at hchar
  -- `2 r = 2 d` in `K`, hence `r = d` in `ℕ`
  have hcast : ((Module.finrank K (LinearMap.range (involutionProj σ t)) : ℕ) : K)
      = ((Module.finrank K V : ℕ) : K) := by
    have h2' : (2 : K) * (Module.finrank K (LinearMap.range (involutionProj σ t)) : K)
        = (2 : K) * (Module.finrank K V : K) := by linear_combination (-1 : K) * hchar
    exact mul_left_cancel₀ h2 h2'
  have hrank : Module.finrank K (LinearMap.range (involutionProj σ t)) = Module.finrank K V :=
    Nat.cast_injective hcast
  -- a subspace of full dimension is everything, so the idempotent is the identity
  have htop : LinearMap.range (involutionProj σ t) = ⊤ :=
    Submodule.eq_top_of_finrank_eq hrank
  have hid : involutionProj σ t = 1 := by
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ LinearMap.range (involutionProj σ t) := by rw [htop]; trivial
    obtain ⟨y, hy⟩ := hx
    have hidem := isIdempotentElem_involutionProj σ h2 ht
    calc involutionProj σ t x = involutionProj σ t (involutionProj σ t y) := by rw [hy]
      _ = involutionProj σ t y := by
          have hy2 := congrArg (fun f : Module.End K V => f y) hidem
          simpa [Module.End.mul_apply] using hy2
      _ = x := hy
      _ = (1 : Module.End K V) x := rfl
  -- unwind `(1 + ρ t)/2 = 1`
  have : (1 : Module.End K V) + σ t = (2 : K) • (1 : Module.End K V) := by
    have := congrArg (fun f : Module.End K V => (2 : K) • f) hid
    rwa [involutionProj, smul_smul, mul_inv_cancel₀ h2, one_smul] at this
  have h2smul : (2 : K) • (1 : Module.End K V) = 1 + 1 := by
    rw [two_smul]
  rw [h2smul] at this
  exact add_left_cancel this

/-! ### Inserting a commuting element: `χ(t y) = 2 χ_{V₊}(y) − χ(y)` -/

/-- **The trace of `P f` is the trace of `f` on the image of `P`**, for an idempotent `P` and an
`f` preserving that image.  Writing `P ∘ f` as `ι ∘ (P ∘ f)ᶜ` with `ι` the inclusion of `im P`,
`trace_comp_comm'` moves the trace to `im P`, where `(P ∘ f)ᶜ ∘ ι = f|_{im P}` because `P` is the
identity on its own image.

Note that `P` and `f` need not commute; only the invariance of `im P` is used. -/
theorem trace_comp_eq_trace_restrict_range {P f : Module.End K V} (hP : IsIdempotentElem P)
    (hf : ∀ v ∈ LinearMap.range P, f v ∈ LinearMap.range P) :
    LinearMap.trace K V (P ∘ₗ f)
      = LinearMap.trace K ↥(LinearMap.range P) (f.restrict hf) := by
  classical
  have hid : ∀ x ∈ LinearMap.range P, P x = x := by
    rintro _ ⟨y, rfl⟩
    exact congrFun (congrArg DFunLike.coe hP) y
  set u : ↥(LinearMap.range P) →ₗ[K] V := (LinearMap.range P).subtype with hu
  set w : V →ₗ[K] ↥(LinearMap.range P) :=
    (P ∘ₗ f).codRestrict (LinearMap.range P) (fun v => LinearMap.mem_range_self P (f v)) with hw
  have huw : u ∘ₗ w = P ∘ₗ f := rfl
  have hwu : w ∘ₗ u = f.restrict hf := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change P (f (x : V)) = f (x : V)
    exact hid _ (hf x x.2)
  rw [← huw, ← LinearMap.trace_comp_comm' u w, hwu]

omit [FiniteDimensional K V] in
/-- The `+1`-eigenspace of an involution is invariant under everything commuting with it. -/
theorem range_involutionProj_invariant (σ : Representation K G V) {t y : G} (hy : Commute t y) :
    ∀ v ∈ LinearMap.range (involutionProj σ t), σ y v ∈ LinearMap.range (involutionProj σ t) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨σ y w, ?_⟩
  have hcomm : σ y * σ t = σ t * σ y := by rw [← map_mul, ← map_mul, hy.symm.eq]
  have := congrFun (congrArg DFunLike.coe hcomm) w
  simp only [involutionProj, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    map_smul, map_add]
  rw [show (σ y) ((σ t) w) = (σ t) ((σ y) w) from this]

/-- **`χ(t y) = 2 χ_{V₊}(y) − χ(y)`** for an involution `t` and `y` commuting with `t`, where
`V₊ = im (1 + σ t)/2`.

This is `character_eq_of_mul_self_eq_one` with `σ y` inserted: `σ t = 2 P − 1`, so
`tr(σ t σ y) = 2 tr(P σ y) − tr(σ y)`, and `tr(P σ y)` is the trace of `σ y` on `V₊`
(`trace_comp_eq_trace_restrict_range`).  Both terms on the right are ordinary characters of the
centraliser of `t`, which is what makes `d^t_{χφ}` a difference of decomposition numbers. -/
theorem character_involution_mul_eq (σ : Representation K G V) (h2 : (2 : K) ≠ 0) {t y : G}
    (ht : t * t = 1) (hy : Commute t y) :
    σ.character (t * y)
      = 2 * LinearMap.trace K ↥(LinearMap.range (involutionProj σ t))
            ((σ y).restrict (range_involutionProj_invariant σ hy))
        - σ.character y := by
  have hσt : σ t = (2 : K) • involutionProj σ t - 1 := by
    rw [involutionProj, smul_smul, mul_inv_cancel₀ h2, one_smul]
    abel
  have hmul : σ (t * y) = (2 : K) • (involutionProj σ t ∘ₗ σ y) - σ y := by
    rw [map_mul, hσt]
    ext v
    simp [Module.End.mul_apply]
  rw [Representation.character, hmul, map_sub, map_smul, smul_eq_mul,
    trace_comp_eq_trace_restrict_range (isIdempotentElem_involutionProj σ h2 ht)]
  rfl

end OddOrder.RepresentationTheory
