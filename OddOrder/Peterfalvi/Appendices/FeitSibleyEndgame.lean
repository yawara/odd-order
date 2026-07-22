/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyXsetInduction

/-!
# Peterfalvi Appendix IV: the Feit–Sibley endgame (steps (4)–(8))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 148–150 (campaign issue 1054, endgame).  With `Q₁` a
non-abelian `p`-group, the two coherent families `𝒳 = 𝒮 − 𝒮(Z)` (reduction (3),
`xset_coherent_of_le_center_Q1`) and `𝒴 = 𝒮(Q')` (the Remark,
`ssetOf_Qder_coherent`) are combined into a single coherence of `𝒳 ∪ 𝒴`, which
then extends to `𝒮(S')` and, by reduction (2), to all of `𝒮`.

This file collects the self-contained pieces of the endgame; the coherence
assembly ((4) notation → (5) orthogonality → (6) `a ∣ λ ⟹ 𝒮` coherent → (7)
class-algebra congruence → (8) conclusion) is built on top.

* `x_eq_zero_or_x_one_of_norm_identity` — the (6) integer inequality core
  (p. 148): from the norm identity `1 + a² = (v,v) + a²(x−1)² + (m−1)x²a²` with
  `(v,v) ≥ 0`, `a ≥ 2` and `m ≥ 2`, the only solutions are `x = 0` or
  `x = 1 ∧ m = 2` (the latter reduces to the former by a sign swap of the `e'`).
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped commutatorElement

/-! ## The (6) integer inequality core (p. 148) -/

/-- **Peterfalvi (6) integer core** (p. 148): writing `χ₁(1) = a·d` and expanding
`(Ind(χ₁ − aη₁), Ind(χ₁ − aη₁)) = 1 + a²` through the orthogonal decomposition
`Ind(χ₁ − aη₁) = v − a·e'₁ + λ·∑ e'ᵢ` (with `λ = a·x`) gives the integer identity
`1 + a² = (v,v) + a²(x−1)² + (m−1)·x²·a²`.  Since `(v,v) ≥ 0`, `a ≥ 2` (as
`𝒳 ∩ 𝒴 = ∅` forces `a > 1`) and `m ≥ 2`, the bracket `(x−1)² + (m−1)x²` is at
most `1 + 1/a² < 2`, hence at most `1`: the only integer solutions are `x = 0`
or `x = 1 ∧ m = 2`. -/
theorem x_eq_zero_or_x_one_of_norm_identity {a m x nvv : ℤ}
    (ha : 2 ≤ a) (hm : 2 ≤ m) (hnvv : 0 ≤ nvv)
    (heq : 1 + a ^ 2 = nvv + a ^ 2 * (x - 1) ^ 2 + (m - 1) * x ^ 2 * a ^ 2) :
    x = 0 ∨ (x = 1 ∧ m = 2) := by
  -- `a² · ((x−1)² + (m−1)x²) ≤ 1 + a²`
  have hb : a ^ 2 * ((x - 1) ^ 2 + (m - 1) * x ^ 2) ≤ 1 + a ^ 2 := by nlinarith [heq, hnvv]
  -- integrality: the bracket is `≤ 1`
  have hk : (x - 1) ^ 2 + (m - 1) * x ^ 2 ≤ 1 := by
    by_contra h
    push Not at h
    have h2 : 2 ≤ (x - 1) ^ 2 + (m - 1) * x ^ 2 := h
    nlinarith [hb, ha, h2, mul_nonneg (sq_nonneg a)
      (by linarith : (0 : ℤ) ≤ (x - 1) ^ 2 + (m - 1) * x ^ 2 - 2)]
  -- `(m−1)x² ≥ 0`, so `(x−1)² ≤ 1`, whence `0 ≤ x ≤ 2`
  have hmx : (0 : ℤ) ≤ (m - 1) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  have hx1 : (x - 1) ^ 2 ≤ 1 := by linarith [hk, hmx]
  have hxlo : 0 ≤ x := by nlinarith [hx1, sq_nonneg (x - 1)]
  have hxhi : x ≤ 2 := by nlinarith [hx1, sq_nonneg (x - 1)]
  interval_cases x
  · exact Or.inl rfl
  · -- `x = 1`: the bracket is `m − 1 ≤ 1`, so `m = 2`
    refine Or.inr ⟨rfl, ?_⟩
    have : m - 1 ≤ 1 := by nlinarith [hk]
    omega
  · -- `x = 2`: the bracket is `1 + 4(m−1) ≥ 5 > 1`, impossible
    exfalso
    nlinarith [hk, hm]

/-- **Sign–degree bookkeeping core for Peterfalvi (5)** (p. 148): if the signed
irreducible constituents satisfy the `λ`-equality `e·f₁ = −(A·(e₁·f₂))` (the two
evaluations of `λ = (eᵢ − aᵢe₁, e'ⱼ)`), the `X`-side degree identity
`e·D₂ = A·(e₁·D₁)` (from `(eᵢ − aᵢe₁)(1) = 0`) and the `Y`-side degree identity
`f₂·D₁ = f₁·D₂` (from `(e'₂ − e'₁)(1) = 0`), with `e₁, f₁, f₂` signs and `A ≠ 0`,
then `D₂ = 0` — contradicting the positivity of the degree `D₂ = ξ(1)` at the
call site.  (This is sharper than the book's route via `aᵢ = 1` and
`e'₁(1) = 0`: the same three relations force the `X`-witness degree to vanish
directly.) -/
theorem eq_zero_of_signed_degree_relations {e e₁ f₁ f₂ A D₁ D₂ : ℂ}
    (he₁ : e₁ ^ 2 = 1) (hf₁ : f₁ ^ 2 = 1) (hf₂ : f₂ ^ 2 = 1) (hA : A ≠ 0)
    (H1 : e * f₁ = -(A * (e₁ * f₂)))
    (H2 : e * D₂ = A * (e₁ * D₁))
    (H3 : f₂ * D₁ = f₁ * D₂) : D₂ = 0 := by
  -- `A·(f₁D₁ + f₂D₂) = 0`, by eliminating `e` between `H1` and `H2`
  have hdag : f₁ * D₁ + f₂ * D₂ = 0 := by
    have hkey : A * (f₁ * D₁ + f₂ * D₂) = 0 := by
      linear_combination (-(e₁ * f₁)) * H2 + (e₁ * D₂) * H1
        - A * (f₁ * D₁ + f₂ * D₂) * he₁
    exact (mul_eq_zero.mp hkey).resolve_left hA
  -- combining with `H3` gives `2·D₂ = 0`
  have h2 : (2 : ℂ) * D₂ = 0 := by
    linear_combination f₂ * hdag - f₁ * H3 - D₂ * hf₁ - D₂ * hf₂
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · exact h

section SignedIrr

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]

open scoped Classical in
/-- Inner product of two signed irreducible characters:
`⟨ε•ξ, ε'•ξ'⟩ = ε·ε'·δ_{ξ,ξ'}` (the `star` on the right scalar is invisible for
integer signs).  Upstream candidate for `ZIrrFourier.lean` next to
`irreducibleCharacter_inner_eq_ite`. -/
theorem inner_zsmul_irreducible_eq (ε ε' : ℤ) (ξ ξ' : IrreducibleCharacter Γ) :
    ClassFunction.inner (ε • (ξ : ClassFunction Γ ℂ)) (ε' • (ξ' : ClassFunction Γ ℂ)) =
      (ε : ℂ) * (ε' : ℂ) * (if ξ = ξ' then 1 else 0) := by
  rw [← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction Γ ℂ),
    ← Int.cast_smul_eq_zsmul ℂ ε' (ξ' : ClassFunction Γ ℂ),
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, star_intCast,
    irreducibleCharacter_inner_eq_ite]
  ring

/-- **Residual orthogonality** (Peterfalvi (6), p. 148): subtracting the Fourier
components of `u` along a finite orthonormal family `w` leaves a residual
orthogonal to every member: `(u − ∑ⱼ (u,wⱼ)·wⱼ, wₖ) = 0`.  Upstream candidate
for `ZIrrFourier.lean`. -/
theorem inner_sub_sum_inner_smul_eq_zero {ι : Type*} {s : Finset ι}
    {w : ι → ClassFunction Γ ℂ}
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ClassFunction.inner (w i) (w j) = 0)
    (hnorm : ∀ j ∈ s, ClassFunction.inner (w j) (w j) = 1)
    (u : ClassFunction Γ ℂ) {k : ι} (hk : k ∈ s) :
    ClassFunction.inner (u - ∑ j ∈ s, ClassFunction.inner u (w j) • w j) (w k) = 0 := by
  rw [ClassFunction.inner_sub_left, inner_sum_left s _ _,
    Finset.sum_eq_single k
      (fun j hj hne => by
        rw [ClassFunction.inner_smul_left, horth j hj k hk hne, mul_zero])
      (fun h => absurd hk h),
    ClassFunction.inner_smul_left, hnorm k hk, mul_one, sub_self]

/-- **Bessel decomposition of the norm** (Peterfalvi (6), p. 148): for a finite
orthonormal family `w` and any `u`,
`(u, u) = (v, v) + ∑ⱼ (u,wⱼ)·star (u,wⱼ)` where `v = u − ∑ⱼ (u,wⱼ)·wⱼ` is the
residual.  Upstream candidate for `ZIrrFourier.lean`. -/
theorem inner_self_eq_residual_add_sum_inner_mul_star {ι : Type*} {s : Finset ι}
    {w : ι → ClassFunction Γ ℂ}
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ClassFunction.inner (w i) (w j) = 0)
    (hnorm : ∀ j ∈ s, ClassFunction.inner (w j) (w j) = 1)
    (u : ClassFunction Γ ℂ) :
    ClassFunction.inner u u =
      ClassFunction.inner (u - ∑ j ∈ s, ClassFunction.inner u (w j) • w j)
        (u - ∑ j ∈ s, ClassFunction.inner u (w j) • w j)
      + ∑ j ∈ s, ClassFunction.inner u (w j) * star (ClassFunction.inner u (w j)) := by
  set S : ClassFunction Γ ℂ := ∑ j ∈ s, ClassFunction.inner u (w j) • w j with hS
  set v : ClassFunction Γ ℂ := u - S with hv
  -- the residual is orthogonal to the projection, on both sides
  have hvw : ∀ k ∈ s, ClassFunction.inner v (w k) = 0 := fun k hk =>
    inner_sub_sum_inner_smul_eq_zero horth hnorm u hk
  have hvS : ClassFunction.inner v S = 0 := by
    rw [hS, inner_sum_right]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [ClassFunction.inner_smul_right, hvw j hj, mul_zero]
  have hSv : ClassFunction.inner S v = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hvS, star_zero]
  -- the projection's self-pairing is the diagonal sum
  have hSS : ClassFunction.inner S S = ∑ j ∈ s, ClassFunction.inner u (w j) *
      star (ClassFunction.inner u (w j)) := by
    rw [hS, inner_sum_left]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ClassFunction.inner_smul_left, inner_sum_right,
      Finset.sum_eq_single j
        (fun k hk hne => by
          rw [ClassFunction.inner_smul_right, horth j hj k hk (Ne.symm hne), mul_zero])
        (fun h => absurd hj h),
      ClassFunction.inner_smul_right, hnorm j hj]
    ring
  have hu : u = v + S := by rw [hv]; abel
  calc ClassFunction.inner u u = ClassFunction.inner (v + S) (v + S) := by rw [← hu]
    _ = ClassFunction.inner v v + ClassFunction.inner v S +
        (ClassFunction.inner S v + ClassFunction.inner S S) := by
        rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
          ClassFunction.inner_add_right]
    _ = _ := by rw [hvS, hSv, hSS, add_zero, zero_add]

/-! ### Span-transport helpers for the (6) coherence assembly

A `ℤ`-linear map that preserves the gram matrix (resp. `ℤ[Irr]`-valuedness) on the
members of a set `T` does so on all of `ℤ[T]`; an orthonormal finite `T` gives
integer Fourier coefficients and the reconstruction `φ = ∑_μ (φ,μ)·μ` on `ℤ[T]`.
These extend the member-level facts of the witness assignments to the lattice. -/

section SpanTransport

variable {Δ : Type*} [Group Δ] [Fintype Δ] [Invertible (Nat.card Δ : ℂ)]

/-- A `ℤ`-linear map preserving inner products on the members of `T` preserves
them on all of `ℤ[T]`. -/
theorem inner_map_eq_on_zSpan (F : ClassFunction Γ ℂ →ₗ[ℤ] ClassFunction Δ ℂ)
    {T : Set (ClassFunction Γ ℂ)}
    (h : ∀ μ ∈ T, ∀ ν ∈ T, ClassFunction.inner (F μ) (F ν) = ClassFunction.inner μ ν) :
    ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := Γ) T,
      ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan (L := Γ) T,
      ClassFunction.inner (F φ) (F ψ) = ClassFunction.inner φ ψ := by
  have hright : ∀ μ ∈ T, ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan (L := Γ) T,
      ClassFunction.inner (F μ) (F ψ) = ClassFunction.inner μ ψ := by
    intro μ hμ ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ν hν => exact h μ hμ ν hν
    | zero => rw [map_zero, ClassFunction.inner_zero_right, ClassFunction.inner_zero_right]
    | add ψ₁ ψ₂ _ _ ih₁ ih₂ =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, ih₁, ih₂]
    | smul c ψ₀ _ ih =>
        rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ c (F ψ₀), ← Int.cast_smul_eq_zsmul ℂ c ψ₀,
          OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, ih]
  intro φ hφ ψ hψ
  induction hφ using Submodule.span_induction with
  | mem μ hμ => exact hright μ hμ ψ hψ
  | zero => rw [map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
  | add φ₁ φ₂ _ _ ih₁ ih₂ =>
      rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left, ih₁, ih₂]
  | smul c φ₀ _ ih =>
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℂ c (F φ₀), ← Int.cast_smul_eq_zsmul ℂ c φ₀,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, ih]

omit [Fintype Γ] [Invertible (Nat.card Γ : ℂ)] [Fintype Δ] [Invertible (Nat.card Δ : ℂ)] in
/-- A `ℤ`-linear map with `ℤ[Irr]`-values on the members of `T` has `ℤ[Irr]`-values
on all of `ℤ[T]`. -/
theorem map_mem_ZIrr_on_zSpan (F : ClassFunction Γ ℂ →ₗ[ℤ] ClassFunction Δ ℂ)
    {T : Set (ClassFunction Γ ℂ)} (h : ∀ μ ∈ T, F μ ∈ ZIrr Δ) :
    ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := Γ) T, F φ ∈ ZIrr Δ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem μ hμ => exact h μ hμ
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add φ₁ φ₂ _ _ ih₁ ih₂ => rw [map_add]; exact Submodule.add_mem _ ih₁ ih₂
  | smul c φ₀ _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

/-- On `ℤ[T]` with integer member gram matrix, all Fourier coefficients against
members are integers. -/
theorem exists_int_inner_of_mem_zSpan {T : Set (ClassFunction Γ ℂ)}
    (hgram : ∀ ν ∈ T, ∀ μ ∈ T, ∃ c : ℤ, ClassFunction.inner ν μ = (c : ℂ)) :
    ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := Γ) T, ∀ μ ∈ T,
      ∃ c : ℤ, ClassFunction.inner φ μ = (c : ℂ) := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem ν hν => exact fun μ hμ => hgram ν hν μ hμ
  | zero => exact fun μ hμ => ⟨0, by rw [ClassFunction.inner_zero_left, Int.cast_zero]⟩
  | add φ₁ φ₂ _ _ ih₁ ih₂ =>
      intro μ hμ
      obtain ⟨c₁, hc₁⟩ := ih₁ μ hμ
      obtain ⟨c₂, hc₂⟩ := ih₂ μ hμ
      exact ⟨c₁ + c₂, by rw [ClassFunction.inner_add_left, hc₁, hc₂, Int.cast_add]⟩
  | smul c φ₀ _ ih =>
      intro μ hμ
      obtain ⟨c₀, hc₀⟩ := ih μ hμ
      refine ⟨c * c₀, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ c φ₀, ClassFunction.inner_smul_left, hc₀, Int.cast_mul]

/-- **Reconstruction on `ℤ[T]`** for a finite orthonormal `T`: every lattice
element is the sum of its Fourier components, `φ = ∑_{μ ∈ T} (φ, μ)·μ`. -/
theorem eq_sum_inner_smul_of_mem_zSpan {T : Set (ClassFunction Γ ℂ)}
    {s : Finset (ClassFunction Γ ℂ)}
    (hsT : ∀ {μ : ClassFunction Γ ℂ}, μ ∈ s ↔ μ ∈ T)
    (hnorm : ∀ μ ∈ T, ClassFunction.inner μ μ = 1)
    (horth : ∀ μ ∈ T, ∀ ν ∈ T, μ ≠ ν → ClassFunction.inner μ ν = 0) :
    ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := Γ) T,
      φ = ∑ μ ∈ s, ClassFunction.inner φ μ • μ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem ν hν =>
      rw [Finset.sum_eq_single ν
        (fun μ hμ hne => by rw [horth ν hν μ (hsT.mp hμ) (Ne.symm hne), zero_smul])
        (fun h => absurd (hsT.mpr hν) h), hnorm ν hν, one_smul]
  | zero =>
      simp only [ClassFunction.inner_zero_left, zero_smul, Finset.sum_const_zero]
  | add φ₁ φ₂ _ _ ih₁ ih₂ =>
      conv_lhs => rw [ih₁, ih₂]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      rw [ClassFunction.inner_add_left, add_smul]
  | smul c φ₀ _ ih =>
      conv_lhs => rw [ih]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      rw [← Int.cast_smul_eq_zsmul ℂ c (ClassFunction.inner φ₀ μ • μ),
        ← Int.cast_smul_eq_zsmul ℂ c φ₀, ClassFunction.inner_smul_left, smul_smul]

omit [Fintype Γ] [Invertible (Nat.card Γ : ℂ)] in
/-- `ℤ`-multiples stay in the supported lattice. -/
theorem zsmul_mem_zSupportedSpan {T : Set (ClassFunction Γ ℂ)} {A : Set Γ}
    {φ : ClassFunction Γ ℂ} (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := Γ) T A)
    (n : ℤ) : n • φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := Γ) T A := by
  refine ⟨Submodule.smul_mem _ _ hφ.1, fun x hx => hφ.2 ?_⟩
  rw [ClassFunction.mem_support] at hx ⊢
  intro h0
  apply hx
  rw [← Int.cast_smul_eq_zsmul ℂ n φ, ClassFunction.smul_apply, h0, mul_zero]

/-- **The member-assignment extension map**: `φ ↦ ∑_{μ ∈ s} (φ, μ)·W(μ)` — the
`m`-fold analogue of the rank-2 `retarget`, sending each member `μ` of an
orthonormal family to its prescribed witness `W μ`.  This is the coherent
extension of the Peterfalvi (6) union `𝒳 ∪ 𝒴`. -/
noncomputable def memberAssignmentMap (s : Finset (ClassFunction Γ ℂ))
    (W : ClassFunction Γ ℂ → ClassFunction Δ ℂ) :
    ClassFunction Γ ℂ →ₗ[ℤ] ClassFunction Δ ℂ :=
  ∑ μ ∈ s, (OddOrder.Peterfalvi.S07.IntegralCharacterMap.innerLeftℤ (L := Γ) μ).smulRight (W μ)

omit [Fintype Δ] [Invertible (Nat.card Δ : ℂ)] in
theorem memberAssignmentMap_apply (s : Finset (ClassFunction Γ ℂ))
    (W : ClassFunction Γ ℂ → ClassFunction Δ ℂ) (φ : ClassFunction Γ ℂ) :
    memberAssignmentMap s W φ = ∑ μ ∈ s, ClassFunction.inner φ μ • W μ := by
  simp [memberAssignmentMap, LinearMap.sum_apply, LinearMap.smulRight_apply]

omit [Fintype Δ] [Invertible (Nat.card Δ : ℂ)] in
/-- On a member of the orthonormal family, the assignment map collapses to the
prescribed witness: `F μ₀ = W μ₀`. -/
theorem memberAssignmentMap_apply_of_mem {T : Set (ClassFunction Γ ℂ)}
    {s : Finset (ClassFunction Γ ℂ)}
    (hsT : ∀ {μ : ClassFunction Γ ℂ}, μ ∈ s ↔ μ ∈ T)
    (hnorm : ∀ μ ∈ T, ClassFunction.inner μ μ = 1)
    (horth : ∀ μ ∈ T, ∀ ν ∈ T, μ ≠ ν → ClassFunction.inner μ ν = 0)
    (W : ClassFunction Γ ℂ → ClassFunction Δ ℂ)
    {μ₀ : ClassFunction Γ ℂ} (hμ₀ : μ₀ ∈ T) :
    memberAssignmentMap s W μ₀ = W μ₀ := by
  rw [memberAssignmentMap_apply, Finset.sum_eq_single μ₀
    (fun μ hμ hne => by rw [horth μ₀ hμ₀ μ (hsT.mp hμ) (Ne.symm hne), zero_smul])
    (fun h => absurd (hsT.mpr hμ₀) h), hnorm μ₀ hμ₀, one_smul]

end SpanTransport

end SignedIrr

/-! ## The endgame central subgroup `Z = ⁅Q₁, Q₁⁆ ⊓ Z(Q₁)` (Peterfalvi (4), p. 147)

For a non-abelian `p`-group `Q₁` the subgroup `Z = [Q₁,Q₁] ∩ Z(Q₁)` is a
nontrivial `H`-invariant central subgroup of `Q₁`; it supplies the `Z` of
reduction (3) (`xset_coherent_of_le_center_Q1`), so `𝒳 = 𝒮 − 𝒮(Z)` is coherent. -/

namespace Hypothesis

variable {G : Type*} [Group G] (hyp : Hypothesis G)

/-- **The endgame central subgroup** `Z = ⁅Q₁, Q₁⁆ ⊓ C_G(Q₁)` (Peterfalvi (4)).
The intersection with the centralizer realises the `Z(Q₁)`-part: `Z ≤ Q₁` and `Z`
centralises `Q₁`, i.e. `Z ≤ Z(Q₁)`. -/
def endgameZ : Subgroup G := ⁅hyp.Q1, hyp.Q1⁆ ⊓ Subgroup.centralizer (hyp.Q1 : Set G)

/-- `⁅Q₁, Q₁⁆ ≤ Q₁`: a subgroup is closed under commutators. -/
theorem commutator_Q1_le_Q1 : ⁅hyp.Q1, hyp.Q1⁆ ≤ hyp.Q1 :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact hyp.Q1.mul_mem (hyp.Q1.mul_mem (hyp.Q1.mul_mem ha hb) (hyp.Q1.inv_mem ha))
      (hyp.Q1.inv_mem hb)

theorem endgameZ_le_Q1 : hyp.endgameZ ≤ hyp.Q1 := inf_le_left.trans hyp.commutator_Q1_le_Q1

/-- **`Z` centralises `Q₁`** (`Z ≤ Z(Q₁)`): `⁅z, y⁆ = 1` for `z ∈ Z`, `y ∈ Q₁`. -/
theorem endgameZ_centralizes {z : G} (hz : z ∈ hyp.endgameZ) {y : G} (hy : y ∈ hyp.Q1) :
    ⁅z, y⁆ = 1 := by
  have hyz : ⁅y, z⁆ = 1 :=
    (Subgroup.mem_centralizer_iff_commutator_eq_one.mp hz.2) y hy
  have : Commute z y := (commutatorElement_eq_one_iff_commute.mp hyz).symm
  exact commutatorElement_eq_one_iff_commute.mpr this

/-- The `↥Q₁`-level commutator maps onto `⁅Q₁, Q₁⁆`. -/
theorem map_commutator_Q1 :
    (commutator ↥hyp.Q1).map hyp.Q1.subtype = ⁅hyp.Q1, hyp.Q1⁆ := by
  rw [commutator_def, Subgroup.map_commutator]
  simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **`Z ≠ ⊥`** for a non-abelian `p`-group `Q₁` (Peterfalvi (4)): the nontrivial
normal subgroup `[Q₁,Q₁]` of the `p`-group `Q₁` meets the centre nontrivially
(`IsPGroup.normal_inf_center_nontrivial`), and the injective `Q₁ ↪ G` carries the
nontriviality up to `Z`. -/
theorem endgameZ_ne_bot [Finite G] {p : ℕ} (hp : p.Prime) (hQ1p : IsPGroup p ↥hyp.Q1)
    (hnonab : ⁅hyp.Q1, hyp.Q1⁆ ≠ ⊥) : hyp.endgameZ ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `commutator ↥Q₁` is nontrivial, else `⁅Q₁,Q₁⁆ = ⊥`
  have hcomm_nt : Nontrivial (commutator ↥hyp.Q1) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hcbot
    exact hnonab (by rw [← hyp.map_commutator_Q1, hcbot, Subgroup.map_bot])
  -- `[Q₁,Q₁] ⊓ Z(Q₁) ≠ ⊥` in `↥Q₁`
  have hK : (commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1 ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    exact OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hQ1p hcomm_nt
  -- its `G`-image sits inside `Z` and is nontrivial (subtype injective)
  have hmaple : ((commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1).map hyp.Q1.subtype
      ≤ hyp.endgameZ := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzc, hzcent⟩ := Subgroup.mem_inf.mp hz
    refine ⟨?_, ?_⟩
    · exact hyp.map_commutator_Q1 ▸ Subgroup.mem_map_of_mem hyp.Q1.subtype hzc
    · refine Subgroup.mem_centralizer_iff_commutator_eq_one.mpr fun g hg => ?_
      have hcz : Commute (⟨g, hg⟩ : ↥hyp.Q1) z :=
        (Subgroup.mem_center_iff.mp hzcent) (⟨g, hg⟩ : ↥hyp.Q1)
      have hcomm : Commute g (hyp.Q1.subtype z) := by
        simpa using hcz.map hyp.Q1.subtype
      exact commutatorElement_eq_one_iff_commute.mpr hcomm
  have hmapne : ((commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1).map hyp.Q1.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff]
    exact hK
  exact fun hbot => hmapne (le_bot_iff.mp (by rw [← hbot]; exact hmaple))

/-- **`Z` is `H`-invariant** (element form): `h · x · h⁻¹ ∈ Z` for `h ∈ H`,
`x ∈ Z`.  Both factors are `H`-invariant — `⁅Q₁,Q₁⁆` because `Q₁ ⊴ H`
(`Q1_map_conj_eq` + `map_commutator`), and `C_G(Q₁)` because conjugation permutes
`Q₁`. -/
theorem endgameZ_conj_mem_of_mem_H [Finite G] {h : G} (hh : h ∈ hyp.H)
    {x : G} (hx : x ∈ hyp.endgameZ) : h * x * h⁻¹ ∈ hyp.endgameZ := by
  obtain ⟨hxc, hxcent⟩ := hx
  refine ⟨?_, ?_⟩
  · -- `h·x·h⁻¹ ∈ ⁅Q₁,Q₁⁆`
    have hφ : Subgroup.map (MulAut.conj h).toMonoidHom ⁅hyp.Q1, hyp.Q1⁆ = ⁅hyp.Q1, hyp.Q1⁆ := by
      rw [Subgroup.map_commutator, hyp.Q1_map_conj_eq hh]
    have hmem : (MulAut.conj h) x ∈ ⁅hyp.Q1, hyp.Q1⁆ :=
      hφ ▸ Subgroup.mem_map_of_mem _ hxc
    simpa [MulAut.conj] using hmem
  · -- `h·x·h⁻¹ ∈ C_G(Q₁)`
    refine Subgroup.mem_centralizer_iff_commutator_eq_one.mpr fun y hy => ?_
    have hy' : h⁻¹ * y * h ∈ hyp.Q1 := by
      have := hyp.Q1_normal_in_H (hyp.H.inv_mem hh) hy
      simpa using this
    -- `x` commutes with `h⁻¹yh`; conjugating by `h` gives `hxh⁻¹` commutes with `y`
    have hxc' : ⁅h⁻¹ * y * h, x⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one.mp hxcent) (h⁻¹ * y * h) hy'
    have hc : Commute (h⁻¹ * y * h) x := commutatorElement_eq_one_iff_commute.mp hxc'
    have hcm := hc.map (MulAut.conj h).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcm
    have hyeq : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
    rw [hyeq] at hcm
    exact commutatorElement_eq_one_iff_commute.mpr hcm

/-! ## The two coherent families `𝒳` and `𝒴` (Peterfalvi (4), p. 147) -/

section Coherence

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

/-- **`𝒳 = 𝒮 − 𝒮(Z) = XsetOf ⊥ Z` is coherent** (Peterfalvi (4), reduction (3) at
the endgame `Z = ⁅Q₁,Q₁⁆ ∩ Z(Q₁)`): the four `Z`-hypotheses of
`xset_coherent_of_le_center_Q1` are the `endgameZ_*` facts, and the three `Normal`
instances descend from `Sder`, `Z` and `S` being `H`-invariant. -/
theorem endgame_Xset_coherent (hd : Odd hyp.d) {p : ℕ} (hp : p.Prime)
    (hQ1p : IsPGroup p ↥hyp.Q1) (hnonab : ⁅hyp.Q1, hyp.Q1⁆ ≠ ⊥) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf (⊥ : Subgroup G) hyp.endgameZ) hyp.A) := by
  haveI : (hyp.Sder.subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx => hyp.Sder_conj_mem_of_mem_H hh hx
  haveI : (hyp.endgameZ.subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx => hyp.endgameZ_conj_mem_of_mem_H hh hx
  haveI : ((hyp.S ⊔ hyp.endgameZ).subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx =>
      conj_mem_sup (fun y hy => hyp.S_normal_in_H hh hy)
        (fun y hy => hyp.endgameZ_conj_mem_of_mem_H hh hy) hx
  exact hyp.xset_coherent_of_le_center_Q1 hd hp hQ1p hyp.endgameZ_le_Q1
    (hyp.endgameZ_ne_bot hp hQ1p hnonab)
    (fun z hz y hy => hyp.endgameZ_centralizes hz hy)
    (fun h hh x hx => hyp.endgameZ_conj_mem_of_mem_H hh hx)

omit [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)] in
/-- **The coherence witness at an irreducible member** (Peterfalvi (4)): the
coherent extension of an irreducible `χ ∈ S` is `±` a single irreducible
character of `G` — `extension χ = ε • ξ` with `ε ∈ {±1}`, `ξ ∈ Irr G`.  The
isometry (`extension_inner_eq`) sends `‖χ‖² = 1` to `‖extension χ‖² = 1`, and
`extension χ ∈ ℤ[Irr G]` (`extension_mem_ZIrr`), so
`exists_zsmul_irreducibleCharacter_of_inner_self_one` gives the signed
irreducible.  This yields the witnesses `eᵢ` (from `𝒳`) and `e'ⱼ` (from `𝒴`). -/
theorem coherent_extension_eq_zsmul_irr {S : Set (ClassFunction ↥hyp.H ℂ)} {A : Set ↥hyp.H}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ S) (hχirr : IsIrreducibleCharacter χ) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧ hcoh.extension χ = ε • (ξ : ClassFunction G ℂ) := by
  have hχspan : χ ∈ OddOrder.Peterfalvi.S07.zSpan S := Submodule.subset_span hχS
  have hmem : hcoh.extension χ ∈ ZIrr G := hcoh.extension_mem_ZIrr χ hχspan
  have hnorm : ClassFunction.inner (hcoh.extension χ) (hcoh.extension χ) = 1 := by
    rw [hcoh.extension_inner_eq χ χ hχspan hχspan]
    exact hχirr.inner_self_eq_one
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one hmem hnorm

/-! ### Peterfalvi (5): the witnesses of `𝒳` and `𝒴` are orthogonal (p. 148)

Both coherent extensions agree with `τ = Ind_H^G` on `A`-supported lattice
elements (`extends_on_supported`), and `τ` is a **global** isometry on the
`A`-supported `𝒮`-sublattice (`tau_inner_eq_of_supported_Sset`), so
cross-family inner products of keystone differences transport back to `H`,
where they vanish (`𝒳 ∩ 𝒴 = ∅` and distinct irreducibles are orthogonal). -/

/-- **Cross-family isometry transport**: for `χ − a•χ₁` supported in `ℤ[X, A]`
and `η − η'` supported in `ℤ[Y, A]` with `X, Y ⊆ 𝒮` disjoint,
`⟨E χ − a·E χ₁, E' η − E' η'⟩ = ⟨χ − a·χ₁, η − η'⟩ = 0`. -/
theorem cross_inner_extension_diff_eq_zero [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ χ₁ : ClassFunction ↥hyp.H ℂ} (hχX : χ ∈ X) (hχ₁X : χ₁ ∈ X) {a : ℕ}
    (hsuppX : χ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {η η' : ClassFunction ↥hyp.H ℂ} (hηY : η ∈ Y) (hη'Y : η' ∈ Y)
    (hsuppY : η - η' ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A) :
    ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η - hcohY.extension η') = 0 := by
  -- both extensions agree with `τ` on the supported differences
  have hEX : hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁ = hyp.tau (χ - a • χ₁) := by
    rw [← hcohX.extends_on_supported _ hsuppX, map_sub, map_nsmul,
      Nat.cast_smul_eq_nsmul ℂ a (hcohX.extension χ₁)]
  have hEY : hcohY.extension η - hcohY.extension η' = hyp.tau (η - η') := by
    rw [← hcohY.extends_on_supported _ hsuppY, map_sub]
  rw [hEX, hEY, hyp.tau_inner_eq_of_supported_Sset
    (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hXS hsuppX)
    (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hYS hsuppY)]
  -- the four member-level cross inner products vanish
  have horth : ∀ φ ∈ X, ∀ ψ ∈ Y, ClassFunction.inner φ ψ = 0 := fun φ hφ ψ hψ =>
    hyp.Sset_pairwiseOrthogonal (hXS hφ) (hYS hψ) (fun h => hdisj φ hφ (h ▸ hψ))
  rw [← Nat.cast_smul_eq_nsmul ℂ a χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left]
  rw [horth χ hχX η hηY, horth χ hχX η' hη'Y, horth χ₁ hχ₁X η hηY, horth χ₁ hχ₁X η' hη'Y]
  ring

/-- **Peterfalvi (5), core case** (p. 148): `λ = (eᵢ − aᵢe₁, e'₁) = 0`.  Assuming
`λ ≠ 0`, the two evaluations of `λ` (at `η₁` and `η₂`, equal by the cross
isometry) force the `𝒴`-witnesses `ξ'₁ ≠ ξ'₂` to exhaust the two `𝒳`-witness
irreducibles `{ξχ, ξ₁}`; the sign–degree relations then make the degree `ξχ(1)`
vanish (`eq_zero_of_signed_degree_relations`), a contradiction. -/
theorem cross_inner_extension_diff_right_eq_zero [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ χ₁ : ClassFunction ↥hyp.H ℂ} (hχX : χ ∈ X) (hχ₁X : χ₁ ∈ X) (hχne : χ ≠ χ₁)
    {a : ℕ} (ha : 0 < a)
    (hsuppX : χ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {η₁ η₂ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hηne : η₂ ≠ η₁)
    (hsuppY : η₂ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A) :
    ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η₁) = 0 := by
  classical
  by_contra hlam
  -- signed-irreducible witnesses (Peterfalvi (4))
  obtain ⟨εχ, ξχ, hεχ, hEχ⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχX (hXS hχX).1
  obtain ⟨ε₁, ξ₁, hε₁, hEχ₁⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχ₁X (hXS hχ₁X).1
  obtain ⟨f₁, ξ'₁, hf₁, hE'₁⟩ := hyp.coherent_extension_eq_zsmul_irr hcohY hη₁Y (hYS hη₁Y).1
  obtain ⟨f₂, ξ'₂, hf₂, hE'₂⟩ := hyp.coherent_extension_eq_zsmul_irr hcohY hη₂Y (hYS hη₂Y).1
  -- distinctness of the witnesses within each family (lattice isometry)
  have hξne : ξχ ≠ ξ₁ := by
    intro h
    have h0 : ClassFunction.inner (hcohX.extension χ) (hcohX.extension χ₁) = 0 := by
      rw [hcohX.extension_inner_eq χ χ₁ (Submodule.subset_span hχX)
        (Submodule.subset_span hχ₁X)]
      exact hyp.Sset_pairwiseOrthogonal (hXS hχX) (hXS hχ₁X) hχne
    rw [hEχ, hEχ₁, h, inner_zsmul_irreducible_eq, if_pos rfl, mul_one] at h0
    rcases hεχ with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> norm_num at h0
  have hξ'ne : ξ'₂ ≠ ξ'₁ := by
    intro h
    have h0 : ClassFunction.inner (hcohY.extension η₂) (hcohY.extension η₁) = 0 := by
      rw [hcohY.extension_inner_eq η₂ η₁ (Submodule.subset_span hη₂Y)
        (Submodule.subset_span hη₁Y)]
      exact hyp.Sset_pairwiseOrthogonal (hYS hη₂Y) (hYS hη₁Y) hηne
    rw [hE'₂, hE'₁, h, inner_zsmul_irreducible_eq, if_pos rfl, mul_one] at h0
    rcases hf₂ with rfl | rfl <;> rcases hf₁ with rfl | rfl <;> norm_num at h0
  -- `λ` evaluated at `η₂` equals `λ` evaluated at `η₁`
  have hlam2 : ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η₂) =
      ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
        (hcohY.extension η₁) := by
    have h := hyp.cross_inner_extension_diff_eq_zero hXS hYS hdisj hcohX hcohY hχX hχ₁X
      hsuppX hη₂Y hη₁Y hsuppY
    rw [ClassFunction.inner_sub_right] at h
    exact sub_eq_zero.mp h
  -- the value of `λ` against a signed irreducible
  have hval : ∀ (f : ℤ) (ξ' : IrreducibleCharacter G),
      ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
        (f • (ξ' : ClassFunction G ℂ)) =
      (εχ : ℂ) * (f : ℂ) * (if ξχ = ξ' then 1 else 0)
        - (a : ℂ) * ((ε₁ : ℂ) * (f : ℂ) * (if ξ₁ = ξ' then 1 else 0)) := by
    intro f ξ'
    rw [hEχ, hEχ₁, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      inner_zsmul_irreducible_eq, inner_zsmul_irreducible_eq]
  -- `λ ≠ 0` forces `ξ'₁, ξ'₂ ∈ {ξχ, ξ₁}`
  have hmem₁ : ξχ = ξ'₁ ∨ ξ₁ = ξ'₁ := by
    by_contra hc
    push Not at hc
    apply hlam
    rw [hE'₁, hval, if_neg hc.1, if_neg hc.2]
    ring
  have hmem₂ : ξχ = ξ'₂ ∨ ξ₁ = ξ'₂ := by
    by_contra hc
    push Not at hc
    apply hlam
    rw [← hlam2, hE'₂, hval, if_neg hc.1, if_neg hc.2]
    ring
  -- degree data of the `𝒳`-witnesses
  obtain ⟨dχ, hdχpos, hdχeq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξχ
  have hdχne : (ξχ : ClassFunction G ℂ) (1 : G) ≠ 0 := by
    rw [hdχeq]
    exact_mod_cast hdχpos.ne'
  -- `(E χ − a·E χ₁)(1) = 0` (the difference is `τ` of a degree-zero element)
  have hv1 : (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁) (1 : G) = 0 := by
    have hEX : hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁ = hyp.tau (χ - a • χ₁) := by
      rw [← hcohX.extends_on_supported _ hsuppX, map_sub, map_nsmul,
        Nat.cast_smul_eq_nsmul ℂ a (hcohX.extension χ₁)]
    rw [hEX]
    refine hyp.tau_apply_one ?_
    by_contra h0
    exact hyp.one_notMem_A (hsuppX.2 (ClassFunction.mem_support.mpr h0))
  have hH2 : (εχ : ℂ) * (ξχ : ClassFunction G ℂ) 1 =
      (a : ℂ) * ((ε₁ : ℂ) * (ξ₁ : ClassFunction G ℂ) 1) := by
    rw [hEχ, hEχ₁, ← Int.cast_smul_eq_zsmul ℂ εχ (ξχ : ClassFunction G ℂ),
      ← Int.cast_smul_eq_zsmul ℂ ε₁ (ξ₁ : ClassFunction G ℂ), ClassFunction.sub_apply,
      ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.smul_apply,
      sub_eq_zero] at hv1
    exact hv1
  -- `(E' η₂ − E' η₁)(1) = 0` likewise
  have hw1' : (hcohY.extension η₂ - hcohY.extension η₁) (1 : G) = 0 := by
    have hEY : hcohY.extension η₂ - hcohY.extension η₁ = hyp.tau (η₂ - η₁) := by
      rw [← hcohY.extends_on_supported _ hsuppY, map_sub]
    rw [hEY]
    refine hyp.tau_apply_one ?_
    by_contra h0
    exact hyp.one_notMem_A (hsuppY.2 (ClassFunction.mem_support.mpr h0))
  have hw1 : (f₂ : ℂ) * (ξ'₂ : ClassFunction G ℂ) 1 =
      (f₁ : ℂ) * (ξ'₁ : ClassFunction G ℂ) 1 := by
    rw [hE'₂, hE'₁, ← Int.cast_smul_eq_zsmul ℂ f₂ (ξ'₂ : ClassFunction G ℂ),
      ← Int.cast_smul_eq_zsmul ℂ f₁ (ξ'₁ : ClassFunction G ℂ), ClassFunction.sub_apply,
      ClassFunction.smul_apply, ClassFunction.smul_apply, sub_eq_zero] at hw1'
    exact hw1'
  -- sign squares and `a ≠ 0`
  have hε₁2 : (ε₁ : ℂ) ^ 2 = 1 := by rcases hε₁ with rfl | rfl <;> norm_num
  have hf₁2 : (f₁ : ℂ) ^ 2 = 1 := by rcases hf₁ with rfl | rfl <;> norm_num
  have hf₂2 : (f₂ : ℂ) ^ 2 = 1 := by rcases hf₂ with rfl | rfl <;> norm_num
  have haC : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  -- case analysis: `{ξ'₁, ξ'₂} = {ξχ, ξ₁}` in one of the two orders
  rcases hmem₁ with h1 | h1 <;> rcases hmem₂ with h2 | h2
  · exact hξ'ne (h2.symm.trans h1)
  · -- `ξ'₁ = ξχ`, `ξ'₂ = ξ₁`: `λ@η₁ = εχ·f₁`, `λ@η₂ = −a·ε₁·f₂`
    have hL : (εχ : ℂ) * (f₁ : ℂ) = -((a : ℂ) * ((ε₁ : ℂ) * (f₂ : ℂ))) := by
      have h := hlam2
      rw [hE'₂, hE'₁, hval, hval, if_pos h1, if_neg (fun hh => hξne (hh.trans h2.symm)),
        if_pos h2, if_neg (fun hh => hξne (h1.trans hh.symm))] at h
      linear_combination -h
    have hH3 : (f₂ : ℂ) * (ξ₁ : ClassFunction G ℂ) 1 =
        (f₁ : ℂ) * (ξχ : ClassFunction G ℂ) 1 := by
      rw [← h1, ← h2] at hw1
      exact hw1
    exact hdχne (eq_zero_of_signed_degree_relations hε₁2 hf₁2 hf₂2 haC hL hH2 hH3)
  · -- `ξ'₁ = ξ₁`, `ξ'₂ = ξχ`: `λ@η₁ = −a·ε₁·f₁`, `λ@η₂ = εχ·f₂`
    have hL : (εχ : ℂ) * (f₂ : ℂ) = -((a : ℂ) * ((ε₁ : ℂ) * (f₁ : ℂ))) := by
      have h := hlam2
      rw [hE'₂, hE'₁, hval, hval, if_pos h2, if_neg (fun hh => hξne (h2.trans hh.symm)),
        if_pos h1, if_neg (fun hh => hξne (hh.trans h1.symm))] at h
      linear_combination h
    have hH3 : (f₁ : ℂ) * (ξ₁ : ClassFunction G ℂ) 1 =
        (f₂ : ℂ) * (ξχ : ClassFunction G ℂ) 1 := by
      rw [← h1, ← h2] at hw1
      exact hw1.symm
    exact hdχne (eq_zero_of_signed_degree_relations hε₁2 hf₂2 hf₁2 haC hL hH2 hH3)
  · exact hξ'ne (h2.symm.trans h1)

/-- **Peterfalvi (5), transported to any `η ∈ 𝒴`**: `(eᵢ − aᵢe₁, e'ⱼ) = 0` for
every `j` (the `η₁`-value vanishes by the core case, and the cross isometry
makes the pairing independent of `j`). -/
theorem cross_inner_extension_diff_any_eq_zero [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ χ₁ : ClassFunction ↥hyp.H ℂ} (hχX : χ ∈ X) (hχ₁X : χ₁ ∈ X) (hχne : χ ≠ χ₁)
    {a : ℕ} (ha : 0 < a)
    (hsuppX : χ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {η₁ η₂ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hηne : η₂ ≠ η₁)
    (hsuppY : η₂ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A)
    {η : ClassFunction ↥hyp.H ℂ} (hηY : η ∈ Y)
    (hsuppη : η - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A) :
    ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η) = 0 := by
  have h₁ := hyp.cross_inner_extension_diff_right_eq_zero hXS hYS hdisj hcohX hcohY
    hχX hχ₁X hχne ha hsuppX hη₁Y hη₂Y hηne hsuppY
  have h₂ := hyp.cross_inner_extension_diff_eq_zero hXS hYS hdisj hcohX hcohY hχX hχ₁X
    hsuppX hηY hη₁Y hsuppη
  rw [ClassFunction.inner_sub_right, h₁, sub_zero] at h₂
  exact h₂

/-- **Peterfalvi (5)** (p. 148): the coherence witnesses of two disjoint coherent
subfamilies `𝒳, 𝒴 ⊆ 𝒮` are orthogonal — `(eᵢ, e'ⱼ) = 0` for all `i, j`, where
`eᵢ = E(χᵢ)`, `e'ⱼ = E'(ηⱼ)` are the two coherent extensions.  Hypotheses:
`𝒳` has an anchor `χ₁` with all scaled differences `χ − a·χ₁` `A`-supported in
`ℤ[𝒳]` and a second member `χ₂ ≠ χ₁`; `𝒴` has equal degrees (differences
`η − η₁` `A`-supported in `ℤ[𝒴]`) and a second member `η₂ ≠ η₁`. -/
theorem cross_extension_inner_eq_zero [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁X : χ₁ ∈ X)
    (hXdiff : ∀ φ ∈ X, ∃ a : ℕ, 0 < a ∧
      φ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {χ₂ : ClassFunction ↥hyp.H ℂ} (hχ₂X : χ₂ ∈ X) (hχ₂ne : χ₂ ≠ χ₁)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y)
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A)
    {η₂ : ClassFunction ↥hyp.H ℂ} (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    {χ η : ClassFunction ↥hyp.H ℂ} (hχX : χ ∈ X) (hηY : η ∈ Y) :
    ClassFunction.inner (hcohX.extension χ) (hcohY.extension η) = 0 := by
  -- Step 1: the anchor pairing `⟨E χ₁, E' η⟩` vanishes
  obtain ⟨a₂, ha₂, hsupp₂⟩ := hXdiff χ₂ hχ₂X
  have hlamEta : ClassFunction.inner (hcohX.extension χ₂ - (a₂ : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η) = 0 :=
    hyp.cross_inner_extension_diff_any_eq_zero hXS hYS hdisj hcohX hcohY hχ₂X hχ₁X hχ₂ne
      ha₂ hsupp₂ hη₁Y hη₂Y hη₂ne (hYdiff η₂ hη₂Y) hηY (hYdiff η hηY)
  have hanchor : ClassFunction.inner (hcohX.extension χ₁) (hcohY.extension η) = 0 := by
    by_contra ht
    obtain ⟨ε₂, ξ₂, hε₂, hE₂⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχ₂X (hXS hχ₂X).1
    obtain ⟨ε₁, ξ₁, hε₁, hE₁⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχ₁X (hXS hχ₁X).1
    obtain ⟨f, ξ', hf, hE'⟩ := hyp.coherent_extension_eq_zsmul_irr hcohY hηY (hYS hηY).1
    -- the two `𝒳`-witnesses are distinct
    have hξ₂₁ : ξ₂ ≠ ξ₁ := by
      intro h
      have h0 : ClassFunction.inner (hcohX.extension χ₂) (hcohX.extension χ₁) = 0 := by
        rw [hcohX.extension_inner_eq χ₂ χ₁ (Submodule.subset_span hχ₂X)
          (Submodule.subset_span hχ₁X)]
        exact hyp.Sset_pairwiseOrthogonal (hXS hχ₂X) (hXS hχ₁X) hχ₂ne
      rw [hE₂, hE₁, h, inner_zsmul_irreducible_eq, if_pos rfl, mul_one] at h0
      rcases hε₂ with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> norm_num at h0
    -- a nonzero anchor pairing forces `ξ' = ξ₁`
    have hξ' : ξ₁ = ξ' := by
      by_contra hcon
      apply ht
      rw [hE₁, hE', inner_zsmul_irreducible_eq, if_neg hcon, mul_zero]
    -- then `⟨E χ₂, E' η⟩ = 0`, so `hlamEta` reads `a₂ · ⟨E χ₁, E' η⟩ = 0`
    have h₂0 : ClassFunction.inner (hcohX.extension χ₂) (hcohY.extension η) = 0 := by
      rw [hE₂, hE', inner_zsmul_irreducible_eq,
        if_neg (fun hh => hξ₂₁ (hh.trans hξ'.symm)), mul_zero]
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h₂0, zero_sub,
      neg_eq_zero, mul_eq_zero] at hlamEta
    rcases hlamEta with h | h
    · exact (Nat.cast_ne_zero.mpr ha₂.ne') h
    · exact ht h
  -- Step 2: split on `χ = χ₁`
  by_cases hcase : χ = χ₁
  · rw [hcase]
    exact hanchor
  · obtain ⟨a, hapos, hsupp⟩ := hXdiff χ hχX
    have hlam0 : ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
        (hcohY.extension η) = 0 :=
      hyp.cross_inner_extension_diff_any_eq_zero hXS hYS hdisj hcohX hcohY hχX hχ₁X hcase
        hapos hsupp hη₁Y hη₂Y hη₂ne (hYdiff η₂ hη₂Y) hηY (hYdiff η hηY)
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hanchor, mul_zero,
      sub_zero] at hlam0
    exact hlam0

/-! ### Peterfalvi (6): the pairing identities of `Ind(χ₁ − a·η₁)` (p. 148)

With `χ₁ ∈ 𝒳` of degree `a·d` and `η₁ ∈ 𝒴` of degree `d`, the element
`δ = χ₁ − a·η₁` is a degree-zero `A`-supported element of `ℤ[𝒮]`, so `τδ = Ind δ`
is controlled by the Lemma 2(b) isometry: `(τδ, τδ) = 1 + a²` and
`(τδ, e'ⱼ − e'₁) = a` for `j > 1`.  These feed the orthogonal decomposition
`τδ = −a·e'₁ + λ·∑ e'ᵢ + v` of (6). -/

omit [Fintype ↥hyp.H] in
/-- **Peterfalvi (6), norm identity** (p. 148): `(Ind(χ − a·η₁), Ind(χ − a·η₁)) = 1 + a²`
for distinct members `χ, η₁` of `𝒮` with `χ − a·η₁` an `A`-supported lattice
element.  Pure Lemma 2(b): no coherence input. -/
theorem tau_scaled_diff_inner_self [Finite G]
    {χ η₁ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset) (hη₁S : η₁ ∈ hyp.Sset)
    (hne : χ ≠ η₁) {a : ℕ}
    (hsupp : χ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A) :
    ClassFunction.inner (hyp.tau (χ - a • η₁)) (hyp.tau (χ - a • η₁)) =
      1 + (a : ℂ) ^ 2 := by
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  rw [hyp.tau_inner_eq_of_supported_Sset hsupp hsupp, ← Nat.cast_smul_eq_nsmul ℂ a η₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, star_natCast]
  rw [(hχS.1).inner_self_eq_one, (hη₁S.1).inner_self_eq_one,
    hyp.Sset_pairwiseOrthogonal hχS hη₁S hne,
    hyp.Sset_pairwiseOrthogonal hη₁S hχS (Ne.symm hne)]
  ring

/-- **Peterfalvi (6), cross pairing** (p. 148): `(Ind(χ − a·η₁), e'ⱼ − e'₁) = a` for
`j > 1` — the isometry sends the pairing back to `H`, where only the
`a·(η₁, η₁)`-term survives.  This determines the `e'`-coefficients of
`Ind(χ₁ − a·η₁)` up to the common shift `λ`. -/
theorem tau_scaled_diff_inner_extension_diff [Finite G]
    {Y : Set (ClassFunction ↥hyp.H ℂ)} (hYS : Y ⊆ hyp.Sset)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset) (hχY : χ ∉ Y)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) {a : ℕ}
    (hsupp : χ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A)
    {η : ClassFunction ↥hyp.H ℂ} (hηY : η ∈ Y) (hne : η ≠ η₁)
    (hsuppY : η - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A) :
    ClassFunction.inner (hyp.tau (χ - a • η₁))
      (hcohY.extension η - hcohY.extension η₁) = (a : ℂ) := by
  have hEY : hcohY.extension η - hcohY.extension η₁ = hyp.tau (η - η₁) := by
    rw [← hcohY.extends_on_supported _ hsuppY, map_sub]
  rw [hEY, hyp.tau_inner_eq_of_supported_Sset hsupp
    (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hYS hsuppY),
    ← Nat.cast_smul_eq_nsmul ℂ a η₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left]
  rw [hyp.Sset_pairwiseOrthogonal hχS (hYS hηY) (fun h => hχY (h ▸ hηY)),
    hyp.Sset_pairwiseOrthogonal hχS (hYS hη₁Y) (fun h => hχY (h ▸ hη₁Y)),
    hyp.Sset_pairwiseOrthogonal (hYS hη₁Y) (hYS hηY) (Ne.symm hne),
    ((hYS hη₁Y).1).inner_self_eq_one]
  ring

/-- **Peterfalvi (6), `𝒳`-side keystone pairing** (p. 148): with `u = Ind(χ₁ − a·η₁)`
(`χ₁ ∈ 𝒳` the anchor, `η₁ ∈ 𝒴`), pairing against the `𝒳`-keystone differences gives
`(u, eᵢ − aᵢ·e₁) = (χ₁ − a·η₁, χᵢ − aᵢ·χ₁) = −aᵢ` — the input of the
`v = e₁ ∨ v = −e₂` analysis of (6). -/
theorem tau_keystone_inner_extensionX_diff [Finite G]
    {X : Set (ClassFunction ↥hyp.H ℂ)} (hXS : X ⊆ hyp.Sset)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁X : χ₁ ∈ X)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁S : η₁ ∈ hyp.Sset) (hη₁X : η₁ ∉ X) {a : ℕ}
    (hsupp : χ₁ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A)
    {χ' : ClassFunction ↥hyp.H ℂ} (hχ'X : χ' ∈ X) (hχ'ne : χ' ≠ χ₁) {a' : ℕ}
    (hsuppX : χ' - a' • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁))
      (hcohX.extension χ' - (a' : ℂ) • hcohX.extension χ₁) = -(a' : ℂ) := by
  have hEX : hcohX.extension χ' - (a' : ℂ) • hcohX.extension χ₁ = hyp.tau (χ' - a' • χ₁) := by
    rw [← hcohX.extends_on_supported _ hsuppX, map_sub, map_nsmul,
      Nat.cast_smul_eq_nsmul ℂ a' (hcohX.extension χ₁)]
  rw [hEX, hyp.tau_inner_eq_of_supported_Sset hsupp
    (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hXS hsuppX),
    ← Nat.cast_smul_eq_nsmul ℂ a η₁, ← Nat.cast_smul_eq_nsmul ℂ a' χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast]
  rw [hyp.Sset_pairwiseOrthogonal (hXS hχ₁X) (hXS hχ'X) (Ne.symm hχ'ne),
    ((hXS hχ₁X).1).inner_self_eq_one,
    hyp.Sset_pairwiseOrthogonal hη₁S (hXS hχ'X) (fun h => hη₁X (h ▸ hχ'X)),
    hyp.Sset_pairwiseOrthogonal hη₁S (hXS hχ₁X) (fun h => hη₁X (h ▸ hχ₁X))]
  ring

/-- **Peterfalvi (6), the `λ`-form norm identity** (p. 148): for `δ = χ − a·η₁`
(`χ ∈ 𝒮 ∖ 𝒴` of degree `a·d`), the Fourier coefficients of `u = Ind δ` along the
witnesses `e'ⱼ` are `λ` at every `ηⱼ ≠ η₁` and `λ − a` at `η₁`, and the Bessel
decomposition of `(u, u) = 1 + a²` gives the integer identity
`1 + a² = (v,v) + (λ−a)² + (m−1)·λ²` with `(v,v) ≥ 0` and `m = |𝒴|`.
Combining with `a ∣ λ` (from (7)/(8)) this feeds
`x_eq_zero_or_x_one_of_norm_identity`. -/
theorem exists_lambda_norm_identity [Finite G]
    {Y : Set (ClassFunction ↥hyp.H ℂ)} (hYS : Y ⊆ hyp.Sset)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset) (hχY : χ ∉ Y)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) {a : ℕ}
    (hsupp : χ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A)
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      Y hyp.A) :
    ∃ lam : ℤ,
      (∀ η ∈ Y, η ≠ η₁ →
        ClassFunction.inner (hyp.tau (χ - a • η₁)) (hcohY.extension η) = (lam : ℂ)) ∧
      ClassFunction.inner (hyp.tau (χ - a • η₁)) (hcohY.extension η₁) = (lam : ℂ) - a ∧
      ∃ nvv : ℤ, 0 ≤ nvv ∧
        1 + (a : ℤ) ^ 2 = nvv + (lam - a) ^ 2 + ((Y.ncard : ℤ) - 1) * lam ^ 2 := by
  classical
  have hYfin : Y.Finite := hyp.Sset_finite.subset hYS
  set s : Finset (ClassFunction ↥hyp.H ℂ) := hYfin.toFinset with hs
  have hmem : ∀ {η : ClassFunction ↥hyp.H ℂ}, η ∈ s ↔ η ∈ Y := fun {η} =>
    Set.Finite.mem_toFinset hYfin
  set u : ClassFunction G ℂ := hyp.tau (χ - a • η₁) with hu
  have huZ : u ∈ ZIrr G := hyp.tau_mem_ZIrr hsupp.1
  -- orthonormality of the `𝒴`-witnesses
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ClassFunction.inner (hcohY.extension i) (hcohY.extension j) = 0 := by
    intro i hi j hj hne
    rw [hcohY.extension_inner_eq i j (Submodule.subset_span (hmem.mp hi))
      (Submodule.subset_span (hmem.mp hj))]
    exact hyp.Sset_pairwiseOrthogonal (hYS (hmem.mp hi)) (hYS (hmem.mp hj)) hne
  have hnorm : ∀ j ∈ s, ClassFunction.inner (hcohY.extension j) (hcohY.extension j) = 1 := by
    intro j hj
    rw [hcohY.extension_inner_eq j j (Submodule.subset_span (hmem.mp hj))
      (Submodule.subset_span (hmem.mp hj))]
    exact ((hYS (hmem.mp hj)).1).inner_self_eq_one
  -- integrality of the Fourier coefficients
  have hint : ∀ η, η ∈ Y → ∃ t : ℤ,
      ClassFunction.inner u (hcohY.extension η) = (t : ℂ) := by
    intro η hη
    obtain ⟨ε, ξ, hε, hE⟩ := hyp.coherent_extension_eq_zsmul_irr hcohY hη (hYS hη).1
    obtain ⟨t0, ht0⟩ := mem_ZIrr_inner_int ξ huZ
    refine ⟨ε * t0, ?_⟩
    rw [hE, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ),
      ClassFunction.inner_smul_right, star_intCast, ht0]
    push_cast
    ring
  choose tz htz using hint
  set c : ClassFunction ↥hyp.H ℂ → ℤ := fun η => if h : η ∈ Y then tz η h else 0 with hcdef
  have hc : ∀ η (hη : η ∈ Y),
      ClassFunction.inner u (hcohY.extension η) = (c η : ℂ) := by
    intro η hη
    rw [hcdef]
    simp only [dif_pos hη]
    exact htz η hη
  -- the common `λ`
  refine ⟨c η₁ + a, ?_, ?_, ?_⟩
  · -- coefficient at `η ≠ η₁`
    intro η hη hne
    have h6a := hyp.tau_scaled_diff_inner_extension_diff hYS hcohY hχS hχY hη₁Y hsupp hη
      hne (hYdiff η hη)
    rw [ClassFunction.inner_sub_right, ← hu] at h6a
    rw [sub_eq_iff_eq_add.mp h6a, hc η₁ hη₁Y]
    push_cast
    ring
  · -- coefficient at `η₁`
    rw [hc η₁ hη₁Y]
    push_cast
    ring
  · -- the Bessel identity
    have hη₁s : η₁ ∈ s := hmem.mpr hη₁Y
    have hBessel := inner_self_eq_residual_add_sum_inner_mul_star horth hnorm u
    -- left side: `(u,u) = 1 + a²`
    have hχη₁ : χ ≠ η₁ := fun h => hχY (h ▸ hη₁Y)
    have huu : ClassFunction.inner u u = 1 + (a : ℂ) ^ 2 := by
      rw [hu]
      exact hyp.tau_scaled_diff_inner_self hχS (hYS hη₁Y) hχη₁ hsupp
    rw [huu] at hBessel
    -- rewrite the residual with integer coefficients
    have hsum_eq : ∑ η ∈ s, ClassFunction.inner u (hcohY.extension η) • hcohY.extension η
        = ∑ η ∈ s, ((c η : ℂ)) • hcohY.extension η :=
      Finset.sum_congr rfl fun η hη => by rw [hc η (hmem.mp hη)]
    rw [hsum_eq] at hBessel
    -- the residual is a virtual character, so its self-pairing is a sum of squares
    have hvZ : u - ∑ η ∈ s, ((c η : ℂ)) • hcohY.extension η ∈ ZIrr G := by
      refine Submodule.sub_mem _ huZ (Submodule.sum_mem _ fun η hη => ?_)
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _
        (hcohY.extension_mem_ZIrr η (Submodule.subset_span (hmem.mp hη)))
    obtain ⟨cf, -, -, hvv⟩ := mem_ZIrr_inner_self_eq_sum_sq hvZ
    refine ⟨∑ α ∈ cf.support, (cf α) ^ 2,
      Finset.sum_nonneg fun α _ => sq_nonneg _, ?_⟩
    -- the coefficient sum: `η₁`-term plus `(m−1)` copies of `λ²`
    have hsum_coeff : ∑ η ∈ s, ClassFunction.inner u (hcohY.extension η) *
        star (ClassFunction.inner u (hcohY.extension η)) =
        ((c η₁ : ℂ)) ^ 2 + ((s.card : ℂ) - 1) * ((c η₁ : ℂ) + a) ^ 2 := by
      rw [← Finset.add_sum_erase s _ hη₁s, hc η₁ hη₁Y, star_intCast]
      congr 1
      · ring
      · have herase : ∀ η ∈ s.erase η₁,
            ClassFunction.inner u (hcohY.extension η) *
              star (ClassFunction.inner u (hcohY.extension η)) =
            ((c η₁ : ℂ) + a) ^ 2 := by
          intro η hη
          obtain ⟨hne, hηs⟩ := Finset.mem_erase.mp hη
          have h6a := hyp.tau_scaled_diff_inner_extension_diff hYS hcohY hχS hχY hη₁Y
            hsupp (hmem.mp hηs) hne (hYdiff η (hmem.mp hηs))
          rw [ClassFunction.inner_sub_right, ← hu] at h6a
          rw [sub_eq_iff_eq_add.mp h6a, hc η₁ hη₁Y]
          rw [show ((a : ℂ)) + (c η₁ : ℂ) = (((c η₁ : ℤ) + (a : ℤ) : ℤ) : ℂ) by push_cast; ring,
            star_intCast]
          push_cast
          ring
        rw [Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem hη₁s,
          nsmul_eq_mul]
        rw [Nat.cast_sub (Finset.card_pos.mpr ⟨η₁, hη₁s⟩)]
        push_cast
        ring
    rw [hsum_coeff, hvv] at hBessel
    -- cast the `ℂ`-identity down to `ℤ`
    have hcardN : Y.ncard = s.card := by
      rw [hs]
      exact Set.ncard_eq_toFinset_card Y hYfin
    have hZidentity : ((1 + (a : ℤ) ^ 2 : ℤ) : ℂ) =
        ((∑ α ∈ cf.support, (cf α) ^ 2 + ((c η₁ + a) - a) ^ 2 +
          ((Y.ncard : ℤ) - 1) * (c η₁ + a) ^ 2 : ℤ) : ℂ) := by
      rw [hcardN]
      push_cast
      linear_combination hBessel
    exact_mod_cast hZidentity

omit [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)] in
/-- **Peterfalvi (6), witness normalization** (p. 148): under `a ∣ λ` (supplied by
(7)/(8)), the integer core `x_eq_zero_or_x_one_of_norm_identity` leaves `λ = 0`, or
`λ = a` with `m = 2`; in the latter case the swapped-and-negated witnesses
`w(η₁) = −e'₂, w(η₂) = −e'₁` restore the `λ = 0` shape while preserving the
difference relations (`m = 2` is exactly what makes the swap compatible).  The
output is a witness assignment `w` on `𝒴` with: (P1) `w η − w η₁ = τ(η − η₁)`;
(P2) each `w η` is `±` a coherence witness of `𝒴`, and the family is orthonormal;
(P3) `(u, w η) = 0` for `η ≠ η₁` and `(u, w η₁) = −a`. -/
theorem exists_normalized_witness_of_dvd [Finite G]
    {Y : Set (ClassFunction ↥hyp.H ℂ)} (hYS : Y ⊆ hyp.Sset)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ}
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) {a : ℕ}
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      Y hyp.A)
    (ha : 2 ≤ a) (hm : 2 ≤ Y.ncard) {lam : ℤ}
    (hlam_ne : ∀ η ∈ Y, η ≠ η₁ →
      ClassFunction.inner (hyp.tau (χ - a • η₁)) (hcohY.extension η) = (lam : ℂ))
    (hlam_1 : ClassFunction.inner (hyp.tau (χ - a • η₁)) (hcohY.extension η₁) =
      (lam : ℂ) - a)
    {nvv : ℤ} (hnvv : 0 ≤ nvv)
    (hident : 1 + (a : ℤ) ^ 2 = nvv + (lam - a) ^ 2 + ((Y.ncard : ℤ) - 1) * lam ^ 2)
    (hdvd : (a : ℤ) ∣ lam) :
    ∃ w : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ,
      (∀ η ∈ Y, w η - w η₁ = hyp.tau (η - η₁)) ∧
      (∀ η ∈ Y, ∃ η' ∈ Y, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ w η = s • hcohY.extension η') ∧
      (∀ η ∈ Y, ClassFunction.inner (w η) (w η) = 1) ∧
      (∀ η ∈ Y, ∀ η' ∈ Y, η ≠ η' → ClassFunction.inner (w η) (w η') = 0) ∧
      (∀ η ∈ Y, η ≠ η₁ → ClassFunction.inner (hyp.tau (χ - a • η₁)) (w η) = 0) ∧
      ClassFunction.inner (hyp.tau (χ - a • η₁)) (w η₁) = -(a : ℂ) := by
  classical
  -- gram facts for the given witnesses
  have hEnorm : ∀ p ∈ Y, ClassFunction.inner (hcohY.extension p) (hcohY.extension p) = 1 := by
    intro p hp
    rw [hcohY.extension_inner_eq p p (Submodule.subset_span hp) (Submodule.subset_span hp)]
    exact ((hYS hp).1).inner_self_eq_one
  have hEorth : ∀ p ∈ Y, ∀ q ∈ Y, p ≠ q →
      ClassFunction.inner (hcohY.extension p) (hcohY.extension q) = 0 := by
    intro p hp q hq hne
    rw [hcohY.extension_inner_eq p q (Submodule.subset_span hp) (Submodule.subset_span hq)]
    exact hyp.Sset_pairwiseOrthogonal (hYS hp) (hYS hq) hne
  -- the difference relations for the given witnesses
  have hEdiff : ∀ η ∈ Y, hcohY.extension η - hcohY.extension η₁ = hyp.tau (η - η₁) := by
    intro η hη
    rw [← hcohY.extends_on_supported _ (hYdiff η hη), map_sub]
  -- the integer core
  obtain ⟨x, hx⟩ := hdvd
  have hxcase : x = 0 ∨ (x = 1 ∧ (Y.ncard : ℤ) = 2) := by
    refine x_eq_zero_or_x_one_of_norm_identity (a := (a : ℤ)) (m := (Y.ncard : ℤ))
      (by exact_mod_cast ha) (by exact_mod_cast hm) hnvv ?_
    rw [hx] at hident
    linear_combination hident
  rcases hxcase with hx0 | ⟨hx1, hm2⟩
  · -- `λ = 0`: the given witnesses already work
    have hlam0 : lam = 0 := by rw [hx, hx0, mul_zero]
    refine ⟨fun η => hcohY.extension η, hEdiff, ?_, hEnorm, hEorth, ?_, ?_⟩
    · exact fun η hη => ⟨η, hη, 1, Or.inl rfl, (one_smul _ _).symm⟩
    · intro η hη hne
      rw [hlam_ne η hη hne, hlam0, Int.cast_zero]
    · rw [hlam_1, hlam0, Int.cast_zero, zero_sub]
  · -- `λ = a`, `m = 2`: swap and negate the two witnesses
    have hlama : lam = a := by rw [hx, hx1, mul_one]
    have hm2' : Y.ncard = 2 := by exact_mod_cast hm2
    obtain ⟨c, b, hcb, hYcb⟩ := Set.ncard_eq_two.mp hm2'
    -- normalize the pair so that `Y = {η₁, η₂}`
    obtain ⟨η₂, hη₂ne, hY2⟩ : ∃ η₂, η₂ ≠ η₁ ∧ Y = {η₁, η₂} := by
      rcases (hYcb ▸ hη₁Y : η₁ ∈ ({c, b} : Set (ClassFunction ↥hyp.H ℂ))) with h | h
      · exact ⟨b, fun hb => hcb ((hb.trans h).symm), by rw [hYcb, h]⟩
      · exact ⟨c, fun hc => hcb (hc.trans h), by rw [hYcb, h, Set.pair_comm]⟩
    have hη₂Y : η₂ ∈ Y := by rw [hY2]; exact Set.mem_insert_of_mem _ rfl
    have hmemY : ∀ {η}, η ∈ Y → η = η₁ ∨ η = η₂ := by
      intro η hη
      rw [hY2] at hη
      exact hη
    set w : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ :=
      fun η => if η = η₁ then -(hcohY.extension η₂) else -(hcohY.extension η₁) with hw
    have hwη₁ : w η₁ = -(hcohY.extension η₂) := by rw [hw]; exact if_pos rfl
    have hwη₂ : w η₂ = -(hcohY.extension η₁) := by rw [hw]; exact if_neg hη₂ne
    refine ⟨w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (P1) difference relations
      intro η hη
      rcases hmemY hη with h | h
      · rw [h, sub_self, sub_self, map_zero]
      · rw [h, hwη₂, hwη₁, neg_sub_neg, hEdiff η₂ hη₂Y]
    · -- (P2a) values are `±` witnesses
      intro η hη
      rcases hmemY hη with h | h
      · exact ⟨η₂, hη₂Y, -1, Or.inr rfl, by rw [h, hwη₁, neg_smul, one_smul]⟩
      · exact ⟨η₁, hη₁Y, -1, Or.inr rfl, by rw [h, hwη₂, neg_smul, one_smul]⟩
    · -- (P2b1) unit norms
      intro η hη
      rcases hmemY hη with h | h
      · rw [h, hwη₁, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg,
          hEnorm η₂ hη₂Y]
      · rw [h, hwη₂, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg,
          hEnorm η₁ hη₁Y]
    · -- (P2b2) orthogonality
      intro η hη η' hη' hne
      rcases hmemY hη with h | h <;> rcases hmemY hη' with h' | h'
      · exact absurd (h.trans h'.symm) hne
      · rw [h, h', hwη₁, hwη₂, ClassFunction.inner_neg_left,
          ClassFunction.inner_neg_right, neg_neg, hEorth η₂ hη₂Y η₁ hη₁Y hη₂ne]
      · rw [h, h', hwη₁, hwη₂, ClassFunction.inner_neg_left,
          ClassFunction.inner_neg_right, neg_neg, hEorth η₁ hη₁Y η₂ hη₂Y (Ne.symm hη₂ne)]
      · exact absurd (h.trans h'.symm) hne
    · -- (P3) vanishing at `η ≠ η₁` (i.e. at `η₂`)
      intro η hη hne
      rcases hmemY hη with h | h
      · exact absurd h hne
      · rw [h, hwη₂, ClassFunction.inner_neg_right, hlam_1, hlama]
        push_cast
        ring
    · -- (P3) value `−a` at `η₁`
      rw [hwη₁, ClassFunction.inner_neg_right, hlam_ne η₂ hη₂Y hη₂ne, hlama]
      push_cast
      ring

/-- **Peterfalvi (6), the residual `v = u + a·w(η₁)`** (p. 148): once `λ = 0`
(normalized witnesses), the residual `v` of the keystone image `u = Ind(χ₁ − a·η₁)`
is a norm-one virtual character orthogonal to every `𝒴`-witness, and its pairings
with the `𝒳`-witnesses satisfy `(v, eᵢ) = aᵢ·((v, e₁) − 1)` — the input of the
`v = e₁ ∨ v = −e₂` case analysis. -/
theorem keystone_residual_props [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁X : χ₁ ∈ X)
    (hXdiff : ∀ φ ∈ X, ∃ b : ℕ, 0 < b ∧
      φ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {χ₂ : ClassFunction ↥hyp.H ℂ} (hχ₂X : χ₂ ∈ X) (hχ₂ne : χ₂ ≠ χ₁)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y)
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      Y hyp.A)
    {η₂ : ClassFunction ↥hyp.H ℂ} (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    {a : ℕ}
    (hsupp : χ₁ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A)
    {w : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ}
    (hwP2a : ∀ η ∈ Y, ∃ η' ∈ Y, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ w η = s • hcohY.extension η')
    (hwnorm : ∀ η ∈ Y, ClassFunction.inner (w η) (w η) = 1)
    (hworth : ∀ η ∈ Y, ∀ η' ∈ Y, η ≠ η' → ClassFunction.inner (w η) (w η') = 0)
    (hwu_ne : ∀ η ∈ Y, η ≠ η₁ →
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (w η) = 0)
    (hwu_1 : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (w η₁) = -(a : ℂ)) :
    ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • w η₁)
        (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • w η₁) = 1 ∧
      (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • w η₁) ∈ ZIrr G ∧
      (∀ η ∈ Y, ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • w η₁) (w η) = 0) ∧
      (∀ χ' ∈ X, χ' ≠ χ₁ → ∀ a' : ℕ,
        χ' - a' • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A →
        ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • w η₁) (hcohX.extension χ') =
          (a' : ℂ) * (ClassFunction.inner (hyp.tau (χ₁ - a • η₁) + (a : ℂ) • w η₁)
            (hcohX.extension χ₁) - 1)) := by
  classical
  set u : ClassFunction G ℂ := hyp.tau (χ₁ - a • η₁) with hu
  set v : ClassFunction G ℂ := u + (a : ℂ) • w η₁ with hv
  have hη₁X : η₁ ∉ X := fun h => hdisj η₁ h hη₁Y
  have hχ₁η₁ : χ₁ ≠ η₁ := fun h => hdisj χ₁ hχ₁X (h ▸ hη₁Y)
  have huu : ClassFunction.inner u u = 1 + (a : ℂ) ^ 2 := by
    rw [hu]
    exact hyp.tau_scaled_diff_inner_self (hXS hχ₁X) (hYS hη₁Y) hχ₁η₁ hsupp
  have hwu_1' : ClassFunction.inner (w η₁) u = -(a : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    rw [hu, hwu_1, star_neg, star_natCast]
  have hwu1u : ClassFunction.inner u (w η₁) = -(a : ℂ) := by rw [hu]; exact hwu_1
  -- `(v, v) = 1`
  have hvv : ClassFunction.inner v v = 1 := by
    rw [hv]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      star_natCast]
    rw [huu, hwu_1', hwnorm η₁ hη₁Y, hwu1u]
    ring
  -- `v ∈ ZIrr`
  have hwη₁Z : w η₁ ∈ ZIrr G := by
    obtain ⟨η', hη'Y, s, -, hws⟩ := hwP2a η₁ hη₁Y
    rw [hws]
    exact Submodule.smul_mem _ _ (hcohY.extension_mem_ZIrr η' (Submodule.subset_span hη'Y))
  have hvZ : v ∈ ZIrr G := by
    rw [hv]
    refine Submodule.add_mem _ (hu ▸ hyp.tau_mem_ZIrr hsupp.1) ?_
    rw [show ((a : ℂ)) = (((a : ℤ)) : ℂ) by push_cast; ring, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ hwη₁Z
  -- `v` is orthogonal to every `𝒴`-witness
  have hvw : ∀ η ∈ Y, ClassFunction.inner v (w η) = 0 := by
    intro η hη
    rw [hv, ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hne : η = η₁
    · rw [hne, hu, hwu_1, hwnorm η₁ hη₁Y]
      ring
    · rw [hu, hwu_ne η hη hne, hworth η₁ hη₁Y η hη (fun h => hne h.symm)]
      ring
  refine ⟨hvv, hvZ, hvw, ?_⟩
  -- the `𝒳`-side pairing relation
  intro χ' hχ'X hχ'ne a' hsuppX'
  -- `(w η₁, E χ') = 0` and `(w η₁, E χ₁) = 0` from (5)
  have hEw : ∀ φ ∈ X, ClassFunction.inner (w η₁) (hcohX.extension φ) = 0 := by
    intro φ hφ
    obtain ⟨η', hη'Y, s, -, hws⟩ := hwP2a η₁ hη₁Y
    rw [hws, ← Int.cast_smul_eq_zsmul ℂ s, ClassFunction.inner_smul_left]
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      hyp.cross_extension_inner_eq_zero hXS hYS hdisj hcohX hcohY hχ₁X hXdiff hχ₂X hχ₂ne
        hη₁Y hYdiff hη₂Y hη₂ne hφ hη'Y, star_zero, mul_zero]
  -- `(v, E χ' − a'·E χ₁) = −a'`
  have hpair : ClassFunction.inner v
      (hcohX.extension χ' - (a' : ℂ) • hcohX.extension χ₁) = -(a' : ℂ) := by
    rw [hv, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast,
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast,
      hEw χ' hχ'X, hEw χ₁ hχ₁X]
    have hkey := hyp.tau_keystone_inner_extensionX_diff hXS hcohX hχ₁X (hYS hη₁Y) hη₁X
      hsupp hχ'X hχ'ne hsuppX'
    rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
      star_natCast, ← hu] at hkey
    linear_combination hkey
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast] at hpair
  linear_combination hpair

/-- **Peterfalvi (6), the `𝒳`-witness assignment** (p. 148): with normalized
`𝒴`-witnesses `w` (so `v = u + a·w(η₁)` has norm one), the case analysis on the
integer pairings `(v, e₁) ∈ {0, ±1}` produces a `𝒳`-witness assignment `wX` —
`v = e₁` gives the coherence witnesses themselves; `(v, e₁) = 0` forces `n = 2`,
`a₂ = 1`, `v = −e₂` and the swapped-negated assignment; `(v, e₁) = −1` is
impossible.  The output satisfies: values in `ℤ[Irr G]`, orthonormality, cross
orthogonality to the `𝒴`-witnesses, the `𝒳`-difference relations, and the
keystone relation `wX(χ₁) − a·w(η₁) = Ind(χ₁ − a·η₁)`. -/
theorem exists_X_witness_assignment [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁X : χ₁ ∈ X)
    (hXdiff : ∀ φ ∈ X, ∃ b : ℕ, 0 < b ∧
      φ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {χ₂ : ClassFunction ↥hyp.H ℂ} (hχ₂X : χ₂ ∈ X) (hχ₂ne : χ₂ ≠ χ₁)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y)
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      Y hyp.A)
    {η₂ : ClassFunction ↥hyp.H ℂ} (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    {a : ℕ}
    (hsupp : χ₁ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A)
    {w : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ}
    (hwP2a : ∀ η ∈ Y, ∃ η' ∈ Y, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ w η = s • hcohY.extension η')
    (hwnorm : ∀ η ∈ Y, ClassFunction.inner (w η) (w η) = 1)
    (hworth : ∀ η ∈ Y, ∀ η' ∈ Y, η ≠ η' → ClassFunction.inner (w η) (w η') = 0)
    (hwu_ne : ∀ η ∈ Y, η ≠ η₁ →
      ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (w η) = 0)
    (hwu_1 : ClassFunction.inner (hyp.tau (χ₁ - a • η₁)) (w η₁) = -(a : ℂ)) :
    ∃ wX : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ,
      (∀ χ' ∈ X, wX χ' ∈ ZIrr G) ∧
      (∀ χ' ∈ X, ClassFunction.inner (wX χ') (wX χ') = 1) ∧
      (∀ χ' ∈ X, ∀ χ'' ∈ X, χ' ≠ χ'' → ClassFunction.inner (wX χ') (wX χ'') = 0) ∧
      (∀ χ' ∈ X, ∀ η ∈ Y, ClassFunction.inner (wX χ') (w η) = 0) ∧
      (∀ χ' ∈ X, ∀ a' : ℕ,
        χ' - a' • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A →
        wX χ' - (a' : ℂ) • wX χ₁ = hyp.tau (χ' - a' • χ₁)) ∧
      wX χ₁ - (a : ℂ) • w η₁ = hyp.tau (χ₁ - a • η₁) := by
  classical
  obtain ⟨hvv, hvZ, hvw, hrel⟩ := hyp.keystone_residual_props hXS hYS hdisj hcohX hcohY
    hχ₁X hXdiff hχ₂X hχ₂ne hη₁Y hYdiff hη₂Y hη₂ne hsupp hwP2a hwnorm hworth hwu_ne hwu_1
  set v : ClassFunction G ℂ := hyp.tau (χ₁ - a • η₁) + (a : ℂ) • w η₁ with hv
  have hvkey : v - (a : ℂ) • w η₁ = hyp.tau (χ₁ - a • η₁) := by rw [hv]; abel
  -- `𝒳`-side gram and difference facts
  have hEnormX : ∀ p ∈ X,
      ClassFunction.inner (hcohX.extension p) (hcohX.extension p) = 1 := by
    intro p hp
    rw [hcohX.extension_inner_eq p p (Submodule.subset_span hp) (Submodule.subset_span hp)]
    exact ((hXS hp).1).inner_self_eq_one
  have hEorthX : ∀ p ∈ X, ∀ q ∈ X, p ≠ q →
      ClassFunction.inner (hcohX.extension p) (hcohX.extension q) = 0 := by
    intro p hp q hq hne
    rw [hcohX.extension_inner_eq p q (Submodule.subset_span hp) (Submodule.subset_span hq)]
    exact hyp.Sset_pairwiseOrthogonal (hXS hp) (hXS hq) hne
  have hEwcross : ∀ χ' ∈ X, ∀ η ∈ Y,
      ClassFunction.inner (hcohX.extension χ') (w η) = 0 := by
    intro χ' hχ' η hη
    obtain ⟨η', hη'Y, s, -, hws⟩ := hwP2a η hη
    rw [hws, ← Int.cast_smul_eq_zsmul ℂ s, OddOrder.RepresentationTheory.inner_smul_right,
      hyp.cross_extension_inner_eq_zero hXS hYS hdisj hcohX hcohY hχ₁X hXdiff hχ₂X hχ₂ne
        hη₁Y hYdiff hη₂Y hη₂ne hχ' hη'Y, mul_zero]
  have hEdiffX : ∀ φ ∈ X, ∀ b : ℕ,
      φ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A →
      hcohX.extension φ - (b : ℂ) • hcohX.extension χ₁ = hyp.tau (φ - b • χ₁) := by
    intro φ hφ b hb
    rw [← hcohX.extends_on_supported _ hb, map_sub, map_nsmul,
      Nat.cast_smul_eq_nsmul ℂ b (hcohX.extension χ₁)]
  -- uniqueness of the scaling coefficient (degrees pin it)
  have hχ₁1ne : χ₁ (1 : ↥hyp.H) ≠ 0 := by
    obtain ⟨d₁, hd₁pos, hd₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, (hXS hχ₁X).1⟩ : IrreducibleCharacter ↥hyp.H)
    rw [show ((⟨χ₁, (hXS hχ₁X).1⟩ : IrreducibleCharacter ↥hyp.H) :
      ClassFunction ↥hyp.H ℂ) = χ₁ from rfl] at hd₁
    rw [hd₁]
    exact_mod_cast hd₁pos.ne'
  have happly1 : ∀ (φ : ClassFunction ↥hyp.H ℂ) (b : ℕ),
      φ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A →
      φ (1 : ↥hyp.H) - (b : ℂ) * χ₁ (1 : ↥hyp.H) = 0 := by
    intro φ b hb
    have h0 : (φ - b • χ₁) (1 : ↥hyp.H) = 0 := by
      by_contra h0
      exact hyp.one_notMem_A (hb.2 (ClassFunction.mem_support.mpr h0))
    rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ b χ₁,
      ClassFunction.smul_apply] at h0
    exact h0
  have hval_eq : ∀ {φ : ClassFunction ↥hyp.H ℂ} {b c : ℕ},
      φ - b • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A →
      φ - c • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A →
      b = c := by
    intro φ b c hb hc
    have hbc : ((b : ℂ) - c) * χ₁ (1 : ↥hyp.H) = 0 := by
      have h1 := happly1 φ b hb
      have h2 := happly1 φ c hc
      linear_combination h2 - h1
    rcases mul_eq_zero.mp hbc with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd h hχ₁1ne
  have hone : χ₁ - (1 : ℕ) • χ₁ ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A := by
    rw [one_nsmul, sub_self]
    exact ⟨Submodule.zero_mem _,
      fun x hx => absurd (ClassFunction.zero_apply x) (ClassFunction.mem_support.mp hx)⟩
  -- signed-irreducible witnesses of `v` and `e₁`
  obtain ⟨εv, ξv, hεv, hveq⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hvZ hvv
  obtain ⟨ε₁, ξ₁w, hε₁, hE₁⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχ₁X (hXS hχ₁X).1
  have ht₁ : ClassFunction.inner v (hcohX.extension χ₁) =
      (εv : ℂ) * (ε₁ : ℂ) * (if ξv = ξ₁w then 1 else 0) := by
    rw [hveq, hE₁, inner_zsmul_irreducible_eq]
  by_cases hξ : ξv = ξ₁w
  · -- `(v, e₁) = ±1`
    rw [if_pos hξ, mul_one] at ht₁
    have hcase : v = hcohX.extension χ₁ ∨
        ClassFunction.inner v (hcohX.extension χ₁) = -1 := by
      rcases hεv with rfl | rfl <;> rcases hε₁ with rfl | rfl
      · exact Or.inl (by rw [hveq, hE₁, hξ])
      · exact Or.inr (by rw [ht₁]; norm_num)
      · exact Or.inr (by rw [ht₁]; norm_num)
      · exact Or.inl (by rw [hveq, hE₁, hξ])
    rcases hcase with hvE | ht₁neg
    · -- **case `v = e₁`**: the coherence witnesses themselves work
      refine ⟨fun χ' => hcohX.extension χ', ?_, hEnormX, hEorthX, hEwcross, ?_, ?_⟩
      · exact fun χ' hχ' =>
          hcohX.extension_mem_ZIrr χ' (Submodule.subset_span hχ')
      · exact fun χ' hχ' a' ha' => hEdiffX χ' hχ' a' ha'
      · simpa only [← hvE] using hvkey
    · -- **case `(v, e₁) = −1`**: impossible via `χ₂`
      exfalso
      obtain ⟨a₂, ha₂pos, hsupp₂⟩ := hXdiff χ₂ hχ₂X
      have h₂ := hrel χ₂ hχ₂X hχ₂ne a₂ hsupp₂
      rw [ht₁neg] at h₂
      obtain ⟨ε₂, ξ₂w, hε₂, hE₂⟩ :=
        hyp.coherent_extension_eq_zsmul_irr hcohX hχ₂X (hXS hχ₂X).1
      rw [hveq, hE₂, inner_zsmul_irreducible_eq] at h₂
      by_cases hξ₂ : ξv = ξ₂w
      · rw [if_pos hξ₂, mul_one] at h₂
        have hsq : ((εv : ℂ) * ε₂) ^ 2 = ((a₂ : ℂ) * (-1 - 1)) ^ 2 := by rw [h₂]
        have hεv2 : (εv : ℂ) ^ 2 = 1 := by rcases hεv with rfl | rfl <;> norm_num
        have hε₂2 : (ε₂ : ℂ) ^ 2 = 1 := by rcases hε₂ with rfl | rfl <;> norm_num
        have h4 : ((4 * a₂ ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
          push_cast
          linear_combination (-1 : ℂ) * hsq + (ε₂ : ℂ) ^ 2 * hεv2 + hε₂2
        have h5 : 4 * a₂ ^ 2 = 1 := Nat.cast_injective h4
        nlinarith [ha₂pos, h5]
      · rw [if_neg hξ₂, mul_zero] at h₂
        have : (a₂ : ℂ) = 0 ∨ (-1 - 1 : ℂ) = 0 := mul_eq_zero.mp h₂.symm
        rcases this with h | h
        · exact ha₂pos.ne' (by exact_mod_cast h)
        · norm_num at h
  · -- **case `(v, e₁) = 0`**: `v = −e'` for every other member; swapped assignment
    rw [if_neg hξ, mul_zero] at ht₁
    -- every `χ' ≠ χ₁` has `a' = 1` and `E χ' = −v`
    have hbad : ∀ χ' ∈ X, χ' ≠ χ₁ → ∀ a' : ℕ,
        χ' - a' • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A →
        hcohX.extension χ' = -v ∧ a' = 1 := by
      intro χ' hχ'X hχ'ne a' hsuppX'
      have h' := hrel χ' hχ'X hχ'ne a' hsuppX'
      rw [ht₁] at h'
      obtain ⟨ε', ξ'w, hε', hE'⟩ :=
        hyp.coherent_extension_eq_zsmul_irr hcohX hχ'X (hXS hχ'X).1
      rw [hveq, hE', inner_zsmul_irreducible_eq] at h'
      by_cases hξ' : ξv = ξ'w
      · rw [if_pos hξ', mul_one] at h'
        -- `εv·ε' = −a'`: squares give `a' = 1`, then the sign gives `E χ' = −v`
        have hεv2 : (εv : ℂ) ^ 2 = 1 := by rcases hεv with rfl | rfl <;> norm_num
        have hε'2 : (ε' : ℂ) ^ 2 = 1 := by rcases hε' with rfl | rfl <;> norm_num
        have hsq' : ((εv : ℂ) * ε') ^ 2 = ((a' : ℂ) * (0 - 1)) ^ 2 := by rw [h']
        have ha'sq : ((a' ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
          push_cast
          linear_combination (-1 : ℂ) * hsq' + (ε' : ℂ) ^ 2 * hεv2 + hε'2
        have ha'1 : a' = 1 := by
          have h2 : a' ^ 2 = 1 := Nat.cast_injective ha'sq
          rcases Nat.pow_eq_one.mp h2 with h | h
          · exact h
          · omega
        refine ⟨?_, ha'1⟩
        have hεε : (ε' : ℂ) = -(εv : ℂ) := by
          have h'' : (εv : ℂ) * ε' = -1 := by
            rw [h', ha'1]
            norm_num
          linear_combination (εv : ℂ) * h'' - (ε' : ℂ) * hεv2
        rw [hE', hveq, ← hξ', ← Int.cast_smul_eq_zsmul ℂ ε',
          ← Int.cast_smul_eq_zsmul ℂ εv, hεε, neg_smul]
      · rw [if_neg hξ', mul_zero] at h'
        exfalso
        rcases mul_eq_zero.mp h'.symm with h | h
        · obtain ⟨b, hbpos, hsuppb⟩ := hXdiff χ' hχ'X
          have hab : a' = b := hval_eq hsuppX' hsuppb
          rw [hab] at h
          exact hbpos.ne' (by exact_mod_cast h)
        · norm_num at h
    set wX : ClassFunction ↥hyp.H ℂ → ClassFunction G ℂ :=
      fun χ' => if χ' = χ₁ then v else -(hcohX.extension χ₁) with hwX
    have hwXχ₁ : wX χ₁ = v := by rw [hwX]; exact if_pos rfl
    have hwXne : ∀ {χ'}, χ' ≠ χ₁ → wX χ' = -(hcohX.extension χ₁) := by
      intro χ' h
      rw [hwX]
      exact if_neg h
    refine ⟨wX, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- values in `ℤ[Irr G]`
      intro χ' hχ'
      by_cases h : χ' = χ₁
      · rw [h, hwXχ₁]; exact hvZ
      · rw [hwXne h]
        exact Submodule.neg_mem _
          (hcohX.extension_mem_ZIrr χ₁ (Submodule.subset_span hχ₁X))
    · -- unit norms
      intro χ' hχ'
      by_cases h : χ' = χ₁
      · rw [h, hwXχ₁]; exact hvv
      · rw [hwXne h, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hEnormX χ₁ hχ₁X]
    · -- orthogonality
      intro χ' hχ' χ'' hχ'' hne
      by_cases h' : χ' = χ₁ <;> by_cases h'' : χ'' = χ₁
      · exact absurd (h'.trans h''.symm) hne
      · rw [h', hwXχ₁, hwXne h'', ClassFunction.inner_neg_right, ht₁, neg_zero]
      · rw [h'', hwXχ₁, hwXne h', ClassFunction.inner_neg_left,
          OddOrder.RepresentationTheory.inner_conj_symm, ht₁, star_zero, neg_zero]
      · exfalso
        obtain ⟨b', hb'pos, hsupp'⟩ := hXdiff χ' hχ'
        obtain ⟨b'', hb''pos, hsupp''⟩ := hXdiff χ'' hχ''
        have h1 := (hbad χ' hχ' h' b' hsupp').1
        have h2 := (hbad χ'' hχ'' h'' b'' hsupp'').1
        have horth := hEorthX χ' hχ' χ'' hχ'' hne
        rw [h1, h2, ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
          neg_neg, hvv] at horth
        exact one_ne_zero horth
    · -- cross orthogonality with the `𝒴`-witnesses
      intro χ' hχ' η hη
      by_cases h : χ' = χ₁
      · rw [h, hwXχ₁]; exact hvw η hη
      · rw [hwXne h, ClassFunction.inner_neg_left, hEwcross χ₁ hχ₁X η hη, neg_zero]
    · -- the `𝒳`-difference relations
      intro χ' hχ' a' hsuppX'
      by_cases h : χ' = χ₁
      · subst h
        have ha'1 : a' = 1 := hval_eq hsuppX' hone
        rw [ha'1, Nat.cast_one, one_smul, sub_self, one_nsmul, sub_self, map_zero]
      · obtain ⟨hEχ', ha'1⟩ := hbad χ' hχ' h a' hsuppX'
        rw [hwXne h, hwXχ₁, ha'1]
        have hτ := hEdiffX χ' hχ' 1 (ha'1 ▸ hsuppX')
        rw [← hτ, hEχ']
        push_cast
        module
    · -- the keystone relation
      rw [hwXχ₁]
      exact hvkey

end Coherence

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
