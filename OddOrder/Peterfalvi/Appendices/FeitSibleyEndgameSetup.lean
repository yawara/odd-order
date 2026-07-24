/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyXsetInduction

/-!
# Feit–Sibley — endgame: setup layer

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
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

/-- **(8) divisibility core** (Peterfalvi Appendix IV, p. 150): if `λ/a + μ` is an algebraic
integer with `μ : ℤ` and `a > 0`, then `a ∣ λ`.  Indeed `λ/a = (λ/a + μ) − μ` is a *rational*
algebraic integer, hence an integer (`isIntegral_rat_imp_int`), so its denominator `a` divides
`λ`.  This is the last step of (8): the central-character congruence
`(e'₁(z) − e'₁(1))/|Q| = −(λ/a + μ)` (from (7) applied to `±e'₁`) is an algebraic integer,
forcing `a ∣ λ` and closing (6). -/
theorem dvd_of_isIntegral_ratio {a : ℕ} (ha : 0 < a) {lam mu : ℤ}
    (hint : IsIntegral ℤ ((lam : ℂ) / (a : ℂ) + (mu : ℂ))) :
    (a : ℤ) ∣ lam := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hmu : IsIntegral ℤ (mu : ℂ) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := mu)
  have hla : IsIntegral ℤ ((lam : ℂ) / (a : ℂ)) := by
    have h := hint.sub hmu
    have he : (lam : ℂ) / (a : ℂ) + (mu : ℂ) - (mu : ℂ) = (lam : ℂ) / (a : ℂ) := by ring
    rwa [he] at h
  set q : ℚ := (lam : ℚ) / (a : ℚ) with hq
  have hqc : (q : ℂ) = (lam : ℂ) / (a : ℂ) := by rw [hq]; push_cast; ring
  obtain ⟨n, hn⟩ := isIntegral_rat_imp_int (q := q) (by rw [hqc]; exact hla)
  rw [hqc] at hn
  refine ⟨n, ?_⟩
  have hlc : (lam : ℂ) = (a : ℂ) * (n : ℂ) := by
    rw [div_eq_iff ha0] at hn; rw [hn]; ring
  exact_mod_cast hlc

/-- **(8) divisibility from the evaluation identity** (Peterfalvi Appendix IV, p. 150).  The `(8)`
evaluation `χ₁(1)·(e'(z) − e'(1)) = −|H|·c₀` (`restrict_apply_sub_eq_neg_card_mul_inner`), rewritten
with `χ₁(1) = a·d`, `|H| = d·|Q|` and the keystone `c₀ = λ + a·μ`, reads
`(a·d)·Δ = −(d·|Q|)·(λ + a·μ)` with `Δ = e'(z) − e'(1)`.  Cancelling the nonzero `d` gives
`a·Δ = −|Q|·(λ + a·μ)`, so `λ/a + μ = −(Δ/|Q|)`.  The central-character congruence (7)
`e'(z) ≡ e'(1) (mod |Q|)` (`peterfalvi_67_hall_of_odd`) says `Δ/|Q|` is an algebraic integer, hence
so is `λ/a + μ`, forcing `a ∣ λ` (`dvd_of_isIntegral_ratio`) — the last step of (6). -/
theorem dvd_lam_of_evaluation_cong {a : ℕ} (ha : 0 < a) {lam mu : ℤ}
    {dc Qc Δ : ℂ} (hd0 : dc ≠ 0) (hQ0 : Qc ≠ 0)
    (heval : (a : ℂ) * dc * Δ = -(dc * Qc) * ((lam : ℂ) + (a : ℂ) * (mu : ℂ)))
    (hcong : IsIntegral ℤ (Δ / Qc)) :
    (a : ℤ) ∣ lam := by
  have ha0 : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  -- cancel `d`: `a·Δ = -Qc·(λ + aμ)`
  have hcancel : (a : ℂ) * Δ = -Qc * ((lam : ℂ) + (a : ℂ) * (mu : ℂ)) :=
    mul_left_cancel₀ hd0 (by linear_combination heval)
  -- the ratio `λ/a + μ = -(Δ/Qc)`
  have hratio : (lam : ℂ) / (a : ℂ) + (mu : ℂ) = -(Δ / Qc) := by
    apply mul_left_cancel₀ (mul_ne_zero ha0 hQ0)
    have hL : (a : ℂ) * Qc * ((lam : ℂ) / (a : ℂ) + (mu : ℂ))
        = Qc * ((lam : ℂ) + (a : ℂ) * (mu : ℂ)) := by field_simp
    have hR : (a : ℂ) * Qc * -(Δ / Qc) = -((a : ℂ) * Δ) := by field_simp
    rw [hL, hR, hcancel]; ring
  refine dvd_of_isIntegral_ratio (lam := lam) (mu := mu) ha ?_
  rw [hratio]
  exact hcong.neg

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

/-- **Member-assignment coherence** (Peterfalvi (6) assembly core, p. 148).
A finite orthonormal set `S ⊆ CF(Γ)` is coherent for `(τ, A)` as soon as its
members carry an orthonormal `ℤ[Irr Δ]`-valued assignment `W` that agrees with
`τ` on every supported difference `μ − b_μ·η₁` to a fixed anchor `η₁ ∈ S`.

The coherent extension is `memberAssignmentMap s W` (the `m`-fold `retarget`).
Isometry and the `ZIrr` codomain come from the orthonormal `W` on members
(`inner_map_eq_on_zSpan`, `map_mem_ZIrr_on_zSpan`).  For `extends_on_supported`
the supported lattice `Z[S, A]` is generated by the differences
`{μ − b_μ·η₁ : μ ∈ S}`: a supported `φ = ∑ c_μ μ` has anchor coefficient
`∑ c_μ b_μ = 0` (degree `0` at `1`, since `1 ∉ A` and `η₁ 1 ≠ 0`), so
`φ = ∑ c_μ (μ − b_μ·η₁)` is an integral combination of generators, and both
maps agree on each generator.  This is the standalone core the Peterfalvi (6)
union `𝒳 ∪ 𝒴` coherence is assembled from. -/
noncomputable def isCoherent_of_memberAssignment
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap Γ Δ}
    {S : Set (ClassFunction Γ ℂ)} {A : Set Γ}
    {W : ClassFunction Γ ℂ → ClassFunction Δ ℂ}
    {s : Finset (ClassFunction Γ ℂ)}
    (hsS : ∀ {μ : ClassFunction Γ ℂ}, μ ∈ s ↔ μ ∈ S)
    (hnorm : ∀ μ ∈ S, ClassFunction.inner μ μ = 1)
    (horth : ∀ μ ∈ S, ∀ ν ∈ S, μ ≠ ν → ClassFunction.inner μ ν = 0)
    (hWnorm : ∀ μ ∈ S, ClassFunction.inner (W μ) (W μ) = 1)
    (hWorth : ∀ μ ∈ S, ∀ ν ∈ S, μ ≠ ν → ClassFunction.inner (W μ) (W ν) = 0)
    (hWZIrr : ∀ μ ∈ S, W μ ∈ ZIrr Δ)
    {η₁ : ClassFunction Γ ℂ} (hη₁S : η₁ ∈ S) (hη₁one : η₁ (1 : Γ) ≠ 0)
    (hAone : (1 : Γ) ∉ A)
    (hdiff : ∀ μ ∈ S, ∃ b : ℕ,
      μ - b • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := Γ) S A ∧
      W μ - (b : ℂ) • W η₁ = τ (μ - b • η₁))
    (hnz : ∃ φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := Γ) S A, φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent τ S A := by
  classical
  -- the assignment map is orthonormal on members, hence isometric on `Z[S]`
  have hmember_inner : ∀ μ ∈ S, ∀ ν ∈ S,
      ClassFunction.inner (memberAssignmentMap s W μ) (memberAssignmentMap s W ν) =
        ClassFunction.inner μ ν := by
    intro μ hμ ν hν
    rw [memberAssignmentMap_apply_of_mem hsS hnorm horth W hμ,
      memberAssignmentMap_apply_of_mem hsS hnorm horth W hν]
    by_cases h : μ = ν
    · subst h; rw [hWnorm μ hμ, hnorm μ hμ]
    · rw [hWorth μ hμ ν hν h, horth μ hμ ν hν h]
  refine
    { nonzero := hnz
      extension := memberAssignmentMap s W
      extension_inner_eq := fun φ ψ hφ hψ =>
        inner_map_eq_on_zSpan (memberAssignmentMap s W) hmember_inner φ hφ ψ hψ
      extends_on_supported := ?_
      extension_mem_ZIrr := fun φ hφ =>
        map_mem_ZIrr_on_zSpan (memberAssignmentMap s W)
          (fun μ hμ => by
            rw [memberAssignmentMap_apply_of_mem hsS hnorm horth W hμ]; exact hWZIrr μ hμ)
          φ hφ }
  -- **the generation argument** for `extends_on_supported`
  intro φ hφ
  have hdiff' : ∀ μ ∈ s, ∃ b : ℕ,
      μ - b • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := Γ) S A ∧
      W μ - (b : ℂ) • W η₁ = τ (μ - b • η₁) := fun μ hμ => hdiff μ (hsS.mp hμ)
  choose! b hbsupp hbeq using hdiff'
  -- integer member gram, hence integer Fourier coefficients `c μ = (φ, μ)`
  have hgram : ∀ ν ∈ S, ∀ μ ∈ S, ∃ cc : ℤ, ClassFunction.inner ν μ = (cc : ℂ) := by
    intro ν hν μ hμ
    by_cases h : ν = μ
    · exact ⟨1, by rw [h, hnorm μ hμ, Int.cast_one]⟩
    · exact ⟨0, by rw [horth ν hν μ hμ h, Int.cast_zero]⟩
  have hcoeff : ∀ μ ∈ s, ∃ cc : ℤ, ClassFunction.inner φ μ = (cc : ℂ) :=
    fun μ hμ => exists_int_inner_of_mem_zSpan hgram φ hφ.1 μ (hsS.mp hμ)
  choose! c hc using hcoeff
  -- reconstruction in integer form: `φ = ∑ c μ • μ`
  have hrecon : φ = ∑ μ ∈ s, (c μ) • μ := by
    conv_lhs => rw [eq_sum_inner_smul_of_mem_zSpan hsS hnorm horth φ hφ.1]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [hc μ hμ, Int.cast_smul_eq_zsmul]
  -- degree `0`: `φ 1 = 0`, and each `μ 1 = b_μ · η₁ 1`
  have hφ1 : φ (1 : Γ) = 0 := by
    by_contra h
    exact hAone (hφ.2 (ClassFunction.mem_support.mpr h))
  have hμ1 : ∀ μ ∈ s, μ (1 : Γ) = (b μ : ℂ) * η₁ (1 : Γ) := by
    intro μ hμ
    have h0 : (μ - b μ • η₁) (1 : Γ) = 0 := by
      by_contra h
      exact hAone ((hbsupp μ hμ).2 (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ (b μ) η₁,
      ClassFunction.smul_apply] at h0
    exact sub_eq_zero.mp h0
  -- the anchor coefficient vanishes: `∑ c μ · b μ = 0`
  have hP : (∑ μ ∈ s, c μ * (b μ : ℤ)) = 0 := by
    have hval : ((∑ μ ∈ s, c μ * (b μ : ℤ) : ℤ) : ℂ) * η₁ (1 : Γ) = 0 := by
      rw [Int.cast_sum, Finset.sum_mul, ← hφ1]
      conv_rhs => rw [hrecon, ClassFunction.sum_apply]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      rw [← Int.cast_smul_eq_zsmul ℂ (c μ) μ, ClassFunction.smul_apply, hμ1 μ hμ]
      push_cast; ring
    rcases mul_eq_zero.mp hval with h | h
    · exact_mod_cast h
    · exact absurd h hη₁one
  -- decompose `φ` over the supported generators `μ − b_μ·η₁`
  have hdecomp : ∑ μ ∈ s, (c μ) • (μ - b μ • η₁) = φ := by
    have hterm : ∀ μ ∈ s, (c μ) • (μ - b μ • η₁)
        = (c μ) • μ - (c μ * (b μ : ℤ)) • η₁ := by
      intro μ _
      rw [smul_sub, ← Nat.cast_smul_eq_nsmul ℤ (b μ) η₁, smul_smul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_smul, hP,
      zero_smul, sub_zero]
    exact hrecon.symm
  -- both maps agree on each generator, hence on `φ`
  calc memberAssignmentMap s W φ
      = memberAssignmentMap s W (∑ μ ∈ s, (c μ) • (μ - b μ • η₁)) := by rw [hdecomp]
    _ = ∑ μ ∈ s, (c μ) • memberAssignmentMap s W (μ - b μ • η₁) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun μ _ => by rw [map_zsmul]
    _ = ∑ μ ∈ s, (c μ) • τ (μ - b μ • η₁) := by
        refine Finset.sum_congr rfl fun μ hμ => ?_
        congr 1
        rw [map_sub, map_nsmul,
          memberAssignmentMap_apply_of_mem hsS hnorm horth W (hsS.mp hμ),
          memberAssignmentMap_apply_of_mem hsS hnorm horth W hη₁S,
          ← Nat.cast_smul_eq_nsmul ℂ (b μ) (W η₁)]
        exact hbeq μ hμ
    _ = τ (∑ μ ∈ s, (c μ) • (μ - b μ • η₁)) := by
        rw [map_sum]; exact (Finset.sum_congr rfl fun μ _ => by rw [map_zsmul]).symm
    _ = τ φ := by rw [hdecomp]

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

/-- `Z = ⁅Q₁,Q₁⁆ ⊓ C(Q₁) ≤ ⁅Q₁,Q₁⁆ ≤ ⁅Q,Q⁆ = Q'`: the endgame centre lies in the derived
subgroup, so `𝒴 = 𝒮(Q')` (trivial on `Q'`) is disjoint from `𝒳 = 𝒮 − 𝒮(Z)`. -/
theorem endgameZ_le_Qder : hyp.endgameZ ≤ hyp.Qder :=
  (inf_le_left.trans (Subgroup.commutator_mono hyp.Q1_le_Q hyp.Q1_le_Q))

/-- **`𝒳 = XsetOf ⊥ Z = {χ ∈ Irr H | Z ⊄ Ker χ}`** when `Z ≤ Q₁` (Peterfalvi (8), p. 150).
The `Q₁ ⊄ Ker χ` defining condition of `𝒮` and the `⊥ ⊆ Ker χ` condition of `𝒮(⊥)` are both
redundant here: `⊥ ⊆ Ker` is vacuous, and `Z ⊄ Ker χ` with `Z ≤ Q₁` forces `Q₁ ⊄ Ker χ`
(a character constant on `Q₁` is constant on `Z ≤ Q₁`).  This identifies `𝒳` with the full family
of irreducibles *not* trivial on `Z`, so its degree-weighted sum is the regular-character
difference `ρ_H − ρ_{H/Z}` (`sumNonInflatedDegreeMulChar_of_mem`), the (8) constancy input. -/
theorem mem_XsetOf_bot_iff {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    {χ : ClassFunction ↥hyp.H ℂ} :
    χ ∈ hyp.XsetOf ⊥ Z ↔ IsIrreducibleCharacter χ ∧ ¬ hyp.LeKer χ Z := by
  constructor
  · rintro ⟨⟨⟨hirr, _⟩, _⟩, hZ⟩
    exact ⟨hirr, hZ⟩
  · rintro ⟨hirr, hZ⟩
    refine ⟨⟨⟨hirr, ?_⟩, ?_⟩, hZ⟩
    · exact fun hQ1 => hZ fun x hxZ => hQ1 x (hZQ1 hxZ)
    · intro x hx
      rw [Subgroup.mem_bot] at hx
      rw [show x = 1 from Subtype.ext hx]

/-- **`Z` centralises `Q₁`** (`Z ≤ Z(Q₁)`): `⁅z, y⁆ = 1` for `z ∈ Z`, `y ∈ Q₁`. -/
theorem endgameZ_centralizes {z : G} (hz : z ∈ hyp.endgameZ) {y : G} (hy : y ∈ hyp.Q1) :
    ⁅z, y⁆ = 1 := by
  have hyz : ⁅y, z⁆ = 1 :=
    (Subgroup.mem_centralizer_iff_commutator_eq_one.mp hz.2) y hy
  have : Commute z y := (commutatorElement_eq_one_iff_commute.mp hyz).symm
  exact commutatorElement_eq_one_iff_commute.mpr this

open scoped Pointwise in
/-- **`Q` centralises a central element of `Q₁`** (Peterfalvi (7)/(8) input).  For `w ∈ Q₁`
that centralises all of `Q₁` (`w ∈ Z(Q₁)`), the whole direct factorisation `Q = S × Q₁`
centralises `w`: `S` commutes with `Q₁` elementwise (`S_commutes_Q1`) and `Q₁` centralises `w`. -/
theorem Q_le_centralizer_of_centralizes_Q1 {w : G} (hwQ1 : w ∈ hyp.Q1)
    (hcent : ∀ y ∈ hyp.Q1, ⁅w, y⁆ = 1) :
    hyp.Q ≤ Subgroup.centralizer ({w} : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  rintro x hx
  rw [Set.mem_singleton_iff] at hx; subst x
  have hqset : (q : G) ∈ (hyp.S : Set G) * (hyp.Q1 : Set G) := by
    rw [hyp.S_mul_Q1_eq_Q]; exact hq
  obtain ⟨s, hs, y, hy, rfl⟩ := Set.mem_mul.mp hqset
  -- `w` commutes with `s ∈ S` (`S_commutes_Q1`, `w ∈ Q₁`) and with `y ∈ Q₁` (`w ∈ Z(Q₁)`)
  have hsw : s * w = w * s := hyp.S_commutes_Q1 s hs w hwQ1
  have hyw : w * y = y * w := commutatorElement_eq_one_iff_commute.mp (hcent y hy)
  calc w * (s * y) = (w * s) * y := by rw [mul_assoc]
    _ = (s * w) * y := by rw [hsw]
    _ = s * (w * y) := by rw [mul_assoc]
    _ = s * (y * w) := by rw [hyw]
    _ = (s * y) * w := by rw [mul_assoc]

open scoped Pointwise in
/-- **`C_H(w) = Q` for `w ∈ Q₁^#` centralised by `Q`** (Peterfalvi (7)/(8) input).  Given
`Q ≤ C_G(w)`, the complement `D` contributes nothing: any `h = q·d ∈ H` (`q ∈ Q`, `d ∈ D`)
centralising `w` forces `d` to centralise `w ∈ Q₁`, so `d = 1` by the fixed-point-freeness of
`D` on `Q₁` (as `w ≠ 1`).  Hence `H ⊓ C_G(w) = Q`; in particular `|H ⊓ C_G(w)| = |Q|` is the same
for every `w ∈ Z^#`, the normalizer–centralizer constancy input of (7). -/
theorem inf_centralizer_eq_Q_of_mem_Q1 {w : G} (hwQ1 : w ∈ hyp.Q1) (hw1 : w ≠ 1)
    (hQcent : hyp.Q ≤ Subgroup.centralizer ({w} : Set G)) :
    hyp.H ⊓ Subgroup.centralizer ({w} : Set G) = hyp.Q := by
  apply le_antisymm
  · rintro h ⟨hhH, hhC⟩
    have hwq : w * h = h * w := by
      have := (Subgroup.mem_centralizer_iff).mp hhC w (Set.mem_singleton _); exact this
    have hhset : (h : G) ∈ (hyp.Q : Set G) * (hyp.D : Set G) := by
      rw [hyp.Q_mul_D_eq_H]; exact hhH
    obtain ⟨q, hq, d, hd, rfl⟩ := Set.mem_mul.mp hhset
    -- `q` centralises `w`, so `d` does too
    have hqw : w * q = q * w :=
      (Subgroup.mem_centralizer_iff).mp (hQcent hq) w (Set.mem_singleton _)
    have hdw : d * w * d⁻¹ = w := by
      -- cancel `q` on the left: `w*q*d = q*w*d = q*d*w` gives `w*d = d*w`
      have hstep : q * (w * d) = q * (d * w) :=
        calc q * (w * d) = (q * w) * d := (mul_assoc q w d).symm
          _ = (w * q) * d := by rw [← hqw]
          _ = w * (q * d) := mul_assoc w q d
          _ = (q * d) * w := hwq
          _ = q * (d * w) := mul_assoc q d w
      have hdw' : w * d = d * w := mul_left_cancel hstep
      rw [← hdw']; group
    have hd1 : d = 1 := by
      by_contra hdne
      exact hw1 (hyp.D_fixedPointFree_on_Q1 d hd hdne w hwQ1 hdw)
    rw [hd1, mul_one]; exact hq
  · exact fun q hq => ⟨hyp.Q_le_H hq, hQcent hq⟩

/-- **`Q ≤ C_G(z)` for `z` in a central `Z ≤ Z(Q₁)`** (Peterfalvi (7)/(8) `hQz` input).  Thin
specialisation of `Q_le_centralizer_of_centralizes_Q1` to a subgroup `Z ≤ Q₁` centralising `Q₁`. -/
theorem Q_le_centralizer_of_mem_central {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    (hZcent : ∀ w ∈ Z, ∀ y ∈ hyp.Q1, ⁅w, y⁆ = 1) {z : G} (hzZ : z ∈ Z) :
    hyp.Q ≤ Subgroup.centralizer ({z} : Set G) :=
  hyp.Q_le_centralizer_of_centralizes_Q1 (hZQ1 hzZ) (hZcent z hzZ)



end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
