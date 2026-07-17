import OddOrder.Peterfalvi.S07_Coherence.NormInequalities

/-!
# Peterfalvi (5.6.3) 準備 — ψ = 0 decomposition, isometry re-targeting keystone, (1.1)+(1.4)

Split from the former monolithic `OddOrder.Peterfalvi.S07_Coherence` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S07
open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]


namespace CharacterPsiDecomposition

open OddOrder.RepresentationTheory

variable {τ : IntegralCharacterMap L G} {χ ψ : ClassFunction L ℂ}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- **Peterfalvi (5.6.2) quadratic bound.**  Suppose the orthogonal part `Y` of the (5.4)
decomposition is written against an **orthogonal family** `v : ι → CF(G)` (indexed over
`s`, with real gram `⟨v i, v j⟩ = if i = j then m i else 0`) plus a residual `Z` orthogonal
to the family, with real coefficients `c`:

`Y = (∑ i ∈ s, (c i) • v i) + Z`.

Then `∑ i ∈ s, (c i)² · m i + ‖Z‖² ≤ ‖ψ‖²`.

This is the geometric half of (5.6.2): the Pythagoras expansion of `‖Y‖²` against the
orthogonal family, combined with the opening bound `‖Y‖² ≤ ‖ψ‖²` (`inner_self_Y_re_le_inner_self_psi`).
The arithmetic half — substituting the (5.6.1) coefficients and forcing the integer `λ = 0` —
is `int_eq_zero_of_sq_mul_le_of_two_mul_lt`. -/
theorem sum_sq_mul_add_normSq_Z_le
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {ι : Type*} (s : Finset ι) (v : ι → ClassFunction G ℂ) (c m : ι → ℝ)
    (Z : ClassFunction G ℂ)
    (hY : D.Y = (∑ i ∈ s, (c i : ℂ) • v i) + Z)
    (horth : ∀ i ∈ s, ∀ j ∈ s, ClassFunction.inner (v i) (v j) =
      if i = j then (m i : ℂ) else 0)
    (hZ : ∀ i ∈ s, ClassFunction.inner Z (v i) = 0) :
    (∑ i ∈ s, (c i) ^ 2 * m i) + (ClassFunction.inner Z Z).re ≤
      (ClassFunction.inner ψ ψ).re := by
  have hpyth := inner_self_orthogonalSum_add_re (G := G) s v c m Z horth hZ
  have hYnorm : (ClassFunction.inner D.Y D.Y).re =
      (∑ i ∈ s, (c i) ^ 2 * m i) + (ClassFunction.inner Z Z).re := by
    rw [hY]; exact hpyth
  have hbound := D.inner_self_Y_re_le_inner_self_psi
  rw [hYnorm] at hbound
  exact hbound

open scoped Classical in
/-- **Peterfalvi (5.6.2) capstone: `λ = 0` and `Z = 0`.**

Composes the geometric half (`sum_sq_mul_add_normSq_Z_le`) and the arithmetic half
(`int_eq_zero_of_sq_mul_le_of_two_mul_lt`).  The (5.6.1) decomposition writes the orthogonal
part as

`Y = (∑ i ∈ s, (a·[i = i₁] - λ·r i) • v i) + Z`,

against the orthogonal family `v i` (real gram `m i = ‖χ_i‖²`, `v i = χ_i^{τ₁}`) with `Z`
orthogonal to the family, where `r i = a_i / ‖χ_i‖²`, `i₁` indexes `χ₁`, and `ψ = a·χ₁` (so
`‖ψ‖² = a²·m i₁`, hypothesis `hψ`) with `a₁ = 1` (so `r i₁ · m i₁ = 1`, hypothesis `hr₁`).

The Pythagoras expansion gives `∑ (a·[i=i₁] - λ·r i)²·m i + ‖Z‖² ≤ ‖ψ‖² = a²·m i₁`; the
algebraic identity collapses the left sum to `a²·m i₁ - 2·a·λ + λ²·D` with
`D = ∑ (r i)²·m i`, so `λ²·D - 2·λ·a + ‖Z‖² ≤ 0`.  Hypothesis (c) `2·a < D` then forces
`λ = 0` (`int_eq_zero_of_sq_mul_le_of_two_mul_lt`), and feeding `λ = 0` back gives `‖Z‖² ≤ 0`,
hence `Z = 0` by positive definiteness. -/
theorem lambda_eq_zero_and_Z_eq_zero
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {ι : Type*} (s : Finset ι) (i₁ : ι) (hi₁ : i₁ ∈ s)
    (a : ℝ) (lam : ℤ) (Z : ClassFunction G ℂ)
    (vc : ι → ClassFunction G ℂ) (mc : ι → ℝ) (rc : ι → ℝ)
    (hY : D.Y = (∑ i ∈ s, ((a * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i : ℝ) : ℂ) • vc i)
      + Z)
    (horth : ∀ i ∈ s, ∀ j ∈ s, ClassFunction.inner (vc i) (vc j) =
      if i = j then (mc i : ℂ) else 0)
    (hZ : ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0)
    (hψ : (ClassFunction.inner ψ ψ).re = a ^ 2 * mc i₁)
    (hr₁ : rc i₁ * mc i₁ = 1)
    (ha : 0 ≤ a)
    (hD : 2 * a < ∑ i ∈ s, (rc i) ^ 2 * mc i) :
    lam = 0 ∧ Z = 0 := by
  classical
  -- Geometric half: `∑ (c i)²·m i + ‖Z‖² ≤ ‖ψ‖²`.
  have hgeo := D.sum_sq_mul_add_normSq_Z_le s vc
    (fun i => a * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i) mc Z hY horth hZ
  -- Algebraic collapse of the left sum.
  have halg : (∑ i ∈ s, (a * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i) ^ 2 * mc i)
      = a ^ 2 * mc i₁ - 2 * a * (lam : ℝ) * (rc i₁ * mc i₁)
        + (lam : ℝ) ^ 2 * ∑ i ∈ s, (rc i) ^ 2 * mc i := by
    have key : ∀ i ∈ s,
        (a * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i) ^ 2 * mc i
        = (if i = i₁ then (a ^ 2 * mc i₁ - 2 * a * (lam : ℝ) * (rc i₁ * mc i₁)) else 0)
          + (lam : ℝ) ^ 2 * ((rc i) ^ 2 * mc i) := by
      intro i hi
      by_cases h : i = i₁
      · subst h; rw [if_pos rfl, if_pos rfl]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq' s i₁,
      if_pos hi₁, ← Finset.mul_sum]
  -- Substitute `r i₁ · m i₁ = 1` and `‖ψ‖² = a²·m i₁`; obtain the quadratic `≤ 0`.
  set Dsum := ∑ i ∈ s, (rc i) ^ 2 * mc i with hDsum
  have hquad : (lam : ℝ) ^ 2 * Dsum - 2 * (lam : ℝ) * a + (ClassFunction.inner Z Z).re ≤ 0 := by
    rw [halg, hr₁, hψ, mul_one] at hgeo
    nlinarith [hgeo]
  -- Integer forcing (cast to ℚ) gives `λ = 0`.
  have hZre_nonneg : (0 : ℝ) ≤ (ClassFunction.inner Z Z).re := inner_self_re_nonneg Z
  have hlam0 : lam = 0 := by
    -- Work over ℝ directly: the integer-forcing argument transcribed.
    by_contra hne
    rcases lt_trichotomy lam 0 with hneg | hzero | hpos
    · have hlamR : (lam : ℝ) < 0 := by exact_mod_cast hneg
      have hsq_pos : 0 < (lam : ℝ) ^ 2 := by positivity
      have hDpos : 0 < Dsum := by
        have : (0 : ℝ) ≤ 2 * a := by linarith
        linarith [hD]
      nlinarith [mul_pos hsq_pos hDpos, hZre_nonneg, mul_nonneg ha (le_of_lt (neg_pos.mpr hlamR))]
    · exact hne hzero
    · have hlam1 : (1 : ℝ) ≤ (lam : ℝ) := by
        have : (1 : ℤ) ≤ lam := hpos; exact_mod_cast this
      have hlampos : (0 : ℝ) < (lam : ℝ) := by linarith
      -- `λ²·D - 2λa + ‖Z‖² ≤ 0`, `‖Z‖² ≥ 0` ⟹ `λ²·D ≤ 2λa`, cancel `λ` ⟹ `λ·D ≤ 2a < D`.
      have hcore : (lam : ℝ) ^ 2 * Dsum ≤ 2 * (lam : ℝ) * a := by linarith
      have hcancel : (lam : ℝ) * Dsum ≤ 2 * a := by
        have h2 : (lam : ℝ) * ((lam : ℝ) * Dsum) ≤ (lam : ℝ) * (2 * a) := by nlinarith [hcore]
        exact le_of_mul_le_mul_left h2 hlampos
      nlinarith [hcancel, hlam1, hD]
  refine ⟨hlam0, ?_⟩
  -- Feed `λ = 0` back: `‖Z‖² ≤ 0`, hence `Z = 0`.
  have hZ0 : (ClassFunction.inner Z Z).re ≤ 0 := by
    rw [hlam0] at hquad; push_cast at hquad; nlinarith [hquad]
  exact eq_zero_of_inner_self_re_eq_zero (le_antisymm hZ0 hZre_nonneg)

open scoped Classical in
/-- **Peterfalvi (5.6.1)→(5.6.2): the `Y`-collapse `Y = a·χ₁^{τ₁}`.**

For the `ψ = a·χ₁` decomposition `D : CharacterPsiDecomposition τ χ (a·χ₁)`, the **(5.6.1)
λ-form** of the orthogonal part is

`Y = a·χ₁^{τ₁} − λ·∑ᵢ (aᵢ/‖χᵢ‖²)·χᵢ^{τ₁} + Z`     (mmd L73)

where `λ ∈ ℤ`, the family `vc i = χᵢ^{τ₁}` (indexed over `s`, with `i₁ ∈ s` indexing `χ₁`, so
`vc i₁ = D.tau1 χ₁`) is orthogonal with real gram `⟨vcᵢ, vcⱼ⟩ = if i = j then mc i else 0`
(`mc i = ‖χᵢ‖²`), `rc i = aᵢ/‖χᵢ‖²`, and `Z` is orthogonal to the family.  Under the (5.4.a) opening
bound (`inner_self_Y_re_le_inner_self_psi`, internal to the family) together with the textbook
hypotheses `‖ψ‖² = a²·‖χ₁‖²` (`hψ`), `a₁ = 1 ⇒ rc i₁·mc i₁ = 1` (`hr₁`), and the degree inequality
(c) `2·a < ∑ᵢ(aᵢ/‖χᵢ‖²)²·‖χᵢ‖²` (`hD`), the integer-forcing capstone
`lambda_eq_zero_and_Z_eq_zero` collapses `λ = 0` and `Z = 0`.  Feeding these back into the λ-form
yields the (5.6.2) conclusion `Y = a·χ₁^{τ₁}` (`D.Y = a • D.tau1 χ₁`).

This is the producer of the `hY` hypothesis that `X_eq_tau1_chi_of_Y_eq` /
`X_eq_of_tau1_eq_on_chi` / `image_eq_of_decomposition` /
`retarget_isCoherent_of_decompositions[_and_memberFamily]` all consume: it *constructs* the
(5.6.2) collapse from the (5.6.1) decomposition and the orthogonal-projection data, rather than
positing `Y = a·χ₁^{τ₁}`. -/
theorem Y_eq_nsmul_tau1_of_lambdaForm {a : ℕ} {chi1 : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    {ι : Type*} (s : Finset ι) (i₁ : ι) (hi₁ : i₁ ∈ s)
    (lam : ℤ) (Z : ClassFunction G ℂ)
    (vc : ι → ClassFunction G ℂ) (mc rc : ι → ℝ)
    (hvc1 : vc i₁ = D.tau1 chi1)
    (hYform : D.Y =
      (a : ℂ) • D.tau1 chi1 - (lam : ℂ) • (∑ i ∈ s, (rc i : ℂ) • vc i) + Z)
    (horth : ∀ i ∈ s, ∀ j ∈ s, ClassFunction.inner (vc i) (vc j) =
      if i = j then (mc i : ℂ) else 0)
    (hZ : ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0)
    (hψ : (ClassFunction.inner (a • chi1 : ClassFunction L ℂ) (a • chi1)).re
      = (a : ℝ) ^ 2 * mc i₁)
    (hr₁ : rc i₁ * mc i₁ = 1)
    (hD : 2 * (a : ℝ) < ∑ i ∈ s, (rc i) ^ 2 * mc i) :
    D.Y = a • D.tau1 chi1 := by
  classical
  -- Bridge the (5.6.1) λ-form to the capstone's pointwise-coefficient form.
  have hbridge : D.Y =
      (∑ i ∈ s, (((a : ℝ) * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i : ℝ) : ℂ) • vc i) + Z := by
    rw [hYform]
    congr 1
    -- `(a:ℂ)•vc(i₁) − λ•∑ rcᵢ•vcᵢ = ∑ᵢ (a[i=i₁] − λ·rcᵢ)•vcᵢ`.
    rw [← hvc1]
    -- Split each summand on the RHS into its `a`-part and its `λ`-part.
    have hsplit : ∀ i ∈ s,
        (((a : ℝ) * (if i = i₁ then 1 else 0) - (lam : ℝ) * rc i : ℝ) : ℂ) • vc i =
          (if i = i₁ then ((a : ℂ) • vc i₁) else 0)
            - (lam : ℂ) • ((rc i : ℂ) • vc i) := by
      intro i _
      by_cases h : i = i₁
      · subst h; simp only [if_pos rfl]; push_cast; rw [sub_smul]; module
      · simp only [if_neg h]; push_cast; rw [sub_smul]; module
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' s i₁, if_pos hi₁, ← Finset.smul_sum]
  -- Capstone forcing: `λ = 0` and `Z = 0`.
  obtain ⟨hlam0, hZ0⟩ :=
    D.lambda_eq_zero_and_Z_eq_zero s i₁ hi₁ (a : ℝ) lam Z vc mc rc hbridge horth hZ
      hψ hr₁ (by positivity) hD
  -- Feed `λ = 0`, `Z = 0` back into the λ-form.
  rw [hYform, hlam0, hZ0]
  simp only [Int.cast_zero, zero_smul, sub_zero, add_zero]
  -- `(a:ℂ)•D.tau1 χ₁ = a • D.tau1 χ₁` (nsmul).
  rw [Nat.cast_smul_eq_nsmul]

/-! #### Peterfalvi (5.6.3) projection identity `Da.X = D₀.X`

The (5.6.3) extension `τ₂` is defined with `χ^{τ₂} = X` where `X` is *the same* `X` for the
`ψ = 0` decomposition `D₀` (giving `χ^{τ₁} = X` by (5.5)) and the `ψ = a·χ₁` decomposition `Da`
(giving `(χ − a·χ₁)^{τ₁} = X − Y`).  This is only well-defined because **the `R(χ)`-projection `X`
is independent of `ψ`**.  The two lemmas below *derive* this, rather than positing it:

* For the `ψ = a·χ₁` decomposition `Da`, the (5.6.2) collapse `Y = a·χ₁^{τ₁}`
  (`lambda_eq_zero_and_Z_eq_zero` fed back) gives `Da.X = Da.tau1 χ` directly, by linearity of
  `Da.tau1` on `χ − a·χ₁` (`X_eq_tau1_chi_of_Y_eq`);
* the (5.5) decomposition `D₀` gives `D₀.tau1 χ = D₀.X` (`eq_sum_of_psi_eq_zero`).

When the two decompositions are built against the *same* auxiliary isometry `τ₁` (the running
coherence extension), `Da.tau1 χ = D₀.tau1 χ`, so `Da.X = Da.tau1 χ = D₀.tau1 χ = D₀.X`
(`X_eq_of_tau1_eq_on_chi`).  The agreement `Da.tau1 χ = D₀.tau1 χ` is the honest input — it is what
"both decompositions use the running `τ₁`" means — *not* the conclusion `Da.X = D₀.X` itself. -/

/-- **Peterfalvi (5.6.2)/(5.6.3) `X = χ^{τ₁}` for the `ψ = a·χ₁` decomposition.**

For a decomposition `D : CharacterPsiDecomposition τ χ (a·χ₁)` whose orthogonal part has collapsed
to `Y = a·χ₁^{τ₁}` (the (5.6.2) conclusion, `hY`), the image part `X` equals `χ^{τ₁}`:
`D.X = D.tau1 χ`.

`D.tau1 (χ − a·χ₁) = D.X − D.Y = D.X − a·χ₁^{τ₁}` (`tau1_image`, `hY`), while linearity gives
`D.tau1 (χ − a·χ₁) = χ^{τ₁} − a·χ₁^{τ₁}` (`map_sub`, `map_nsmul`).  Cancelling `a·χ₁^{τ₁}` yields
`D.X = χ^{τ₁}`.  This is the `ψ`-independence of the `R(χ)`-projection used in (5.6.3). -/
theorem X_eq_tau1_chi_of_Y_eq {a : ℕ} {chi1 : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    (hY : D.Y = a • D.tau1 chi1) :
    D.X = D.tau1 χ := by
  have himg := D.tau1_image
  rw [hY, map_sub, map_nsmul] at himg
  -- `χ^{τ₁} − a·χ₁^{τ₁} = X − a·χ₁^{τ₁}` ⟹ `χ^{τ₁} = X` ⟹ `X = χ^{τ₁}`.
  exact (sub_left_inj.mp himg).symm

/-- **Peterfalvi (5.6.3) projection identity `Da.X = D₀.X`.**

The `R(χ)`-projection `X` is the same for the `ψ = 0` decomposition `D₀` and the `ψ = a·χ₁`
decomposition `Da`, *provided both use the same auxiliary isometry `τ₁` on `χ`* (the honest input
`htau1_chi : Da.tau1 χ = D₀.tau1 χ`, expressing that both decompositions are built against the
running coherence extension).

`Da.X = Da.tau1 χ` (by `X_eq_tau1_chi_of_Y_eq`, using the (5.6.2) collapse `hY`), `Da.tau1 χ =
D₀.tau1 χ` (`htau1_chi`), `D₀.tau1 χ = D₀.X` (`eq_sum_of_psi_eq_zero` for `ψ = 0`).  Chaining gives
`Da.X = D₀.X`.  This *constructs* the `hX_eq` hypothesis of
`retarget_isCoherent_of_decompositions` from the two decompositions and the τ₁-agreement, rather
than positing it. -/
theorem X_eq_of_tau1_eq_on_chi {a : ℕ} {chi1 : ClassFunction L ℂ}
    (D₀ : CharacterPsiDecomposition (L := L) (G := G) τ χ 0)
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • chi1))
    (hY : Da.Y = a • Da.tau1 chi1)
    (htau1_chi : Da.tau1 χ = D₀.tau1 χ) :
    Da.X = D₀.X := by
  rw [Da.X_eq_tau1_chi_of_Y_eq hY, htau1_chi, (D₀.eq_sum_of_psi_eq_zero).2.1]

open scoped Classical in
/-- **Peterfalvi (5.6.3) conjugate image as a complementary signed sum.**
Given the (5.4.b)/(5.5) output `X = ∑_{α ∈ E} α` for a subset `E ⊆ R(χ)`, the candidate
image of `χ̄` under `τ₂`, namely `X - (χ - χ̄)^τ`, equals the **negated** sum over the
complement `R(χ) - E`:

`X - τ(χ - χ̄) = -∑_{α ∈ R(χ) - E} α`.

Since `(χ - χ̄)^τ = ∑_{α ∈ R(χ)} α` (the image-family equation) and `E ⊆ R(χ)`, the
difference telescopes to the complement. -/
theorem conjImage_eq_neg_sum_sdiff
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {E : Finset (ClassFunction G ℂ)} (hE : E ⊆ D.imageFamily.imageSet)
    (hX : D.X = ∑ α ∈ E, α) :
    D.X - τ (χ - χ.conj) = -(∑ α ∈ D.imageFamily.imageSet \ E, α) := by
  classical
  rw [hX, D.imageFamily.image_eq]
  have h := Finset.sum_sdiff (s₁ := E) (s₂ := D.imageFamily.imageSet) hE (f := fun a => a)
  rw [← h]; abel

open scoped Classical in
/-- **Peterfalvi (5.6.3) norm of the conjugate image:** `‖X - (χ - χ̄)^τ‖² = |R(χ)| - |E|`.
With `X = ∑_{α ∈ E} α` (`E ⊆ R(χ)`), the candidate `χ̄^{τ₂} = X - (χ - χ̄)^τ` is the negated
sum over `R(χ) - E`, whose squared norm is the cardinality `|R(χ) - E| = |R(χ)| - |E|` by
orthonormality of `R(χ)`.  This is the computation
`‖χ̄^{τ₂}‖² = |R(χ) - E| = ‖χ - χ̄‖² - ‖χ‖² = ‖χ̄‖²` of the text. -/
theorem inner_self_conjImage_eq_card_sdiff
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {E : Finset (ClassFunction G ℂ)} (hE : E ⊆ D.imageFamily.imageSet)
    (hX : D.X = ∑ α ∈ E, α) :
    ClassFunction.inner (D.X - τ (χ - χ.conj)) (D.X - τ (χ - χ.conj)) =
      ((D.imageFamily.imageSet.card : ℤ) - (E.card : ℤ) : ℂ) := by
  classical
  have horth' : ∀ a ∈ D.imageFamily.imageSet \ E, ∀ b ∈ D.imageFamily.imageSet \ E,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 :=
    fun a ha b hb => D.imageFamily.orthonormal a (Finset.mem_sdiff.mp ha).1 b
      (Finset.mem_sdiff.mp hb).1
  rw [D.conjImage_eq_neg_sum_sdiff hE hX, ClassFunction.inner_neg_left,
    ClassFunction.inner_neg_right, neg_neg,
    inner_self_sum_orthonormal_eq_card horth', Finset.card_sdiff_of_subset hE]
  have hle : E.card ≤ D.imageFamily.imageSet.card := Finset.card_le_card hE
  push_cast [Nat.cast_sub hle]
  ring

open scoped Classical in
/-- **Peterfalvi (5.6.3) orthogonality `⟨X, χ̄^{τ₂}⟩ = 0`.**  The candidate images
`χ^{τ₂} = X = ∑_{α ∈ E} α` and `χ̄^{τ₂} = X - (χ - χ̄)^τ = -∑_{α ∈ R(χ) - E} α` are
orthogonal: their inner product is a cross term over the disjoint subsets `E` and
`R(χ) - E` of the orthonormal family `R(χ)`, hence `0`. -/
theorem inner_X_conjImage_eq_zero
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {E : Finset (ClassFunction G ℂ)} (hE : E ⊆ D.imageFamily.imageSet)
    (hX : D.X = ∑ α ∈ E, α) :
    ClassFunction.inner D.X (D.X - τ (χ - χ.conj)) = 0 := by
  classical
  rw [D.conjImage_eq_neg_sum_sdiff hE hX, ClassFunction.inner_neg_right, hX,
    inner_sum_orthonormal_eq_zero_of_disjoint hE (Finset.sdiff_subset)
      (Finset.disjoint_sdiff) D.imageFamily.orthonormal, neg_zero]

/-! ##### Peterfalvi (5.5)+(5.2.e): the image-side orthogonality `X, X̄ ⊥ η`

`retarget_isCoherent_of_decomposition` consumes the lattice orthogonalities `hX_ortho`/`hXbar_ortho`
— `⟨τ₁ ξ, X⟩ = ⟨τ₁ ξ, X̄⟩ = 0` for `ξ ∈ ℤ[S₁]` (`τ₁ := hS₁.extension`).  In the text these are the
(5.5)+(5.2.e) facts: `X ∈ ℤ[R(χ)]` (the (5.5) output `X = ∑ coeff•α`, `X_eq`), `X̄ = X − (χ − χ̄)^τ ∈
ℤ[R(χ)]` too (`(χ − χ̄)^τ = ∑_{α∈R(χ)}α`, `imageFamily.image_eq`), and for every `χᵢ ∈ S₁` the image
`χᵢ^{τ₁}` is orthogonal to `R(χ)` (by (5.5) for `χᵢ` and (5.2.e) `R(χᵢ) ⊥ R(χ)`), so `τ₁ ξ ⊥ R(χ)`
for every `ξ ∈ ℤ[S₁]`.

The two reductions *derive* `hX_ortho`/`hXbar_ortho` from the **per-element** `R(χ)`-orthogonality
`∀ α ∈ R(χ), ⟨η, α⟩ = 0` (the genuine (5.5)+(5.2.e) input, leaving only that as the residual coupling
to the family `{R(χᵢ)}`).  Stated for an arbitrary `η : CF(G)`, so the caller plugs
`η := hS₁.extension ξ`. -/

/-- **(5.5) reduction `η ⊥ X`.**  If `η` is orthogonal to every member of `R(χ)`, then `η` is
orthogonal to `X = D.X ∈ ℤ[R(χ)]` (the (5.5) output `X = ∑ coeff•α`).  This is the `hX_ortho` half
of (5.6.3): `⟨η, X⟩ = ∑ coeff·⟨η, α⟩ = 0`. -/
theorem inner_X_eq_zero_of_orthogonal_imageSet
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {η : ClassFunction G ℂ}
    (hη : ∀ α ∈ D.imageFamily.imageSet, ClassFunction.inner η α = 0) :
    ClassFunction.inner η D.X = 0 := by
  rw [D.X_eq, OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_smul_right, hη α hα, mul_zero]

/-- **(5.5) reduction `η ⊥ X̄`.**  If `η` is orthogonal to every member of `R(χ)`, then `η` is
orthogonal to `X̄ = X − (χ − χ̄)^τ`.  Both `X = ∑ coeff•α` (`X_eq`) and `(χ − χ̄)^τ = ∑_{α∈R(χ)}α`
(`imageFamily.image_eq`) lie in `ℤ[R(χ)]`, so `⟨η, X̄⟩ = ⟨η, X⟩ − ⟨η, (χ−χ̄)^τ⟩ = 0 − 0 = 0`.  This
is the `hXbar_ortho` half of (5.6.3). -/
theorem inner_conjImage_eq_zero_of_orthogonal_imageSet
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    {η : ClassFunction G ℂ}
    (hη : ∀ α ∈ D.imageFamily.imageSet, ClassFunction.inner η α = 0) :
    ClassFunction.inner η (D.X - τ (χ - χ.conj)) = 0 := by
  rw [ClassFunction.inner_sub_right, D.inner_X_eq_zero_of_orthogonal_imageSet hη,
    D.imageFamily.image_eq, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_eq_zero fun α hα => hη α hα, sub_zero]

/-- **Peterfalvi (5.2.e) feed: `X ⊥ R(χ')` from `R(χ) ⊥ R(χ')`.**  The image part `X = D.X ∈
ℤ[R(χ)]` of the (5.4) decomposition for `χ` is orthogonal to every member of a *second* image
family `R'` whenever the two families are orthogonal (`D.imageFamily.Orthogonal R'`, the (5.2.e)
hypothesis).  `⟨X, α⟩ = ⟨∑_{β∈R(χ)} coeff β • β, α⟩ = ∑ coeff β · ⟨β, α⟩ = 0` since each `⟨β, α⟩ =
0`.  This is the per-character half of the (5.6.1) remark "`χᵢ^{τ₁}` is orthogonal to `R(χ)` by
(5.5) and (5.2.e)" (mmd L77): for the family member `χ' := χᵢ` (with `D` its `ψ = 0` decomposition,
so `χᵢ^{τ₁} = D.X` by (5.5)) and the distinguished `R' := R(χ)`. -/
theorem inner_X_orthogonal_imageSet_of_orthogonal
    {χ' : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (R' : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ')
    (hortho : D.imageFamily.Orthogonal R')
    {α : ClassFunction G ℂ} (hα : α ∈ R'.imageSet) :
    ClassFunction.inner D.X α = 0 := by
  rw [D.X_eq, OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun β hβ => ?_
  rw [ClassFunction.inner_smul_left, hortho.inner_eq_zero hβ hα, mul_zero]

/-! #### Peterfalvi (5.6.3) target pair `{X, X̄}` from the `ψ = 0` decomposition

The §7 keystone `retarget_isCoherent` consumes an **orthonormal target pair** `{X, X̄} ⊂ ℤ[Irr G]`
with `X̄ = X − (χ − χ̄)^τ` and the lattice orthogonality `X, X̄ ⊥ τ₁ S₁`.  For an *irreducible*
`χ` (the (6.6) case: every `χᵢ` is irreducible, so `‖χ‖² = 1`) this whole pair is **forced** by
the (5.5) decomposition `D : CharacterPsiDecomposition τ χ 0` together with the orthonormality of
the source pair `{χ, χ̄}` — *no* free-module basis extension / Gram–Schmidt is needed.  The
arithmetic is the one Peterfalvi performs verbatim in (5.6.3):

* `(5.5)` gives `X^{τ₂} = X = ∑_{α ∈ E} α` with `|E| = ‖χ‖² = 1`, so `X` is a **single**
  element of `R(χ)`, hence orthonormal (`‖X‖² = |E| = 1`) and a virtual character;
* `|R(χ)| = ‖(χ − χ̄)^τ‖² = ‖χ − χ̄‖² = 2` (isometry of `τ₁`, `tau1_agrees`, orthonormal `{χ, χ̄}`),
  so `‖X̄‖² = |R(χ)| − |E| = 2 − 1 = 1` (`inner_self_conjImage_eq_card_sdiff`);
* `⟨X, X̄⟩ = 0` (`inner_X_conjImage_eq_zero`), and `X̄ = X − (χ − χ̄)^τ ∈ ℤ[Irr G]`.

This is the constructible foundational brick of the G2.7 hstep gate: it discharges the `{X, X̄}`
block of `retarget_isCoherent` (`hXX`/`hXbarXbar`/`hXXbar`/`hXbarX`/`hXbar_def`) plus virtual-character
membership, *from* a decomposition `D`.  Producing `D` itself (the auxiliary isometry `τ₁` agreeing
with the running coherence extension on `χ − χ̄`) is the separate, genuinely hard step. -/

/-- The orthonormal target pair `{X, X̄}` of Peterfalvi (5.6.3), bundled with the facts the
re-targeting keystone needs.  Here `X̄ = X − (χ − χ̄)^τ`. -/
structure RetargetTargetPair (D : CharacterPsiDecomposition (L := L) (G := G) τ χ 0) where
  /-- `X ∈ ℤ[Irr G]` (a virtual character of `G`). -/
  X_mem_ZIrr : D.X ∈ ZIrr G
  /-- The conjugate image `X̄ = X − (χ − χ̄)^τ ∈ ℤ[Irr G]`. -/
  conjImage_mem_ZIrr : D.X - τ (χ - χ.conj) ∈ ZIrr G
  /-- `‖X‖² = 1`. -/
  inner_self_X : ClassFunction.inner D.X D.X = 1
  /-- `‖X̄‖² = 1`. -/
  inner_self_conjImage :
    ClassFunction.inner (D.X - τ (χ - χ.conj)) (D.X - τ (χ - χ.conj)) = 1
  /-- `⟨X, X̄⟩ = 0`. -/
  inner_X_conjImage : ClassFunction.inner D.X (D.X - τ (χ - χ.conj)) = 0
  /-- `⟨X̄, X⟩ = 0`. -/
  inner_conjImage_X : ClassFunction.inner (D.X - τ (χ - χ.conj)) D.X = 0

open scoped Classical in
/-- **Peterfalvi (5.6.3): the orthonormal target pair `{X, X̄}` for an irreducible `χ`.**

From the (5.5) decomposition `D` of an irreducible `χ` (`‖χ‖² = 1`) together with the
orthonormality of the source pair `{χ, χ̄}`, the pair `{X, X̄ := X − (χ − χ̄)^τ}` is orthonormal
in `ℤ[Irr G]`.  This *constructs* — does not posit — the `{X, X̄}` block of `retarget_isCoherent`.

`(5.5)` yields `X = ∑_{α ∈ E} α` with `|E| = ‖χ‖² = 1`; the source-pair norm computation
`|R(χ)| = ‖χ − χ̄‖² = 2` (via `tau1_agrees` and the isometry of `τ₁`) then gives
`‖X̄‖² = |R(χ)| − |E| = 1`, while `‖X‖² = |E| = 1` and `⟨X, X̄⟩ = 0` are read off the orthonormal
family directly. -/
noncomputable def retargetTargetPair
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ 0)
    (hχχ : ClassFunction.inner χ χ = 1)
    (hχbarχbar : ClassFunction.inner χ.conj χ.conj = 1)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0) :
    D.RetargetTargetPair := by
  classical
  -- (5.5): `X = ∑_{α ∈ E} α` with `|E| = ‖χ‖² = 1`.
  obtain ⟨_hY0, _hτ1χ, E, hEsub, hXsum, hEcard⟩ := D.eq_sum_of_psi_eq_zero
  have hEcard1 : E.card = 1 := by
    have : (E.card : ℂ) = 1 := by rw [hEcard, hχχ]
    exact_mod_cast this
  -- `|R(χ)| = ‖(χ − χ̄)^τ‖²`, and `(χ − χ̄)^τ = (χ − χ̄)^{τ₁}` is a `τ₁`-isometry image, so
  -- `|R(χ)| = ‖χ − χ̄‖² = 2`.
  have hcardR : D.imageFamily.imageSet.card = 2 := by
    have h1 : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) =
        (D.imageFamily.imageSet.card : ℂ) := by
      rw [D.imageFamily.image_eq, inner_self_sum_orthonormal_eq_card D.imageFamily.orthonormal]
    have h2 : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) =
        ClassFunction.inner (χ - χ.conj) (χ - χ.conj) := by
      rw [← D.tau1_agrees, D.tau1_inner_eq_on_support (χ - χ.conj) (χ - χ.conj)
        chi_sub_conj_mem_zSpan_support chi_sub_conj_mem_zSpan_support]
    have h3 : ClassFunction.inner (χ - χ.conj) (χ - χ.conj) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hχχ, hχbarχbar, hχχbar, hχbarχ]
      ring
    have : (D.imageFamily.imageSet.card : ℂ) = 2 := by rw [← h1, h2, h3]
    exact_mod_cast this
  -- `‖X‖² = |E| = 1`.
  have hXnorm : ClassFunction.inner D.X D.X = 1 := by
    rw [hXsum, inner_self_sum_orthonormal_eq_card
      (fun a ha b hb => D.imageFamily.orthonormal a (hEsub ha) b (hEsub hb)), hEcard1]
    norm_num
  -- `‖X̄‖² = |R(χ)| − |E| = 2 − 1 = 1`.
  have hXbarnorm : ClassFunction.inner (D.X - τ (χ - χ.conj)) (D.X - τ (χ - χ.conj)) = 1 := by
    rw [D.inner_self_conjImage_eq_card_sdiff hEsub hXsum, hcardR, hEcard1]
    push_cast
    norm_num
  -- `⟨X, X̄⟩ = 0`, and `⟨X̄, X⟩ = 0` by conjugate symmetry.
  have hXXbar : ClassFunction.inner D.X (D.X - τ (χ - χ.conj)) = 0 :=
    D.inner_X_conjImage_eq_zero hEsub hXsum
  have hXbarX : ClassFunction.inner (D.X - τ (χ - χ.conj)) D.X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXXbar, star_zero]
  -- `X ∈ ℤ[Irr G]` (sum of `R(χ)` members) and `X̄ = X − (χ − χ̄)^τ ∈ ℤ[Irr G]`.
  have hXmem : D.X ∈ ZIrr G := by
    rw [hXsum]
    exact Submodule.sum_mem _ fun α hα => D.imageFamily.mem_ZIrr α (hEsub hα)
  have hτmem : τ (χ - χ.conj) ∈ ZIrr G := by
    rw [D.imageFamily.image_eq]
    exact Submodule.sum_mem _ fun α hα => D.imageFamily.mem_ZIrr α hα
  exact
    { X_mem_ZIrr := hXmem
      conjImage_mem_ZIrr := Submodule.sub_mem _ hXmem hτmem
      inner_self_X := hXnorm
      inner_self_conjImage := hXbarnorm
      inner_X_conjImage := hXXbar
      inner_conjImage_X := hXbarX }

end CharacterPsiDecomposition

/-! ### The orthonormal-block isometry re-targeting keystone

The (5.6.3) construction of `τ₂` from `τ₁` is an instance of a reusable operation: given a
**global** integral isometry `τ₁ : ℤ[Irr L] → ℤ[Irr G]` (here at the class-function level over
`ℂ`), an **orthonormal pair** `{χ, χ̄}` in the source and an **orthonormal pair** `{X, X̄}` in the
target with the *same* gram matrix, re-target the rank-`2` block: send `χ ↦ X`, `χ̄ ↦ X̄`, keeping
`τ₁` on the orthogonal complement of `{χ, χ̄}`.  The single hypothesis making this a global isometry
is that `X` and `X̄` are orthogonal to `τ₁ ψ` for *every* `ψ` orthogonal to both `χ` and `χ̄`
(in the (5.6) application this is `(5.5) + (5.2.e)`: `S₁^{τ₁} ⊥ R(χ)` and `X, X̄ ∈ ℤ[R(χ)]`).

The construction is the explicit correction map
`τ₂ φ = τ₁ φ + ⟨φ,χ⟩·(X − τ₁χ) + ⟨φ,χ̄⟩·(X̄ − τ₁χ̄)`,
which automatically equals `τ₁` off `{χ, χ̄}` (the Gram–Schmidt residual
`φ⊥ = φ − ⟨φ,χ⟩χ − ⟨φ,χ̄⟩χ̄` lands in `{χ, χ̄}^⊥`, so the hypothesis applies to it). -/

/-- Pointwise evaluation of a finite sum of class functions (the `Finset` analogue of
`ClassFunction.add_apply`). -/
theorem classFunction_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → ClassFunction L ℂ) (g : L) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]

namespace IntegralCharacterMap

open OddOrder.RepresentationTheory

variable [Fintype L] [Invertible (Nat.card L : ℂ)]

/-- The integral-linear functional `φ ↦ ⟨φ, η⟩` (linear in the **first** argument). -/
noncomputable def innerLeftℤ (η : ClassFunction L ℂ) : ClassFunction L ℂ →ₗ[ℤ] ℂ where
  toFun φ := ClassFunction.inner φ η
  map_add' a b := ClassFunction.inner_add_left a b η
  map_smul' n a := by
    simp only [RingHom.id_apply, zsmul_eq_mul]
    rw [← Int.cast_smul_eq_zsmul ℂ n a, ClassFunction.inner_smul_left]

@[simp] theorem innerLeftℤ_apply (η φ : ClassFunction L ℂ) :
    innerLeftℤ (L := L) η φ = ClassFunction.inner φ η := rfl

/-- The Gram–Schmidt residual `φ⊥ = φ − ⟨φ,χ⟩χ − ⟨φ,χ̄⟩χ̄` against `{χ, χ̄}`, as a `ℤ`-linear
endomorphism of `ClassFunction L ℂ`.  This is `ℂ`-linear (the inner product is `ℂ`-linear in
its first argument), and in particular `ℤ`-linear, so it composes with the `ℤ`-linear `τ₁`. -/
noncomputable def orthoResidualMap (χ chibar : ClassFunction L ℂ) :
    ClassFunction L ℂ →ₗ[ℤ] ClassFunction L ℂ :=
  LinearMap.id - (innerLeftℤ (L := L) χ).smulRight χ
    - (innerLeftℤ (L := L) chibar).smulRight chibar

@[simp] theorem orthoResidualMap_apply (χ chibar φ : ClassFunction L ℂ) :
    orthoResidualMap (L := L) χ chibar φ =
      φ - ClassFunction.inner φ χ • χ - ClassFunction.inner φ chibar • chibar := by
  simp [orthoResidualMap, LinearMap.smulRight_apply]

/-- The residual `φ⊥` is orthogonal to `χ` (using orthonormality of `{χ, χ̄}`). -/
theorem inner_orthoResidualMap_left {χ chibar : ClassFunction L ℂ}
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (φ : ClassFunction L ℂ) :
    ClassFunction.inner (orthoResidualMap (L := L) χ chibar φ) χ = 0 := by
  rw [orthoResidualMap_apply, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, hχχ, hχbarχ,
    mul_one, mul_zero, sub_zero, sub_self]

/-- The residual `φ⊥` is orthogonal to `χ̄` (using orthonormality of `{χ, χ̄}`). -/
theorem inner_orthoResidualMap_right {χ chibar : ClassFunction L ℂ}
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (φ : ClassFunction L ℂ) :
    ClassFunction.inner (orthoResidualMap (L := L) χ chibar φ) chibar = 0 := by
  rw [orthoResidualMap_apply, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, hχχbar, hχbarχbar,
    mul_one, mul_zero, sub_zero, sub_self]

/-- The rank-`2` **re-targeting** of an integral isometry `τ₁`:
`φ ↦ τ₁ φ⊥ + ⟨φ,χ⟩·X + ⟨φ,χ̄⟩·X̄`, where `φ⊥ = φ − ⟨φ,χ⟩χ − ⟨φ,χ̄⟩χ̄` is the Gram–Schmidt
residual.  For an orthonormal pair `{χ, χ̄}` this sends `χ ↦ X`, `χ̄ ↦ X̄`, and keeps `τ₁`
on the orthogonal complement `{χ, χ̄}^⊥` (where `φ⊥ = φ`).

Concretely, `τ₂ = τ₁ ∘ φ⊥ + ⟨·,χ⟩·X + ⟨·,χ̄⟩·X̄`, a genuine `ℤ`-linear map (the projection is
`ℂ`-linear, hence `ℤ`-linear; the inner-product functionals are `ℤ`-linear).  Note `τ₁` is *not*
applied to the complex Fourier coefficients, so the construction is correct even though `τ₁` is
only `ℤ`-linear. -/
noncomputable def retarget (τ₁ : IntegralCharacterMap L G)
    (χ chibar : ClassFunction L ℂ) (X Xbar : ClassFunction G ℂ) :
    IntegralCharacterMap L G :=
  τ₁ ∘ₗ orthoResidualMap (L := L) χ chibar
    + (innerLeftℤ (L := L) χ).smulRight X
    + (innerLeftℤ (L := L) chibar).smulRight Xbar

@[simp] theorem retarget_apply (τ₁ : IntegralCharacterMap L G)
    (χ chibar : ClassFunction L ℂ) (X Xbar : ClassFunction G ℂ) (φ : ClassFunction L ℂ) :
    retarget τ₁ χ chibar X Xbar φ =
      τ₁ (orthoResidualMap (L := L) χ chibar φ)
        + ClassFunction.inner φ χ • X + ClassFunction.inner φ chibar • Xbar := by
  simp [retarget, LinearMap.smulRight_apply]

variable {τ₁ : IntegralCharacterMap L G} {χ chibar : ClassFunction L ℂ}
  {X Xbar : ClassFunction G ℂ}

/-- On the orthogonal complement of `{χ, χ̄}` the re-targeting agrees with `τ₁`. -/
theorem retarget_eq_of_orthogonal {φ : ClassFunction L ℂ}
    (hφχ : ClassFunction.inner φ χ = 0) (hφχbar : ClassFunction.inner φ chibar = 0) :
    retarget τ₁ χ chibar X Xbar φ = τ₁ φ := by
  rw [retarget_apply, hφχ, hφχbar, zero_smul, zero_smul, add_zero, add_zero,
    orthoResidualMap_apply, hφχ, hφχbar, zero_smul, zero_smul, sub_zero, sub_zero]

/-- `χ ↦ X` for an orthonormal pair `{χ, χ̄}`. -/
theorem retarget_apply_left
    (hχχ : ClassFunction.inner χ χ = 1) (hχχbar : ClassFunction.inner χ chibar = 0) :
    retarget τ₁ χ chibar X Xbar χ = X := by
  have hres : orthoResidualMap (L := L) χ chibar χ = 0 := by
    rw [orthoResidualMap_apply, hχχ, hχχbar, one_smul, zero_smul, sub_zero, sub_self]
  rw [retarget_apply, hres, map_zero, hχχ, hχχbar, one_smul, zero_smul, add_zero, zero_add]

/-- `χ̄ ↦ X̄` for an orthonormal pair `{χ, χ̄}`. -/
theorem retarget_apply_right
    (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hχbarχbar : ClassFunction.inner chibar chibar = 1) :
    retarget τ₁ χ chibar X Xbar chibar = Xbar := by
  have hres : orthoResidualMap (L := L) χ chibar chibar = 0 := by
    rw [orthoResidualMap_apply, hχbarχ, hχbarχbar, one_smul, zero_smul, sub_zero, sub_self]
  rw [retarget_apply, hres, map_zero, hχbarχ, hχbarχbar, one_smul, zero_smul, add_zero, zero_add]

/-- **Block expansion of a sesquilinear inner product against an orthonormal pair.**
For `u, u' ∈ W` with `⟨e,e⟩ = ⟨f,f⟩ = 1`, `⟨e,f⟩ = ⟨f,e⟩ = 0`, and `u, u'` each orthogonal
to `e` and `f`, the inner product of `u + s·e + t·f` and `u' + s'·e + t'·f` collapses to
`⟨u,u'⟩ + s·conj s' + t·conj t'`.  This is the common normal form both sides of the
re-targeting isometry reduce to. -/
theorem inner_block_expand {W : Type*} [Group W] [Fintype W] [Invertible (Nat.card W : ℂ)]
    {e f u u' : ClassFunction W ℂ} {s t s' t' : ℂ}
    (hee : ClassFunction.inner e e = 1) (hff : ClassFunction.inner f f = 1)
    (hef : ClassFunction.inner e f = 0) (hfe : ClassFunction.inner f e = 0)
    (hue : ClassFunction.inner u e = 0) (huf : ClassFunction.inner u f = 0)
    (hu'e : ClassFunction.inner u' e = 0) (hu'f : ClassFunction.inner u' f = 0) :
    ClassFunction.inner (u + s • e + t • f) (u' + s' • e + t' • f) =
      ClassFunction.inner u u' + s * star s' + t * star t' := by
  have heu' : ClassFunction.inner e u' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hu'e, star_zero]
  have hfu' : ClassFunction.inner f u' = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hu'f, star_zero]
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    hue, huf, heu', hfu', hee, hff, hef, hfe]
  ring

/-- **The orthonormal-block isometry re-targeting keystone.**

Let `τ₁` be a *global* integral isometry, `{χ, χ̄}` an orthonormal pair in the source and
`{X, X̄}` an orthonormal pair in the target with the same gram matrix.  Suppose `X` and `X̄`
are each orthogonal to `τ₁ ξ` for **every** `ξ` orthogonal to both `χ` and `χ̄`.  Then the
re-targeted map `τ₂ = retarget τ₁ χ χ̄ X X̄` is again a global integral isometry.

This is the reusable form of Peterfalvi (5.6.3)'s `τ₂`: the orthogonality hypothesis is
exactly `(5.5) + (5.2.e)` (`X, X̄ ∈ ℤ[R(χ)]` and `S₁^{τ₁} ⊥ R(χ)`), and the conclusion is the
global isometry that, together with `retarget_apply_left`/`retarget_apply_right`/
`retarget_eq_of_orthogonal`, witnesses coherence of `S₁ ∪ {χ, χ̄}`. -/
theorem retarget_isIntegralIsometry [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hτ₁ : IsIntegralIsometry (L := L) (G := G) τ₁)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = 1) (hXbarXbar : ClassFunction.inner Xbar Xbar = 1)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hX_ortho : ∀ ξ : ClassFunction L ℂ, ClassFunction.inner ξ χ = 0 →
      ClassFunction.inner ξ chibar = 0 → ClassFunction.inner (τ₁ ξ) X = 0)
    (hXbar_ortho : ∀ ξ : ClassFunction L ℂ, ClassFunction.inner ξ χ = 0 →
      ClassFunction.inner ξ chibar = 0 → ClassFunction.inner (τ₁ ξ) Xbar = 0) :
    IsIntegralIsometry (L := L) (G := G) (retarget τ₁ χ chibar X Xbar) := by
  refine ⟨fun φ ψ => ?_⟩
  set s := ClassFunction.inner φ χ with hs
  set t := ClassFunction.inner φ chibar with ht
  set s' := ClassFunction.inner ψ χ with hs'
  set t' := ClassFunction.inner ψ chibar with ht'
  set φperp := orthoResidualMap (L := L) χ chibar φ with hφperp
  set ψperp := orthoResidualMap (L := L) χ chibar ψ with hψperp
  -- Orthogonality of the residuals to `{χ, χ̄}`.
  have hφperp_χ : ClassFunction.inner φperp χ = 0 :=
    inner_orthoResidualMap_left hχχ hχbarχ φ
  have hφperp_χbar : ClassFunction.inner φperp chibar = 0 :=
    inner_orthoResidualMap_right hχχbar hχbarχbar φ
  have hψperp_χ : ClassFunction.inner ψperp χ = 0 :=
    inner_orthoResidualMap_left hχχ hχbarχ ψ
  have hψperp_χbar : ClassFunction.inner ψperp chibar = 0 :=
    inner_orthoResidualMap_right hχχbar hχbarχbar ψ
  -- Image side: `⟨τ₂φ, τ₂ψ⟩ = ⟨τ₁φ⊥, τ₁ψ⊥⟩ + s·conj s' + t·conj t'`.
  have himg : ClassFunction.inner (retarget τ₁ χ chibar X Xbar φ)
      (retarget τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner (τ₁ φperp) (τ₁ ψperp) + s * star s' + t * star t' := by
    rw [retarget_apply, retarget_apply, ← hφperp, ← hψperp, ← hs, ← ht, ← hs', ← ht']
    exact inner_block_expand hXX hXbarXbar hXXbar hXbarX
      (hX_ortho φperp hφperp_χ hφperp_χbar) (hXbar_ortho φperp hφperp_χ hφperp_χbar)
      (hX_ortho ψperp hψperp_χ hψperp_χbar) (hXbar_ortho ψperp hψperp_χ hψperp_χbar)
  -- Source side: `⟨φ, ψ⟩ = ⟨φ⊥, ψ⊥⟩ + s·conj s' + t·conj t'`.
  have hsrc : ClassFunction.inner φ ψ =
      ClassFunction.inner φperp ψperp + s * star s' + t * star t' := by
    have hφ : φ = φperp + s • χ + t • chibar := by
      rw [hφperp, orthoResidualMap_apply, ← hs, ← ht]; abel
    have hψ : ψ = ψperp + s' • χ + t' • chibar := by
      rw [hψperp, orthoResidualMap_apply, ← hs', ← ht']; abel
    rw [hφ, hψ]
    exact inner_block_expand hχχ hχbarχbar hχχbar hχbarχ
      hφperp_χ hφperp_χbar hψperp_χ hψperp_χbar
  rw [himg, hsrc, hτ₁.inner_eq φperp ψperp]

/-- **The lattice-relative orthonormal-block re-targeting isometry.**

The genuinely satisfiable form of `retarget_isIntegralIsometry`: rather than demanding the
orthogonality `X, X̄ ⊥ τ₁ ξ` for *every* `ξ ⊥ {χ, χ̄}` (which forces `X, X̄ ∈ span{τ₁χ, τ₁χ̄}`,
not met in (5.6) general position), it only demands it for `ξ` in a submodule `M` closed under the
Gram–Schmidt residual against `{χ, χ̄}` (with `χ, χ̄ ∈ M`).  The conclusion is then inner-product
preservation **on `M`** — exactly the lattice `Z[S₁ ∪ {χ, χ̄}]` isometry of Peterfalvi (5.6.3).

In the (5.6) application `M = span_ℂ(S₁ ∪ {χ, χ̄})`; the residual of any `φ ∈ M` lies in
`span_ℂ S₁`, so the hypotheses `hX_ortho`/`hXbar_ortho` are the genuine `(5.5)+(5.2.e)` fact
`X, X̄ ⊥ τ₁(span_ℂ S₁) = S₁^{τ₁}` (and *not* the over-strong global version).  `τ₁` need only be an
isometry on `M`. -/
theorem retarget_inner_eq_on {τ₁ : IntegralCharacterMap L G}
    {χ chibar : ClassFunction L ℂ} {X Xbar : ClassFunction G ℂ}
    {M : Submodule ℂ (ClassFunction L ℂ)} [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hχM : χ ∈ M) (hchibarM : chibar ∈ M)
    (hτ₁ : ∀ u v : ClassFunction L ℂ, u ∈ M → v ∈ M →
      ClassFunction.inner (τ₁ u) (τ₁ v) = ClassFunction.inner u v)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = 1) (hXbarXbar : ClassFunction.inner Xbar Xbar = 1)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hX_ortho : ∀ ξ ∈ M, ClassFunction.inner ξ χ = 0 →
      ClassFunction.inner ξ chibar = 0 → ClassFunction.inner (τ₁ ξ) X = 0)
    (hXbar_ortho : ∀ ξ ∈ M, ClassFunction.inner ξ χ = 0 →
      ClassFunction.inner ξ chibar = 0 → ClassFunction.inner (τ₁ ξ) Xbar = 0)
    {φ ψ : ClassFunction L ℂ} (hφ : φ ∈ M) (hψ : ψ ∈ M) :
    ClassFunction.inner (retarget τ₁ χ chibar X Xbar φ) (retarget τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner φ ψ := by
  set s := ClassFunction.inner φ χ with hs
  set t := ClassFunction.inner φ chibar with ht
  set s' := ClassFunction.inner ψ χ with hs'
  set t' := ClassFunction.inner ψ chibar with ht'
  set φperp := orthoResidualMap (L := L) χ chibar φ with hφperp
  set ψperp := orthoResidualMap (L := L) χ chibar ψ with hψperp
  -- The residuals lie in `M` (since `χ, χ̄ ∈ M`).
  have hφperpM : φperp ∈ M := by
    rw [hφperp, orthoResidualMap_apply]
    exact M.sub_mem (M.sub_mem hφ (M.smul_mem _ hχM)) (M.smul_mem _ hchibarM)
  have hψperpM : ψperp ∈ M := by
    rw [hψperp, orthoResidualMap_apply]
    exact M.sub_mem (M.sub_mem hψ (M.smul_mem _ hχM)) (M.smul_mem _ hchibarM)
  -- Orthogonality of the residuals to `{χ, χ̄}`.
  have hφperp_χ : ClassFunction.inner φperp χ = 0 :=
    inner_orthoResidualMap_left hχχ hχbarχ φ
  have hφperp_χbar : ClassFunction.inner φperp chibar = 0 :=
    inner_orthoResidualMap_right hχχbar hχbarχbar φ
  have hψperp_χ : ClassFunction.inner ψperp χ = 0 :=
    inner_orthoResidualMap_left hχχ hχbarχ ψ
  have hψperp_χbar : ClassFunction.inner ψperp chibar = 0 :=
    inner_orthoResidualMap_right hχχbar hχbarχbar ψ
  -- Image side.
  have himg : ClassFunction.inner (retarget τ₁ χ chibar X Xbar φ)
      (retarget τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner (τ₁ φperp) (τ₁ ψperp) + s * star s' + t * star t' := by
    rw [retarget_apply, retarget_apply, ← hφperp, ← hψperp, ← hs, ← ht, ← hs', ← ht']
    exact inner_block_expand hXX hXbarXbar hXXbar hXbarX
      (hX_ortho φperp hφperpM hφperp_χ hφperp_χbar)
      (hXbar_ortho φperp hφperpM hφperp_χ hφperp_χbar)
      (hX_ortho ψperp hψperpM hψperp_χ hψperp_χbar)
      (hXbar_ortho ψperp hψperpM hψperp_χ hψperp_χbar)
  -- Source side.
  have hsrc : ClassFunction.inner φ ψ =
      ClassFunction.inner φperp ψperp + s * star s' + t * star t' := by
    have hφ' : φ = φperp + s • χ + t • chibar := by
      rw [hφperp, orthoResidualMap_apply, ← hs, ← ht]; abel
    have hψ' : ψ = ψperp + s' • χ + t' • chibar := by
      rw [hψperp, orthoResidualMap_apply, ← hs', ← ht']; abel
    rw [hφ', hψ']
    exact inner_block_expand hχχ hχbarχbar hχχbar hχbarχ
      hφperp_χ hφperp_χbar hψperp_χ hψperp_χbar
  rw [himg, hsrc, hτ₁ φperp ψperp hφperpM hψperpM]

/-- The Gram–Schmidt residual against an orthonormal pair `{χ, χ̄}` carries
`ℤ[S₁ ∪ {χ, χ̄}]` into `ℤ[S₁]`, provided `χ, χ̄ ⊥ S₁`.

For a generator `x ∈ S₁` the residual is `x` itself (`x ⊥ {χ, χ̄}`); for `x = χ`
(resp. `χ̄`) it is `0`; and `orthoResidualMap` is `ℤ`-linear, so the property
propagates over the `ℤ`-span by `span_induction`.  This is the lattice fact making
the re-targeting an isometry on the *integral* span `ℤ[S₁ ∪ {χ, χ̄}]` using only
the coherence isometry of `τ₁` on `ℤ[S₁]`. -/
theorem orthoResidualMap_mem_zSpan {χ chibar : ClassFunction L ℂ}
    {S₁ : Set (ClassFunction L ℂ)}
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar})) :
    orthoResidualMap (L := L) χ chibar φ ∈ Submodule.span ℤ S₁ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      rcases hx with hxS1 | hxpair
      · -- `x ∈ S₁`: residual is `x ∈ ℤ[S₁]` since `x ⊥ {χ, χ̄}`.
        have hxχ : ClassFunction.inner x χ = 0 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 x hxS1, star_zero]
        have hxχbar : ClassFunction.inner x chibar = 0 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 x hxS1, star_zero]
        rw [orthoResidualMap_apply, hxχ, hxχbar, zero_smul, zero_smul, sub_zero, sub_zero]
        exact Submodule.subset_span hxS1
      · rcases hxpair with rfl | rfl
        · -- `x = χ`: residual is `0`.
          rw [orthoResidualMap_apply, hχχ, hχχbar, one_smul, zero_smul, sub_zero, sub_self]
          exact Submodule.zero_mem _
        · -- `x = χ̄`: residual is `0`.
          rw [orthoResidualMap_apply, hχbarχ, hχbarχbar, one_smul, zero_smul, sub_zero,
            sub_self]
          exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih

/-- **The integral-span re-targeting isometry (the genuine (5.6.3) lattice isometry).**

The honestly-satisfiable companion of `retarget_inner_eq_on`, stated over the *integral*
span `ℤ[S₁ ∪ {χ, χ̄}]` instead of a complex submodule.  Re-targeting an isometry `τ₁` (here only
required isometric on `ℤ[S₁]` — exactly the coherence isometry of `S₁`) preserves `⟨·,·⟩` on all of
`ℤ[S₁ ∪ {χ, χ̄}]`, given:

* `{χ, χ̄}` orthonormal with `χ, χ̄ ⊥ S₁`, and the target pair `{X, X̄}` orthonormal in `ℤ[Irr G]`;
* the honest `(5.5)+(5.2.e)` orthogonality `X, X̄ ⊥ τ₁ ξ` for **`ξ ∈ ℤ[S₁]`** (not the over-strong
  global version, and not posited beyond the lattice `S₁^{τ₁}`).

Every Gram–Schmidt residual of `φ ∈ ℤ[S₁ ∪ {χ, χ̄}]` lands in `ℤ[S₁]`
(`orthoResidualMap_mem_zSpan`), so the block expansion `inner_block_expand` closes the proof using
only the `ℤ[S₁]`-isometry of `τ₁` and the lattice orthogonality.  This is what realizes the weakened
`IsCoherent.extension_inner_eq` for the union `S₁ ∪ {χ, χ̄}`. -/
theorem retarget_inner_eq_on_zSpan_union [Fintype G] [Invertible (Nat.card G : ℂ)]
    {τ₁ : IntegralCharacterMap L G} {χ chibar : ClassFunction L ℂ}
    {X Xbar : ClassFunction G ℂ} {S₁ : Set (ClassFunction L ℂ)}
    (hτ₁ : ∀ u v : ClassFunction L ℂ, u ∈ Submodule.span ℤ S₁ → v ∈ Submodule.span ℤ S₁ →
      ClassFunction.inner (τ₁ u) (τ₁ v) = ClassFunction.inner u v)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner chibar chibar = 1)
    (hχχbar : ClassFunction.inner χ chibar = 0) (hχbarχ : ClassFunction.inner chibar χ = 0)
    (hXX : ClassFunction.inner X X = 1) (hXbarXbar : ClassFunction.inner Xbar Xbar = 1)
    (hXXbar : ClassFunction.inner X Xbar = 0) (hXbarX : ClassFunction.inner Xbar X = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (τ₁ ξ) X = 0)
    (hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (τ₁ ξ) Xbar = 0)
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar}))
    (hψ : ψ ∈ Submodule.span ℤ (S₁ ∪ {χ, chibar})) :
    ClassFunction.inner (retarget τ₁ χ chibar X Xbar φ) (retarget τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner φ ψ := by
  set s := ClassFunction.inner φ χ with hs
  set t := ClassFunction.inner φ chibar with ht
  set s' := ClassFunction.inner ψ χ with hs'
  set t' := ClassFunction.inner ψ chibar with ht'
  set φperp := orthoResidualMap (L := L) χ chibar φ with hφperp
  set ψperp := orthoResidualMap (L := L) χ chibar ψ with hψperp
  -- The residuals lie in `ℤ[S₁]`.
  have hφperpS1 : φperp ∈ Submodule.span ℤ S₁ :=
    orthoResidualMap_mem_zSpan hχχ hχbarχbar hχχbar hχbarχ hχ_S1 hχbar_S1 hφ
  have hψperpS1 : ψperp ∈ Submodule.span ℤ S₁ :=
    orthoResidualMap_mem_zSpan hχχ hχbarχbar hχχbar hχbarχ hχ_S1 hχbar_S1 hψ
  -- Orthogonality of the residuals to `{χ, χ̄}`.
  have hφperp_χ : ClassFunction.inner φperp χ = 0 :=
    inner_orthoResidualMap_left hχχ hχbarχ φ
  have hφperp_χbar : ClassFunction.inner φperp chibar = 0 :=
    inner_orthoResidualMap_right hχχbar hχbarχbar φ
  have hψperp_χ : ClassFunction.inner ψperp χ = 0 :=
    inner_orthoResidualMap_left hχχ hχbarχ ψ
  have hψperp_χbar : ClassFunction.inner ψperp chibar = 0 :=
    inner_orthoResidualMap_right hχχbar hχbarχbar ψ
  -- Image side.
  have himg : ClassFunction.inner (retarget τ₁ χ chibar X Xbar φ)
      (retarget τ₁ χ chibar X Xbar ψ) =
      ClassFunction.inner (τ₁ φperp) (τ₁ ψperp) + s * star s' + t * star t' := by
    rw [retarget_apply, retarget_apply, ← hφperp, ← hψperp, ← hs, ← ht, ← hs', ← ht']
    exact inner_block_expand hXX hXbarXbar hXXbar hXbarX
      (hX_ortho φperp hφperpS1) (hXbar_ortho φperp hφperpS1)
      (hX_ortho ψperp hψperpS1) (hXbar_ortho ψperp hψperpS1)
  -- Source side.
  have hsrc : ClassFunction.inner φ ψ =
      ClassFunction.inner φperp ψperp + s * star s' + t * star t' := by
    have hφ' : φ = φperp + s • χ + t • chibar := by
      rw [hφperp, orthoResidualMap_apply, ← hs, ← ht]; abel
    have hψ' : ψ = ψperp + s' • χ + t' • chibar := by
      rw [hψperp, orthoResidualMap_apply, ← hs', ← ht']; abel
    rw [hφ', hψ']
    exact inner_block_expand hχχ hχbarχbar hχχbar hχbarχ
      hφperp_χ hφperp_χbar hψperp_χ hψperp_χbar
  rw [himg, hsrc, hτ₁ φperp ψperp hφperpS1 hψperpS1]

/-! #### Agreement on the supported span

The `extends_on_supported` field of `IsCoherent` for the re-targeted map `τ₂` is discharged by
a `span_induction`: two integral character maps that agree on a generating set `T` agree on all of
`ℤ[T] = Submodule.span ℤ T` (`eq_on_zSpan_of_eq_on`).  For (5.6) the generating set is the three
*differences* `{χ - χ̄, χ - a·χ₁} ∪ Z[S₁, L^#]` — Peterfalvi's "which generate `Z[S₁∪S₂, L^#]`"
— and the `zSupportedSpan` is contained in their `ℤ`-span (the (5.1)-type generation input).  -/

omit [Fintype L] [Invertible (Nat.card L : ℂ)] in
/-- **Two integral character maps agreeing on a set agree on its integral span.**
If `f, g : IntegralCharacterMap L G` agree on every element of `T ⊆ ClassFunction L ℂ`, they
agree on all of `Submodule.span ℤ T`.  Pure `span_induction`; reused to discharge
`extends_on_supported`. -/
theorem eq_on_zSpan_of_eq_on {f g : IntegralCharacterMap L G}
    {T : Set (ClassFunction L ℂ)} (h : ∀ x ∈ T, f x = g x)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ T) :
    f φ = g φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy]
  | smul a x _ ih => rw [map_zsmul, map_zsmul, ih]

/-- A class function orthogonal to every element of `T` is orthogonal to all of `ℤ[T]`. -/
theorem inner_eq_zero_of_mem_zSpan {η : ClassFunction L ℂ}
    {T : Set (ClassFunction L ℂ)} (h : ∀ x ∈ T, ClassFunction.inner η x = 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ T) :
    ClassFunction.inner η φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ClassFunction.inner_zero_right η
  | add x y _ _ ihx ihy => rw [ClassFunction.inner_add_right, ihx, ihy, add_zero]
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x,
        OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]

/-- **(5.5)+(5.2.e) orthogonality, sum form.**  If `X = ∑_{α ∈ R} c(α)·α` is an integer
combination of an indexed family and `η` is orthogonal to every `α ∈ R`, then `⟨η, X⟩ = 0`.

This packages the `hX_ortho`/`hXbar_ortho` hypotheses of `retarget_isCoherent` from the (5.5)
output `X ∈ ℤ[R(χ)]` (in the explicit `CharacterPsiDecomposition.X_eq` form `X = ∑ coeff α • α`)
and the per-element (5.2.e) orthogonality `⟨τ₁ ξ, α⟩ = 0` for `α ∈ R(χ)`. -/
theorem inner_eq_zero_of_eq_intCast_sum {W : Type*} [Group W] [Fintype W]
    [Invertible (Nat.card W : ℂ)] {η X : ClassFunction W ℂ}
    {R : Finset (ClassFunction W ℂ)} {c : ClassFunction W ℂ → ℤ}
    (hX : X = ∑ α ∈ R, (c α : ℂ) • α)
    (hη : ∀ α ∈ R, ClassFunction.inner η α = 0) :
    ClassFunction.inner η X = 0 := by
  rw [hX, OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_smul_right, hη α hα, mul_zero]

/-- On the integral span of a set orthogonal to `{χ, χ̄}`, the re-targeting agrees with `τ₁`. -/
theorem retarget_eq_on_zSpan_of_orthogonal {τ₁ : IntegralCharacterMap L G}
    {χ chibar : ClassFunction L ℂ} {X Xbar : ClassFunction G ℂ}
    {T : Set (ClassFunction L ℂ)}
    (hTχ : ∀ x ∈ T, ClassFunction.inner χ x = 0)
    (hTχbar : ∀ x ∈ T, ClassFunction.inner chibar x = 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ T) :
    retarget τ₁ χ chibar X Xbar φ = τ₁ φ := by
  refine retarget_eq_of_orthogonal ?_ ?_
  · rw [OddOrder.RepresentationTheory.inner_conj_symm,
      inner_eq_zero_of_mem_zSpan hTχ hφ, star_zero]
  · rw [OddOrder.RepresentationTheory.inner_conj_symm,
      inner_eq_zero_of_mem_zSpan hTχbar hφ, star_zero]

/-! ### Peterfalvi (1.1)+(1.4): the Fourier-image extension for an equal-degree set

For an orthonormal source family `χ : Fin n → CF(L)` and target family `X : Fin n → CF(G)`, the
`ℤ`-linear map `ν φ = ∑ⱼ ⟨φ, χⱼ⟩ • Xⱼ` sends `χₖ ↦ Xₖ` and, when both families are orthonormal, is
an isometry on the lattice `ℤ[range χ]`.  This is the coherence extension witnessing coherence of an
*equal-degree* set via Peterfalvi (1.1)+(1.4) — e.g. the equal-minimal-degree base prefix of (6.6),
or the set `Y = S(H')` of (6.8), where the (5.6) degree induction is unavailable (it needs strictly
increasing degrees, `2χᵢ(1)χ₁(1) < ∑χⱼ(1)²`, which fails at equal degree).

Unlike `retarget`, **no `τ₁`-residual term is needed**: on `ℤ[range χ]` the Gram–Schmidt residual of
any element vanishes, so the isometry is pure Parseval and the base map `τ` enters only through the
agreement on the supported sublattice `ℤ[range χ, A]` (generated by the differences `χⱼ − χ₀`). -/
noncomputable def coherentImageMap {n : ℕ} (χ : Fin n → ClassFunction L ℂ)
    (X : Fin n → ClassFunction G ℂ) : IntegralCharacterMap L G :=
  ∑ j : Fin n, (innerLeftℤ (L := L) (χ j)).smulRight (X j)

@[simp] theorem coherentImageMap_apply {n : ℕ} (χ : Fin n → ClassFunction L ℂ)
    (X : Fin n → ClassFunction G ℂ) (φ : ClassFunction L ℂ) :
    coherentImageMap (L := L) (G := G) χ X φ =
      ∑ j : Fin n, ClassFunction.inner φ (χ j) • X j := by
  simp only [coherentImageMap, LinearMap.sum_apply, LinearMap.smulRight_apply, innerLeftℤ_apply]

/-- `ν χₖ = Xₖ` for an orthonormal source family. -/
theorem coherentImageMap_apply_eq {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    {X : Fin n → ClassFunction G ℂ}
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    (k : Fin n) :
    coherentImageMap (L := L) (G := G) χ X (χ k) = X k := by
  classical
  rw [coherentImageMap_apply, Finset.sum_eq_single k]
  · rw [horthχ k k, if_pos rfl, one_smul]
  · intro j _ hjk; rw [horthχ k j, if_neg (fun h => hjk h.symm), zero_smul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **The two-family Fourier glue** `ν = νX-image on `range χX` ⊕ νY-image on `range χY``.
For orthonormal families `χX`, `χY` with mutually orthogonal ranges, `ν φ =
∑ᵢ ⟨φ,χXᵢ⟩•νX(χXᵢ) + ∑ⱼ ⟨φ,χYⱼ⟩•νY(χYⱼ)` sends `χXₖ ↦ νX(χXₖ)` and `χYₖ ↦ νY(χYₖ)` — the cross
terms vanish by `⟨χXₖ,χYⱼ⟩ = 0`.  This is the `τ₃` glue of Peterfalvi (6.8.1): with `νX = τ₂`
(the `X`-coherence extension) and `νY = τ₁` (the `Y`-coherence extension), it is the combined map
agreeing with `τ₂` on `X` and `τ₁` on `Y`, ready for `coherentUnion_of_glued` (the only remaining
input being `himg_ortho`). -/
noncomputable def coherentImageMapGlue {n m : ℕ} (χX : Fin n → ClassFunction L ℂ)
    (χY : Fin m → ClassFunction L ℂ) (νX νY : IntegralCharacterMap L G) :
    IntegralCharacterMap L G :=
  coherentImageMap (L := L) (G := G) χX (fun i => νX (χX i))
    + coherentImageMap (L := L) (G := G) χY (fun j => νY (χY j))

/-- The glue sends `χXₖ ↦ νX(χXₖ)`: the `νX`-image term is Parseval-exact (`χX` orthonormal), the
`νY`-image term vanishes (`χXₖ ⊥ χYⱼ`). -/
theorem coherentImageMapGlue_apply_left {n m : ℕ} {χX : Fin n → ClassFunction L ℂ}
    {χY : Fin m → ClassFunction L ℂ} {νX νY : IntegralCharacterMap L G}
    (horthX : ∀ i j, ClassFunction.inner (χX i) (χX j) = if i = j then (1 : ℂ) else 0)
    (hXY : ∀ (k : Fin n) (j : Fin m), ClassFunction.inner (χX k) (χY j) = 0) (k : Fin n) :
    coherentImageMapGlue (L := L) (G := G) χX χY νX νY (χX k) = νX (χX k) := by
  rw [coherentImageMapGlue, LinearMap.add_apply, coherentImageMap_apply_eq horthX k,
    coherentImageMap_apply, Finset.sum_eq_zero (fun j _ => by rw [hXY k j, zero_smul]), add_zero]

/-- The glue sends `χYₖ ↦ νY(χYₖ)` (symmetric to `coherentImageMapGlue_apply_left`). -/
theorem coherentImageMapGlue_apply_right {n m : ℕ} {χX : Fin n → ClassFunction L ℂ}
    {χY : Fin m → ClassFunction L ℂ} {νX νY : IntegralCharacterMap L G}
    (horthY : ∀ i j, ClassFunction.inner (χY i) (χY j) = if i = j then (1 : ℂ) else 0)
    (hXY : ∀ (i : Fin n) (k : Fin m), ClassFunction.inner (χY k) (χX i) = 0) (k : Fin m) :
    coherentImageMapGlue (L := L) (G := G) χX χY νX νY (χY k) = νY (χY k) := by
  rw [coherentImageMapGlue, LinearMap.add_apply, coherentImageMap_apply,
    Finset.sum_eq_zero (fun i _ => by rw [hXY i k, zero_smul]), zero_add,
    coherentImageMap_apply_eq horthY k]

open scoped Classical in
/-- **Existence of the two-family glue over orthonormal sets** (Peterfalvi (6.8.1) `τ₃`, set form).
For finite, mutually orthogonal orthonormal sets `X`, `Y ⊆ CF(L)` and integral maps `νX`, `νY`,
there is an `IntegralCharacterMap ν` agreeing with `νX` on `X` and `νY` on `Y` — namely
`coherentImageMapGlue` of any enumerations (agreement `coherentImageMapGlue_apply_left/right`).
With `νX = τ₂` (`X`-coherence extension) and `νY = τ₁` (`Y`-coherence extension) this supplies the
`ν` that `coherentUnion_of_glued` takes, reducing the (6.8) `X ∪ Y`-coherence to `himg_ortho`. -/
theorem exists_integralCharacterMap_glue_of_orthonormal
    {X Y : Set (ClassFunction L ℂ)} (hXfin : X.Finite) (hYfin : Y.Finite)
    (hXorth : ∀ x ∈ X, ∀ x' ∈ X, ClassFunction.inner x x' = if x = x' then (1 : ℂ) else 0)
    (hYorth : ∀ y ∈ Y, ∀ y' ∈ Y, ClassFunction.inner y y' = if y = y' then (1 : ℂ) else 0)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ClassFunction.inner x y = 0)
    (νX νY : IntegralCharacterMap L G) :
    ∃ ν : IntegralCharacterMap L G, (∀ x ∈ X, ν x = νX x) ∧ (∀ y ∈ Y, ν y = νY y) := by
  classical
  let χX : Fin hXfin.toFinset.card → ClassFunction L ℂ :=
    fun i => ↑(hXfin.toFinset.equivFin.symm i)
  let χY : Fin hYfin.toFinset.card → ClassFunction L ℂ :=
    fun j => ↑(hYfin.toFinset.equivFin.symm j)
  have hχX_mem : ∀ i, χX i ∈ X := fun i =>
    hXfin.mem_toFinset.mp (hXfin.toFinset.equivFin.symm i).2
  have hχY_mem : ∀ j, χY j ∈ Y := fun j =>
    hYfin.mem_toFinset.mp (hYfin.toFinset.equivFin.symm j).2
  have horthX : ∀ i j, ClassFunction.inner (χX i) (χX j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [hXorth (χX i) (hχX_mem i) (χX j) (hχX_mem j)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · refine (if_neg ?_).trans (if_neg hij).symm
      exact fun hx => hij (hXfin.toFinset.equivFin.symm.injective (Subtype.ext hx))
  have horthY : ∀ i j, ClassFunction.inner (χY i) (χY j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [hYorth (χY i) (hχY_mem i) (χY j) (hχY_mem j)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · refine (if_neg ?_).trans (if_neg hij).symm
      exact fun hy => hij (hYfin.toFinset.equivFin.symm.injective (Subtype.ext hy))
  have hXYfam : ∀ (i : Fin hXfin.toFinset.card) (j : Fin hYfin.toFinset.card),
      ClassFunction.inner (χX i) (χY j) = 0 :=
    fun i j => hXY (χX i) (hχX_mem i) (χY j) (hχY_mem j)
  have hYXfam : ∀ (i : Fin hXfin.toFinset.card) (j : Fin hYfin.toFinset.card),
      ClassFunction.inner (χY j) (χX i) = 0 := fun i j => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXYfam i j, star_zero]
  refine ⟨coherentImageMapGlue χX χY νX νY, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ : ∃ i, χX i = x :=
      ⟨hXfin.toFinset.equivFin ⟨x, hXfin.mem_toFinset.mpr hx⟩, by simp [χX]⟩
    exact coherentImageMapGlue_apply_left horthX hXYfam i
  · intro y hy
    obtain ⟨j, rfl⟩ : ∃ j, χY j = y :=
      ⟨hYfin.toFinset.equivFin ⟨y, hYfin.mem_toFinset.mpr hy⟩, by simp [χY]⟩
    exact coherentImageMapGlue_apply_right horthY hYXfam j

/-! ### Peterfalvi (6.8.1) `τ₃` glue for **non-orthonormal** (merely pairwise-orthogonal) families

The Fourier glue `coherentImageMapGlue` / `exists_integralCharacterMap_glue_of_orthonormal` above
reproduces `νX`/`νY` on the source families only when those families are **orthonormal** (Parseval
is exact only for unit norms).  Peterfalvi's coherence families (e.g. the induced-character set
`𝒮`, and its (11.8.6) piece `S₂ = 𝒮(C) − 𝒮(HC)`) are **pairwise orthogonal but reducible** — their
members have `‖·‖² > 1` (`subcoherent` (c) in mathcomp `PFsection5.v` asks only
`pairwise_orthogonal S`, not `orthonormal`).  The following generalizes the glue to that setting:
each Fourier coefficient is divided by the (nonzero) squared norm `⟨χⱼ,χⱼ⟩`, so `ν χⱼ = Xⱼ` still
holds.  This is the constructor of the `ν` (`hagreeX`/`hagreeY`) that `coherentUnion_of_glued*`
consumes; the isometry / `himg_ortho` / diagonal `hDτ` data remain the caller's genuine
character-theoretic inputs (Peterfalvi's `b ≡ 0` congruence), exactly as in the orthonormal case. -/

/-- **Orthogonal (non-normalized) Fourier reconstruction** sends `χₖ ↦ Xₖ`.  For a *pairwise-
orthogonal* family `χ` (distinct members orthogonal, each of nonzero norm — **not** required
orthonormal), the norm-rescaled map `φ ↦ ∑ⱼ ⟨φ, χⱼ⟩ • (⟨χⱼ,χⱼ⟩⁻¹ • Xⱼ)` sends `χₖ ↦ Xₖ`: the cross
terms vanish by orthogonality and the diagonal term is `⟨χₖ,χₖ⟩ • ⟨χₖ,χₖ⟩⁻¹ • Xₖ = Xₖ` (norm
nonzero).  This is the `orthonormal → orthogonal` generalization of `coherentImageMap_apply_eq`
(there `⟨χⱼ,χⱼ⟩ = 1` makes the rescaling trivial). -/
theorem coherentImageMap_apply_eq_of_orthogonal {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    {X : Fin n → ClassFunction G ℂ}
    (horthχ : ∀ i j, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0)
    (hnorm : ∀ j, ClassFunction.inner (χ j) (χ j) ≠ 0) (k : Fin n) :
    coherentImageMap (L := L) (G := G) χ
        (fun j => (ClassFunction.inner (χ j) (χ j))⁻¹ • X j) (χ k) = X k := by
  classical
  simp only [coherentImageMap_apply]
  rw [Finset.sum_eq_single k]
  · rw [smul_smul, mul_inv_cancel₀ (hnorm k), one_smul]
  · intro j _ hjk
    rw [horthχ k j fun h => hjk h.symm, zero_smul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **Two-family orthogonal glue** — the `τ₃` of Peterfalvi (6.8.1) for *non-normalized* families.
`ν = [norm-rescaled reconstruction of νX over χX] + [norm-rescaled reconstruction of νY over χY]`.
For pairwise-orthogonal `χX`, `χY` (each of nonzero norm) with mutually orthogonal ranges it sends
`χXₖ ↦ νX(χXₖ)` and `χYₖ ↦ νY(χYₖ)`; the cross terms vanish by `⟨χXₖ,χYⱼ⟩ = 0`.  Unlike
`coherentImageMapGlue` this does **not** require the families orthonormal. -/
noncomputable def coherentImageMapGlueOrthogonal {n m : ℕ} (χX : Fin n → ClassFunction L ℂ)
    (χY : Fin m → ClassFunction L ℂ) (νX νY : IntegralCharacterMap L G) :
    IntegralCharacterMap L G :=
  coherentImageMap (L := L) (G := G) χX
      (fun i => (ClassFunction.inner (χX i) (χX i))⁻¹ • νX (χX i))
    + coherentImageMap (L := L) (G := G) χY
      (fun j => (ClassFunction.inner (χY j) (χY j))⁻¹ • νY (χY j))

/-- The orthogonal glue sends `χXₖ ↦ νX(χXₖ)`: the `νX`-reconstruction is exact for the orthogonal
family `χX` (`coherentImageMap_apply_eq_of_orthogonal`), the `νY`-reconstruction vanishes
(`χXₖ ⊥ χYⱼ`). -/
theorem coherentImageMapGlueOrthogonal_apply_left {n m : ℕ} {χX : Fin n → ClassFunction L ℂ}
    {χY : Fin m → ClassFunction L ℂ} {νX νY : IntegralCharacterMap L G}
    (horthX : ∀ i j, i ≠ j → ClassFunction.inner (χX i) (χX j) = 0)
    (hnormX : ∀ i, ClassFunction.inner (χX i) (χX i) ≠ 0)
    (hXY : ∀ (k : Fin n) (j : Fin m), ClassFunction.inner (χX k) (χY j) = 0) (k : Fin n) :
    coherentImageMapGlueOrthogonal (L := L) (G := G) χX χY νX νY (χX k) = νX (χX k) := by
  rw [coherentImageMapGlueOrthogonal, LinearMap.add_apply,
    coherentImageMap_apply_eq_of_orthogonal horthX hnormX k]
  simp only [coherentImageMap_apply]
  rw [Finset.sum_eq_zero fun j _ => by rw [hXY k j, zero_smul], add_zero]

/-- The orthogonal glue sends `χYₖ ↦ νY(χYₖ)` (symmetric to
`coherentImageMapGlueOrthogonal_apply_left`). -/
theorem coherentImageMapGlueOrthogonal_apply_right {n m : ℕ} {χX : Fin n → ClassFunction L ℂ}
    {χY : Fin m → ClassFunction L ℂ} {νX νY : IntegralCharacterMap L G}
    (horthY : ∀ i j, i ≠ j → ClassFunction.inner (χY i) (χY j) = 0)
    (hnormY : ∀ i, ClassFunction.inner (χY i) (χY i) ≠ 0)
    (hYX : ∀ (i : Fin n) (k : Fin m), ClassFunction.inner (χY k) (χX i) = 0) (k : Fin m) :
    coherentImageMapGlueOrthogonal (L := L) (G := G) χX χY νX νY (χY k) = νY (χY k) := by
  rw [coherentImageMapGlueOrthogonal, LinearMap.add_apply,
    coherentImageMap_apply_eq_of_orthogonal horthY hnormY k]
  simp only [coherentImageMap_apply]
  rw [Finset.sum_eq_zero fun i _ => by rw [hYX i k, zero_smul], zero_add]

open scoped Classical in
/-- **Existence of the two-family glue over pairwise-orthogonal (non-normalized) sets**
(Peterfalvi (6.8.1) `τ₃`, the form (11.8.6) needs).  For finite, mutually orthogonal sets `X`,
`Y ⊆ CF(L)` that are each *pairwise orthogonal* with members of nonzero norm (**not** required
orthonormal — Peterfalvi's `S₂ = 𝒮(C) − 𝒮(HC)` is a family of reducible induced characters), and
integral maps `νX`, `νY`, there is an `IntegralCharacterMap ν` agreeing with `νX` on `X` and `νY`
on `Y`.  This is the `ν` (`hagreeX`/`hagreeY`) that `coherentUnion_of_glued*` takes; it strengthens
`exists_integralCharacterMap_glue_of_orthonormal` by dropping the orthonormality of both families
(the diagonal normalization `⟨·,·⟩⁻¹` in `coherentImageMapGlueOrthogonal` absorbs the non-unit
norms).  Mirrors mathcomp `bridge_coherent`'s `Zisometry_of_cfnorm` extension over the merely
`pairwise_orthogonal` source and image sequences. -/
theorem exists_integralCharacterMap_glue_of_orthogonal
    {X Y : Set (ClassFunction L ℂ)} (hXfin : X.Finite) (hYfin : Y.Finite)
    (hXorth : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ClassFunction.inner x x' = 0)
    (hXnorm : ∀ x ∈ X, ClassFunction.inner x x ≠ 0)
    (hYorth : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ClassFunction.inner y y' = 0)
    (hYnorm : ∀ y ∈ Y, ClassFunction.inner y y ≠ 0)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ClassFunction.inner x y = 0)
    (νX νY : IntegralCharacterMap L G) :
    ∃ ν : IntegralCharacterMap L G, (∀ x ∈ X, ν x = νX x) ∧ (∀ y ∈ Y, ν y = νY y) := by
  classical
  let χX : Fin hXfin.toFinset.card → ClassFunction L ℂ :=
    fun i => ↑(hXfin.toFinset.equivFin.symm i)
  let χY : Fin hYfin.toFinset.card → ClassFunction L ℂ :=
    fun j => ↑(hYfin.toFinset.equivFin.symm j)
  have hχX_mem : ∀ i, χX i ∈ X := fun i =>
    hXfin.mem_toFinset.mp (hXfin.toFinset.equivFin.symm i).2
  have hχY_mem : ∀ j, χY j ∈ Y := fun j =>
    hYfin.mem_toFinset.mp (hYfin.toFinset.equivFin.symm j).2
  have horthX : ∀ i j, i ≠ j → ClassFunction.inner (χX i) (χX j) = 0 := fun i j hij =>
    hXorth (χX i) (hχX_mem i) (χX j) (hχX_mem j)
      (fun hx => hij (hXfin.toFinset.equivFin.symm.injective (Subtype.ext hx)))
  have horthY : ∀ i j, i ≠ j → ClassFunction.inner (χY i) (χY j) = 0 := fun i j hij =>
    hYorth (χY i) (hχY_mem i) (χY j) (hχY_mem j)
      (fun hy => hij (hYfin.toFinset.equivFin.symm.injective (Subtype.ext hy)))
  have hnormX : ∀ i, ClassFunction.inner (χX i) (χX i) ≠ 0 := fun i => hXnorm (χX i) (hχX_mem i)
  have hnormY : ∀ j, ClassFunction.inner (χY j) (χY j) ≠ 0 := fun j => hYnorm (χY j) (hχY_mem j)
  have hXYfam : ∀ (k : Fin hXfin.toFinset.card) (j : Fin hYfin.toFinset.card),
      ClassFunction.inner (χX k) (χY j) = 0 :=
    fun k j => hXY (χX k) (hχX_mem k) (χY j) (hχY_mem j)
  have hYXfam : ∀ (i : Fin hXfin.toFinset.card) (k : Fin hYfin.toFinset.card),
      ClassFunction.inner (χY k) (χX i) = 0 := fun i k => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXYfam i k, star_zero]
  refine ⟨coherentImageMapGlueOrthogonal χX χY νX νY, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ : ∃ i, χX i = x :=
      ⟨hXfin.toFinset.equivFin ⟨x, hXfin.mem_toFinset.mpr hx⟩, by simp [χX]⟩
    exact coherentImageMapGlueOrthogonal_apply_left horthX hnormX hXYfam i
  · intro y hy
    obtain ⟨j, rfl⟩ : ∃ j, χY j = y :=
      ⟨hYfin.toFinset.equivFin ⟨y, hYfin.mem_toFinset.mpr hy⟩, by simp [χY]⟩
    exact coherentImageMapGlueOrthogonal_apply_right horthY hnormY hYXfam j

/-- **Fourier expansion on the integral span of an orthonormal family.**
Every `φ ∈ ℤ[range χ]` equals `∑ⱼ ⟨φ, χⱼ⟩ • χⱼ`. -/
theorem eq_sum_inner_smul_of_mem_span {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    {φ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) :
    ∑ j : Fin n, ClassFunction.inner φ (χ j) • χ j = φ := by
  classical
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [Finset.sum_eq_single k]
      · rw [horthχ k k, if_pos rfl, one_smul]
      · intro j _ hjk; rw [horthχ k j, if_neg (fun h => hjk h.symm), zero_smul]
      · intro h; exact absurd (Finset.mem_univ k) h
  | zero => simp
  | add x y _ _ ihx ihy =>
      simp only [ClassFunction.inner_add_left, add_smul]
      rw [Finset.sum_add_distrib, ihx, ihy]
  | smul a x _ ih =>
      have hcast : ∀ j, ClassFunction.inner (a • x) (χ j) • χ j
          = (a : ℂ) • (ClassFunction.inner x (χ j) • χ j) := fun j => by
        rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, mul_smul]
      simp only [hcast]
      rw [← Finset.smul_sum, ih, Int.cast_smul_eq_zsmul]

/-- **Parseval on the span:** for `φ ∈ ℤ[range χ]` and any `ψ`,
`⟨φ, ψ⟩ = ∑ⱼ ⟨φ, χⱼ⟩ · conj ⟨ψ, χⱼ⟩`. -/
theorem inner_eq_sum_inner_mul_conj {n : ℕ} {χ : Fin n → ClassFunction L ℂ}
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    {φ ψ : ClassFunction L ℂ} (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) :
    ClassFunction.inner φ ψ =
      ∑ j : Fin n, ClassFunction.inner φ (χ j) * star (ClassFunction.inner ψ (χ j)) := by
  conv_lhs => rw [← eq_sum_inner_smul_of_mem_span horthχ hφ]
  rw [inner_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.inner_smul_left, inner_conj_symm ψ (χ j)]

/-- **The Fourier-image map is an isometry on the lattice `ℤ[range χ]`** when both `χ` and `X` are
orthonormal.  This is the lattice-relative `IsCoherent.extension_inner_eq` for an equal-degree set:
the `τ`-residual is inert on `ℤ[range χ]`, leaving pure Parseval. -/
theorem coherentImageMap_inner_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    {n : ℕ} {χ : Fin n → ClassFunction L ℂ} {X : Fin n → ClassFunction G ℂ}
    (horthχ : ∀ i j, ClassFunction.inner (χ i) (χ j) = if i = j then (1 : ℂ) else 0)
    (horthX : ∀ i j, ClassFunction.inner (X i) (X j) = if i = j then (1 : ℂ) else 0)
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ Submodule.span ℤ (Set.range χ)) (_hψ : ψ ∈ Submodule.span ℤ (Set.range χ)) :
    ClassFunction.inner (coherentImageMap (L := L) (G := G) χ X φ)
        (coherentImageMap (L := L) (G := G) χ X ψ) =
      ClassFunction.inner φ ψ := by
  classical
  rw [inner_eq_sum_inner_mul_conj horthχ hφ, coherentImageMap_apply, coherentImageMap_apply,
    inner_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.inner_smul_left, inner_sum_right]
  congr 1
  rw [Finset.sum_eq_single j]
  · rw [OddOrder.RepresentationTheory.inner_smul_right, horthX j j, if_pos rfl, mul_one]
  · intro k _ hkj
    rw [OddOrder.RepresentationTheory.inner_smul_right, horthX j k,
      if_neg (fun h => hkj h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

end IntegralCharacterMap

end OddOrder.Peterfalvi.S07
