/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourEquations

/-!
# Peterfalvi Part II, Ch. IV §4: `λ = 1` and the trace relation

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, p. 134:

> These equations imply that
>
>   **(9)** `(ζ⁻¹ + a^{-2μ})^μ / (1 + b² a^{-2μ})^μ = (b² + ζ) / (1 + b² a^{-2μ})`.
>
> Thus `λ = (ζ⁻¹ + a^{-2μ²})/(b² + ζ) ∈ F` and `λ ζ² + (λ b² + a^{-2μ²}) ζ + 1 = 0`.  As
> `ζ^{1+q} = 1` and `ζ ∉ F`, it follows that `λ = 1` and that `b² + a^{-2μ²} = ζ + ζ⁻¹`.
> The denominators on the two sides of (9) are then equal and
> `b² a^{-2μ} = (ζ + ζ⁻¹ + a^{-2μ²}) a^{-2μ}` is fixed by `μ`.

This file is that paragraph.  The linear algebra of "`1` and `ζ` are independent over `F`"
is `sectionFour_lambda_eq_one` in `PSU3SectionFourArithmetic`; what is added here are the
membership facts it needs on the model:

* `μ` maps `F` to `F` — because `μ` carries `K`-scalars to `K`-scalars and `μ(K) = F^×`;
* `ζ ∉ F` — the hypothesis `hznot`, `F` being closed under inverses;
* `ζ + ζ⁻¹ ∈ F` — the trace of a norm-one element (the existing
  `mu_W_add_inv_mem_frobFixed` of Ch. IV §3, `ζ^q = ζ⁻¹`).

## Main results

* `Hypothesis.coordFieldAut_mapsTo_frobFixed` — `μ(F) ⊆ F`.
* `Hypothesis.sectionFour_lambda` — **`λ = 1` and `b² + a^{-2μ²} = ζ + ζ⁻¹`**, the first
  in the book's form "`b² a^{-2μ}` is fixed by `μ`".
* `sectionFour_ten` — **(10)**, the substitution of the trace relation into that
  invariance.
* `Hypothesis.mem_W_of_coordFieldAut_eq_id` — **`μ = 1 ⟹ η ∈ W`**, the book's closing
  "Thus `η ∈ W`".
* `Hypothesis.coordFieldAut_eq_id_on_frobFixed_of_sq` — `μ²|_F = id ⟹ μ|_F = id`.
* `Hypothesis.coordFieldAut_eq_id_of_fixes_frobFixed` — **`μ = 1`** from `μ|_F = id` and
  the odd order of `η`.
* `Hypothesis.exists_mem_K_coordFieldAut_sq_inv_eq` — every nonzero `X ∈ F` is `a^{-2μ}`.
* `Hypothesis.coordFieldAut_sq_eq_id_of_ten` — the density step: `μ²` fixing all but a
  sparse subset of `F` fixes all of `F`.
* `Hypothesis.sectionFour_ten_at` — the whole chain (3)→(10) run at one admissible `a`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

/-- **Peterfalvi Part II, Ch. IV §4, (10)** (p. 134):

  `(ζ + ζ⁻¹ + X^μ) X = (ζ + ζ⁻¹ + X^{μ²}) X^μ`.

The book reaches it from `λ = 1` by substituting `b² = ζ + ζ⁻¹ + a^{-2μ²}` into
"`b² a^{-2μ}` is fixed by `μ`", with `X = a^{-2μ}`.  That substitution is all this is:
`hfix` is the `μ`-invariance, `htr` the trace relation, and `hσs` says `μ` fixes
`s = ζ + ζ⁻¹` (true because `μ` fixes `ζ`). -/
theorem sectionFour_ten {E : Type*} [Field E] (h2 : (2 : E) = 0) (σ : E ≃+* E)
    {s B X : E} (hσs : σ s = s) (hfix : σ (B * X) = B * X) (htr : B + σ X = s) :
    (s + σ X) * X = (s + σ (σ X)) * σ X := by
  have hB : B = s + σ X := by linear_combination htr - σ X * h2
  have hσB : σ B = s + σ (σ X) := by rw [hB, map_add, hσs]
  rw [map_mul, hσB] at hfix
  rw [← hB]
  exact hfix.symm

/-- The `n`-th power of a ring automorphism is its `n`-fold iterate. -/
theorem ringEquiv_pow_apply {E : Type*} [Field E] (σ : E ≃+* E) (n : ℕ) (x : E) :
    (σ ^ n) x = (σ : E → E)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hstep : ((σ ^ n) * σ) x = (σ ^ n) (σ x) := rfl
      rw [pow_succ, hstep, ih, Function.iterate_succ_apply]

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

variable {m : ℕ}

include hyp in
/-- **`μ` maps `F` into `F`** (Peterfalvi Part II, Ch. IV §4, p. 134, used silently in
"`λ ∈ F`").

The nonzero elements of `F` are exactly the `K`-scalars (`exists_actualKActor_mu_eq`), and
`μ` carries a `K`-scalar to a `K`-scalar (`coordFieldAut_muK`), which lies in `F`
(`mu_K_frobFixed`). -/
theorem coordFieldAut_mapsTo_frobFixed (M : hyp.QuotientFieldModel m)
    (s : hyp.LemmaFiveSetup m) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {d ζ : G} (hd : d ∈ hyp.D) (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    {x : M.E} (hx : x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :
    hyp.coordFieldAut s M hm hQ0card hd hζ hznot x
      ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero]
    exact (OddOrder.FiniteField.frobFixedSubfield M.E 2 m).zero_mem
  obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq s M hm hQ0card hx hx0
  obtain ⟨κ, hκ, hkκ⟩ := hyp.exists_kActor_eq k
  subst hkκ
  subst hk
  rw [hyp.coordFieldAut_muK s M hm hQ0card hd hζ hznot hκ]
  exact OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed _)

include hyp in
/-- **🎯 Peterfalvi Part II, Ch. IV §4, `λ = 1`** (p. 134).

From (9), `λ := (1 + b^{2μ} a^{-2μ²}) / (1 + b² a^{-2μ})` satisfies
`λ (b² + ζ) = ζ⁻¹ + a^{-2μ²}`, hence `λ ζ² + (λ b² + a^{-2μ²}) ζ + 1 = 0` in
characteristic `2`.  All of `λ`, `b²`, `a^{-2μ²}` and `ζ + ζ⁻¹` lie in `F` while `ζ` does
not, so `1` and `ζ` are independent over `F` and both coefficients of the resulting linear
relation vanish (`sectionFour_lambda_eq_one`).  The two conclusions are the book's

* "the denominators on the two sides of (9) are then equal", i.e. `b² a^{-2μ}` is fixed by
  `μ`; and
* `b² + a^{-2μ²} = ζ + ζ⁻¹`.

The repository's scalars are the inverses of the book's, so its `ζ` is `μ(1, ζ)⁻¹` here,
and `A` below is already a `μ`-image (the book's `a^{2μ}`), so `μ A` is `a^{2μ²}`. -/
theorem sectionFour_lambda (M : hyp.QuotientFieldModel m) (s : hyp.LemmaFiveSetup m)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {ζ η a b : G} (hζ : ζ ∈ hyp.W) (hηD : η ∈ hyp.D) (hηζ : η * ζ = ζ * η)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    (ha2 : a ^ 2 ∈ hyp.K) (hb2 : b ^ 2 ∈ hyp.K)
    (hAB : hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
          ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
        + ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E) ≠ 0)
    (h9 : hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
        ((((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
            + (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
                ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E))⁻¹)
          / (1 + ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E)
              * (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
                  ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E))⁻¹))
      = (((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E)
          + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹)
        / (1 + ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E)
            * (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
                ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E))⁻¹)) :
    hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
          (((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E)
            * (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
                ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E))⁻¹)
        = ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E)
          * (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
              ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E))⁻¹
      ∧ ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E)
          + (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
              (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
                ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)))⁻¹
        = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹
          + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := OddOrder.FiniteField.frobFixedSubfield M.E 2 m with hFdef
  set σ := hyp.coordFieldAut s M hm hQ0card hηD hζ hznot with hσdef
  set C := ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) with hCdef
  set A := σ (((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)) with hAdef
  set B := ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E) with hBdef
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hC0 : C ≠ 0 := Units.ne_zero _
  have hcinv0 : C⁻¹ ≠ 0 := inv_ne_zero hC0
  have hCC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC0
  have hA0 : A ≠ 0 := by
    rw [hAdef, hσdef]
    exact (map_ne_zero _).mpr (Units.ne_zero _)
  have hD0 : 1 + B * A⁻¹ ≠ 0 := one_add_mul_inv_ne_zero hA0 hAB
  -- memberships in `F`
  have hBF : B ∈ F := OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed _)
  have hAF : A ∈ F := by
    rw [hAdef, hσdef, hyp.coordFieldAut_muK s M hm hQ0card hηD hζ hznot ha2]
    exact OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed _)
  have hσBF : σ B ∈ F :=
    hyp.coordFieldAut_mapsTo_frobFixed M s hm hQ0card hηD hζ hznot hBF
  have hσAF : σ A ∈ F :=
    hyp.coordFieldAut_mapsTo_frobFixed M s hm hQ0card hηD hζ hznot hAF
  have hCnotF : C⁻¹ ∉ F := by
    intro hc
    exact hznot (by simpa using F.inv_mem hc)
  have hsF : C⁻¹ + C ∈ F := by
    have hmem := hyp.mu_W_add_inv_mem_frobFixed M (⟨ζ, hζ⟩ : ↥hyp.W)
    rw [← hCdef, ← hFdef] at hmem
    rw [add_comm]
    exact hmem
  -- `μ` fixes `ζ`, because `η` centralizes it
  have hfixζ : η * ζ * η⁻¹ = ζ := by
    rw [hηζ, mul_assoc, mul_inv_cancel, mul_one]
  have hσC : σ C = C :=
    hyp.coordFieldAut_muW_eq_self s M hm hQ0card hηD hζ hznot hζ hfixζ
  -- unwind (9) into `λ (b² + ζ) = ζ⁻¹ + a^{-2μ²}`
  set lam := (1 + σ B * (σ A)⁻¹) / (1 + B * A⁻¹) with hlamdef
  have hσnum : σ (C + A⁻¹) = C + (σ A)⁻¹ := by rw [map_add, map_inv₀, hσC]
  have hσden : σ (1 + B * A⁻¹) = 1 + σ B * (σ A)⁻¹ := by
    rw [map_add, map_one, map_mul, map_inv₀]
  have hσD0 : (1 : M.E) + σ B * (σ A)⁻¹ ≠ 0 := by
    rw [← hσden, hσdef]
    exact (map_ne_zero _).mpr hD0
  have h9' : (C + (σ A)⁻¹) / (1 + σ B * (σ A)⁻¹) = (B + C⁻¹) / (1 + B * A⁻¹) := by
    rw [← hσnum, ← hσden, ← map_div₀]
    exact h9
  have hlameq : lam * (B + C⁻¹) = C + (σ A)⁻¹ := by
    rw [div_eq_div_iff hσD0 hD0] at h9'
    rw [hlamdef, div_mul_eq_mul_div, eq_comm, eq_div_iff hD0]
    linear_combination h9'
  have hlamF : lam ∈ F :=
    F.div_mem (F.add_mem F.one_mem (F.mul_mem hσBF (F.inv_mem hσAF)))
      (F.add_mem F.one_mem (F.mul_mem hBF (F.inv_mem hAF)))
  -- the quadratic satisfied by `ζ`, and the relation `λ ζ² + (λ b² + a^{-2μ²}) ζ + 1 = 0`
  have hmin : C⁻¹ ^ 2 + (C⁻¹ + C) * C⁻¹ + 1 = 0 := by
    have hq := sq_add_traceCoeff_mul_add_one h2 hcinv0
    rwa [inv_inv] at hq
  have heq : lam * C⁻¹ ^ 2 + (lam * B + (σ A)⁻¹) * C⁻¹ + 1 = 0 := by
    linear_combination C⁻¹ * hlameq + hCC + ((σ A)⁻¹ * C⁻¹ + 1) * h2
  obtain ⟨hlam1, htr⟩ :=
    sectionFour_lambda_eq_one h2 hCnotF hsF hlamF (F.inv_mem hσAF) hBF hmin heq
  refine ⟨?_, htr⟩
  -- `λ = 1` says the two denominators agree, i.e. `b² a^{-2μ}` is `μ`-fixed
  have hden : (1 : M.E) + σ B * (σ A)⁻¹ = 1 + B * A⁻¹ := by
    rw [hlamdef, div_eq_iff hD0, one_mul] at hlam1
    exact hlam1
  rw [map_mul, map_inv₀]
  linear_combination hden

include hyp in
/-- **🎯 `μ = 1` implies `η ∈ W`** (Peterfalvi Part II, Ch. IV §4, p. 134: "Thus `η ∈ W`
and `h(ω) ∈ W`").

The book states this without argument; it is the *definition* of `W`.  `W = C_V(K)`
(`Hypothesis.W`, p. 98), so for `η ∈ V` it suffices that `η` centralize `K`.  And `μ` on a
`K`-scalar is conjugation of the corresponding element of `K` by `η`
(`coordFieldAut_muK`); `μ = 1` therefore says `μ(κ^η) = μ(κ)` for every `κ ∈ K`, and both
`μ` on `K` (`mu_K_injective`) and the conjugation action of `K` on `Q`
(`conjQByK_injective`) are faithful, so `κ^η = κ`.

No property of `Q₀` or of the Galois correspondence `V/W ↪ Aut(F)` is needed. -/
theorem mem_W_of_coordFieldAut_eq_id (M : hyp.QuotientFieldModel m)
    (s : hyp.LemmaFiveSetup m) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {ζ η : G} (hζ : ζ ∈ hyp.W) (hηD : η ∈ hyp.D) (hηV : η ∈ hyp.V)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    (hσ : ∀ x : M.E, hyp.coordFieldAut s M hm hQ0card hηD hζ hznot x = x) :
    η ∈ hyp.W := by
  refine Subgroup.mem_inf.mpr ⟨hηV, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro κ hκ
  have hκK : κ ∈ hyp.K := by
    rw [← SetLike.mem_coe, hyp.coe_K]
    exact hκ
  -- `μ` fixes the `K`-scalar of `κ`, so `κ^η` and `κ` have the same scalar
  have hval := hyp.coordFieldAut_muK s M hm hQ0card hηD hζ hznot hκK
  rw [hσ] at hval
  have hunits : M.mu (hyp.kActor hκK, 1)
      = M.mu (hyp.kActor (hyp.conj_mem_K_of_mem_D hηD hκK), 1) := Units.ext hval
  have hactor : hyp.kActor hκK = hyp.kActor (hyp.conj_mem_K_of_mem_D hηD hκK) :=
    M.mu_K_injective hunits
  have hconj : (⟨κ, hκK⟩ : ↥hyp.K)
      = ⟨η * κ * η⁻¹, hyp.conj_mem_K_of_mem_D hηD hκK⟩ :=
    hyp.conjQByK_injective (congrArg Subtype.val hactor)
  have hfix : η * κ * η⁻¹ = κ := (congrArg Subtype.val hconj).symm
  calc κ * η = (η * κ * η⁻¹) * η := by rw [hfix]
    _ = η * κ := by group

include hyp in
/-- **`μ²` fixing `F` pointwise already forces `μ|_F = id`**, `μ` having odd order.

The book's "we see that `X^{μ²} = X` ... it follows that `μ = 1` since `μ` has odd order"
splits into this step and `coordFieldAut_eq_id_of_fixes_frobFixed`.  Here `μ(F) ⊆ F`
(`coordFieldAut_mapsTo_frobFixed`) lets `μ²` be iterated inside `F`, so `μ^[2k] = id`
there, and `μ^[2k+1] = id` on all of `E` then reads `μ x = x`. -/
theorem coordFieldAut_eq_id_on_frobFixed_of_sq (M : hyp.QuotientFieldModel m)
    (s : hyp.LemmaFiveSetup m) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {d ζ : G} (hd : d ∈ hyp.D) (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    {k : ℕ} (hdn : d ^ (2 * k + 1) = 1)
    (hsq : ∀ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      hyp.coordFieldAut s M hm hQ0card hd hζ hznot
        (hyp.coordFieldAut s M hm hQ0card hd hζ hznot x) = x)
    {x : M.E} (hx : x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :
    hyp.coordFieldAut s M hm hQ0card hd hζ hznot x = x := by
  set σ := hyp.coordFieldAut s M hm hQ0card hd hζ hznot with hσdef
  have hiter2 : ∀ j : ℕ, ∀ y ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      (σ : M.E → M.E)^[2 * j] y = y := by
    intro j
    induction j with
    | zero => intro y _; simp
    | succ j ih =>
        intro y hy
        have he : 2 * (j + 1) = 2 * j + 2 := by ring
        rw [he, Function.iterate_add_apply]
        have h2y : (σ : M.E → M.E)^[2] y = y := hsq y hy
        rw [h2y]
        exact ih y hy
  have hfull := hyp.coordFieldAut_iterate_eq_self s M hm hQ0card hd hζ hznot hdn x
  have he : 2 * k + 1 = 1 + 2 * k := by ring
  rw [he, Function.iterate_add_apply, hiter2 k x hx] at hfull
  simpa using hfull

include hyp in
/-- **🎯 `μ = 1`** (Peterfalvi Part II, Ch. IV §4, p. 134: "It follows that `μ = 1` since
`μ` has odd order and, if `μ ≠ 1`, then `|F| ≥ 8`").

An automorphism of `E` fixing `F = {x : x^q = x}` pointwise is `1` or the `q`-power
Frobenius (`eq_one_or_eq_qFrobenius_of_fixes`).  The Frobenius has order `2`, while `μ`
has odd order because `η` does (`coordFieldAut_iterate_eq_self`); so the second
alternative would force `μ = 1 = σ₀`, contradicting `qFrobenius_ne_one`. -/
theorem coordFieldAut_eq_id_of_fixes_frobFixed (M : hyp.QuotientFieldModel m)
    (s : hyp.LemmaFiveSetup m) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {d ζ : G} (hd : d ∈ hyp.D) (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    {n : ℕ} (hodd : Odd n) (hdn : d ^ n = 1)
    (hfix : ∀ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      hyp.coordFieldAut s M hm hQ0card hd hζ hznot x = x) (x : M.E) :
    hyp.coordFieldAut s M hm hQ0card hd hζ hznot x = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := hyp.coordFieldAut s M hm hQ0card hd hζ hznot with hσdef
  have hfix' : ∀ y : M.E, y ^ 2 ^ m = y → σ y = y := fun y hy =>
    hfix y (OddOrder.FiniteField.mem_frobFixedSubfield.mpr hy)
  have hpow : σ ^ n = 1 := by
    refine RingEquiv.ext fun y => ?_
    rw [ringEquiv_pow_apply, hσdef,
      hyp.coordFieldAut_iterate_eq_self s M hm hQ0card hd hζ hznot hdn]
    rfl
  rcases OddOrder.FiniteField.eq_one_or_eq_qFrobenius_of_fixes M.card hm hfix' with h1 | h1
  · rw [h1]; rfl
  · exfalso
    have hsq : σ ^ 2 = 1 := by
      rw [h1]
      exact OddOrder.FiniteField.qFrobenius_sq M.card
    have hone : σ = 1 := eq_one_of_sq_eq_one_of_odd_pow hodd hsq hpow
    rw [h1] at hone
    exact OddOrder.FiniteField.qFrobenius_ne_one M.card hm hone

include hyp in
/-- `kActor` depends only on the element, not on the membership proof. -/
theorem kActor_congr {x y : G} (hx : x ∈ hyp.K) (hy : y ∈ hyp.K) (hxy : x = y) :
    hyp.kActor hx = hyp.kActor hy := by
  subst hxy
  rfl

include hyp in
/-- **Every nonzero `X ∈ F` is `a^{-2μ}` for some `a ∈ K`** (Peterfalvi Part II,
Ch. IV §4, p. 134: (10) is asserted "for `X ∈ F − {0, α^{2τ}}`").

Three surjectivities compose: squaring is bijective on `K` because `|K| = q − 1` is odd
(`powCoprime`), `μ` maps `K` onto `F^×` (`exists_actualKActor_mu_eq`), and the field
automorphism is a bijection of `F` (`coordFieldAut_mapsTo_frobFixed` plus injectivity and
finiteness).  This is what lets (10) — proved at one `a` by `sectionFour_ten_at` — be
quantified over `F`. -/
theorem exists_mem_K_coordFieldAut_sq_inv_eq (M : hyp.QuotientFieldModel m)
    (s : hyp.LemmaFiveSetup m) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {d ζ : G} (hd : d ∈ hyp.D) (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    {X : M.E} (hXF : X ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (hX0 : X ≠ 0) :
    ∃ (a : G) (haK : a ∈ hyp.K),
      (hyp.coordFieldAut s M hm hQ0card hd hζ hznot
        ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E))⁻¹ = X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmaps : ∀ {y : M.E}, y ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m →
      hyp.coordFieldAut s M hm hQ0card hd hζ hznot y
        ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := fun hy =>
    hyp.coordFieldAut_mapsTo_frobFixed M s hm hQ0card hd hζ hznot hy
  -- `μ` is a bijection of `F`
  let ρ : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
      → ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) := fun z =>
    ⟨hyp.coordFieldAut s M hm hQ0card hd hζ hznot (z : M.E), hmaps z.2⟩
  have hρinj : Function.Injective ρ := fun z w hzw =>
    Subtype.ext ((hyp.coordFieldAut s M hm hQ0card hd hζ hznot).injective
      (congrArg Subtype.val hzw))
  obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.mp hρinj
    ⟨X⁻¹, (OddOrder.FiniteField.frobFixedSubfield M.E 2 m).inv_mem hXF⟩
  have hzval : hyp.coordFieldAut s M hm hQ0card hd hζ hznot (z : M.E) = X⁻¹ :=
    congrArg Subtype.val hz
  have hz0 : (z : M.E) ≠ 0 := by
    intro hc
    rw [hc, map_zero] at hzval
    exact inv_ne_zero hX0 hzval.symm
  -- pull `z` back to `K`
  obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq s M hm hQ0card z.2 hz0
  obtain ⟨κ, hκ, hkκ⟩ := hyp.exists_kActor_eq k
  -- squaring is bijective on `K`
  have hcop : (Nat.card ↥hyp.K).Coprime 2 := Nat.coprime_two_right.mpr hyp.card_K_odd
  obtain ⟨a, ha⟩ := (powCoprime (n := 2) hcop).surjective (⟨κ, hκ⟩ : ↥hyp.K)
  have haval : ((a : G)) ^ 2 = κ := congrArg Subtype.val ha
  refine ⟨(a : G), a.2, ?_⟩
  rw [hyp.kActor_congr (pow_mem a.2 2) hκ haval, hkκ, hk, hzval, inv_inv]

include hyp in
/-- **The shift trick, on `F`** (Peterfalvi Part II, Ch. IV §4, p. 134: "Writing (10) with
`X + 1` in place of `X` and subtracting (10) from the result, we see that `X^{μ²} = X`").

`sectionFour_fixed_of_shift` turns the pair of instances of (10) at `X` and `X + 1` into
`X^{μ²} = X`; this lemma is the density step that follows.  `μ²` is additive and maps `F`
to itself (`coordFieldAut_mapsTo_frobFixed`), so its fixed points form an additive
subgroup of `F`; if it fixes everything outside a set of fewer than half the elements of
`F`, that subgroup is all of `F` (`eq_id_of_fixes_compl`).

⚠ This is the `F`-level counterpart of `sectionFour_sq_eq_id`, which is stated for the
whole field: (10) is only available on `F`, since its `X` is `a^{-2μ}` with `a ∈ K`. -/
theorem coordFieldAut_sq_eq_id_of_ten (M : hyp.QuotientFieldModel m)
    (s : hyp.LemmaFiveSetup m) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {d ζ : G} (hd : d ∈ hyp.D) (hζ : ζ ∈ hyp.W)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    (S : Finset ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hten : ∀ z : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m), z ∉ S →
      hyp.coordFieldAut s M hm hQ0card hd hζ hznot
        (hyp.coordFieldAut s M hm hQ0card hd hζ hznot (z : M.E)) = (z : M.E))
    (hcard : 2 * S.card < 2 ^ m)
    {x : M.E} (hx : x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :
    hyp.coordFieldAut s M hm hQ0card hd hζ hznot
        (hyp.coordFieldAut s M hm hQ0card hd hζ hznot x) = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmaps : ∀ {y : M.E}, y ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m →
      hyp.coordFieldAut s M hm hQ0card hd hζ hznot y
        ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m := fun hy =>
    hyp.coordFieldAut_mapsTo_frobFixed M s hm hQ0card hd hζ hznot hy
  let φ : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
      →+ ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :=
    { toFun := fun z => ⟨hyp.coordFieldAut s M hm hQ0card hd hζ hznot
        (hyp.coordFieldAut s M hm hQ0card hd hζ hznot (z : M.E)), hmaps (hmaps z.2)⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun z w => Subtype.ext (by simp) }
  have hFcard : Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) = 2 ^ m :=
    OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm
  have hkey := OddOrder.FiniteField.eq_id_of_fixes_compl φ S
    (fun z hz => Subtype.ext (hten z hz)) (by rw [hFcard]; exact hcard) ⟨x, hx⟩
  exact congrArg Subtype.val hkey

include hyp in
/-- **🎯 (10) at one admissible `a`** (Peterfalvi Part II, Ch. IV §4, p. 134).

The whole chain of §4 run once: (3) and (4) give (5) and (6), the arithmetic of
`PSU3SectionFourArithmetic` turns those into (7), (8), (9), `sectionFour_lambda` extracts
`λ = 1` and the trace relation, and `sectionFour_ten` substitutes one into the other.  The
outcome is the book's

  `(ζ + ζ⁻¹ + X^μ) X = (ζ + ζ⁻¹ + X^{μ²}) X^μ`   at `X = a^{-2μ}`.

`s₀` and `X` are passed as parameters with their defining equations so that the statement
stays readable; a caller supplies `rfl` twice. -/
theorem sectionFour_ten_at {f g k : G → G}
    (H : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g k)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (M : hyp.QuotientFieldModel m) (s : hyp.LemmaFiveSetup m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {ζ ω y a b η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsqω : ω * ω = y)
    (haK : a ∈ hyp.K) (haKset : a ∈ hyp.KSet) (hbKset : b ∈ hyp.KSet)
    (hb2 : b ^ 2 ∈ hyp.K)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) (hηζ : η * ζ = ζ * η) (hkω : k ω = ζ ^ 3 * η)
    (htη : hyp.t * η * hyp.t = η) (hηD : η ∈ hyp.D) (hηω : η * ω * η⁻¹ = ω)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    (hb : b * hyp.distinguishedInvolution * b⁻¹
      = y * (a⁻¹ * hyp.distinguishedInvolution * a))
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (hYQ : f (ω * (b * hyp.distinguishedInvolution * b⁻¹)) ∈ hyp.Q)
    {s₀ X : M.E}
    (hs₀ : s₀ = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹
      + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E))
    (hX : X = (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
      ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E))⁻¹) :
    (s₀ + hyp.coordFieldAut s M hm hQ0card hηD hζ hznot X) * X
      = (s₀ + hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
          (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot X))
        * hyp.coordFieldAut s M hm hQ0card hηD hζ hznot X := by
  subst hs₀
  subst hX
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hw : M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) ≠ 0 :=
    hyp.coord_ne_zero_of_not_mem_Q0 M hZ hωQ hωQ0
  have hPsiw : hyp.coordConjD M ⟨η, hηD⟩
      (M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) :=
    hyp.coordConjD_fixed_of_conj_eq M hηD hωQ hηω
  have h5 := hyp.sectionFour_five_of_three H hC2 M s hZ hm hQ0card hζ hωQ hωQ0 hyQ0 hsqω
    haK haKset hf hηζ hkω htη hηD hznot hb hXQ hYQ
  have h6 := hyp.sectionFour_six_linear H hC2 M hZ hζ hωQ hωQ0 hbKset hb2 hf hηζ hkω htη
    hηD hYQ
  obtain ⟨-, -, h9⟩ := hyp.sectionFour_seven_eight_nine M s hm hQ0card hζ hηD hznot
    (pow_mem haK 2) hb2 hw hPsiw h5 h6
  have hA0 : hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
      ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero _)
  have hc0 : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹ ≠ 0 :=
    inv_ne_zero (Units.ne_zero _)
  have h6' : ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E)
        * M.coord (Additive.ofMul (QuotientGroup.mk
            (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q)))
      = (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹)⁻¹
          * hyp.coordConjD M ⟨η, hηD⟩
            (M.coord (Additive.ofMul (QuotientGroup.mk
              (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q))))
        + M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
    rw [inv_inv]
    exact h6
  have hAB : hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
        ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)
      + ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E) ≠ 0 := fun hc =>
    hyp.coordFieldAut_muK_ne_mu_W_inv M s hm hQ0card hηD hζ hznot (pow_mem haK 2)
      (sectionFour_eq_of_add_eq_zero h2 hA0 hc0 hw h5 h6' hc)
  obtain ⟨hfix, htr⟩ := hyp.sectionFour_lambda M s hm hQ0card hζ hηD hηζ hznot
    (pow_mem haK 2) hb2 hAB h9
  have hfixζ : η * ζ * η⁻¹ = ζ := by rw [hηζ, mul_assoc, mul_inv_cancel, mul_one]
  have hsigC : hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
      ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) :=
    hyp.coordFieldAut_muW_eq_self s M hm hQ0card hηD hζ hznot hζ hfixζ
  refine sectionFour_ten h2 _ ?_ hfix ?_
  · rw [map_add, map_inv₀, hsigC]
  · rw [map_inv₀]
    exact htr

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
