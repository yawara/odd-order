/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourEquations
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourCorollaryTwo

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
* `Hypothesis.sectionFour_ten_of_mem_frobFixed` — the same at every admissible `X ∈ F^×`,
  with `a` and `b` produced rather than assumed.
* `Hypothesis.coordFieldAut_sq_eq_id_on_frobFixed` — **`μ² = id` on `F`**, the shift trick
  plus the count of the excluded points.
* `Hypothesis.SectionFourSetup.eight_lt_natCard_Q0` — `q > 8`, the counting hypothesis.
* `Hypothesis.center_le_subgroupOf_D`, `Hypothesis.center_residualImage_le_subgroupOf_D` —
  **`Z(U) ⊆ D`**, the `hZD` that §4's step (2)/(3) endpoints thread as a hypothesis.
* `Hypothesis.nonempty_psu3Data_sectionFour` — the `PSU(3, ℓ)` branch data for `X = P`,
  which step (2) and step (3) run on.
* `Hypothesis.conj_t_eq_of_mem_center`, `Hypothesis.SectionFourSetup.pow_odd_eq_one_of_mem_P`
  — the `htη` and `hηord` of `sectionFour_mem_W`.
* `Hypothesis.SectionFourSetup.exists_mem_P_mem_W_mul` — `P ⊔ W = P · W`, the `hfac` of
  `inf_le_sup_centralizer_W` and `eq_P_of_centralizes`.
* `Hypothesis.residualImage_le_centralizer` — `U ≤ C_G(X)`, its `hUC`.
* `Hypothesis.SectionFourSetup.exists_refined_zeta` — **the book's `ζ₁ ∈ ζ P` with
  `ζ ∈ C_W(P)`**.
* `Hypothesis.mem_residualImage_of_mem_Q`,
  `Hypothesis.SectionFourSetup.center_residualImage_le_D` — `hZD` straight from
  Glauberman's `ω ∈ C_Q(P) − Q₀`.
* `conj_inv_eq_of_commute`, `cube_mul_eq_of_commute` — the book's refinement
  `ζ₁ ∈ ζ P` (p. 133): `ω^{ζ₁} = ω^ζ` and `ζ₁³ P = ζ³ P`.
* `Hypothesis.sectionFour_mem_W` — **🎯🎯 the conclusion of §4: `η ∈ W` and `h(ω) ∈ W`.**
* `Hypothesis.SectionFourSetup.mem_W_of_stepThree` — **🎯🎯🎯 the same from step (3)'s
  output**, with the `ζ₁ ∈ ζ P` refinement carried out.
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

include hyp in
/-- **🎯 (10) at every admissible `X ∈ F^×`** (Peterfalvi Part II, Ch. IV §4, p. 134).

`exists_mem_K_coordFieldAut_sq_inv_eq` produces the `a ∈ K` with `a^{-2μ} = X`, the book's
`b` comes from `stepTen_exists` (its side condition `y · s^{a⁻¹} ≠ 1` is the book's
`a ≠ α^{-τ}`, here hoisted into `hadm`), and `sectionFour_ten_at` runs the chain.

The two `f`-values are in `Q` because `ω s^a ∈ Q − Q₀` is nontrivial, so `IsFGH.mem`
applies. -/
theorem sectionFour_ten_of_mem_frobFixed {f g k : G → G}
    (H : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g k)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (M : hyp.QuotientFieldModel m) (s : hyp.LemmaFiveSetup m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {ζ ω y η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsqω : ω * ω = y)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) (hηζ : η * ζ = ζ * η) (hkω : k ω = ζ ^ 3 * η)
    (htη : hyp.t * η * hyp.t = η) (hηD : η ∈ hyp.D) (hηω : η * ω * η⁻¹ = ω)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    {X : M.E} (hXF : X ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) (hX0 : X ≠ 0)
    (hadm : ∀ (a : G) (haK : a ∈ hyp.K),
      (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
        ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E))⁻¹ = X →
      y * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1)
    {s₀ : M.E}
    (hs₀ : s₀ = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹
      + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)) :
    (s₀ + hyp.coordFieldAut s M hm hQ0card hηD hζ hznot X) * X
      = (s₀ + hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
          (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot X))
        * hyp.coordFieldAut s M hm hQ0card hηD hζ hznot X := by
  obtain ⟨a, haK, hXa⟩ :=
    hyp.exists_mem_K_coordFieldAut_sq_inv_eq M s hm hQ0card hηD hζ hznot hXF hX0
  have hne := hadm a haK hXa
  -- `ω⁴ = 1`, so `f(ω) = (ω y)^ζ`
  have hy2 : y * y = 1 := by
    have hq := hyp.sq_eq_one_of_mem_Q0 hyQ0
    rwa [sq] at hq
  have hω4 : ω * y = ω⁻¹ := by
    have h4 : ω * ω * (ω * ω) = 1 := by rw [hsqω]; exact hy2
    calc ω * y = ω * (ω * ω) := by rw [hsqω]
      _ = (ω * ω * (ω * ω)) * ω⁻¹ := by group
      _ = ω⁻¹ := by rw [h4, one_mul]
  have hfω : f ω = ζ⁻¹ * (ω * y) * ζ := by rw [hω4]; exact hf
  -- the book's `b`
  have haiK : a⁻¹ ∈ hyp.K := hyp.K.inv_mem haK
  have hne' : y * (a⁻¹ * hyp.distinguishedInvolution * a⁻¹⁻¹) ≠ 1 := by rwa [inv_inv]
  obtain ⟨b, hbK, hbconj, -⟩ :=
    hyp.stepTen_exists H hC2 hζ hωQ hωQ0 hyQ0 haiK hfω hne'
  have hbiK : b⁻¹ ∈ hyp.K := hyp.K.inv_mem hbK
  have hb : b⁻¹ * hyp.distinguishedInvolution * b⁻¹⁻¹
      = y * (a⁻¹ * hyp.distinguishedInvolution * a) := by
    rw [inv_inv, hbconj, inv_inv]
  -- the two `f`-values lie in `Q`
  have hmemQ : ∀ {c : G}, c ∈ hyp.K →
      f (ω * (c * hyp.distinguishedInvolution * c⁻¹)) ∈ hyp.Q := by
    intro c hc
    have hzQ0 : c * hyp.distinguishedInvolution * c⁻¹ ∈ hyp.Q0 :=
      hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D hc) hyp.distinguishedInvolution_mem_Q0
    obtain ⟨hprodQ, hprodQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hzQ0
    exact (H.mem _ hprodQ (fun hc1 => hprodQ0 (hc1 ▸ hyp.Q0.one_mem))).1
  have haKset : a ∈ hyp.KSet := by rw [← SetLike.mem_coe, hyp.coe_K] at haK; exact haK
  have hbiKset : b⁻¹ ∈ hyp.KSet := by
    rw [← SetLike.mem_coe, hyp.coe_K] at hbiK; exact hbiK
  exact hyp.sectionFour_ten_at H hC2 M s hZ hm hQ0card hζ hωQ hωQ0 hyQ0 hsqω haK haKset
    hbiKset (pow_mem hbiK 2) hf hηζ hkω htη hηD hηω hznot hb (hmemQ haK) (hmemQ hbiK)
    hs₀ hXa.symm

include hyp in
/-- **🎯 `μ² = id` on `F`** (Peterfalvi Part II, Ch. IV §4, p. 134: "Let
`X ∈ F − {0, α^{2τ}, α^{2τ} + 1}`.  Writing (10) with `X + 1` in place of `X` and
subtracting (10) from the result, we see that `X^{μ²} = X`").

(10) is available at every `X ∈ F^×` whose `a` satisfies `y · s^{a⁻¹} ≠ 1`
(`sectionFour_ten_of_mem_frobFixed`), and there is at most *one* offending `a`: it would
have to satisfy `s^{a⁻¹} = y⁻¹`, and conjugation is injective on `K`
(`injOn_conj_KSet`).  So (10) fails on at most two points of `F`, the shift trick needs
two more, and four is fewer than half of `|F| = q` as soon as `q > 8` — which holds since
`q = ℓ^p` with `ℓ > 2` and `p` an odd prime. -/
theorem coordFieldAut_sq_eq_id_on_frobFixed {f g k : G → G}
    (H : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g k)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (M : hyp.QuotientFieldModel m) (s : hyp.LemmaFiveSetup m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) (hq : 8 < 2 ^ m)
    {ζ ω y η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsqω : ω * ω = y)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) (hηζ : η * ζ = ζ * η) (hkω : k ω = ζ ^ 3 * η)
    (htη : hyp.t * η * hyp.t = η) (hηD : η ∈ hyp.D) (hηω : η * ω * η⁻¹ = ω)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    {x : M.E} (hx : x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) :
    hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
        (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot x) = x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := OddOrder.FiniteField.frobFixedSubfield M.E 2 m with hFdef
  haveI : Fintype ↥F := Fintype.ofFinite _
  set σ := hyp.coordFieldAut s M hm hQ0card hηD hζ hznot with hσdef
  set s₀ := ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)⁻¹
    + ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) with hs₀def
  have h2 : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  -- the admissibility predicate and the equation (10)
  set Ten : M.E → Prop := fun X => (s₀ + σ X) * X = (s₀ + σ (σ X)) * σ X with hTendef
  set Adm : M.E → Prop := fun X => ∀ (a : G) (haK : a ∈ hyp.K),
    (σ ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E))⁻¹ = X →
      y * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1 with hAdmdef
  have hTen : ∀ z : M.E, z ∈ F → z ≠ 0 → Adm z → Ten z := fun z hzF hz0 hadm =>
    hyp.sectionFour_ten_of_mem_frobFixed H hC2 M s hZ hm hQ0card hζ hωQ hωQ0 hyQ0 hsqω hf
      hηζ hkω htη hηD hηω hznot hzF hz0 hadm rfl
  -- at most one `a` is inadmissible, so at most one nonzero `X` fails `Adm`
  have hUniq : ∀ z w : M.E, ¬ Adm z → ¬ Adm w → z = w := by
    intro z w hz hw
    simp only [hAdmdef, not_forall, not_not] at hz hw
    obtain ⟨a₁, ha₁K, hz₁, hz₂⟩ := hz
    obtain ⟨a₂, ha₂K, hw₁, hw₂⟩ := hw
    have e1 : a₁⁻¹ * hyp.distinguishedInvolution * a₁ = y⁻¹ :=
      eq_inv_of_mul_eq_one_right hz₂
    have e2 : a₂⁻¹ * hyp.distinguishedInvolution * a₂ = y⁻¹ :=
      eq_inv_of_mul_eq_one_right hw₂
    have hconj : a₁⁻¹ * hyp.distinguishedInvolution * a₁
        = a₂⁻¹ * hyp.distinguishedInvolution * a₂ := by rw [e1, e2]
    have hset : ∀ {c : G}, c ∈ hyp.K → c ∈ hyp.KSet := by
      intro c hc
      have hx : c ∈ (hyp.K : Set G) := hc
      rwa [hyp.coe_K] at hx
    have ha : a₁ = a₂ :=
      hyp.injOn_conj_KSet hyp.distinguishedInvolution_mem_H
        hyp.distinguishedInvolution_sq hyp.distinguishedInvolution_ne_one
        (hset ha₁K) (hset ha₂K) hconj
    subst ha
    rw [← hz₁, ← hw₁]
  -- the exclusion set
  set T : Finset ↥F := Finset.univ.filter (fun z : ↥F => ¬ Ten (z : M.E)) with hTdef
  have hTsub : ∃ x₀ : ↥F, ∀ z ∈ T, z = 0 ∨ z = x₀ := by
    by_cases hex : ∃ z ∈ T, (z : M.E) ≠ 0
    · obtain ⟨x₀, hx₀T, hx₀0⟩ := hex
      refine ⟨x₀, fun z hz => ?_⟩
      by_cases hz0 : (z : M.E) = 0
      · exact Or.inl (Subtype.ext (by rw [hz0]; rfl))
      · refine Or.inr (Subtype.ext ?_)
        refine hUniq (z : M.E) (x₀ : M.E) (fun hadm => ?_) (fun hadm => ?_)
        · exact (Finset.mem_filter.mp hz).2 (hTen _ z.2 hz0 hadm)
        · exact (Finset.mem_filter.mp hx₀T).2 (hTen _ x₀.2 hx₀0 hadm)
    · refine ⟨0, fun z hz => Or.inl (Subtype.ext ?_)⟩
      by_contra hc
      exact hex ⟨z, hz, hc⟩
  obtain ⟨x₀, hx₀⟩ := hTsub
  have hTcard : T.card ≤ 2 := by
    have hsub : T ⊆ ({0, x₀} : Finset ↥F) := by
      intro z hz
      rcases hx₀ z hz with h | h <;> simp [h]
    exact le_trans (Finset.card_le_card hsub)
      ((Finset.card_insert_le _ _).trans (by simp))
  set S : Finset ↥F := T ∪ T.image (fun z => z + 1) with hSdef
  have hScard : 2 * S.card < 2 ^ m := by
    have h1 : S.card ≤ T.card + (T.image (fun z : ↥F => z + 1)).card :=
      Finset.card_union_le _ _
    have h2' : (T.image (fun z : ↥F => z + 1)).card ≤ T.card := Finset.card_image_le
    omega
  refine hyp.coordFieldAut_sq_eq_id_of_ten M s hm hQ0card hηD hζ hznot S ?_ hScard hx
  intro z hzS
  have hzT : z ∉ T := fun hc => hzS (Finset.mem_union_left _ hc)
  have hz1T : z + 1 ∉ T := by
    intro hc
    refine hzS (Finset.mem_union_right _ ?_)
    refine Finset.mem_image.mpr ⟨z + 1, hc, ?_⟩
    refine Subtype.ext ?_
    push_cast
    linear_combination h2
  have hTz : Ten (z : M.E) := by
    by_contra hc
    exact hzT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  have hTz1 : Ten ((z : M.E) + 1) := by
    by_contra hc
    refine hz1T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    push_cast
    exact hc
  exact sectionFour_fixed_of_shift σ.toRingHom hTz hTz1

/-- **`q > 8`** (Peterfalvi Part II, Ch. IV §4, p. 134: "if `μ ≠ 1`, then `|F| ≥ 8`").

Step (1) computes `q = |Q₀| = ℓ^p` with `ℓ = |C_{Q₀}(P)|` and `p` the odd prime order of
`P` (`natCard_Q0_eq_pow_cardP`).  The section's standing `ℓ > 2` and `p ≥ 3` give
`q ≥ 27`, which is the counting hypothesis `hq` of
`coordFieldAut_sq_eq_id_on_frobFixed`. -/
theorem SectionFourSetup.eight_lt_natCard_Q0 (s4 : hyp.SectionFourSetup)
    (hl : 2 < Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G)))) :
    8 < Nat.card ↥hyp.Q0 := by
  rw [s4.natCard_Q0_eq_pow_cardP]
  have hp : 3 ≤ s4.cardP := by
    obtain ⟨j, hj⟩ := s4.odd_cardP
    have h2 := s4.prime_cardP.two_le
    omega
  calc 8 < 3 ^ 3 := by norm_num
    _ ≤ Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) ^ 3 :=
        Nat.pow_le_pow_left hl 3
    _ ≤ Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) ^ s4.cardP :=
        Nat.pow_le_pow_right (by omega) hp

/-! ### `Z(U) ⊆ D`

Peterfalvi Part II, Ch. IV §4, step (1) (p. 132) opens with

> As `Z(U) ⊂ C_V(C_{Q₀}(P))`, `Z(U) ⊂ P W` by the theorem of Galois.

The inclusion `Z(U) ⊆ V ≤ D` is used without comment.  It follows from the two-point
description `D = H ∩ H^t` of the standing hypothesis: `Z(U)` centralizes `t ∈ U`, which
makes `H`-membership and `H^t`-membership the same condition, and it centralizes a
nontrivial element of `Q` (namely the `ω ∈ C_Q(P) − Q₀` of step (1)), whose centralizer
lies in `H` because `Q` is regular on `Ω − {basept}` (`centralizer_le_H_of_mem_Q`). -/

include hyp in
/-- An element of `H` commuting with `t` lies in the two-point stabilizer `D = H ∩ H^t`. -/
theorem mem_D_of_mem_H_of_commute_t {z : G} (hzH : z ∈ hyp.H)
    (hzt : z * hyp.t = hyp.t * z) : z ∈ hyp.D := by
  rw [hyp.D_def]
  refine ⟨hzH, ⟨z, hzH, ?_⟩⟩
  change hyp.t * z * hyp.t⁻¹ = z
  rw [← hzt, mul_assoc, mul_inv_cancel, mul_one]

include hyp in
/-- **🎯 `Z(U) ⊆ D`** (Peterfalvi Part II, Ch. IV §4, step (1), p. 132).

Only two memberships in `U` are used: the distinguished involution `t`
(`t_mem_primeComplementResidual`) and a nontrivial element of `Q` — in §4 the
`ω ∈ C_Q(P) − Q₀` that Glauberman's step produces.  A central element of `U` commutes with
both, so it lies in `C_G(ω) ≤ H` and commutes with `t`, hence in `D`. -/
theorem center_le_subgroupOf_D {U : Subgroup G} {ω : G} (hωQ : ω ∈ hyp.Q) (hω1 : ω ≠ 1)
    (hωU : ω ∈ U) (htU : hyp.t ∈ U) :
    Subgroup.center ↥U ≤ hyp.D.subgroupOf U := by
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  have hcω : (z : G) * ω = ω * (z : G) := by
    have hc := Subgroup.mem_center_iff.mp hz ⟨ω, hωU⟩
    exact (congrArg Subtype.val hc).symm
  have hct : (z : G) * hyp.t = hyp.t * (z : G) := by
    have hc := Subgroup.mem_center_iff.mp hz ⟨hyp.t, htU⟩
    exact (congrArg Subtype.val hc).symm
  have hzH : (z : G) ∈ hyp.H :=
    hyp.centralizer_le_H_of_mem_Q hωQ hω1
      (Subgroup.mem_centralizer_singleton_iff.mpr hcω)
  exact hyp.mem_D_of_mem_H_of_commute_t hzH hct

omit [MulAction G Ω] [Finite G] in
/-- A `2`-element of `C_G(X)` lies in `U = O^{2′}(C_G(X))`: it generates a `2`-group, which
sits inside a Sylow `2`-subgroup, and every Sylow `2`-subgroup lies in the residual. -/
theorem mem_residualImage_of_orderOf_eq_two_pow {X : Subgroup G} {x : G}
    (hxC : x ∈ Subgroup.centralizer ((X : Set G))) {n : ℕ} (hord : orderOf x = 2 ^ n) :
    x ∈ residualImage (G := G) X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set xC : ↥(Subgroup.centralizer ((X : Set G))) := ⟨x, hxC⟩ with hxCdef
  have hordC : orderOf xC = 2 ^ n := by
    rw [← hord]
    exact (orderOf_injective (Subgroup.centralizer ((X : Set G))).subtype
      (Subgroup.subtype_injective _) xC).symm
  have hT : IsPGroup 2 ↥(Subgroup.zpowers xC) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hordC])
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  exact ⟨xC, Subgroup.le_primeComplementResidual S (hS (Subgroup.mem_zpowers xC)), rfl⟩

include hyp in
/-- **🎯 `hZD` for `U = residualImage P`** — `center_le_subgroupOf_D` with both memberships
discharged: `t` is an involution of `C_G(P)` and `ω` is the `2`-element of `C_Q(P) − Q₀`
that step (1) produces. -/
theorem center_residualImage_le_subgroupOf_D (s4 : hyp.SectionFourSetup)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hω1 : ω ≠ 1)
    (hωC : ω ∈ Subgroup.centralizer ((s4.P : Set G))) {n : ℕ} (hord : orderOf ω = 2 ^ n) :
    Subgroup.center ↥(residualImage (G := G) s4.P)
      ≤ hyp.D.subgroupOf (residualImage (G := G) s4.P) :=
  hyp.center_le_subgroupOf_D hωQ hω1
    (mem_residualImage_of_orderOf_eq_two_pow (G := G) hωC hord)
    (mem_residualImage_of_orderOf_eq_two_pow (G := G) s4.t_mem_centralizer
      (n := 1) (by
        rw [pow_one]
        exact orderOf_eq_prime hyp.t_sq hyp.t_ne_one))

include hyp in
/-- **🎯 The `PSU(3, ℓ)` branch data for `X = P`** (Peterfalvi Part II, Ch. IV §4, step (1),
p. 132).

Ch. I §3 Proposition 1(c) applied inductively to `C_G(P)`
(`centralizer_trichotomy_of_induction`) gives the trichotomy; §4's two discriminators —
`|st| = 3` and "`C_Q(P)` has exponent `4`" (`not_isElementaryAbelian_cQ`) — pick the
unitary branch (`nonempty_psu3Data_of_orderOf_eq_three`).  This is the `details` that
step (2) and step (3) run on. -/
theorem nonempty_psu3Data_sectionFour (s4 : hyp.SectionFourSetup)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q) (hP : s4.P ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (ih : TheoremAInductionBelow G Ω) :
    letI := hyp.centralizerQuotientMulAction s4.P_le_V
    ∃ (result : TheoremAConclusion (hyp.centralizerActionQuotient s4.P)
        ↥(MulAction.fixedPoints s4.P Ω))
      (data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints s4.P Ω)) result.L),
      Nonempty (CentralizerPSUData hyp s4.P result data) := by
  letI := hyp.centralizerQuotientMulAction s4.P_le_V
  have hnea := s4.not_isElementaryAbelian_cQ hQsuz hZ hCop hSolv
  obtain ⟨tri⟩ := hyp.centralizer_trichotomy_of_induction s4.P_le_V hP hA3 ih
  obtain ⟨data, -, details⟩ :=
    nonempty_psu3Data_of_orderOf_eq_three tri.branch hord hnea |>.some
  exact ⟨tri.result, data, ⟨details⟩⟩

include hyp in
/-- **`t` commutes with `Z(U)`** — since `t ∈ U`.  This is `htη` of
`sectionFour_mem_W`, in the `t η t = η` shape §3's chain uses (`t² = 1`). -/
theorem conj_t_eq_of_mem_center {U : Subgroup G} (htU : hyp.t ∈ U)
    {η : G} (hη : η ∈ U) (hηc : (⟨η, hη⟩ : ↥U) ∈ Subgroup.center ↥U) :
    hyp.t * η * hyp.t = η := by
  have hc : hyp.t * η = η * hyp.t := by
    have hz := Subgroup.mem_center_iff.mp hηc ⟨hyp.t, htU⟩
    exact congrArg Subtype.val hz
  calc hyp.t * η * hyp.t = η * (hyp.t * hyp.t) := by rw [hc]; group
    _ = η := by rw [← sq, hyp.t_sq, mul_one]

include hyp in
/-- **`η ∈ P` has odd order** — `|P| = p` is an odd prime.  This is `hηord` of
`sectionFour_mem_W`. -/
theorem SectionFourSetup.pow_odd_eq_one_of_mem_P (s4 : hyp.SectionFourSetup) {η : G}
    (hη : η ∈ s4.P) : ∃ j : ℕ, η ^ (2 * j + 1) = 1 := by
  obtain ⟨j, hj⟩ := s4.odd_cardP
  refine ⟨j, ?_⟩
  rw [← hj, ← s4.card_P]
  have h1 : (⟨η, hη⟩ : ↥s4.P) ^ Nat.card ↥s4.P = 1 := pow_card_eq_one'
  have h2 := congrArg (Subtype.val (p := fun x => x ∈ s4.P)) h1
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  exact h2

omit [MulAction G Ω] [Finite G] in
/-- **`U ≤ C_G(X)`** — `U = O^{2′}(C_G(X))` is by construction a subgroup of the
centralizer, read in `G` along the inclusion.  This is the `hUC` of
`inf_le_sup_centralizer_W`. -/
theorem residualImage_le_centralizer {X : Subgroup G} :
    residualImage (G := G) X ≤ Subgroup.centralizer ((X : Set G)) := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

include hyp in
/-- Every element of `Q` centralizing `X` lies in `U = O^{2′}(C_G(X))`, because `Q` is a
`2`-group. -/
theorem mem_residualImage_of_mem_Q (hQ2 : IsPGroup 2 ↥hyp.Q) {X : Subgroup G} {x : G}
    (hxQ : x ∈ hyp.Q) (hxC : x ∈ Subgroup.centralizer ((X : Set G))) :
    x ∈ residualImage (G := G) X := by
  obtain ⟨n, hn⟩ := hQ2 ⟨x, hxQ⟩
  have hxn : x ^ 2 ^ n = 1 := by
    have hv := congrArg (Subtype.val (p := fun z => z ∈ hyp.Q)) hn
    simpa using hv
  obtain ⟨j, -, hj⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxn)
  exact mem_residualImage_of_orderOf_eq_two_pow (G := G) hxC hj

include hyp in
/-- **🎯 `hZD` from Glauberman's `ω`** — the `ω ∈ C_Q(P) − Q₀` of step (1) is a nontrivial
element of `Q` centralizing `P`, hence lies in `U`; that plus `t ∈ U` gives `Z(U) ⊆ D`. -/
theorem SectionFourSetup.center_residualImage_le_D (s4 : hyp.SectionFourSetup)
    (hQ2 : IsPGroup 2 ↥hyp.Q) {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hωfix : ∀ a ∈ s4.P, a * ω * a⁻¹ = ω) :
    Subgroup.center ↥(residualImage (G := G) s4.P)
      ≤ hyp.D.subgroupOf (residualImage (G := G) s4.P) := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have hωC : ω ∈ Subgroup.centralizer ((s4.P : Set G)) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => by
      have hconj := hωfix a ha
      calc a * ω = (a * ω * a⁻¹) * a := by group
        _ = ω * a := by rw [hconj]
  refine hyp.center_le_subgroupOf_D hωQ hω1
    (hyp.mem_residualImage_of_mem_Q hQ2 hωQ hωC)
    (mem_residualImage_of_orderOf_eq_two_pow (G := G) s4.t_mem_centralizer (n := 1)
      (by rw [pow_one]; exact orderOf_eq_prime hyp.t_sq hyp.t_ne_one))

open scoped Pointwise in
include hyp in
/-- **`P ⊔ W = P · W`** — `P ≤ D` normalizes `W` (`D_le_normalizer_W`), so the join is a
product.  This is the factorization hypothesis `hfac` of both
`inf_le_sup_centralizer_W` and `eq_P_of_centralizes`. -/
theorem SectionFourSetup.exists_mem_P_mem_W_mul (s4 : hyp.SectionFourSetup)
    {v : G} (hv : v ∈ s4.P ⊔ hyp.W) :
    ∃ p ∈ s4.P, ∃ w ∈ hyp.W, v = p * w := by
  have hcoe : ((s4.P ⊔ hyp.W : Subgroup G) : Set G) = (s4.P : Set G) * (hyp.W : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (le_trans s4.P_le_D hyp.D_le_normalizer_W)
  obtain ⟨p, hp, w, hw, hpw⟩ : v ∈ (s4.P : Set G) * (hyp.W : Set G) := hcoe ▸ hv
  exact ⟨p, hp, w, hw, hpw.symm⟩

include hyp in
/-- **🎯 The book's `ζ₁ ∈ ζ P` with `ζ ∈ C_W(P)`** (Peterfalvi Part II, Ch. IV §4, p. 133).

The theorem of Galois puts `ζ₁ ∈ V ∩ U` into `P W` (`inf_le_sup_W_of_centralizes`), and
`P ⊔ W = P · W` factors it as `ζ₁ = p ζ`.  That `ζ` centralizes `P` is then automatic:
`ζ = p⁻¹ ζ₁` with `p ∈ P ≤ C_G(P)` (`P` is cyclic of prime order, hence abelian) and
`ζ₁ ∈ U ≤ C_G(P)`.

`hcent` is the one input the book reads off the structure of `PSU(3, ℓ)`:
"(V ∩ U)/(P ∩ U) centralizes `C_{Q₀}(P)`". -/
theorem SectionFourSetup.exists_refined_zeta (s4 : hyp.SectionFourSetup)
    (hcent : hyp.V ⊓ residualImage (G := G) s4.P ≤ Subgroup.centralizer
      (((hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) : Subgroup G) : Set G))
    {ζ₁ : G} (hζ₁V : ζ₁ ∈ hyp.V) (hζ₁U : ζ₁ ∈ residualImage (G := G) s4.P) :
    ∃ p ∈ s4.P, ∃ ζ ∈ hyp.W,
      ζ ∈ Subgroup.centralizer ((s4.P : Set G)) ∧ ζ₁ = p * ζ := by
  haveI : Fact (Nat.Prime s4.cardP) := ⟨s4.prime_cardP⟩
  haveI : IsCyclic ↥s4.P := isCyclic_of_prime_card s4.card_P
  have hPW : ζ₁ ∈ s4.P ⊔ hyp.W :=
    s4.inf_le_sup_W_of_centralizes hcent ⟨hζ₁V, hζ₁U⟩
  obtain ⟨p, hp, ζ, hζ, hpζ⟩ := SectionFourSetup.exists_mem_P_mem_W_mul hyp s4 hPW
  refine ⟨p, hp, ζ, hζ, ?_, hpζ⟩
  have hPC : s4.P ≤ Subgroup.centralizer ((s4.P : Set G)) := by
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    letI := IsCyclic.commGroup (α := ↥s4.P)
    exact congrArg (Subtype.val (p := fun z => z ∈ s4.P))
      (mul_comm (⟨b, hb⟩ : ↥s4.P) (⟨a, ha⟩ : ↥s4.P))
  have hζ₁C : ζ₁ ∈ Subgroup.centralizer ((s4.P : Set G)) :=
    residualImage_le_centralizer hζ₁U
  have hζeq : ζ = p⁻¹ * ζ₁ := by rw [hpζ]; group
  rw [hζeq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hPC hp)) hζ₁C

/-! ### The book's refinement `ζ₁ ∈ ζ P`

Peterfalvi Part II, Ch. IV §4, p. 133:

> Let `ζ₁ ∈ (V ∩ U) − (P ∩ U)` and `ζ ∈ C_W(P)` be such that `ζ₁ ∈ ζ P`.  ... there is an
> element `ω ∈ (Q − Q₀) ∩ U` such that `f₁(ω) ∈ ω^{-ζ₁}(P ∩ U)` and
> `h₁(ω) ∈ ζ₁³ (P ∩ U)`.  ... `f(ω) = ω^{-ζ₁} = ω^{-ζ}` and `h(ω) = h₁(ω) ∈ ζ³ P`.

`inf_le_sup_centralizer_W` supplies the factorization `ζ₁ = p ζ` with `p ∈ P` and
`ζ ∈ C_W(P)`; these two lemmas are the "`= ω^{-ζ}`" and "`∈ ζ³ P`" of the display.  Both
are pure group algebra: `ω` is centralized by `P` (it lies in `C_Q(P)`), and `p` commutes
with `ζ` because `ζ ∈ C_W(P)`. -/

omit [Finite G] in
/-- **`ω^{ζ₁} = ω^ζ` when `ζ₁ = p ζ` with `p ∈ P` centralizing `ω`.** -/
theorem conj_inv_eq_of_commute {p w ω : G} (hpω : p * ω = ω * p) :
    (p * w)⁻¹ * ω⁻¹ * (p * w) = w⁻¹ * ω⁻¹ * w := by
  have hcomm : Commute p ω := hpω
  have hinv : p⁻¹ * ω⁻¹ * p = ω⁻¹ := by
    have h : ω⁻¹ * p = p * ω⁻¹ := hcomm.inv_right.eq.symm
    calc p⁻¹ * ω⁻¹ * p = p⁻¹ * (ω⁻¹ * p) := by group
      _ = p⁻¹ * (p * ω⁻¹) := by rw [h]
      _ = ω⁻¹ := by group
  calc (p * w)⁻¹ * ω⁻¹ * (p * w) = w⁻¹ * (p⁻¹ * ω⁻¹ * p) * w := by group
    _ = w⁻¹ * ω⁻¹ * w := by rw [hinv]

omit [Finite G] in
/-- **`ζ₁³ c = ζ³ (p³ c)` when `p` and `ζ` commute** — the book's `h(ω) ∈ ζ³ P`. -/
theorem cube_mul_eq_of_commute {p w c : G} (hpw : p * w = w * p) :
    (p * w) ^ 3 * c = w ^ 3 * (p ^ 3 * c) := by
  have hcomm : Commute p w := hpw
  rw [hcomm.mul_pow 3, (hcomm.pow_pow 3 3).eq, mul_assoc]

include hyp in
/-- **🎯🎯 Peterfalvi Part II, Ch. IV §4, p. 134: `η ∈ W` and `h(ω) ∈ W`.**

The whole of §4 assembled: (10) holds on `F` off four points, so `μ² = id` there
(`coordFieldAut_sq_eq_id_on_frobFixed`); `μ` having odd order this gives `μ|_F = id`
(`coordFieldAut_eq_id_on_frobFixed_of_sq`) and then `μ = 1`
(`coordFieldAut_eq_id_of_fixes_frobFixed`); and `μ = 1` is `η ∈ C_V(K) = W`
(`mem_W_of_coordFieldAut_eq_id`).  Finally `h(ω) = ζ³η` with `ζ ∈ W`.

This is what §3's Corollary 1 consumes to finish the chapter. -/
theorem sectionFour_mem_W {f g k : G → G}
    (H : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g k)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (M : hyp.QuotientFieldModel m) (s : hyp.LemmaFiveSetup m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) (hq : 8 < 2 ^ m)
    {ζ ω y η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsqω : ω * ω = y)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) (hηζ : η * ζ = ζ * η) (hkω : k ω = ζ ^ 3 * η)
    (htη : hyp.t * η * hyp.t = η) (hηD : η ∈ hyp.D) (hηV : η ∈ hyp.V)
    (hηω : η * ω * η⁻¹ = ω)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    {j : ℕ} (hηord : η ^ (2 * j + 1) = 1) :
    η ∈ hyp.W ∧ k ω ∈ hyp.W := by
  have hsq := fun {x : M.E} (hx : x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m) =>
    hyp.coordFieldAut_sq_eq_id_on_frobFixed H hC2 M s hZ hm hQ0card hq hζ hωQ hωQ0 hyQ0
      hsqω hf hηζ hkω htη hηD hηω hznot hx
  have hFid : ∀ x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m,
      hyp.coordFieldAut s M hm hQ0card hηD hζ hznot x = x := fun x hx =>
    hyp.coordFieldAut_eq_id_on_frobFixed_of_sq M s hm hQ0card hηD hζ hznot hηord
      (fun z hz => hsq hz) hx
  have hall : ∀ x : M.E, hyp.coordFieldAut s M hm hQ0card hηD hζ hznot x = x := fun x =>
    hyp.coordFieldAut_eq_id_of_fixes_frobFixed M s hm hQ0card hηD hζ hznot
      (odd_two_mul_add_one j) hηord hFid x
  have hηW := hyp.mem_W_of_coordFieldAut_eq_id M s hm hQ0card hζ hηD hηV hznot hall
  refine ⟨hηW, ?_⟩
  rw [hkω]
  exact hyp.W.mul_mem (pow_mem hζ 3) hηW

include hyp in
/-- **🎯🎯🎯 Peterfalvi Part II, Ch. IV §4 from step (3)'s output** (pp. 133–134).

Step (3) produces `ζ₁ ∈ (V ∩ U) − (P ∩ U)`, an `x ∈ (Q − Q₀) ∩ U` with
`f(x) = x^{-ζ₁}`, and an `η ∈ Z(U) ⊆ P` with `k(x) = ζ₁³ η`.  This theorem turns that
into the section's conclusion `k(x) ∈ W`.

The refinement `ζ₁ = p ζ` with `ζ ∈ C_W(P)` (`exists_refined_zeta`) rewrites both:
`f(x) = x^{-ζ}` because `p` centralizes `x ∈ U ≤ C_G(P)`, and `k(x) = ζ³ (p³ η)` because
`p` commutes with `ζ ∈ C_W(P)`.  The new conjugator `η' = p³ η` again lies in `P`, is
centralized by `t ∈ C_G(P)` and by `ζ`, and centralizes `x`; so `sectionFour_mem_W`
applies and gives `η' ∈ W`, whence `k(x) = ζ³ η' ∈ W`. -/
theorem SectionFourSetup.mem_W_of_stepThree (s4 : hyp.SectionFourSetup) {f g k : G → G}
    (H : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g k)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m) (sfive : hyp.LemmaFiveSetup m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hmu : Function.Injective M.mu)
    (hl : 2 < Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))))
    (hcent : hyp.V ⊓ residualImage (G := G) s4.P ≤ Subgroup.centralizer
      (((hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) : Subgroup G) : Set G))
    {ζ₁ x η : G}
    (hζ₁V : ζ₁ ∈ hyp.V) (hζ₁U : ζ₁ ∈ residualImage (G := G) s4.P)
    (hζ₁P : ζ₁ ∉ s4.P)
    (hxQ : x ∈ hyp.Q) (hxQ0 : x ∉ hyp.Q0) (hxU : x ∈ residualImage (G := G) s4.P)
    (hfx : f x = ζ₁⁻¹ * x⁻¹ * ζ₁)
    (hηU : η ∈ residualImage (G := G) s4.P)
    (hηc : (⟨η, hηU⟩ : ↥(residualImage (G := G) s4.P))
      ∈ Subgroup.center ↥(residualImage (G := G) s4.P))
    (hηP : η ∈ s4.P) (hkx : k x = ζ₁ ^ 3 * η) :
    k x ∈ hyp.W := by
  classical
  haveI : Fact (Nat.Prime s4.cardP) := ⟨s4.prime_cardP⟩
  haveI : IsCyclic ↥s4.P := isCyclic_of_prime_card s4.card_P
  obtain ⟨p, hp, ζ, hζW, hζC, hζ₁eq⟩ :=
    SectionFourSetup.exists_refined_zeta hyp s4 hcent hζ₁V hζ₁U
  -- `ζ ≠ 1`, else `ζ₁ = p ∈ P`
  have hζ1 : ζ ≠ 1 := by
    intro hc
    exact hζ₁P (by rw [hζ₁eq, hc, mul_one]; exact hp)
  -- `p` centralizes `x ∈ U ≤ C_G(P)` and commutes with `ζ ∈ C_W(P)`
  have hxC : x ∈ Subgroup.centralizer ((s4.P : Set G)) := residualImage_le_centralizer hxU
  have hpx : p * x = x * p := Subgroup.mem_centralizer_iff.mp hxC p hp
  have hpζ : p * ζ = ζ * p := Subgroup.mem_centralizer_iff.mp hζC p hp
  -- the rewritten `f` and `k`
  have hfζ : f x = ζ⁻¹ * x⁻¹ * ζ := by
    rw [hfx, hζ₁eq]
    exact conj_inv_eq_of_commute hpx
  have hkζ : k x = ζ ^ 3 * (p ^ 3 * η) := by
    rw [hkx, hζ₁eq]
    exact cube_mul_eq_of_commute hpζ
  -- the new conjugator `η' = p³ η`
  set η' := p ^ 3 * η with hη'def
  have hη'P : η' ∈ s4.P := s4.P.mul_mem (pow_mem hp 3) hηP
  have hη'V : η' ∈ hyp.V := s4.P_le_V hη'P
  have hη'D : η' ∈ hyp.D := s4.P_le_D hη'P
  -- `t` centralizes `P` and `Z(U)`
  have htp : hyp.t * p = p * hyp.t :=
    (Subgroup.mem_centralizer_iff.mp s4.t_mem_centralizer p hp).symm
  have htη : hyp.t * η * hyp.t = η :=
    hyp.conj_t_eq_of_mem_center
      (mem_residualImage_of_orderOf_eq_two_pow (G := G) s4.t_mem_centralizer (n := 1)
        (by rw [pow_one]; exact orderOf_eq_prime hyp.t_sq hyp.t_ne_one)) hηU hηc
  have htη' : hyp.t * η' * hyp.t = η' := by
    have htp3 : hyp.t * p ^ 3 = p ^ 3 * hyp.t := (Commute.pow_right (htp : Commute hyp.t p) 3).eq
    calc hyp.t * η' * hyp.t = p ^ 3 * (hyp.t * η * hyp.t) := by
          rw [hη'def, ← mul_assoc, htp3]; group
      _ = η' := by rw [htη]
  -- `η'` commutes with `ζ` and centralizes `x`
  have hηζ : η * ζ = ζ * η := Subgroup.mem_centralizer_iff.mp hζC η hηP
  have hη'ζ : η' * ζ = ζ * η' := by
    calc η' * ζ = p ^ 3 * (η * ζ) := by rw [hη'def]; group
      _ = p ^ 3 * (ζ * η) := by rw [hηζ]
      _ = (p ^ 3 * ζ) * η := by group
      _ = (ζ * p ^ 3) * η := by rw [(Commute.pow_left (hpζ : Commute p ζ) 3).eq]
      _ = ζ * η' := by rw [hη'def]; group
  have hηx : η * x = x * η := by
    have hz := Subgroup.mem_center_iff.mp hηc ⟨x, hxU⟩
    exact (congrArg Subtype.val hz).symm
  have hη'x : η' * x * η'⁻¹ = x := by
    have hp3x : p ^ 3 * x = x * p ^ 3 := (Commute.pow_left (hpx : Commute p x) 3).eq
    calc η' * x * η'⁻¹ = p ^ 3 * (η * x) * η'⁻¹ := by rw [hη'def]; group
      _ = p ^ 3 * (x * η) * η'⁻¹ := by rw [hηx]
      _ = (p ^ 3 * x) * (η * η'⁻¹) := by group
      _ = (x * p ^ 3) * (η * η'⁻¹) := by rw [hp3x]
      _ = x * (p ^ 3 * η * η'⁻¹) := by group
      _ = x := by rw [← hη'def, mul_inv_cancel, mul_one]
  -- the remaining numeric inputs
  have hq : 8 < 2 ^ m := by
    rw [← hQ0card]
    exact SectionFourSetup.eight_lt_natCard_Q0 hyp s4 hl
  have hznot := hyp.mu_W_notMem_frobFixed M hmu
    (show (⟨ζ, hζW⟩ : ↥hyp.W) ≠ 1 from fun hc => hζ1 (congrArg Subtype.val hc))
  obtain ⟨j, hj⟩ := SectionFourSetup.pow_odd_eq_one_of_mem_P hyp s4 hη'P
  obtain ⟨hη'W, hkW⟩ := hyp.sectionFour_mem_W H hC2 M sfive hZ hm hQ0card hq hζW hxQ hxQ0
    (hyp.sq_mem_Q0_of_lemmaFiveSetup sfive hxQ) rfl hfζ hη'ζ hkζ htη' hη'D hη'V hη'x
    hznot hj
  exact hkW

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
