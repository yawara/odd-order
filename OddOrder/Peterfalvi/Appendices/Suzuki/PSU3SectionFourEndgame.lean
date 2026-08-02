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
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
