/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourEquations
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourCorollaryTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourStepThree
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourEndgameCore

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
* `Hypothesis.SectionFourSetup.center_residualImage_le_P` — **`Z(U) ⊆ P`** of step (1).
* `Hypothesis.mem_W_intrinsicResidualQuotient_of_mem_V` — the book's `ζ₁ ∈ V ∩ U` really
  is an element of the quotient's `W̄`, because there `V̄ = W̄`.
* `Hypothesis.SectionFourSetup.eq_one_of_conj_t_mem_P` — a `t`-commutator landing in `P`
  is trivial; this is why lifting a `V̄`-element to `U` stays inside `V`.
* `Hypothesis.inf_le_centralizer_centralizer_Q0` — the `hcent` of §4, *derived* from the
  quotient's `V̄ = W̄` rather than assumed.
* `Hypothesis.SectionFourSetup.exists_mem_W` — **🎯🎯🎯🎯 all of §4 from the section's
  standing data and the book's choice of `ζ₁`.**
* `Hypothesis.SectionFourSetup.exists_stepThree_data` — that output, produced from the
  section's standing data (steps (1)–(3) plumbed together).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

variable {m : ℕ}
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

include hyp in
/-- **🎯 `Z(U) ⊆ P`** (Peterfalvi Part II, Ch. IV §4, step (1), p. 132):

> Since `P Z(U)` centralizes `C_Q(P) ⊄ Q₀`, `P Z(U) ∩ W = 1` and so `Z(U) ⊂ P`.

Everything the book uses here is now available: `Z(U) ⊆ D` (`center_le_subgroupOf_D`) and
`Z(U) ⊆ C_G(t)` (as `t ∈ U`) put `Z(U)` in `V ∩ U`, which the theorem of Galois
(`inf_le_sup_W_of_centralizes`) puts in `P W`; and `P Z(U)` centralizes Glauberman's
`ω ∈ C_Q(P) − Q₀` because `P` fixes it and `Z(U)` is central in `U ∋ ω`.  So
`eq_P_of_centralizes` applies to `S = P Z(U)`. -/
theorem SectionFourSetup.center_residualImage_le_P (s4 : hyp.SectionFourSetup)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hQ2 : IsPGroup 2 ↥hyp.Q)
    (hcent : hyp.V ⊓ residualImage (G := G) s4.P ≤ Subgroup.centralizer
      (((hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G))) : Subgroup G) : Set G))
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hωfix : ∀ a ∈ s4.P, a * ω * a⁻¹ = ω)
    {η : G} (hηU : η ∈ residualImage (G := G) s4.P)
    (hηc : (⟨η, hηU⟩ : ↥(residualImage (G := G) s4.P))
      ∈ Subgroup.center ↥(residualImage (G := G) s4.P)) :
    η ∈ s4.P := by
  classical
  have hZD := SectionFourSetup.center_residualImage_le_D hyp s4 hQ2 hωQ hωQ0 hωfix
  have htU : hyp.t ∈ residualImage (G := G) s4.P :=
    mem_residualImage_of_orderOf_eq_two_pow (G := G) s4.t_mem_centralizer (n := 1)
      (by rw [pow_one]; exact orderOf_eq_prime hyp.t_sq hyp.t_ne_one)
  have hωC : ω ∈ Subgroup.centralizer ((s4.P : Set G)) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => by
      have hconj := hωfix a ha
      calc a * ω = (a * ω * a⁻¹) * a := by group
        _ = ω * a := by rw [hconj]
  have hωU : ω ∈ residualImage (G := G) s4.P :=
    hyp.mem_residualImage_of_mem_Q hQ2 hωQ hωC
  -- `Z(U)`, read in `G`
  set Z : Subgroup G :=
    (Subgroup.center ↥(residualImage (G := G) s4.P)).map
      (residualImage (G := G) s4.P).subtype with hZdef
  have hZV : Z ≤ hyp.V ⊓ residualImage (G := G) s4.P := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨⟨Subgroup.mem_subgroupOf.mp (hZD hc),
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, c.2⟩
    have hz := Subgroup.mem_center_iff.mp hc ⟨hyp.t, htU⟩
    exact (congrArg Subtype.val hz).symm
  have hZPW : Z ≤ s4.P ⊔ hyp.W :=
    le_trans hZV (s4.inf_le_sup_W_of_centralizes hcent)
  set S : Subgroup G := s4.P ⊔ Z with hSdef
  have hSPW : S ≤ s4.P ⊔ hyp.W := sup_le le_sup_left hZPW
  have hfac : ∀ v ∈ S, ∃ p ∈ s4.P, ∃ w ∈ hyp.W, v = p * w := fun v hv =>
    SectionFourSetup.exists_mem_P_mem_W_mul hyp s4 (hSPW hv)
  have hPC : s4.P ≤ Subgroup.centralizer ({ω} : Set G) := by
    intro a ha
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hconj := hωfix a ha
    calc a * ω = (a * ω * a⁻¹) * a := by group
      _ = ω * a := by rw [hconj]
  have hZC : Z ≤ Subgroup.centralizer ({ω} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hz := Subgroup.mem_center_iff.mp hc ⟨ω, hωU⟩
    exact (congrArg Subtype.val hz).symm
  have hSω : ∀ c ∈ S, c * ω = ω * c := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mp
      ((sup_le hPC hZC : S ≤ Subgroup.centralizer ({ω} : Set G)) hc)
  have hSP : S = s4.P :=
    s4.eq_P_of_centralizes M hZ hmu le_sup_left hfac hωQ hωQ0 hSω
  have hηZ : η ∈ Z := ⟨⟨η, hηU⟩, hηc, rfl⟩
  have hηS : η ∈ S := (le_sup_right : Z ≤ S) hηZ
  rwa [hSP] at hηS

include hyp in
/-- **🎯🎯 Step (3)'s output, packaged for `mem_W_of_stepThree`** (Peterfalvi Part II,
Ch. IV §4, pp. 132–133).

The plumbing of steps (1)–(3): Glauberman's `ω ∈ C_Q(P) − Q₀` gives `Z(U) ⊆ D`
(`center_residualImage_le_D`), Ch. I §3 Proposition 1(c) gives the `PSU(3, ℓ)` branch
(`nonempty_psu3Data_sectionFour`), the transported standing hypothesis has a nontrivial
`W̄`-element (`exists_ne_one_mem_W_intrinsicResidualQuotient`), and step (3)
(`exists_f_eq_conj_inv_residual`) reads the resulting `f`- and `h`-values back into `G`. -/
theorem SectionFourSetup.exists_stepThree_data (s4 : hyp.SectionFourSetup) {f g k : G → G}
    (H : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g k)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hQ2 : IsPGroup 2 ↥hyp.Q)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q) (hP : s4.P ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer ((s4.P : Set G)))))
    (ih : TheoremAInductionBelow G Ω) :
    ∃ ζ₁ x η : G, ζ₁ ∈ hyp.D ∧ ζ₁ ∈ residualImage (G := G) s4.P ∧
      x ∈ hyp.Q ∧ x ∉ hyp.Q0 ∧ x ∈ residualImage (G := G) s4.P ∧
      f x = ζ₁⁻¹ * x⁻¹ * ζ₁ ∧
      ∃ hηU : η ∈ residualImage (G := G) s4.P,
        (⟨η, hηU⟩ : ↥(residualImage (G := G) s4.P))
            ∈ Subgroup.center ↥(residualImage (G := G) s4.P) ∧
          k x = ζ₁ ^ 3 * η := by
  classical
  letI := hyp.centralizerQuotientMulAction s4.P_le_V
  obtain ⟨ω, hωQ, hωQ0, hωfix⟩ := s4.exists_fixed_not_mem_Q0 hZ hCop hSolv
  have hZD := SectionFourSetup.center_residualImage_le_D hyp s4 hQ2 hωQ hωQ0 hωfix
  obtain ⟨result, data, ⟨details⟩⟩ :=
    hyp.nonempty_psu3Data_sectionFour s4 hZ hQsuz hCop hSolv hP hA3 hord ih
  obtain ⟨zbar, hzbarW, hzbar1⟩ :=
    hyp.exists_ne_one_mem_W_intrinsicResidualQuotient details s4.P_le_D
      s4.t_mem_centralizer hCQ hZD
  obtain ⟨z, x, hzD, -, hxQ, hxQ0, hfx, c, hcZ, hkx⟩ :=
    hyp.exists_f_eq_conj_inv_residual H s4.P_le_V hP details s4.P_le_D
      s4.t_mem_centralizer hCQ hZD ih zbar hzbarW hzbar1
  refine ⟨(z : G), (x : G), (c : G), hzD, z.2, hxQ, hxQ0, x.2, hfx, c.2, ?_, ?_⟩
  · simpa using hcZ
  · rw [hkx]
    push_cast
    ring

include hyp in
/-- **A `t`-commutator landing in `P` is trivial.**

For any `ζ`, the element `c = ζ⁻¹ · ζ^t` satisfies `c^t = c⁻¹` (a two-line computation
using `t² = 1`).  If moreover `c ∈ P`, then `t` centralizes it (`t ∈ C_G(P)`), so
`c = c⁻¹`; and `P` has odd order, so `c = 1`.

This is what makes lifting from `U/Z(U)` to `U` harmless for `V`-membership: a lift of a
`V̄`-element has its `t`-commutator in `Z(U) ⊆ P`, hence commutes with `t` outright. -/
theorem SectionFourSetup.eq_one_of_conj_t_mem_P (s4 : hyp.SectionFourSetup)
    {ζ c : G} (heq : ζ⁻¹ * (hyp.t * ζ * hyp.t) = c) (hc : c ∈ s4.P) : c = 1 := by
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  have htinv : hyp.t⁻¹ = hyp.t := inv_eq_of_mul_eq_one_right htt
  -- `c^t = c⁻¹`
  have hLHS : hyp.t * c * hyp.t = hyp.t * ζ⁻¹ * hyp.t * ζ := by
    rw [← heq]
    calc hyp.t * (ζ⁻¹ * (hyp.t * ζ * hyp.t)) * hyp.t
        = hyp.t * ζ⁻¹ * hyp.t * ζ * (hyp.t * hyp.t) := by group
      _ = hyp.t * ζ⁻¹ * hyp.t * ζ := by rw [htt, mul_one]
  have hRHS : c⁻¹ = hyp.t * ζ⁻¹ * hyp.t * ζ := by
    rw [← heq]
    calc (ζ⁻¹ * (hyp.t * ζ * hyp.t))⁻¹ = hyp.t⁻¹ * ζ⁻¹ * hyp.t⁻¹ * ζ := by group
      _ = hyp.t * ζ⁻¹ * hyp.t * ζ := by rw [htinv]
  -- `t` centralizes `P`
  have hcomm := Subgroup.mem_centralizer_iff.mp s4.t_mem_centralizer c hc
  have hfix : hyp.t * c * hyp.t = c := by
    calc hyp.t * c * hyp.t = c * hyp.t * hyp.t := by rw [hcomm]
      _ = c * (hyp.t * hyp.t) := by group
      _ = c := by rw [htt, mul_one]
  have hsq : c * c = 1 := by
    have hcinv : c⁻¹ = c := by rw [hRHS, ← hLHS, hfix]
    calc c * c = c⁻¹ * c := by rw [hcinv]
      _ = 1 := inv_mul_cancel c
  obtain ⟨j, hj⟩ := SectionFourSetup.pow_odd_eq_one_of_mem_P hyp s4 hc
  exact eq_one_of_sq_eq_one_of_odd_pow (odd_two_mul_add_one j) (by rw [sq]; exact hsq) hj

/-! ### The book's `ζ₁ ∈ (V ∩ U) − (P ∩ U)` as a `W̄`-element -/

section Intrinsic

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

variable {X : Subgroup G}
  [MulAction (hyp.centralizerActionQuotient X) ↥(MulAction.fixedPoints X Ω)]
  {result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Ω)}
  {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Ω)) result.L}

include hyp in
/-- **The image of `ζ₁ ∈ V ∩ U` lies in `W̄`** (Peterfalvi Part II, Ch. IV §4, p. 133).

The book applies §3's Corollary 2 — which wants an element of the `W` of the `U`-relative
standing hypothesis — to its `ζ₁ ∈ (V ∩ U) − (P ∩ U)`.  What makes that legitimate is that
on `U/Z(U) ≅ PSU(3, ℓ)` one has `V̄ = W̄` (`V_eq_W_intrinsicResidualQuotient`); the image of
`ζ₁` is in `D̄` and commutes with `t̄`, hence lies in `V̄`.

⚠ This is the *quotient's* `V = W`, not the ambient one — §4 is precisely the case
`V ≠ W` in `G`. -/
theorem mem_W_intrinsicResidualQuotient_of_mem_V
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    {ζ₁ : G} (hζ₁D : ζ₁ ∈ hyp.D) (hζ₁t : ζ₁ * hyp.t = hyp.t * ζ₁)
    (hζ₁U : ζ₁ ∈ residualImage (G := G) X) :
    QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)) ⟨ζ₁, hζ₁U⟩
      ∈ (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).W := by
  rw [← hyp.V_eq_W_intrinsicResidualQuotient details hXD htX hCQ hZD]
  refine ⟨⟨⟨ζ₁, hζ₁U⟩, Subgroup.mem_subgroupOf.mpr hζ₁D, rfl⟩, ?_⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  change QuotientGroup.mk' _ _ * QuotientGroup.mk' _ _
    = QuotientGroup.mk' _ _ * QuotientGroup.mk' _ _
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hζ₁t

include hyp in
/-- **🎯 `V ∩ U` centralizes `C_{Q₀}(X)`** (Peterfalvi Part II, Ch. IV §4, step (2),
p. 133: "By the structure of `PSU(3, ℓ)`, `(V ∩ U)/(P ∩ U)` centralizes `C_{Q₀}(P)`").

Not an external input: it follows from the quotient's `V̄ = W̄`.  Indeed
`W_eq_inf_centralizer_Q0` (`W = D ∩ C(Q₀)`, a theorem about *any* standing hypothesis)
applied to `U/Z(U)` gives `W̄ = D̄ ∩ C(Q̄₀)`, so `V̄ ≤ C(Q̄₀)`; hence `[ζ₁, y] ∈ Z(U)`
for `ζ₁ ∈ V ∩ U` and `y ∈ C_{Q₀}(X) ⊆ U`.  But `[ζ₁, y] ∈ Q` (as `ζ₁ ∈ D ≤ H` normalizes
`Q`) and `Z(U) ≤ D`, and `Q ∩ D = 1` is an axiom of the standing hypothesis — so the
commutator is trivial. -/
theorem inf_le_centralizer_centralizer_Q0
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    (hQ2 : IsPGroup 2 ↥hyp.Q) :
    hyp.V ⊓ residualImage (G := G) X ≤ Subgroup.centralizer
      (((hyp.Q0 ⊓ Subgroup.centralizer ((X : Set G))) : Subgroup G) : Set G) := by
  rintro ζ₁ ⟨hζ₁V, hζ₁U⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  obtain ⟨hyQ0, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyQ : y ∈ hyp.Q := hyp.Q0_le_Q hyQ0
  have hyU : y ∈ residualImage (G := G) X := hyp.mem_residualImage_of_mem_Q hQ2 hyQ hyC
  -- `ζ₁`'s image centralizes `Q̄₀`
  have hzbarW := hyp.mem_W_intrinsicResidualQuotient_of_mem_V details hXD htX hCQ hZD
    (hyp.V_le_D hζ₁V) (Subgroup.mem_centralizer_singleton_iff.mp hζ₁V.2) hζ₁U
  rw [(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).W_eq_inf_centralizer_Q0]
    at hzbarW
  have hybar : (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))
      ⟨y, hyU⟩) ∈ (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0 := by
    refine ⟨?_, ⟨⟨y, hyU⟩, Subgroup.mem_subgroupOf.mpr (hyp.Q_le_H hyQ), rfl⟩⟩
    have hsq : (⟨y, hyU⟩ : ↥(residualImage (G := G) X)) ^ 2 = 1 :=
      Subtype.ext (by simpa using hyp.sq_eq_one_of_mem_Q0 hyQ0)
    rw [← map_pow, hsq, map_one]
  have hcomm := Subgroup.mem_centralizer_iff.mp hzbarW.2 _ hybar
  -- lift the commuting relation: the commutator is in `Z(U) ≤ D` and in `Q`, so trivial
  have hker : ((⟨y, hyU⟩ : ↥(residualImage (G := G) X)) * ⟨ζ₁, hζ₁U⟩)⁻¹
      * ((⟨ζ₁, hζ₁U⟩ : ↥(residualImage (G := G) X)) * ⟨y, hyU⟩)
      ∈ Subgroup.center ↥(residualImage (G := G) X) := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    simpa using hcomm
  have hcD : ζ₁⁻¹ * y⁻¹ * (ζ₁ * y) ∈ hyp.D := by
    have h := Subgroup.mem_subgroupOf.mp (hZD hker)
    simpa using h
  have hcQ : ζ₁⁻¹ * y⁻¹ * (ζ₁ * y) ∈ hyp.Q := by
    have h1 : ζ₁⁻¹ * y⁻¹ * ζ₁⁻¹⁻¹ ∈ hyp.Q :=
      hyp.Q_normal_in_H ζ₁⁻¹ (hyp.H.inv_mem (hyp.D_le_H (hyp.V_le_D hζ₁V)))
        y⁻¹ (hyp.Q.inv_mem hyQ)
    rw [inv_inv] at h1
    have h2 : ζ₁⁻¹ * y⁻¹ * (ζ₁ * y) = (ζ₁⁻¹ * y⁻¹ * ζ₁) * y := by group
    rw [h2]
    exact hyp.Q.mul_mem h1 hyQ
  have hc1 : ζ₁⁻¹ * y⁻¹ * (ζ₁ * y) = 1 := by
    have hmem : ζ₁⁻¹ * y⁻¹ * (ζ₁ * y) ∈ hyp.Q ⊓ hyp.D := ⟨hcQ, hcD⟩
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hyζ : ζ₁ * y = y * ζ₁ := by
    have h := eq_inv_of_mul_eq_one_right hc1
    rw [h, mul_inv_rev, inv_inv, inv_inv]
  exact hyζ.symm

include hyp in
/-- **`P ∩ U ⊆ Z(U)`** — `U ≤ C_G(P)`, so an element of `P` inside `U` is central there. -/
theorem SectionFourSetup.mem_center_of_mem_P (s4 : hyp.SectionFourSetup) {x : G}
    (hxP : x ∈ s4.P) (hxU : x ∈ residualImage (G := G) s4.P) :
    (⟨x, hxU⟩ : ↥(residualImage (G := G) s4.P))
      ∈ Subgroup.center ↥(residualImage (G := G) s4.P) := by
  refine Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_
  exact (Subgroup.mem_centralizer_iff.mp
    (residualImage_le_centralizer (G := G) u.2) x hxP).symm

include hyp in
/-- **A `U`-element with nontrivial image is outside `P`** — because `P ∩ U ⊆ Z(U)`.

This is the book's `ζ₁ ∉ P ∩ U` (p. 133), obtained from `ζ̄ ≠ 1` rather than from the
count `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1`. -/
theorem SectionFourSetup.notMem_P_of_mk_ne_one (s4 : hyp.SectionFourSetup) {ζ₁ : G}
    (hζ₁U : ζ₁ ∈ residualImage (G := G) s4.P)
    (hne : QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) s4.P))
      ⟨ζ₁, hζ₁U⟩ ≠ 1) : ζ₁ ∉ s4.P := by
  intro hc
  refine hne ?_
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact SectionFourSetup.mem_center_of_mem_P hyp s4 hc hζ₁U

include hyp in
/-- **🎯 The book's `ζ₁ ∈ (V ∩ U) − (P ∩ U)`, produced** (Peterfalvi Part II, Ch. IV §4,
p. 133).

A nontrivial element of the quotient's `W̄ = V̄` lifts to `z₀ ∈ D ∩ U`; the lift lies in
`V` because `[z₀, t] ∈ Z(U) ⊆ P` is a `t`-commutator inside `P`, hence trivial
(`eq_one_of_conj_t_mem_P`); and it lies outside `P` because `P ∩ U ⊆ Z(U)`
(`notMem_P_of_mk_ne_one`).

⚠ The book instead *counts*: `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1`.  That is not
needed — no property of `PSU(3, ℓ)` enters. -/
theorem SectionFourSetup.exists_zeta_one (s4 : hyp.SectionFourSetup)
    [MulAction (hyp.centralizerActionQuotient s4.P) ↥(MulAction.fixedPoints s4.P Ω)]
    {result : TheoremAConclusion (hyp.centralizerActionQuotient s4.P)
      ↥(MulAction.fixedPoints s4.P Ω)}
    {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints s4.P Ω)) result.L}
    (details : CentralizerPSUData hyp s4.P result data)
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer ((s4.P : Set G)))))
    (hZD : Subgroup.center ↥(residualImage (G := G) s4.P)
      ≤ hyp.D.subgroupOf (residualImage (G := G) s4.P))
    (hZP : ∀ {c : G} (hc : c ∈ residualImage (G := G) s4.P),
      (⟨c, hc⟩ : ↥(residualImage (G := G) s4.P))
        ∈ Subgroup.center ↥(residualImage (G := G) s4.P) → c ∈ s4.P) :
    ∃ ζ₁ ∈ hyp.V, ζ₁ ∈ residualImage (G := G) s4.P ∧ ζ₁ ∉ s4.P := by
  classical
  obtain ⟨zeta, hzetaW, hzeta1⟩ := hyp.exists_ne_one_mem_W_intrinsicResidualQuotient
    details s4.P_le_D s4.t_mem_centralizer hCQ hZD
  have hzetaV : zeta ∈ (hyp.intrinsicResidualQuotient details s4.P_le_D
      s4.t_mem_centralizer hCQ hZD).V := by
    rw [hyp.V_eq_W_intrinsicResidualQuotient details s4.P_le_D s4.t_mem_centralizer hCQ
      hZD]
    exact hzetaW
  obtain ⟨z₀, hz₀D, hz₀eq⟩ := hzetaV.1
  set tU : ↥(residualImage (G := G) s4.P) :=
    ⟨hyp.t, hyp.t_mem_residual s4.t_mem_centralizer⟩ with htUdef
  have htUval : (tU : G) = hyp.t := rfl
  -- the `t`-commutator of the lift lies in `Z(U)`
  have hmk : (QuotientGroup.mk (tU * z₀) :
        ↥(residualImage (G := G) s4.P) ⧸ Subgroup.center ↥(residualImage (G := G) s4.P))
      = QuotientGroup.mk (z₀ * tU) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    have h := (Subgroup.mem_centralizer_singleton_iff.mp hzetaV.2).symm
    rw [← hz₀eq] at h
    exact h
  have hker : (tU * z₀)⁻¹ * (z₀ * tU)
      ∈ Subgroup.center ↥(residualImage (G := G) s4.P) := QuotientGroup.eq.mp hmk
  have hcP : (((tU * z₀)⁻¹ * (z₀ * tU) : ↥(residualImage (G := G) s4.P)) : G) ∈ s4.P :=
    hZP ((tU * z₀)⁻¹ * (z₀ * tU)).2 hker
  have heq : (z₀ : G)⁻¹ * (hyp.t * (z₀ : G) * hyp.t)
      = (((tU * z₀)⁻¹ * (z₀ * tU) : ↥(residualImage (G := G) s4.P)) : G) := by
    push_cast
    rw [htUval, mul_inv_rev, hyp.t_inv_eq]
    group
  have hone := SectionFourSetup.eq_one_of_conj_t_mem_P hyp s4 heq hcP
  have hz₀t : hyp.t * (z₀ : G) * hyp.t = (z₀ : G) := by
    have h := heq.trans hone
    rw [inv_mul_eq_one] at h
    exact h.symm
  refine ⟨(z₀ : G), ⟨Subgroup.mem_subgroupOf.mp hz₀D,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, z₀.2, ?_⟩
  · calc (z₀ : G) * hyp.t = (hyp.t * (z₀ : G) * hyp.t) * hyp.t := by rw [hz₀t]
      _ = hyp.t * (z₀ : G) * (hyp.t * hyp.t) := by group
      _ = hyp.t * (z₀ : G) := by rw [← sq, hyp.t_sq, mul_one]
  · refine SectionFourSetup.notMem_P_of_mk_ne_one hyp s4 z₀.2 ?_
    intro hc
    exact hzeta1 (by rw [← hz₀eq]; exact hc)

end Intrinsic

include hyp in
/-- **🎯🎯🎯🎯 Peterfalvi Part II, Ch. IV §4, from the section's standing data**
(pp. 132–134).

Given the book's `ζ₁ ∈ (V ∩ U) − (P ∩ U)`, the whole section runs: its image is a
nontrivial element of the quotient's `W̄` (`mem_W_intrinsicResidualQuotient_of_mem_V`,
`center_residualImage_le_P`), step (3) produces `z` lifting it, and `z` inherits
`z ∈ V`, `z ∉ P` because it differs from `ζ₁` by an element of `Z(U) ⊆ P ≤ V`.
`mem_W_of_stepThree` then gives `k(x) ∈ W`, which is what §3's Corollary 1 consumes. -/
theorem SectionFourSetup.exists_mem_W (s4 : hyp.SectionFourSetup) {f g k : G → G}
    (H : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g k)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m) (sfive : hyp.LemmaFiveSetup m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hmu : Function.Injective M.mu) (hQ2 : IsPGroup 2 ↥hyp.Q)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q) (hP : s4.P ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer ((s4.P : Set G)))))
    (ih : TheoremAInductionBelow G Ω)
    (hl : 2 < Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G)))) :
    ∃ x ∈ hyp.Q, x ∉ hyp.Q0 ∧ k x ∈ hyp.W := by
  classical
  letI := hyp.centralizerQuotientMulAction s4.P_le_V
  obtain ⟨ω, hωQ, hωQ0, hωfix⟩ := s4.exists_fixed_not_mem_Q0 hZ hCop hSolv
  have hZD := SectionFourSetup.center_residualImage_le_D hyp s4 hQ2 hωQ hωQ0 hωfix
  obtain ⟨result, data, ⟨details⟩⟩ :=
    hyp.nonempty_psu3Data_sectionFour s4 hZ hQsuz hCop hSolv hP hA3 hord ih
  have hcent := hyp.inf_le_centralizer_centralizer_Q0 details s4.P_le_D
    s4.t_mem_centralizer hCQ hZD hQ2
  have hZP : ∀ {c : G} (hc : c ∈ residualImage (G := G) s4.P),
      (⟨c, hc⟩ : ↥(residualImage (G := G) s4.P))
        ∈ Subgroup.center ↥(residualImage (G := G) s4.P) → c ∈ s4.P := fun hc hcc =>
    SectionFourSetup.center_residualImage_le_P hyp s4 M hZ hmu hQ2 hcent hωQ hωQ0 hωfix
      hc hcc
  obtain ⟨ζ₁, hζ₁V, hζ₁U, hζ₁P⟩ :=
    SectionFourSetup.exists_zeta_one hyp s4 details hCQ hZD hZP
  have hζ₁t : ζ₁ * hyp.t = hyp.t * ζ₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp hζ₁V.2
  have hzbarW := hyp.mem_W_intrinsicResidualQuotient_of_mem_V details s4.P_le_D
    s4.t_mem_centralizer hCQ hZD (hyp.V_le_D hζ₁V) hζ₁t hζ₁U
  have hzbar1 : QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) s4.P))
      ⟨ζ₁, hζ₁U⟩ ≠ 1 := by
    intro hc
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
    exact hζ₁P (hZP hζ₁U hc)
  obtain ⟨z, x, hzD, hzζ, hxQ, hxQ0, hfx, c, hcZ, hkx⟩ :=
    hyp.exists_f_eq_conj_inv_residual H s4.P_le_V hP details s4.P_le_D
      s4.t_mem_centralizer hCQ hZD ih _ hzbarW hzbar1
  -- `z` differs from `ζ₁` by an element of `Z(U) ⊆ P`
  have hdiff : (⟨ζ₁, hζ₁U⟩ : ↥(residualImage (G := G) s4.P))⁻¹ * z
      ∈ Subgroup.center ↥(residualImage (G := G) s4.P) := by
    rw [← QuotientGroup.eq]
    exact hzζ.symm
  set c₀ : ↥(residualImage (G := G) s4.P) :=
    (⟨ζ₁, hζ₁U⟩ : ↥(residualImage (G := G) s4.P))⁻¹ * z with hc₀def
  have hc₀P : (c₀ : G) ∈ s4.P := hZP c₀.2 (by simpa using hdiff)
  have hzeq : (z : G) = ζ₁ * (c₀ : G) := by
    have hprod : (⟨ζ₁, hζ₁U⟩ : ↥(residualImage (G := G) s4.P)) * c₀ = z := by
      rw [hc₀def]; group
    have hv := congrArg Subtype.val hprod
    push_cast at hv
    exact hv.symm
  have hzV : (z : G) ∈ hyp.V := by
    rw [hzeq]
    exact hyp.V.mul_mem hζ₁V (s4.P_le_V hc₀P)
  have hzP : (z : G) ∉ s4.P := by
    intro hc
    refine hζ₁P ?_
    have : ζ₁ = (z : G) * (c₀ : G)⁻¹ := by rw [hzeq]; group
    rw [this]
    exact s4.P.mul_mem hc (s4.P.inv_mem hc₀P)
  -- the conjugator
  have hcP : (c : G) ∈ s4.P := hZP c.2 (by simpa using hcZ)
  have hkx' : k (x : G) = (z : G) ^ 3 * (c : G) := by
    rw [hkx]; push_cast; ring
  refine ⟨(x : G), hxQ, hxQ0, ?_⟩
  exact SectionFourSetup.mem_W_of_stepThree hyp s4 H hC2 M sfive hZ hm hQ0card hmu hl
    hcent hzV z.2 hzP hxQ hxQ0 x.2 hfx c.2 (by simpa using hcZ) hcP hkx'

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
