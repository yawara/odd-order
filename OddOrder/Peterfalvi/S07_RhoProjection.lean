/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S04_DadeIsometry
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction

/-!
# Peterfalvi §7: the `ρ` projection (Hypothesis (7.1))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §7, pp. 38–43.

Under Hypothesis (2.2) (`S04.Hypothesis G A L`, with its family of subgroups `H(a)` for `a ∈ A`),
**(7.1)** attaches to each `χ ∈ CF(G)` the function `χ^ρ` on `A` defined by averaging `χ` over the
coset `aH(a)`:
$$ \chi^\rho(a) = \frac{1}{|H(a)|}\sum_{x \in H(a)} \chi(ax). $$
This `ρ` is the adjoint of the Dade isometry `τ`: (7.2.a) `α^{τρ} = α` for `α ∈ CF(L,A)`, and
(7.2.b)/(7.3) give the norm bounds `‖χ^ρ‖² ≤ ‖χ‖²` and
`(1/|G|)∑_{g∈A^τ}|χ(g)|² ≥ ‖χ^ρ‖²` feeding the final inequality of (12.16).

This file builds the foundational **value** `rhoValue` of (7.1) and its `ℂ`-linearity in `χ`; the
class-function packaging (`L`-conjugation equivariance of the average) and the (7.2)/(7.3) norm
theory follow.
-/

namespace OddOrder.Peterfalvi.S07

open scoped BigOperators
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}

/-- `|G|` is invertible in `ℂ` (for the class-function inner product), since `G` is a finite group.
Scoped so it does not leak outside §7. -/
noncomputable scoped instance natCardInvCG [Finite G] : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- `|H|` is invertible in `ℂ` for any subgroup `H` of a finite group. -/
noncomputable scoped instance natCardInvC [Finite G] (H : Subgroup G) :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- **Peterfalvi (7.1)**, the value of the `ρ` projection at a support point `a ∈ A`:
`χ^ρ(a) = (1/|H(a)|) ∑_{x ∈ H(a)} χ(a·x)`, the average of `χ` over the coset `aH(a)`. -/
noncomputable def rhoValue (hyp : S04.Hypothesis G A L) (χ : ClassFunction G ℂ)
    (a : {a : G // a ∈ A}) : ℂ :=
  letI : Fintype (hyp.H a) := Fintype.ofFinite _
  (Nat.card (hyp.H a) : ℂ)⁻¹ * ∑ x : (hyp.H a), χ (a.1 * (x : G))

variable (hyp : S04.Hypothesis G A L)

@[simp] theorem rhoValue_zero (a : {a : G // a ∈ A}) : rhoValue hyp 0 a = 0 := by
  simp [rhoValue]

theorem rhoValue_add (χ ψ : ClassFunction G ℂ) (a : {a : G // a ∈ A}) :
    rhoValue hyp (χ + ψ) a = rhoValue hyp χ a + rhoValue hyp ψ a := by
  simp only [rhoValue, ClassFunction.add_apply, Finset.sum_add_distrib, mul_add]

theorem rhoValue_smul (c : ℂ) (χ : ClassFunction G ℂ) (a : {a : G // a ∈ A}) :
    rhoValue hyp (c • χ) a = c * rhoValue hyp χ a := by
  simp only [rhoValue, ClassFunction.smul_apply, Finset.mul_sum]
  ring

theorem rhoValue_sub (χ ψ : ClassFunction G ℂ) (a : {a : G // a ∈ A}) :
    rhoValue hyp (χ - ψ) a = rhoValue hyp χ a - rhoValue hyp ψ a := by
  simp only [rhoValue, ClassFunction.sub_apply, Finset.sum_sub_distrib, mul_sub]

/-- **Peterfalvi (7.1), `L`-conjugation invariance of the average.**  The value `χ^ρ(a)` is
invariant under conjugating the support point `a` by `ℓ ∈ L`: `χ^ρ(ℓ·a·ℓ⁻¹) = χ^ρ(a)`.  This is the
class-function (equivariance) property of `ρ` — the input needed to package `χ^ρ` as an element of
`CF(L, A)` — and rests on `(2.4.a)` (`HConjInvariant`, i.e. `H(ℓ·a·ℓ⁻¹) = ℓ·H(a)·ℓ⁻¹`) together with
`χ` being a class function on `G`.  Concretely, conjugation by `ℓ` is a bijection
`H(ℓ·a·ℓ⁻¹) ≃ H(a)`, `y ↦ ℓ⁻¹·y·ℓ`, under which the coset element `(ℓ·a·ℓ⁻¹)·y` is `G`-conjugate to
`a·(ℓ⁻¹·y·ℓ)`, so the two averages agree term by term. -/
theorem rhoValue_conjA (hconj : hyp.HConjInvariant) (χ : ClassFunction G ℂ)
    (l : L) (a : {a : G // a ∈ A}) :
    rhoValue hyp χ (hyp.conjA l a) = rhoValue hyp χ a := by
  letI iA : Fintype (hyp.H a) := Fintype.ofFinite _
  letI iB : Fintype (hyp.H (hyp.conjA l a)) := Fintype.ofFinite _
  -- conjugation by `ℓ⁻¹` is the bijection `H(ℓ·a·ℓ⁻¹) ≃ H(a)`
  let e : (hyp.H (hyp.conjA l a)) ≃ (hyp.H a) :=
    { toFun := fun y => ⟨(l : G)⁻¹ * (y : G) * (l : G),
        (hyp.mem_H_conjA_iff hconj a l).mp y.2⟩
      invFun := fun x => ⟨(l : G) * (x : G) * (l : G)⁻¹,
        (hyp.mem_H_conjA_iff hconj a l).mpr (by
          have hx : (l : G)⁻¹ * ((l : G) * (x : G) * (l : G)⁻¹) * (l : G) = (x : G) := by group
          rw [hx]; exact x.2)⟩
      left_inv := fun y => by
        apply Subtype.ext
        change (l : G) * ((l : G)⁻¹ * (y : G) * (l : G)) * (l : G)⁻¹ = (y : G); group
      right_inv := fun x => by
        apply Subtype.ext
        change (l : G)⁻¹ * ((l : G) * (x : G) * (l : G)⁻¹) * (l : G) = (x : G); group }
  -- rewrite both `rhoValue`s into their averaging form under the chosen `Fintype` instances
  have hB : rhoValue hyp χ (hyp.conjA l a)
      = (Nat.card (hyp.H (hyp.conjA l a)) : ℂ)⁻¹
          * ∑ y : (hyp.H (hyp.conjA l a)), χ ((hyp.conjA l a).1 * (y : G)) := rfl
  have hA : rhoValue hyp χ a
      = (Nat.card (hyp.H a) : ℂ)⁻¹ * ∑ x : (hyp.H a), χ (a.1 * (x : G)) := rfl
  rw [hA, hB, Nat.card_congr e]
  congr 1
  refine Fintype.sum_equiv e _ _ (fun y => ?_)
  change χ ((hyp.conjA l a).1 * (y : G)) = χ (a.1 * ((l : G)⁻¹ * (y : G) * (l : G)))
  rw [hyp.conjA_coe]
  exact χ.of_isConj (isConj_iff.mpr ⟨(l : G)⁻¹, by group⟩)

open Classical in
/-- **Peterfalvi (7.1), the `ρ` projection as a class function on `L`.**  Packages the averaged
value `χ^ρ` (`rhoValue`) into `CF(L)`: it takes the value `χ^ρ(a)` at support points `a ∈ A` and `0`
elsewhere.  Class-function (conjugation) invariance is `rhoValue_conjA` on `A`, and the
`L`-invariance of `A` (`L_normalizes_A`, applied to `ℓ` and to `ℓ⁻¹`) off `A`. -/
noncomputable def rhoClassFun (hconj : hyp.HConjInvariant) (χ : ClassFunction G ℂ) :
    ClassFunction L ℂ :=
  ⟨fun g => if hg : (g : G) ∈ A then rhoValue hyp χ ⟨(g : G), hg⟩ else 0, by
    intro g h
    dsimp only
    by_cases hg : (g : G) ∈ A
    · have hcm : ((h * g * h⁻¹ : L) : G) ∈ A := by
        have hmem := hyp.L_normalizes_A h hg
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem
      rw [dif_pos hcm, dif_pos hg]
      have hconjeq : (⟨((h * g * h⁻¹ : L) : G), hcm⟩ : {a : G // a ∈ A})
          = hyp.conjA h ⟨(g : G), hg⟩ := by
        apply Subtype.ext
        simp only [hyp.conjA_coe, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hconjeq]
      exact rhoValue_conjA hyp hconj χ h ⟨(g : G), hg⟩
    · have hcnm : ((h * g * h⁻¹ : L) : G) ∉ A := by
        intro hmem
        have hback := hyp.L_normalizes_A h⁻¹ hmem
        have heq : ((h⁻¹ : L) : G) * ((h * g * h⁻¹ : L) : G) * ((h⁻¹ : L) : G)⁻¹ = (g : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        rw [heq] at hback
        exact hg hback
      rw [dif_neg hcnm, dif_neg hg]⟩

open Classical in
@[simp] theorem rhoClassFun_apply_mem (hconj : hyp.HConjInvariant) (χ : ClassFunction G ℂ)
    {g : L} (hg : (g : G) ∈ A) :
    rhoClassFun hyp hconj χ g = rhoValue hyp χ ⟨(g : G), hg⟩ :=
  dif_pos hg

open Classical in
@[simp] theorem rhoClassFun_apply_not_mem (hconj : hyp.HConjInvariant) (χ : ClassFunction G ℂ)
    {g : L} (hg : (g : G) ∉ A) :
    rhoClassFun hyp hconj χ g = 0 :=
  dif_neg hg

/-- The `ρ` projection `χ^ρ` (as a class function on `L`) is supported on `A`. -/
theorem rhoClassFun_support_subset (hconj : hyp.HConjInvariant) (χ : ClassFunction G ℂ) :
    (rhoClassFun hyp hconj χ).support ⊆ S04.supportInSubgroup A L := by
  intro g hg
  rw [ClassFunction.mem_support] at hg
  rw [S04.mem_supportInSubgroup]
  by_contra hgA
  exact hg (rhoClassFun_apply_not_mem hyp hconj χ hgA)

/-- **Peterfalvi (7.1), the `ρ` projection `χ ↦ χ^ρ` as an element of `CF(L, A)`.** -/
noncomputable def rho (hconj : hyp.HConjInvariant) (χ : ClassFunction G ℂ) :
    S04.SupportedClassFunctions ℂ A L :=
  ⟨rhoClassFun hyp hconj χ,
    ClassFunction.mem_supportedSubmodule.mpr (rhoClassFun_support_subset hyp hconj χ)⟩

/-- Additivity of the `ρ` projection (class-function form). -/
theorem rhoClassFun_add (hconj : hyp.HConjInvariant) (χ ψ : ClassFunction G ℂ) :
    rhoClassFun hyp hconj (χ + ψ) = rhoClassFun hyp hconj χ + rhoClassFun hyp hconj ψ := by
  apply ClassFunction.ext
  intro g
  by_cases hg : (g : G) ∈ A
  · rw [ClassFunction.add_apply, rhoClassFun_apply_mem hyp hconj _ hg,
      rhoClassFun_apply_mem hyp hconj _ hg, rhoClassFun_apply_mem hyp hconj _ hg, rhoValue_add]
  · rw [ClassFunction.add_apply, rhoClassFun_apply_not_mem hyp hconj _ hg,
      rhoClassFun_apply_not_mem hyp hconj _ hg, rhoClassFun_apply_not_mem hyp hconj _ hg, add_zero]

/-- Homogeneity of the `ρ` projection (class-function form). -/
theorem rhoClassFun_smul (hconj : hyp.HConjInvariant) (c : ℂ) (χ : ClassFunction G ℂ) :
    rhoClassFun hyp hconj (c • χ) = c • rhoClassFun hyp hconj χ := by
  apply ClassFunction.ext
  intro g
  by_cases hg : (g : G) ∈ A
  · rw [ClassFunction.smul_apply, rhoClassFun_apply_mem hyp hconj _ hg,
      rhoClassFun_apply_mem hyp hconj _ hg, rhoValue_smul]
  · rw [ClassFunction.smul_apply, rhoClassFun_apply_not_mem hyp hconj _ hg,
      rhoClassFun_apply_not_mem hyp hconj _ hg, mul_zero]

/-- **Peterfalvi (7.2.a), pointwise**: for `α ∈ CF(L, A)` and `a ∈ A`, the `τρ`-roundtrip recovers
`α(a)`.  The Dade image `α^τ` is constant equal to `α(a)` on the coset `a·H(a)`
(`Hypothesis.dadeValue_eq`), so its `ρ`-average over `H(a)` is just `α(a)`. -/
theorem rhoValue_dadeMap (α : S04.SupportedClassFunctions ℂ A L) {a : G} (ha : a ∈ A) :
    rhoValue hyp (hyp.dadeMap α) ⟨a, ha⟩ = (α : ClassFunction L ℂ) ⟨a, hyp.mem_L ha⟩ := by
  letI : Fintype (hyp.H ⟨a, ha⟩) := Fintype.ofFinite _
  have hval : ∀ x : (hyp.H ⟨a, ha⟩),
      (hyp.dadeMap α) (a * (x : G)) = (α : ClassFunction L ℂ) ⟨a, hyp.mem_L ha⟩ := fun x => by
    rw [hyp.dadeMap_apply]
    exact hyp.dadeValue_eq α x.2 (IsConj.refl (a * (x : G)))
  have hcard : (Nat.card (hyp.H ⟨a, ha⟩) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hexp : rhoValue hyp (hyp.dadeMap α) ⟨a, ha⟩
      = (Nat.card (hyp.H ⟨a, ha⟩) : ℂ)⁻¹
          * ∑ x : (hyp.H ⟨a, ha⟩), (hyp.dadeMap α) (a * (x : G)) := rfl
  rw [hexp]
  simp_rw [hval]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
    inv_mul_cancel_left₀ hcard]

/-- **Peterfalvi (7.2.a), class-function form**: `α^{τρ} = α` (as a class function on `L`). -/
theorem rhoClassFun_dadeMap (hconj : hyp.HConjInvariant) (α : S04.SupportedClassFunctions ℂ A L) :
    rhoClassFun hyp hconj (hyp.dadeMap α) = (α : ClassFunction L ℂ) := by
  apply ClassFunction.ext
  intro g
  by_cases hg : (g : G) ∈ A
  · rw [rhoClassFun_apply_mem hyp hconj _ hg, rhoValue_dadeMap hyp α hg]
  · rw [rhoClassFun_apply_not_mem hyp hconj _ hg]
    symm
    by_contra hne
    exact hg (S04.mem_supportInSubgroup.mp
      ((ClassFunction.mem_supportedSubmodule.mp α.property) (ClassFunction.mem_support.mpr hne)))

/-- **Peterfalvi (7.2.a)**: `α^{τρ} = α` for `α ∈ CF(L, A)` — the `ρ` projection is a left inverse
of the Dade isometry `τ` on `CF(L, A)`. -/
theorem rho_dadeMap (hconj : hyp.HConjInvariant) (α : S04.SupportedClassFunctions ℂ A L) :
    rho hyp hconj (hyp.dadeMap α) = α :=
  Subtype.ext (rhoClassFun_dadeMap hyp hconj α)

/-- The `ρ`-value (`rhoValue`) agrees with S04's Peterfalvi (2.7) `adjointAverageFun`, bridging the
two `Fintype` conventions for the average over `H(a)`. -/
theorem rhoValue_eq_adjointAverageFun (χ : ClassFunction G ℂ) {a : G} (ha : a ∈ A) :
    rhoValue hyp χ ⟨a, ha⟩ = S04.adjointAverageFun hyp χ ⟨a, hyp.mem_L ha⟩ := by
  classical
  letI : Fintype (hyp.H ⟨a, ha⟩) := Fintype.ofFinite _
  have h1 : rhoValue hyp χ ⟨a, ha⟩
      = (Nat.card (hyp.H ⟨a, ha⟩) : ℂ)⁻¹ * ∑ x : (hyp.H ⟨a, ha⟩), χ (a * (x : G)) := rfl
  have h2 : S04.adjointAverageFun hyp χ ⟨a, hyp.mem_L ha⟩
      = (Nat.card (hyp.H ⟨a, ha⟩) : ℂ)⁻¹ * ∑ x : (hyp.H ⟨a, ha⟩), χ (a * (x : G)) := by
    simp only [S04.adjointAverageFun]
    rw [dif_pos ha]
    congr 1
    refine Finset.sum_congr (Finset.ext fun x => ?_) (fun _ _ => rfl)
    simp only [Finset.mem_univ]
  rw [h1, h2]

variable [Fintype ↥L]

/-- **Peterfalvi (2.7), adjunction for `ρ`**: `⟨α^τ, χ⟩_G = ⟨α, χ^ρ⟩_L` — the Dade isometry `τ` and
the `ρ` projection are adjoint.  Cites S04's `adjoint_formula` with `ψ = χ^ρ` (`rhoClassFun`), whose
averaging hypothesis is `rhoValue_eq_adjointAverageFun`. -/
theorem rho_adjoint (hconj : hyp.HConjInvariant)
    (α : S04.SupportedClassFunctions ℂ A L) (χ : ClassFunction G ℂ) :
    ClassFunction.inner (hyp.dadeMap α) χ
      = ClassFunction.inner (α : ClassFunction L ℂ) (rhoClassFun hyp hconj χ) :=
  S04.adjoint_formula hyp hyp.dadeMap hyp.isDadeMap_dadeMap hconj α χ (rhoClassFun hyp hconj χ)
    (fun a => by
      rw [rhoClassFun_apply_mem hyp hconj χ a.2]
      exact rhoValue_eq_adjointAverageFun hyp χ a.2)

end OddOrder.Peterfalvi.S07
