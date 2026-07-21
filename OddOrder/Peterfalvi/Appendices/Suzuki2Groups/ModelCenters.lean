/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types
import OddOrder.Higman.Suzuki2Groups.HigmanTypesCD

/-!
# Centers of the type-B/C/D models have exponent two

G. Higman, *Suzuki 2-groups*, pp. 90--92; T. Peterfalvi, Appendix III.

The center of a quadratic central extension is cut out by the radical of the
polarization: an element is central iff its quotient coordinate pairs
trivially with everything.  For each of the three model quadratic maps the
polarization has trivial radical (Dedekind's independence of automorphisms
supplies the type-D case), so central elements have vanishing quotient
coordinate, and every element of the kernel copy has order at most two.

Transported through `equivModel`, any group of type B, C, or D has a center
of exponent two — the fact behind "`Z(Q) = Q₀`" in Peterfalvi's Lemma I.3.5.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.Higman.Suzuki2Groups (typeCQuadraticMap typeDQuadraticMap
  typeCQuadraticMap_apply typeDQuadraticMap_apply TypeCModel TypeDModel
  TypeCData TypeDData)
open LinearMap (BilinMap)
open Module

noncomputable section

universe uP uF uV uW uI

/-! ## Dedekind's independence of automorphisms, two and three terms -/

/-- **Two-term Dedekind**: if `a·σ(x) + c·x = 0` for all `x` and `σ ≠ 1`,
then `a = c = 0`. -/
theorem eq_zero_of_ringAut_comb_two {F : Type uF} [Field F]
    (σ : RingAut F) (hσ : σ ≠ 1) (a c : F)
    (h : ∀ x : F, a * σ x + c * x = 0) : a = 0 ∧ c = 0 := by
  obtain ⟨x0, hx0⟩ : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    exact hσ (RingEquiv.ext hall)
  have h1 := h 1
  rw [map_one, mul_one, mul_one] at h1
  have hc : c = -a := by linear_combination h1
  have hprod : a * (σ x0 - x0) = 0 := by linear_combination h x0 - x0 * hc
  have ha : a = 0 := by
    rcases mul_eq_zero.mp hprod with ha | hd
    · exact ha
    · exact absurd (sub_eq_zero.mp hd) hx0
  exact ⟨ha, by rw [hc, ha, neg_zero]⟩

/-- **Three-term Dedekind**: if `a·σ(x) + b·τ(x) + c·x = 0` for all `x` with
`σ`, `τ`, `1` pairwise distinct, then `a = b = c = 0`. -/
theorem eq_zero_of_ringAut_comb_three {F : Type uF} [Field F]
    (σ τ : RingAut F) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hστ : σ ≠ τ) (a b c : F)
    (h : ∀ x : F, a * σ x + b * τ x + c * x = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have key : ∀ y x : F, a * (σ y - τ y) * σ x + c * (y - τ y) * x = 0 := by
    intro y x
    have h1 := h (x * y)
    rw [map_mul, map_mul] at h1
    linear_combination h1 - τ y * h x
  have ha : a = 0 := by
    obtain ⟨y0, hy0⟩ : ∃ y, σ y ≠ τ y := by
      by_contra hall
      push_neg at hall
      exact hστ (RingEquiv.ext hall)
    obtain ⟨hA, -⟩ := eq_zero_of_ringAut_comb_two σ hσ1 _ _ (key y0)
    rcases mul_eq_zero.mp hA with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') hy0
  have hc : c = 0 := by
    obtain ⟨y1, hy1⟩ : ∃ y, τ y ≠ y := by
      by_contra hall
      push_neg at hall
      exact hτ1 (RingEquiv.ext hall)
    obtain ⟨-, hC⟩ := eq_zero_of_ringAut_comb_two σ hσ1 _ _ (key y1)
    rcases mul_eq_zero.mp hC with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h').symm hy1
  have hb : b = 0 := by
    have h1 := h 1
    rw [ha, hc] at h1
    simpa using h1
  exact ⟨ha, hb, hc⟩

/-! ## The center of a twisted product -/

namespace BilinearTwistedProduct

variable {R : Type uF} {V : Type uV} {W : Type uW}
  [CommRing R] [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W] {B : BilinMap R V W}

/-- An element of the twisted product is central iff its quotient coordinate
pairs symmetrically with every vector. -/
theorem mem_center_iff (x : BilinearTwistedProduct B) :
    x ∈ Subgroup.center (BilinearTwistedProduct B) ↔
      ∀ v : V, B v x.quotient = B x.quotient v := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h v
    have h1 := congrArg BilinearTwistedProduct.central
      (h ⟨v, 0⟩)
    simp only [central_mul] at h1
    -- `B v x.q + 0 + x.c = B x.q v + x.c + 0`
    have : B v x.quotient + x.central = B x.quotient v + x.central := by
      calc B v x.quotient + x.central
          = B v x.quotient + 0 + x.central := by rw [add_zero]
        _ = B x.quotient v + x.central + 0 := h1
        _ = B x.quotient v + x.central := by rw [add_zero]
    exact add_right_cancel this
  · intro h g
    ext
    · exact add_comm _ _
    · show B g.quotient x.quotient + g.central + x.central =
        B x.quotient g.quotient + x.central + g.central
      rw [h g.quotient]
      abel

end BilinearTwistedProduct

namespace QuadraticExtension

open BilinearTwistedProduct

variable {V : Type uV} {W : Type uW} {ι : Type uI} [LinearOrder ι]
  [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]

private theorem add_self_zmodTwo (w : W) : w + w = 0 := by
  calc w + w = 2 • w := (two_nsmul w).symm
    _ = (2 : ZMod 2) • w := (Nat.cast_smul_eq_nsmul (ZMod 2) 2 w).symm
    _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- **Central elements square to one when the polarization has trivial
radical.**  A central element's quotient coordinate is additive for `q`,
hence vanishes; the remaining kernel coordinate is `2`-torsion. -/
theorem sq_eq_one_of_mem_center
    (q : QuadraticMap (ZMod 2) V W) (basis : Basis ι (ZMod 2) V)
    (hrad : ∀ v : V, (∀ v' : V, q (v + v') = q v + q v') → v = 0)
    (z : QuadraticExtension q basis)
    (hz : z ∈ Subgroup.center (QuadraticExtension q basis)) :
    z ^ 2 = 1 := by
  have hcomm : ∀ v : V,
      q.toBilin basis v z.quotient = q.toBilin basis z.quotient v :=
    (BilinearTwistedProduct.mem_center_iff z).mp hz
  have hq0 : z.quotient = 0 := by
    refine hrad _ fun v' => ?_
    have hexp : q (z.quotient + v') =
        q z.quotient + q v' +
          (q.toBilin basis z.quotient v' + q.toBilin basis v' z.quotient) := by
      rw [← toBilin_self q basis (z.quotient + v'),
        ← toBilin_self q basis z.quotient, ← toBilin_self q basis v']
      simp only [map_add, LinearMap.add_apply]
      abel
    rw [hexp, hcomm v', add_self_zmodTwo, add_zero]
  rw [sq_eq_inl_q, hq0, QuadraticMap.map_zero]
  exact map_one _

end QuadraticExtension

/-! ## Trivial radical of the three model polarizations -/

section Radicals

variable {F : Type uF} [Field F]

/-- **Trivial radical of the type-B polarization.** -/
theorem typeBQuadraticMap_radical_eq_zero [CharP F 2]
    (phi : RingAut F) (epsilon : F) (hε : epsilon ≠ 0) (w : F × F)
    (hadd : ∀ v : F × F, typeBQuadraticMap phi epsilon (w + v) =
      typeBQuadraticMap phi epsilon w + typeBQuadraticMap phi epsilon v) :
    w = 0 := by
  obtain ⟨α, β⟩ := w
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have eq1 : ∀ γ : F,
      α * phi γ + γ * phi α + epsilon * (γ * phi β) = 0 := by
    intro γ
    have h := hadd (γ, 0)
    simp only [Prod.mk_add_mk, typeBQuadraticMap_apply, map_add, map_zero,
      add_zero, zero_add, zero_mul, mul_zero] at h
    linear_combination h
  have eq2 : ∀ δ : F,
      epsilon * (α * phi δ) + β * phi δ + δ * phi β = 0 := by
    intro δ
    have h := hadd (0, δ)
    simp only [Prod.mk_add_mk, typeBQuadraticMap_apply, map_add, map_zero,
      add_zero, zero_add, zero_mul, mul_zero] at h
    linear_combination h
  have eq2one := eq2 1
  rw [map_one, mul_one, mul_one, one_mul] at eq2one
  have hphiβ : phi β = epsilon * α + β := by
    linear_combination eq2one - (epsilon * α + β) * h2
  by_cases hθ : phi = 1
  · have hεα : epsilon * α = 0 := by
      rw [hθ, RingAut.one_apply] at hphiβ
      linear_combination -hphiβ
    have hα : α = 0 := (mul_eq_zero.mp hεα).resolve_left hε
    have h1 := eq1 1
    rw [hθ, hα] at h1
    simp only [RingAut.one_apply, map_one, zero_mul, one_mul, mul_one,
      zero_add, add_zero] at h1
    have hβ : β = 0 := (mul_eq_zero.mp h1).resolve_left hε
    rw [hα, hβ]
    rfl
  · have hc : epsilon * α + β = 0 := by
      by_contra hcne
      apply hθ
      refine RingEquiv.ext fun δ => ?_
      rw [RingAut.one_apply]
      have h := eq2 δ
      rw [hphiβ] at h
      have hprod : (epsilon * α + β) * (phi δ + δ) = 0 := by
        linear_combination h
      have hzero : phi δ + δ = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hcne
      linear_combination hzero - δ * h2
    have hβ : β = 0 := by
      have hphiβ0 : phi β = 0 := by rw [hphiβ, hc]
      exact phi.injective (hphiβ0.trans (map_zero phi).symm)
    have hα : α = 0 := by
      have hεα : epsilon * α = 0 := by
        have := hc
        rwa [hβ, add_zero] at this
      exact (mul_eq_zero.mp hεα).resolve_left hε
    rw [hα, hβ]
    rfl

/-- **Trivial radical of the type-C polarization.** -/
theorem typeCQuadraticMap_radical_eq_zero [Finite F] [CharP F 2]
    (theta : RingAut F) (epsilon : F) (hε : epsilon ≠ 0) (w : F × F)
    (hadd : ∀ v : F × F, typeCQuadraticMap theta epsilon (w + v) =
      typeCQuadraticMap theta epsilon w + typeCQuadraticMap theta epsilon v) :
    w = 0 := by
  obtain ⟨α, β⟩ := w
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have eq2 : ∀ δ : F,
      epsilon * ((frobeniusEquiv F 2)⁻¹ α *
        (frobeniusEquiv F 2 * theta) δ) + β * δ + δ * β = 0 := by
    intro δ
    have h := hadd (0, δ)
    simp only [Prod.mk_add_mk, typeCQuadraticMap_apply, map_add, map_zero,
      add_zero, zero_add, zero_mul, mul_zero] at h
    linear_combination h
  have hα : α = 0 := by
    have h := eq2 1
    rw [map_one, mul_one] at h
    have hεα : epsilon * (frobeniusEquiv F 2)⁻¹ α = 0 := by
      linear_combination h - β * h2
    have hinvα : (frobeniusEquiv F 2)⁻¹ α = 0 :=
      (mul_eq_zero.mp hεα).resolve_left hε
    exact ((frobeniusEquiv F 2)⁻¹).injective
      (hinvα.trans (map_zero _).symm)
  have hβ : β = 0 := by
    have eq1 : ∀ γ : F,
        α * theta γ + γ * theta α + epsilon *
          ((frobeniusEquiv F 2)⁻¹ γ *
            (frobeniusEquiv F 2 * theta) β) = 0 := by
      intro γ
      have h := hadd (γ, 0)
      simp only [Prod.mk_add_mk, typeCQuadraticMap_apply, map_add, map_zero,
        add_zero, zero_add, zero_mul, mul_zero] at h
      linear_combination h
    have h := eq1 1
    rw [hα] at h
    simp only [map_zero, map_one, zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero] at h
    have hεβ : epsilon * (frobeniusEquiv F 2 * theta) β = 0 := h
    have hmulβ : (frobeniusEquiv F 2 * theta) β = 0 :=
      (mul_eq_zero.mp hεβ).resolve_left hε
    exact (frobeniusEquiv F 2 * theta).injective
      (hmulβ.trans (map_zero _).symm)
  rw [hα, hβ]
  rfl

/-- **Trivial radical of the type-D polarization** (three-term Dedekind). -/
theorem typeDQuadraticMap_radical_eq_zero [CharP F 2]
    (theta : RingAut F) (theta_pow_five : theta ^ 5 = 1)
    (theta_ne_one : theta ≠ 1)
    (epsilon : F) (hε : epsilon ≠ 0) (w : F × F)
    (hadd : ∀ v : F × F, typeDQuadraticMap theta epsilon (w + v) =
      typeDQuadraticMap theta epsilon w + typeDQuadraticMap theta epsilon v) :
    w = 0 := by
  obtain ⟨α, β⟩ := w
  have hτ1 : theta ^ 2 ≠ 1 := by
    intro h
    apply theta_ne_one
    have h4 : theta ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
    have h5 : theta ^ 5 = theta := by
      rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, h4, one_mul]
    rw [← h5, theta_pow_five]
  have hστ : theta ≠ theta ^ 2 := by
    intro h
    apply theta_ne_one
    have : theta * 1 = theta * theta := by
      rw [mul_one, ← pow_two, ← h]
    exact (mul_left_cancel this).symm
  have eq2 : ∀ δ : F,
      epsilon * (theta ^ 3) α * theta δ + β * (theta ^ 2) δ +
        (theta ^ 2) β * δ = 0 := by
    intro δ
    have h := hadd (0, δ)
    simp only [Prod.mk_add_mk, typeDQuadraticMap_apply, map_add, map_zero,
      add_zero, zero_add, zero_mul, mul_zero] at h
    linear_combination h
  obtain ⟨ha, hb, -⟩ :=
    eq_zero_of_ringAut_comb_three theta (theta ^ 2) theta_ne_one hτ1 hστ
      (epsilon * (theta ^ 3) α) β ((theta ^ 2) β) eq2
  have hα : α = 0 := by
    have h3α : (theta ^ 3) α = 0 :=
      (mul_eq_zero.mp ha).resolve_left hε
    exact (theta ^ 3).injective (h3α.trans (map_zero _).symm)
  rw [hα, hb]
  rfl

end Radicals

/-! ## Transport to groups of type B, C, D -/

/-- A `MulEquiv` maps central elements to central elements. -/
private theorem mem_center_map {G : Type uV} {H : Type uW}
    [Group G] [Group H] (e : G ≃* H) {z : G}
    (hz : z ∈ Subgroup.center G) : e z ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro h
  calc h * e z = e (e.symm h) * e z := by rw [e.apply_symm_apply]
    _ = e (e.symm h * z) := (map_mul e _ _).symm
    _ = e (z * e.symm h) := by rw [hz]
    _ = e z * h := by rw [map_mul, e.apply_symm_apply]

/-- **The center of a type-B group has exponent two.** -/
theorem TypeBData.sq_eq_one_of_mem_center {P : Type uP} [Group P]
    (data : TypeBData.{uP, uF} P) {z : P}
    (hz : z ∈ Subgroup.center P) : z ^ 2 = 1 := by
  letI := data.fieldF
  letI := data.finiteF
  letI := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  have hsq : data.equivModel z ^ 2 = 1 :=
    QuadraticExtension.sq_eq_one_of_mem_center _ _
      (typeBQuadraticMap_radical_eq_zero data.phi (data.epsilon : data.F)
        data.epsilon.ne_zero)
      (data.equivModel z) (mem_center_map data.equivModel hz)
  apply data.equivModel.injective
  rw [map_pow, hsq, map_one]

/-- **The center of a type-C group has exponent two.** -/
theorem TypeCData.sq_eq_one_of_mem_center {P : Type uP} [Group P]
    (data : TypeCData.{uP, uF} P) {z : P}
    (hz : z ∈ Subgroup.center P) : z ^ 2 = 1 := by
  letI := data.fieldF
  letI := data.finiteF
  letI := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  have hsq : data.equivModel z ^ 2 = 1 :=
    QuadraticExtension.sq_eq_one_of_mem_center _ _
      (typeCQuadraticMap_radical_eq_zero data.theta (data.epsilon : data.F)
        data.epsilon.ne_zero)
      (data.equivModel z) (mem_center_map data.equivModel hz)
  apply data.equivModel.injective
  rw [map_pow, hsq, map_one]

/-- **The center of a type-D group has exponent two.** -/
theorem TypeDData.sq_eq_one_of_mem_center {P : Type uP} [Group P]
    (data : TypeDData.{uP, uF} P) {z : P}
    (hz : z ∈ Subgroup.center P) : z ^ 2 = 1 := by
  letI := data.fieldF
  letI := data.finiteF
  letI := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  have hsq : data.equivModel z ^ 2 = 1 :=
    QuadraticExtension.sq_eq_one_of_mem_center _ _
      (typeDQuadraticMap_radical_eq_zero data.theta data.theta_pow_five
        data.theta_ne_one (data.epsilon : data.F) data.epsilon.ne_zero)
      (data.equivModel z) (mem_center_map data.equivModel hz)
  apply data.equivModel.injective
  rw [map_pow, hsq, map_one]

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
