/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Clifford
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter

/-!
# Pointwise product of class functions; products of characters

This leaf equips `ClassFunction G k` with the **pointwise product** `φ * ψ` (conjugation-invariant
because each factor is), and proves:

* `IsCharacter.mul` — the product of two genuine characters is again a character, via the tensor
  product of representations (`Representation.tprod`, `Representation.char_tensor`);
* `mul_mem_ZIrr` — `ZIrr G` is closed under products (it is a subring of the pointwise ring of
  class functions), by bilinear reduction to the base case of two irreducible characters.

The immediate consumer is **Gallagher's theorem** (Isaacs 6.17): for `χ ∈ Irr(I)` extending
`θ ∈ Irr(H)` and a linear character `Inf(β)` of `I` (`β ∈ Irr(I/H)`, `I/H` abelian), the product
`χ · Inf(β)` is again a character — of squared norm one, since twisting by a linear character
preserves the norm — hence irreducible.  This feeds the constructive-Clifford decomposition of
`Ind_H^L θ` (Peterfalvi (1.7), the general type-I `typeI_induced_char_constituents`).
-/

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

/-- **Pointwise product** of class functions.  The product `g ↦ φ g * ψ g` is again constant on
conjugacy classes because each factor is (`ClassFunction.conj_eq`). -/
instance instMul : Mul (ClassFunction G k) where
  mul φ ψ := ⟨fun g => φ g * ψ g, fun g h => by
    simp only [φ.conj_eq, ψ.conj_eq]⟩

@[simp] theorem mul_apply (φ ψ : ClassFunction G k) (g : G) : (φ * ψ) g = φ g * ψ g := rfl

/-- Restriction to a subgroup is multiplicative for the pointwise product. -/
@[simp] theorem restrict_mul (H : Subgroup G) (φ ψ : ClassFunction G k) :
    restrict H (φ * ψ) = restrict H φ * restrict H ψ := by
  ext h; simp

/-- Pullback along a group homomorphism is multiplicative for the pointwise product. -/
@[simp] theorem compHom_mul {K : Type*} [Group K] (f : K →* G) (φ ψ : ClassFunction G k) :
    compHom f (φ * ψ) = compHom f φ * compHom f ψ := by
  ext x; simp

/-- **Twisting by a factor that is `1` on `H` does not change the restriction to `H`.**  If
`lam x = 1` for every `x ∈ H`, then `Res_H (χ · lam) = Res_H χ`.  In Gallagher's theorem `lam =
Inf(β)` is inflated from `I/H`, hence `1` on `H`, so `χ · Inf(β)` restricts to `Res_H χ = θ` — i.e.
it lies over `θ` — and `⟨Ind_H^I θ, χ·Inf(β)⟩ = ⟨θ, Res_H(χ·Inf β)⟩ = ⟨θ, θ⟩ = 1`. -/
theorem restrict_mul_of_apply_eq_one {H : Subgroup G} (χ lam : ClassFunction G k)
    (hlam : ∀ x : ↥H, lam (x : G) = 1) :
    restrict H (χ * lam) = restrict H χ := by
  ext h
  simp only [restrict_apply, mul_apply, hlam, mul_one]

end ClassFunction

variable {G : Type*} [Group G]

/-- **The product of two characters is a character.**  If `φ = χ_ρ` and `ψ = χ_σ` are the characters
of finite-dimensional representations `ρ, σ`, then `φ · ψ` is the character of the tensor-product
representation `ρ ⊗ σ` (`Representation.char_tensor`), hence a genuine character.  This is the
character-level form of "`Irr` is closed under tensor products", and the engine behind Gallagher. -/
theorem IsCharacter.mul {φ ψ : ClassFunction G ℂ} (hφ : IsCharacter φ) (hψ : IsCharacter ψ) :
    IsCharacter (φ * ψ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  obtain ⟨W, _, _, _, σ, hσ⟩ := hψ
  refine ⟨TensorProduct ℂ V W, inferInstance, inferInstance, inferInstance,
    Representation.tprod ρ σ, ?_⟩
  funext g
  rw [ClassFunction.mul_apply, Representation.char_tensor, Pi.mul_apply, congrFun hρ g,
    congrFun hσ g]

/-- **`ZIrr G` is closed under products** — it is a subring of the pointwise class-function ring.
Bilinear reduction (`Submodule.span_induction` in each factor) to the base case of two irreducible
characters, whose product is a genuine character (`IsCharacter.mul`) and hence lies in `ZIrr`
(`IsCharacter.mem_ZIrr`). -/
theorem mul_mem_ZIrr [Finite G] {φ ψ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hψ : ψ ∈ ZIrr G) : φ * ψ ∈ ZIrr G := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    induction hψ using Submodule.span_induction with
    | mem y hy =>
      exact (((mem_irreducibleCharacters.mp hx).isCharacter).mul
        ((mem_irreducibleCharacters.mp hy).isCharacter)).mem_ZIrr
    | zero =>
      have hz : x * (0 : ClassFunction G ℂ) = 0 := by ext g; simp
      rw [hz]; exact Submodule.zero_mem _
    | add a b _ _ iha ihb =>
      have hd : x * (a + b) = x * a + x * b := by ext g; simp [mul_add]
      rw [hd]; exact Submodule.add_mem _ iha ihb
    | smul c a _ ih =>
      have hs : x * (c • a) = c • (x * a) := by
        ext g
        rw [← Int.cast_smul_eq_zsmul ℂ c a, ← Int.cast_smul_eq_zsmul ℂ c (x * a)]
        simp only [ClassFunction.mul_apply, ClassFunction.smul_apply]; ring
      rw [hs]; exact Submodule.smul_mem _ c ih
  | zero =>
    have hz : (0 : ClassFunction G ℂ) * ψ = 0 := by ext g; simp
    rw [hz]; exact Submodule.zero_mem _
  | add a b _ _ iha ihb =>
    have hd : (a + b) * ψ = a * ψ + b * ψ := by ext g; simp [add_mul]
    rw [hd]; exact Submodule.add_mem _ iha ihb
  | smul c a _ ih =>
    have hs : (c • a) * ψ = c • (a * ψ) := by
      ext g
      rw [← Int.cast_smul_eq_zsmul ℂ c a, ← Int.cast_smul_eq_zsmul ℂ c (a * ψ)]
      simp only [ClassFunction.mul_apply, ClassFunction.smul_apply]; ring
    rw [hs]; exact Submodule.smul_mem _ c ih

/-- **Twisting by a unit-norm class function preserves the inner product.**  If `lam` has unit norm
at every element (`lam g · conj (lam g) = 1` — e.g. a linear character, whose values are roots of
unity), then `⟨χ · lam, χ · lam⟩ = ⟨χ, χ⟩` for every class function `χ`.  Pointwise,
`(χ·lam)(g) · conj((χ·lam)(g)) = χ(g)·conj(χ(g)) · (lam g · conj (lam g)) = χ(g)·conj(χ(g))`.

This is the norm-preservation behind Gallagher's theorem: `χ · Inf(β)` has the same norm as `χ`, so
an irreducible `χ` twisted by a linear character `Inf(β)` stays of norm one — hence irreducible. -/
theorem inner_mul_self_eq_of_star_mul_self_eq_one {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (χ : ClassFunction G ℂ) {lam : ClassFunction G ℂ}
    (hlam : ∀ g, lam g * star (lam g) = 1) :
    ClassFunction.inner (χ * lam) (χ * lam) = ClassFunction.inner χ χ := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum]
  congr 1
  unfold ClassFunction.innerSum
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [ClassFunction.mul_apply, star_mul']
  rw [show χ g * lam g * (star (χ g) * star (lam g))
        = χ g * star (χ g) * (lam g * star (lam g)) from by ring, hlam g, mul_one]

/-- **An irreducible character has squared norm one** (`⟨χ, χ⟩ = 1`), `Prop`-level restatement of the
orthonormality `irreducibleCharacter_inner_eq_ite` for the bundled `⟨χ, hχ⟩ : IrreducibleCharacter G`. -/
theorem IsIrreducibleCharacter.inner_self_eq_one {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) :
    ClassFunction.inner χ χ = 1 := by
  simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hχ⟩ : IrreducibleCharacter G) ⟨χ, hχ⟩

/-- **An irreducible character has a positive natural degree** (`χ(1) = d`, `0 < d`), `Prop`-level
restatement of `irreducibleCharacter_apply_one_eq_pos_natCast` for the bundled `⟨χ, hχ⟩`. -/
theorem IsIrreducibleCharacter.exists_apply_one_eq_pos_natCast {G : Type*} [Group G] [Finite G]
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) :
    ∃ d : ℕ, 0 < d ∧ (χ : G → ℂ) 1 = (d : ℂ) := by
  obtain ⟨d, hd, h1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hχ⟩ : IrreducibleCharacter G)
  exact ⟨d, hd, by simpa using h1⟩

/-- **Twisting an irreducible character by a unit-norm degree-one character preserves
irreducibility.**  If `χ ∈ Irr G` and `lam` is a genuine character with unit norm everywhere
(`lam g · conj (lam g) = 1`) and degree one (`lam 1 = 1`) — e.g. a linear character — then
`χ · lam ∈ Irr G`.  Indeed `χ · lam` is a virtual character (`IsCharacter.mul` + `mem_ZIrr`) of
squared norm `⟨χ · lam, χ · lam⟩ = ⟨χ, χ⟩ = 1` (`inner_mul_self_eq_of_star_mul_self_eq_one` +
`inner_self_eq_one`) and positive degree `(χ · lam)(1) = χ(1) · 1 = χ(1) > 0`; so it is irreducible
(`isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos`).  This is the irreducibility engine of
Gallagher's theorem: `χ · Inf(β)` (with `Inf(β)` a linear character) is irreducible. -/
theorem isIrreducibleCharacter_mul_of_unit_norm {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ lam : ClassFunction G ℂ}
    (hχ : IsIrreducibleCharacter χ) (hlamC : IsCharacter lam)
    (hlamU : ∀ g, lam g * star (lam g) = 1) (hlam1 : (lam : G → ℂ) 1 = 1) :
    IsIrreducibleCharacter (χ * lam) := by
  have hzirr : (χ * lam) ∈ ZIrr G := (hχ.isCharacter.mul hlamC).mem_ZIrr
  have hnorm : ClassFunction.inner (χ * lam) (χ * lam) = 1 := by
    rw [inner_mul_self_eq_of_star_mul_self_eq_one χ hlamU, hχ.inner_self_eq_one]
  have hpos : ∃ d : ℕ, 0 < d ∧ (χ * lam) 1 = (d : ℂ) := by
    obtain ⟨d, hd, h1⟩ := hχ.exists_apply_one_eq_pos_natCast
    refine ⟨d, hd, ?_⟩
    simp only [ClassFunction.mul_apply, hlam1, mul_one, h1]
  exact isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos hzirr hnorm hpos

/-- **A linear character has unit norm at every element.**  For `χ : H →* ℂˣ` on a *finite* group,
the value `(χ h : ℂ)` is a root of unity — `(χ h)^{|H|} = χ(h^{|H|}) = χ(1) = 1` (`pow_card_eq_one'`) —
so `‖χ h‖ = 1` (`Complex.norm_eq_one_of_pow_eq_one`), whence `star (χ h) = (χ h)⁻¹`
(`RCLike.inv_eq_conj`) and `(χ h) · star (χ h) = 1`.  This supplies the unit-norm hypothesis of
`isIrreducibleCharacter_mul_of_unit_norm`, so twisting an irreducible character by the linear
character `linearClassFunction χ` (e.g. `Inf(β)` in Gallagher's theorem) preserves irreducibility. -/
theorem linearClassFunction_mul_star_self_eq_one {H : Type*} [Group H] [Finite H]
    (χ : H →* ℂˣ) (h : H) :
    (linearClassFunction χ) h * star ((linearClassFunction χ) h) = 1 := by
  have hpow : (χ h : ℂ) ^ (Nat.card H) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have hnorm : ‖(χ h : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow Nat.card_pos.ne'
  have hstar : star (χ h : ℂ) = (χ h : ℂ)⁻¹ := by
    rw [RCLike.inv_eq_conj hnorm, starRingEnd_apply]
  rw [linearClassFunction_apply, hstar]
  exact mul_inv_cancel₀ (Units.ne_zero (χ h))

/-- **Twisting an irreducible character by a linear character preserves irreducibility.**
Specialization of `isIrreducibleCharacter_mul_of_unit_norm` to `lam = linearClassFunction χlin`
(`χlin : G →* ℂˣ`): the linear character is a genuine character of unit norm
(`linearClassFunction_mul_star_self_eq_one`) and degree one, so `χ · linearClassFunction χlin ∈
Irr G` whenever `χ ∈ Irr G`.  This is the form used in Gallagher's theorem (`χlin = Inf(β)`). -/
theorem isIrreducibleCharacter_mul_linearClassFunction {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ)
    (χlin : G →* ℂˣ) :
    IsIrreducibleCharacter (χ * linearClassFunction χlin) := by
  have hlirr : IsIrreducibleCharacter (linearClassFunction χlin) := by
    have h := (linearIrreducibleCharacter χlin).isIrreducible
    rwa [linearIrreducibleCharacter_coe] at h
  refine isIrreducibleCharacter_mul_of_unit_norm hχ hlirr.isCharacter
    (linearClassFunction_mul_star_self_eq_one χlin) ?_
  simp

/-- **An inflated linear character is `1` on the normal subgroup.**  For `χbar : (G ⧸ H) →* ℂˣ`,
the linear character `Inf(χbar) = linearClassFunction (χbar ∘ mk' H)` of `G` takes the value `1` at
every `x ∈ H` (the quotient map kills `H`).  Combined with `ClassFunction.restrict_mul_of_apply_eq_one`
this gives `Res_H (χ · Inf(χbar)) = Res_H χ`: the Gallagher twist `χ · Inf(β)` lies over the same
character of `H` as `χ`. -/
theorem linearClassFunction_comp_mk'_apply_eq_one {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    (χbar : (G ⧸ H) →* ℂˣ) {x : G} (hx : x ∈ H) :
    (linearClassFunction (χbar.comp (QuotientGroup.mk' H))) x = 1 := by
  rw [linearClassFunction_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff x).mpr hx, map_one, Units.val_one]

end OddOrder.RepresentationTheory
