/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Clifford

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

end OddOrder.RepresentationTheory
