/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.RepresentationDeterminant
import OddOrder.GroupTheory.RepresentationTheory.CyclicCharacterExtension
import OddOrder.GroupTheory.RepresentationTheory.ExtensionLinearTwist

/-!
# The canonical extension along a prime-cyclic quotient (toward Isaacs 6.28)

**Isaacs, _Character Theory of Finite Groups_, Theorem 6.25/Corollary 6.28 (prime-cyclic
step)**: let `N ⊴ N'` with `[N' : N] = p` prime, and let `φ ∈ Irr(N)` be `N'`-invariant with
`gcd(p, o(φ)·φ(1)) = 1`, where `o(φ)` is the order of the determinantal character.  Then
`φ` has a **unique** extension `χ ∈ Irr(N')` with `p ∤ o(χ)` — the *canonical* extension.
Uniqueness makes the canonical extension conjugation-equivariant, which propagates
invariance through the composition-series iterate for an abelian coprime quotient
(Isaacs 8.16; issue 9002 (v-c)/(v-d)).

This file assembles the determinantal bookkeeping on top of

* `CyclicCharacterExtension` — existence of *some* extension (Isaacs 11.22),
* `ExtensionLinearTwist` — any two extensions differ by a linear character trivial on `N`,
* `RepresentationDeterminant` — the character-level determinant and its twist formula.

## Main results (this file, growing)

* `IsIrreducibleCharacter.determinant_mul_linearClassFunction` — `det (χ·β) = β^{χ(1)}·det χ`.
* `IsIrreducibleCharacter.determinant_conjBy` — the determinant is conjugation-equivariant.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press 1976, 6.25/6.28/8.16.
* Peterfalvi §3 (1.7)(b); issue 9002 (v-c).
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **The determinant of a linear twist**: `det (χ · lcf β) = β^d · det χ`, where `d = χ(1)`
is the degree.  Character-level form of `representationDeterminant_twistRep`. -/
theorem IsIrreducibleCharacter.determinant_mul_linearClassFunction [Finite G]
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) (β : G →* ℂˣ)
    (hχβ : IsIrreducibleCharacter (χ * linearClassFunction β))
    {d : ℕ} (hd : χ 1 = (d : ℂ)) :
    hχβ.determinant = β ^ d * hχ.determinant := by
  obtain ⟨V', _, _, _, ρ, hρ, hc⟩ := id hχ
  -- the twisted representation affords `χ · lcf β`
  have h1 : ((χ * linearClassFunction β : ClassFunction G ℂ) : G → ℂ)
      = (twistRep ρ β).character := by
    funext y
    rw [show ((χ * linearClassFunction β : ClassFunction G ℂ) : G → ℂ) y
          = χ y * (β y : ℂ) from by
        rw [show ((χ * linearClassFunction β : ClassFunction G ℂ) : G → ℂ) y
            = (χ * linearClassFunction β) y from rfl, ClassFunction.mul_apply,
          linearClassFunction_apply],
      twistRep_character, congrFun hc y]
    ring
  rw [IsIrreducibleCharacter.determinant_spec hχβ (twistRep ρ β) h1]
  refine MonoidHom.ext fun y => ?_
  -- the degree is the dimension of the affording space
  have hfr : Module.finrank ℂ V' = d := by
    have h2 := congrFun hc 1
    rw [show (χ : G → ℂ) 1 = χ 1 from rfl, hd, Representation.char_one] at h2
    exact_mod_cast h2.symm
  rw [representationDeterminant_twistRep, hfr,
    IsIrreducibleCharacter.determinant_spec hχ ρ hc]
  rfl

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]

/-- **Conjugation-equivariance of the determinantal character**:
`det (θ^g) = (det θ) ∘ conj_g`.  The witnessing representation of `θ^g` can be taken to be
the conjugate representation `conjRep ρ g = ρ ∘ conj_g`, whose determinant is
`det ρ ∘ conj_g` by `representationDeterminant_comp`.

This is the equivariance that lets uniqueness of the canonical extension propagate
invariance in the abelian iterate (issue 9002 (v-d)): if `θ` is `K`-invariant, the conjugate
of the canonical extension is again an extension with the same determinantal order, hence
equals the canonical extension. -/
theorem IsIrreducibleCharacter.determinant_conjBy [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) (g : K)
    (hconj : IsIrreducibleCharacter (ClassFunction.conjBy g θ)) :
    hconj.determinant
      = hθ.determinant.comp
          (ClassFunction.conjByMulEquiv (G := K) (H := H) g).toMonoidHom := by
  obtain ⟨V', _, _, _, ρ, hρ, hc⟩ := id hθ
  -- `conjRep ρ g` affords `θ^g`
  have h1 : ((ClassFunction.conjBy g θ : ClassFunction ↥H ℂ) : ↥H → ℂ)
      = (conjRep ρ g).character := by
    funext h
    rw [conjRep_character]
    exact congrFun hc (ClassFunction.conjByMulEquiv (G := K) (H := H) g h)
  rw [IsIrreducibleCharacter.determinant_spec hconj (conjRep ρ g) h1, conjRep,
    representationDeterminant_comp, IsIrreducibleCharacter.determinant_spec hθ ρ hc]

/-- **A linear character trivial on `H ⊴ K` is `[K:H]`-torsion**: it factors through `K/H`,
so its `[K:H]`-th power evaluates as `μ(y^{[K:H]})` with `y^{[K:H]} ∈ H`
(`Subgroup.pow_index_mem`).  Bounds the determinantal drift of an extension: the twist
between any two extensions is `[K:H]`-torsion, so a `[K:H]`-coprime determinantal order pins
the extension down (issue 9002 (v-c3)/(v-c4)). -/
theorem pow_index_eq_one_of_forall_coe_eq_one {μ : K →* ℂˣ}
    (hμ : ∀ h : ↥H, μ ((h : K)) = 1) :
    μ ^ H.index = 1 := by
  refine MonoidHom.ext fun y => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow]
  exact hμ ⟨y ^ H.index, H.pow_index_mem y⟩

end OddOrder.RepresentationTheory
