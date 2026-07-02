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

/-- **Uniqueness of the canonical extension** (Isaacs *CT* 6.25/6.28, uniqueness half; issue
9002 (v-c4)).  Let `[K:H] = p` be prime and let `θ = Res_H χ₁ = Res_H χ₂` be irreducible of
degree `d` with `p ∤ d`.  If both extensions have determinantal order coprime to `p`, they
are **equal**.

The twist `β` between them (`ExtensionLinearTwist`) satisfies: `β^p = 1` (trivial on `H`,
index-torsion) and `β^d = det χ₂ · (det χ₁)⁻¹` has order dividing both `p` and the coprime
number `o₁·o₂`, hence is trivial; then `p ∤ d` forces `β = 1`. -/
theorem extension_unique_of_not_dvd_orderOf_determinant [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    {χ₁ χ₂ : ClassFunction K ℂ}
    (hχ₁ : IsIrreducibleCharacter χ₁) (hχ₂ : IsIrreducibleCharacter χ₂)
    (hr₁ : ClassFunction.restrict H χ₁ = θ) (hr₂ : ClassFunction.restrict H χ₂ = θ)
    {p : ℕ} (hp : p.Prime) (hidx : H.index = p)
    {d : ℕ} (hd : θ 1 = (d : ℂ)) (hpd : ¬ p ∣ d)
    (ho₁ : ¬ p ∣ orderOf hχ₁.determinant) (ho₂ : ¬ p ∣ orderOf hχ₂.determinant) :
    χ₂ = χ₁ := by
  -- the two extensions differ by a linear character `β` trivial on `H`
  obtain ⟨β, hβH, hβeq⟩ :=
    exists_linearClassFunction_mul_of_restrict_eq_restrict hχ₁ hχ₂
      (hr₁.trans hr₂.symm) (hr₁ ▸ hθ)
  -- the degree of `χ₁` is `d`
  have hd₁ : χ₁ 1 = (d : ℂ) := by
    rw [← hd, ← hr₁]
    change χ₁ (((1 : ↥H) : K)) = χ₁ 1
    rw [OneMemClass.coe_one]
  -- `β` is `p`-torsion
  have hβp : β ^ p = 1 := by
    rw [← hidx]
    exact pow_index_eq_one_of_forall_coe_eq_one hβH
  -- `β^d` is the determinantal drift, killed by both `p`-torsion and coprime order
  have hβd : β ^ d = hχ₂.determinant * hχ₁.determinant⁻¹ := by
    have h1 : hχ₂.determinant = β ^ d * hχ₁.determinant := by
      have h2 : ∀ (hχ₂' : IsIrreducibleCharacter (χ₁ * linearClassFunction β)),
          hχ₂'.determinant = β ^ d * hχ₁.determinant := fun hχ₂' =>
        IsIrreducibleCharacter.determinant_mul_linearClassFunction hχ₁ β hχ₂' hd₁
      calc hχ₂.determinant = (hβeq ▸ hχ₂ :
              IsIrreducibleCharacter (χ₁ * linearClassFunction β)).determinant := by
            congr 1
        _ = β ^ d * hχ₁.determinant := h2 _
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  have hβd1 : β ^ d = 1 := by
    have hdvd_p : orderOf (β ^ d) ∣ p := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul, mul_comm d p, pow_mul, hβp, one_pow]
    have hdvd_o : orderOf (β ^ d)
        ∣ orderOf hχ₂.determinant * orderOf hχ₁.determinant := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [hβd, mul_pow]
      have e1 : hχ₂.determinant
          ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) = 1 := by
        rw [pow_mul, pow_orderOf_eq_one, one_pow]
      have e2 : (hχ₁.determinant⁻¹)
          ^ (orderOf hχ₂.determinant * orderOf hχ₁.determinant) = 1 := by
        rw [inv_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, inv_one]
      rw [e1, e2, one_mul]
    have hcop : Nat.Coprime p (orderOf hχ₂.determinant * orderOf hχ₁.determinant) :=
      hp.coprime_iff_not_dvd.mpr (fun hcon => (hp.dvd_mul.mp hcon).elim ho₂ ho₁)
    rw [← orderOf_eq_one_iff]
    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd_p hdvd_o)
  -- `p ∤ d` upgrades `β^d = 1`, `β^p = 1` to `β = 1`
  have hβ1 : β = 1 := by
    have hdvd_d : orderOf β ∣ d := orderOf_dvd_of_pow_eq_one hβd1
    have hdvd_p : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβp
    have hcop : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hpd
    rw [← orderOf_eq_one_iff]
    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd_p hdvd_d)
  rw [hβeq, hβ1, ClassFunction.mul_linearClassFunction_one]

end OddOrder.RepresentationTheory
