/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.CaseSplitBCD

/-!
# Higman Lemma 12: the mixed-term value (functional-equation core)

G. Higman, *Suzuki 2-groups*, pp. 90--92.  The actor-equivariance layer
(`CaseSplitBCD`) shows the ambient mixed term satisfies `M(λα, μβ) = ν · M(α, β)`.
Over `F = GF(2ⁿ)` a `ZMod 2`-bilinear form `M : F × F → F` is a Frobenius
polynomial `M(α, β) = Σ_{i,j} c_{ij} α^{2^i} β^{2^j}`, and the eigenvalue relation
forces every `c_{ij}` with `λ^{2^i} μ^{2^j} ≠ ν` to vanish.  Together with the
weight-equation congruence this pins `M` to the single monomial
`ε · α^{2^i} β^{2^j}` of Higman's type-B/C/D rows.

This file builds that functional-equation core.  It starts from the field-theory
foundation: the `n` Frobenius powers are `F`-linearly independent (Artin), so the
monomial coefficients `c_{ij}` are uniquely determined and the eigenvalue
argument can extract them.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open Module

noncomputable section

/-- **Artin's independence of the Frobenius powers.**  Over a finite field of
characteristic `2` and cardinality `2ⁿ`, the `n` distinct Frobenius powers
`x ↦ x^{2^i}` (`0 ≤ i < n`) are linearly independent over the field, viewed as
functions.  This is the basis fact behind the Frobenius-polynomial normal form
of a `ZMod 2`-linear map, hence of the mixed-term bilinear form. -/
theorem frobenius_powers_linearIndependent
    {F : Type*} [Field F] [Finite F] [CharP F 2] (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) :
    LinearIndependent F
      (fun i : Fin n => ((((frobeniusEquiv F 2) ^ (i : ℕ)).toMonoidHom) : F → F)) := by
  have hord : orderOf (frobeniusEquiv F 2) = n :=
    orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard
  have hli : LinearIndependent F (fun f : F →* F => (f : F → F)) :=
    linearIndependent_monoidHom F F
  have hinj : Function.Injective
      (fun i : Fin n => (((frobeniusEquiv F 2) ^ (i : ℕ)).toMonoidHom : F →* F)) := by
    intro i j hij
    have hpow : (frobeniusEquiv F 2) ^ (i : ℕ) = (frobeniusEquiv F 2) ^ (j : ℕ) := by
      ext x
      have := congrArg (fun (f : F →* F) => f x) hij
      simpa using this
    have hlt_i : (i : ℕ) < orderOf (frobeniusEquiv F 2) := by rw [hord]; exact i.2
    have hlt_j : (j : ℕ) < orderOf (frobeniusEquiv F 2) := by rw [hord]; exact j.2
    exact Fin.ext
      (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hlt_i) (Set.mem_Iio.mpr hlt_j) hpow)
  exact hli.comp _ hinj

/-- The `GaloisField 2 n`-dimension of the `ZMod 2`-linear endomorphisms of
`GaloisField 2 n` is `n`.  Combined with `frobenius_powers_linearIndependent`
(the `n` Frobenius powers are independent) this shows the Frobenius powers form a
basis, hence every `ZMod 2`-linear map is a unique Frobenius polynomial. -/
theorem galoisField_linearMap_finrank (n : ℕ) (hn : n ≠ 0) :
    Module.finrank (GaloisField 2 n) (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) = n := by
  rw [Module.finrank_linearMap (ZMod 2) (GaloisField 2 n) (GaloisField 2 n)
      (GaloisField 2 n),
    Module.finrank_self, mul_one]
  exact GaloisField.finrank 2 hn

/-- `x ↦ x^{2^i}` as a `ZMod 2`-linear endomorphism of `GaloisField 2 n`.  Built
from the additive homomorphism of the Frobenius power; the `ZMod 2`-linearity is
automatic (`ZMod.map_smul`). -/
def frobLin (n : ℕ) (i : ℕ) : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n :=
  { (frobeniusEquiv (GaloisField 2 n) 2 ^ i).toRingHom.toAddMonoidHom with
    map_smul' :=
      ZMod.map_smul (frobeniusEquiv (GaloisField 2 n) 2 ^ i).toRingHom.toAddMonoidHom }

@[simp] theorem frobLin_apply (n i : ℕ) (x : GaloisField 2 n) :
    frobLin n i x = (frobeniusEquiv (GaloisField 2 n) 2 ^ i) x := rfl

/-- The `n` Frobenius endomorphisms are `GaloisField 2 n`-linearly independent
(transported from `frobenius_powers_linearIndependent` through the injective
coefficient map). -/
theorem frobLin_linearIndependent (n : ℕ) (hn : n ≠ 0) :
    LinearIndependent (GaloisField 2 n) (fun i : Fin n => frobLin n i) := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 n hn
  have h1a := frobenius_powers_linearIndependent (F := GaloisField 2 n) n hcard
  let φ : (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) →ₗ[GaloisField 2 n]
      (GaloisField 2 n → GaloisField 2 n) :=
    { toFun := fun f => (f : GaloisField 2 n → GaloisField 2 n)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp φ h1a

/-- **The Frobenius basis.**  The `n` powers `frobLin n i` form a
`GaloisField 2 n`-basis of the `ZMod 2`-linear endomorphisms of
`GaloisField 2 n`.  Hence every `ZMod 2`-linear map is a unique Frobenius
polynomial `Σᵢ cᵢ · x^{2^i}` — the normal form powering the mixed-term
functional-equation argument. -/
noncomputable def frobeniusBasis (n : ℕ) (hn : n ≠ 0) :
    Basis (Fin n) (GaloisField 2 n) (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) :=
  haveI : NeZero n := ⟨hn⟩
  basisOfLinearIndependentOfCardEqFinrank (frobLin_linearIndependent n hn)
    (by rw [Fintype.card_fin, galoisField_linearMap_finrank n hn])

end

end OddOrder.Higman.Suzuki2Groups
