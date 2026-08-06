/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecompositionInverse

/-!
# Generalized decomposition numbers with respect to a basic set — Navarro (7.5)

A **basic set** `𝓑` for a block `b` of `H` is a basis of the lattice spanned by
`{ψ⁰ : ψ ∈ Irr(b)}`; `IBr(b)` is one, and any other is obtained from it by an integer matrix
`U = (u_{μφ})` with integer inverse.  Navarro's equation (1) on p. 135 then *defines* the
generalized decomposition numbers relative to `𝓑` by

`d^x_{χφ} = ∑_{μ ∈ IBr(b)} d^x_{χμ} u_{μφ}`.

Once that is taken as the definition, Lemma (7.5) is pure bilinearity on top of the `IBr`-versions
already available:

* (a) `d^x_{χφ} = 0` as soon as every `μ` with `u_{μφ} ≠ 0` has `d^x_{χμ} = 0` — i.e. the second
  main theorem plus the block-diagonality of `U`;
* (b)/(c) the pairing of two columns is the `U`-congruent of the pairing of the `IBr`-columns,
  `∑_χ d^{x⁻¹}_{χφ} d^x_{χη} = (UᵗCU)_{φη}` (and `0` for two non-conjugate `p`-elements).

This file supplies the definition and those two computations; the choice of `U` (i.e. of the basic
set) is left to the caller, which is what Navarro (7.4) provides for the principal block of a
group with a Klein four Sylow `2`-subgroup.

Since only bilinearity is used, `U` is allowed to have entries in `K`: the existence of `U` is a
consequence of the invertibility of the Cartan matrix over `K`
(`sum_ordinaryCombination_block_eq_irreducibleBrauerCharacter`), whereas the integrality of `U`
is the separate content of Navarro (3.16).

## Main definitions

* `OddOrder.RepresentationTheory.Modular.basicDecompositionNumber` — Navarro's equation (1)

## Main results

* `OddOrder.RepresentationTheory.Modular.basicDecompositionNumber_eq_zero` — (7.5)(a)
* `OddOrder.RepresentationTheory.Modular.sum_basicDecompositionNumber` — the defining expansion
  `χ(x w) = ∑_φ d^x_{χφ} η_φ(w)`
* `OddOrder.RepresentationTheory.Modular.sum_mul_basicDecompositionNumber` — the `U`-congruence
* `OddOrder.RepresentationTheory.Modular.sum_mul_basicDecompositionNumber_eq_cartanMatrix` —
  (7.5)(c)
* `OddOrder.RepresentationTheory.Modular.sum_mul_basicDecompositionNumber_eq_zero` — (7.5)(d)
* `OddOrder.RepresentationTheory.Modular.sum_mul_basicDecompositionNumber_left_eq_zero` —
  the weak orthogonality `(χ(1), D^t_j) = 0`
* `OddOrder.RepresentationTheory.Modular.sum_basicDecompositionNumber_eq_character` —
  `χ(x w) = ∑_φ d^x_{χφ} η_φ(w)` (the display on p. 141)
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

/-! ### The definition and the two bilinear computations -/

section Generic

variable {K ι ι₂ J : Type*} [CommRing K] [Fintype ι] [Fintype J]

/-- **Navarro's equation (1), p. 135**: the generalized decomposition numbers relative to a basic
set, `d^x_{χφ} = ∑_μ d^x_{χμ} u_{μφ}`.

Navarro's `U` is an integer matrix; the entries are only ever used bilinearly here, so `u` is
allowed to take values in `K` (feed `fun μ φ => ((u μ φ : ℤ) : K)` for the integral case).  This
matters because the *existence* of `U` comes from the invertibility of the Cartan matrix over `K`
(`sum_ordinaryCombination_block_eq_irreducibleBrauerCharacter`), while its integrality is the
separate content of Navarro (3.16). -/
def basicDecompositionNumber (d : ι → K) (u : ι → ι₂ → K) (φ : ι₂) : K :=
  ∑ μ : ι, d μ * u μ φ

/-- **Navarro (7.5)(a)**: the basic-set number vanishes as soon as every `IBr`-number it uses
does.  For a basic set of a block `b` the matrix `U` is supported on `IBr(b)`, and the second main
theorem kills `d^x_{χμ}` for `μ ∈ IBr(b)` when `b` does not induce the block of `χ`. -/
theorem basicDecompositionNumber_eq_zero {d : ι → K} {u : ι → ι₂ → K} {φ : ι₂}
    (h : ∀ μ : ι, u μ φ ≠ 0 → d μ = 0) : basicDecompositionNumber d u φ = 0 := by
  refine Finset.sum_eq_zero fun μ _ => ?_
  by_cases hμ : u μ φ = 0
  · rw [hμ, mul_zero]
  · rw [h μ hμ, zero_mul]

/-- **The pairing of two basic-set columns is the `U`-congruent of the `IBr`-pairing.**  This is
what turns Navarro (5.13) into (7.5)(b),(c): whatever the matrix `c` of pairings of the
`IBr`-columns is, the basic-set pairing is `UᵗcU`. -/
theorem sum_mul_basicDecompositionNumber {dinv d : J → ι → K} {u : ι → ι₂ → K} (φ η : ι₂)
    (c : ι → ι → K) (hc : ∀ μ τ : ι, (∑ j : J, dinv j μ * d j τ) = c μ τ) :
    (∑ j : J, basicDecompositionNumber (dinv j) u φ * basicDecompositionNumber (d j) u η)
      = ∑ μ : ι, ∑ τ : ι, u μ φ * c μ τ * u τ η := by
  classical
  calc (∑ j : J, basicDecompositionNumber (dinv j) u φ * basicDecompositionNumber (d j) u η)
      = ∑ j : J, ∑ μ : ι, ∑ τ : ι,
          (dinv j μ * u μ φ) * (d j τ * u τ η) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [basicDecompositionNumber, basicDecompositionNumber, Finset.sum_mul]
        exact Finset.sum_congr rfl fun μ _ => Finset.mul_sum _ _ _
    _ = ∑ μ : ι, ∑ τ : ι, u μ φ * (∑ j : J, dinv j μ * d j τ) * u τ η := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ μ : ι, ∑ τ : ι, u μ φ * c μ τ * u τ η :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun τ _ => by rw [hc μ τ]

/-- **Navarro (7.5)(d)**: two basic-set columns belonging to non-conjugate `p`-elements are
orthogonal, because their `IBr`-columns already are.

The two elements have different centralisers, so the two basic sets are expressed by *different*
matrices `u`, `u'` over different index sets — which is why this is not a special case of
`sum_mul_basicDecompositionNumber` (`c = 0`). -/
theorem sum_mul_basicDecompositionNumber_eq_zero {ι' ι₂' : Type*} [Fintype ι']
    {dinv : J → ι → K} {d : J → ι' → K} {u : ι → ι₂ → K} {u' : ι' → ι₂' → K} (φ : ι₂) (η : ι₂')
    (h : ∀ (μ : ι) (τ : ι'), (∑ j : J, dinv j μ * d j τ) = 0) :
    (∑ j : J, basicDecompositionNumber (dinv j) u φ * basicDecompositionNumber (d j) u' η)
      = 0 := by
  classical
  calc (∑ j : J, basicDecompositionNumber (dinv j) u φ * basicDecompositionNumber (d j) u' η)
      = ∑ j : J, ∑ μ : ι, ∑ τ : ι', (dinv j μ * u μ φ) * (d j τ * u' τ η) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [basicDecompositionNumber, basicDecompositionNumber, Finset.sum_mul]
        exact Finset.sum_congr rfl fun μ _ => Finset.mul_sum _ _ _
    _ = ∑ μ : ι, ∑ τ : ι', u μ φ * (∑ j : J, dinv j μ * d j τ) * u' τ η := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun τ _ => ?_
        rw [h μ τ, mul_zero, zero_mul]

/-- **The weak orthogonality that Navarro reads as `(χ(1), D^t_j) = 0`**: a family of scalars
orthogonal to every `IBr`-column is orthogonal to every basic-set column. -/
theorem sum_mul_basicDecompositionNumber_left_eq_zero {c : J → K} {d : J → ι → K}
    {u : ι → ι₂ → K} (η : ι₂) (h : ∀ τ : ι, (∑ j : J, c j * d j τ) = 0) :
    (∑ j : J, c j * basicDecompositionNumber (d j) u η) = 0 := by
  classical
  calc (∑ j : J, c j * basicDecompositionNumber (d j) u η)
      = ∑ j : J, ∑ τ : ι, c j * d j τ * u τ η := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [basicDecompositionNumber, Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by ring
    _ = ∑ τ : ι, (∑ j : J, c j * d j τ) * u τ η := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun τ _ => (Finset.sum_mul _ _ _).symm
    _ = 0 := Finset.sum_eq_zero fun τ _ => by rw [h τ, zero_mul]

/-- **The defining expansion in the basic set.**  If `U` expresses each irreducible Brauer
character in the basic set — `μ = ∑_φ u_{μφ} η_φ` — then the basic-set numbers reproduce the
expansion: `∑_φ d^x_{χφ} η_φ = ∑_μ d^x_{χμ} μ`.

This is the form Navarro uses in the "analysis at `t`" (p. 141): `χ(t u) = ∑_j d^t_{χ ψ_j} ψ_j(u)`
for a basic set `{ψ_0, ψ_1, ψ_2}` of the principal block of `C_G(t)`. -/
theorem sum_basicDecompositionNumber [Fintype ι₂] {d : ι → K} {u : ι → ι₂ → K}
    {μval : ι → K} {ηval : ι₂ → K} (hu : ∀ μ : ι, μval μ = ∑ φ : ι₂, u μ φ * ηval φ) :
    (∑ φ : ι₂, basicDecompositionNumber d u φ * ηval φ) = ∑ μ : ι, d μ * μval μ := by
  classical
  calc (∑ φ : ι₂, basicDecompositionNumber d u φ * ηval φ)
      = ∑ φ : ι₂, ∑ μ : ι, d μ * (u μ φ * ηval φ) := by
        refine Finset.sum_congr rfl fun φ _ => ?_
        rw [basicDecompositionNumber, Finset.sum_mul]
        exact Finset.sum_congr rfl fun μ _ => by ring
    _ = ∑ μ : ι, d μ * ∑ φ : ι₂, u μ φ * ηval φ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun μ _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ μ : ι, d μ * μval μ :=
        Finset.sum_congr rfl fun μ _ => by rw [hu μ]

/-! ### Descent to `ℤ`

The endgame of Brauer–Suzuki (`OddOrder.Algebra.exists_eq_of_columns`) runs over `ℤ`, so the
basic-set columns have to be recognised as integer columns: `d^t_{χμ} ∈ ℤ` at an involution
(`exists_intCast_generalizedDecompositionNumber`) and `U` integral (`intBasicSetMatrix`) make each
`D^x_{χφ}` an integer, and then every pairing identity descends by injectivity of `ℤ → K`. -/

/-- **An integral `IBr`-column against an integral `U` gives an integral basic-set column.** -/
theorem intCast_basicDecompositionNumber {d : ι → K} {u : ι → ι₂ → K} {n : ι → ℤ} {U : ι → ι₂ → ℤ}
    (hd : ∀ μ, d μ = (n μ : K)) (hu : ∀ μ φ, u μ φ = (U μ φ : K)) (φ : ι₂) :
    basicDecompositionNumber d u φ = ((∑ μ : ι, n μ * U μ φ : ℤ) : K) := by
  rw [basicDecompositionNumber, Int.cast_sum]
  exact Finset.sum_congr rfl fun μ _ => by rw [hd μ, hu μ φ, Int.cast_mul]

/-- **A pairing of two integer columns, computed in `K`, is that integer.**  This is how the
identities `(D^t_i, D^t_j) = 2(1 + δ_ij)` and `(χ(1), D^t_j) = 0` of Navarro (7.5) reach the
integer endgame. -/
theorem sum_mul_eq_of_intCast [CharZero K] {S : Type*} [Fintype S] {D D' : S → K} {Dz Dz' : S → ℤ}
    {c : ℤ} (h : ∀ k, D k = (Dz k : K)) (h' : ∀ k, D' k = (Dz' k : K))
    (hc : (∑ k, D k * D' k) = (c : K)) :
    (∑ k, Dz k * Dz' k) = c := by
  refine Int.cast_injective (α := K) ?_
  rw [Int.cast_sum, ← hc]
  exact Finset.sum_congr rfl fun k _ => by rw [h k, h' k, Int.cast_mul]

end Generic

/-! ### Navarro (7.5)(c) -/

section Cartan

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G] {x : G}
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
variable {J : Type*} [Fintype J] {mG : J → Type*} [∀ j, Fintype (mG j)]
  [∀ j, DecidableEq (mG j)] [∀ j, Nonempty (mG j)]
variable [Invertible (Nat.card G : K)]
variable (hpC : p.Prime) {ω : 𝒪}
  (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
  (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (mG j) (mG j) K)

include hpC hω hω' hπ hlin hkerJ in
/-- **Navarro (7.5)(c)**: for a basic set given by the integer matrix `U`, the pairing of two
columns of the basic-set generalized decomposition matrix is `UᵗCU`, where `C` is the Cartan
matrix of `C_G(x)` in the `IBr` basis. -/
theorem sum_mul_basicDecompositionNumber_eq_cartanMatrix {ι₂ : Type*} (u : ι → ι₂ → K)
    (hx : IsPElement p x) (φ η : ι₂) :
    (∑ j : J, basicDecompositionNumber
        (generalizedDecompositionNumberInv (x := x) hpC hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG j).character)
          (fun _ _ h => character_eq_of_isConj _ h)) u φ *
      basicDecompositionNumber
        (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ
          ((wedderburnRepresentation eG j).character)
          (fun _ _ h => character_eq_of_isConj _ h)) u η)
      = ∑ μ : ι, ∑ τ : ι, u μ φ
          * (cartanMatrix hpC hω hω' hπ hlin hkerJ e μ τ : K) * u τ η :=
  sum_mul_basicDecompositionNumber (J := J) φ η _ fun μ τ =>
    sum_mul_generalizedDecompositionNumberInv_eq_cartanMatrix hpC hω hω' hπ hlin hkerJ e eG hx μ τ

omit [Invertible (Nat.card G : K)] in
include hpC hω' hπ hlin hkerJ in
/-- **`χ(x w) = ∑_φ d^x_{χφ} η_φ(w)`** for a basic set `η` given by the integer matrix `U`
expressing `IBr(C_G(x))` in it.  This is Navarro's display on p. 141. -/
theorem sum_basicDecompositionNumber_eq_character {ι₂ : Type*} [Fintype ι₂] (u : ι → ι₂ → K)
    (η : ι₂ → ↥(centralizerOf x) → K)
    (hu : ∀ (μ : ι) (w : ↥(centralizerOf x)), IsPRegular p w →
      algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ w)
        = ∑ φ : ι₂, u μ φ * η φ w)
    (χ : G → K) (hχ : ∀ g h : G, IsConj g h → χ g = χ h)
    {w : ↥(centralizerOf x)} (hw : IsPRegular p w) :
    (∑ φ : ι₂, basicDecompositionNumber
        (generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ) u φ * η φ w)
      = χ (x * (w : G)) := by
  rw [sum_basicDecompositionNumber (fun μ => hu μ w hw)]
  exact sum_generalizedDecompositionNumber x hpC hω' hπ hlin hkerJ χ hχ hw

end Cartan

end OddOrder.RepresentationTheory.Modular
