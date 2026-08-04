/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryDecomposition

/-!
# Navarro (5.2): the core computation

Brauer's second main theorem says that for `x` a `p`-element, `H = C_G(x)`, `b ∈ Bl(H)` with
`b^G = B` and `χ ∈ Irr(G)` outside `B`, the generalized decomposition numbers `d^x_{χφ}` vanish
for `φ ∈ IBr(b)`.

Navarro's computation runs
`0 = χ(f_b x y) = ∑_{ψ ∈ Irr(b)} [χ_H,ψ] ψ(xy) = ∑_{ψ} [χ_H,ψ] (ψ(x)/ψ(1)) ψ(y) = ∑_φ d^x_{χφ} φ(y)`
and concludes by linear independence of `IBr(H)`.

Here is the same computation with the pieces already in place.  Writing `c^g_φ` for the
coefficients produced by a central element `g`,

`tr(ρ(g · x · y)) = ∑_φ c^g_φ φ(y)`   with   `c^g_φ = ∑_i d_i ω_i(g) ω_i(x) D_{iφ}`,

the argument is:

* `c^{f} = 0`, because `tr(ρ(f x y)) = 0` (that is (5.7)) and the `φ` are independent;
* `c^{1} = c^{f} + c^{1-f}` by linearity of the `ω_i`;
* `c^{1-f}_φ = 0` for `φ ∈ IBr(b)`, because a constituent with `ω_i(f) ≠ 1` lies outside `b` and
  block-diagonality of the decomposition numbers kills `D_{iφ}`;
* and `c^{1}` is the generalized decomposition of `χ`.

⚠ Only the two idempotents `f` and `1 - f` are needed — not the whole family `∑_{b'} f_{b'} = 1`
that the textbook implicitly sums over.

## Main results

* `OddOrder.RepresentationTheory.Modular.blockCoeff_eq_zero_of_vanishing` — Navarro (5.2), core
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra

variable {K H : Type*} [Field K] [Group H] {ι' ι : Type*} {mm : ι' → Type*}
  [∀ i, Fintype (mm i)] [∀ i, DecidableEq (mm i)] [Fintype ι'] [∀ i, Nonempty (mm i)]
  [Fintype ι]
variable {π : MonoidAlgebra K H →+* ∀ j, Matrix (mm j) (mm j) K} (hπ : Function.Surjective π)
  (hlin : ∀ (c : K) (a : MonoidAlgebra K H), π (c • a) = c • π a)

/-- The coefficients that a central element `g` contributes to the `IBr`-expansion of
`y ↦ tr(ρ(g · x · y))`. -/
noncomputable def blockCoeff (d : ι' → ℕ) (D : ι' → ι → ℕ)
    (g w : Subalgebra.center K (MonoidAlgebra K H)) (j : ι) : K :=
  ∑ i, (d i : K) * MatrixModule.centralCharacterAlg π i hπ hlin g
    * MatrixModule.centralCharacterAlg π i hπ hlin w * (D i j : K)

include hπ hlin in
omit [Fintype ι] in
/-- `blockCoeff` is additive in the central element. -/
theorem blockCoeff_add (d : ι' → ℕ) (D : ι' → ι → ℕ)
    (g g' w : Subalgebra.center K (MonoidAlgebra K H)) (j : ι) :
    blockCoeff hπ hlin d D (g + g') w j
      = blockCoeff hπ hlin d D g w j + blockCoeff hπ hlin d D g' w j := by
  rw [blockCoeff, blockCoeff, blockCoeff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add]
  ring

include hπ hlin in
/-- **`blockCoeff` computes the expansion.**  This packages
`trace_asAlgebraHom_center_center_mul` with the decomposition of each irreducible character into
Brauer characters, and swaps the order of summation. -/
theorem sum_blockCoeff_eq_trace {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K H V} {d : ι' → ℕ}
    (hd : ∀ g : H, LinearMap.trace K V (ρ g)
      = ∑ i, (d i : K) * LinearMap.trace K (mm i → K) (blockRepresentation π i g))
    {D : ι' → ι → ℕ} {φ : ι → H → K} {y : H}
    (hD : ∀ i : ι', LinearMap.trace K (mm i → K) (blockRepresentation π i y)
      = ∑ j, (D i j : K) * φ j y)
    (g w : Subalgebra.center K (MonoidAlgebra K H)) :
    ∑ j, blockCoeff hπ hlin d D g w j * φ j y
      = LinearMap.trace K V
          (ρ.asAlgebraHom ((g : MonoidAlgebra K H)
            * ((w : MonoidAlgebra K H) * single y 1))) := by
  rw [trace_asAlgebraHom_center_center_mul hπ hlin hd]
  have hstep : ∀ i : ι', (d i : K) * MatrixModule.centralCharacterAlg π i hπ hlin g
        * MatrixModule.centralCharacterAlg π i hπ hlin w
        * LinearMap.trace K (mm i → K) (blockRepresentation π i y)
      = ∑ j, ((d i : K) * MatrixModule.centralCharacterAlg π i hπ hlin g
          * MatrixModule.centralCharacterAlg π i hπ hlin w * (D i j : K)) * φ j y := by
    intro i
    rw [hD i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [blockCoeff, Finset.sum_mul]

include hπ hlin in
/-- **Navarro (5.2), the core.**  If the `f`-part of the character vanishes on the `p`-regular
elements — which is (5.7) — and the constituents outside `f` contribute nothing to the Brauer
characters in `S` — which is block-diagonality — then the generalized decomposition numbers
vanish on `S`. -/
theorem blockCoeff_eq_zero_of_vanishing {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K H V} {d : ι' → ℕ}
    (hd : ∀ g : H, LinearMap.trace K V (ρ g)
      = ∑ i, (d i : K) * LinearMap.trace K (mm i → K) (blockRepresentation π i g))
    {D : ι' → ι → ℕ} {φ : ι → H → K} {P : H → Prop}
    (hD : ∀ (y : H), P y → ∀ i : ι', LinearMap.trace K (mm i → K) (blockRepresentation π i y)
      = ∑ j, (D i j : K) * φ j y)
    (hindep : ∀ c : ι → K, (∀ y : H, P y → ∑ j, c j * φ j y = 0) → c = 0)
    {f w : Subalgebra.center K (MonoidAlgebra K H)}
    (hvanish : ∀ y : H, P y → LinearMap.trace K V
      (ρ.asAlgebraHom ((f : MonoidAlgebra K H)
        * ((w : MonoidAlgebra K H) * single y 1))) = 0)
    {S : Set ι}
    (hblock : ∀ (i : ι') (j : ι), j ∈ S →
      MatrixModule.centralCharacterAlg π i hπ hlin f ≠ 1 → D i j = 0)
    (hfidem : ∀ i : ι', MatrixModule.centralCharacterAlg π i hπ hlin f = 0 ∨
      MatrixModule.centralCharacterAlg π i hπ hlin f = 1)
    {j : ι} (hj : j ∈ S) :
    blockCoeff hπ hlin d D 1 w j = 0 := by
  -- the `f`-part vanishes identically
  have hzero : blockCoeff hπ hlin d D f w = 0 :=
    hindep _ fun y hy => by
      rw [sum_blockCoeff_eq_trace hπ hlin hd (hD y hy), hvanish y hy]
  -- the complementary part misses `S`
  have hcompl : blockCoeff hπ hlin d D (1 - f) w j = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hfidem i with h0 | h1
    · rw [hblock i j hj (by rw [h0]; exact zero_ne_one), Nat.cast_zero, mul_zero]
    · rw [map_sub, map_one, h1, sub_self, mul_zero, zero_mul, zero_mul]
  have hsplit : blockCoeff hπ hlin d D 1 w j
      = blockCoeff hπ hlin d D f w j + blockCoeff hπ hlin d D (1 - f) w j := by
    rw [← blockCoeff_add, add_sub_cancel]
  rw [hsplit, hcompl, add_zero, hzero]
  rfl

end OddOrder.RepresentationTheory.Modular
