/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CharacterInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecomposition
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryIrreducibles

/-!
# The generalized decomposition numbers at an involution are rational integers

Navarro's remark after (5.1) is that `d^x_{χφ} ∈ ℤ[ζ]` for `ζ` a primitive `o(x)`-th root of
unity.  For `x = t` an **involution** that ring is `ℤ`, and the Brauer–Suzuki argument on
pp. 141–145 needs exactly this: the columns `D^t_j` it manipulates over `ℤ`
(`OddOrder.Algebra.exists_eq_of_columns`) are `ℤ`-combinations of the `d^t_{χφ}`.

The proof avoids `ℤ[ζ]` and the Schur-scalar argument entirely.  Write `V₊` for the
`+1`-eigenspace of `σ t`; it is a subrepresentation of `C_G(t)`, and

`χ(t y) = 2 χ_{V₊}(y) − χ(y)`   (`character_involution_mul_eq`).

Both `χ_{V₊}` and `χ|_{C_G(t)}` are ordinary characters of `C_G(t)`, so on the `p`-regular classes
both are `ℕ`-combinations of `IBr(C_G(t))` — that is the decomposition map applied to *any*
invariant lattice (`decompositionNumber`), not just to an irreducible one.  Hence

`d^t_{χφ} = 2 n⁺_φ − n_φ ∈ ℤ`.

Nothing here needs `p = 2`, nor `t` to be a `p`-element.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_nat_character_eq_sum_irreducibleBrauerCharacter` —
  every ordinary character is an `ℕ`-combination of `IBr` on the `p`-regular classes
* `OddOrder.RepresentationTheory.Modular.involutionPlusRepresentation` — `V₊` as a
  representation of `C_G(t)`
* `OddOrder.RepresentationTheory.Modular.exists_intCast_generalizedDecompositionNumber` —
  `d^t_{χφ} ∈ ℤ`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]

/-! ### Every ordinary character is an `ℕ`-combination of `IBr` -/

section AnyRepresentation

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module K W] [Module 𝒪 W]
  [IsScalarTower 𝒪 K W] [FiniteDimensional K W]

/-- **On the `p`-regular classes every ordinary character is an `ℕ`-combination of the irreducible
Brauer characters.**  Pick a `G`-invariant `𝒪`-lattice (`exists_isLattice_invariant`) and read off
its decomposition numbers; the point is that `decompositionNumber` is defined for an arbitrary
lattice representation, not only for the irreducible ones. -/
theorem exists_nat_character_eq_sum_irreducibleBrauerCharacter (hp : p.Prime) {ω : 𝒪}
    (hω : IsPrimitiveRoot ω (pRegularExponent p H))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p H))
    {π : MonoidAlgebra (ResidueField 𝒪) H →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) H), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) H))
    (σ : Representation K H W) :
    ∃ n : ι → ℕ, ∀ y : H, IsPRegular p y →
      σ.character y
        = ∑ φ, (n φ : K) * algebraMap 𝒪 K
            (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y) := by
  classical
  obtain ⟨L, hLat, hinv⟩ := exists_isLattice_invariant (𝒪 := 𝒪) σ
  have := hLat
  refine ⟨decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ (latticeRepresentation σ hinv),
    fun y hy => ?_⟩
  rw [Representation.character, ← algebraMap_trace_latticeRepresentation σ hinv y,
    trace_eq_sum_decompositionNumber hp hω hω' hπ hlin hkerJ (latticeRepresentation σ hinv) y hy,
    map_sum]
  exact Finset.sum_congr rfl fun φ _ => by rw [map_mul, map_natCast]

end AnyRepresentation

/-! ### The `+1`-eigenspace of an involution as a representation of its centraliser -/

section Plus

variable {G V : Type*} [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {t : G}


omit [IsDomain 𝒪] [ValuationRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Algebra 𝒪 K] [IsFractionRing 𝒪 K] in
/-- Elements of `C_G(t)` commute with `t`. -/
theorem commute_of_mem_centralizerOf (y : ↥(centralizerOf t)) : Commute t (y : G) :=
  (Subgroup.mem_centralizer_iff.mp y.2) t rfl

/-- **The `+1`-eigenspace of an involution, as a representation of its centraliser.**  `C_G(t)`
commutes with `t`, hence preserves `im (1 + σ t)/2`. -/
noncomputable def involutionPlusRepresentation (σ : Representation K G V) (t : G) :
    Representation K ↥(centralizerOf t) ↥(LinearMap.range (involutionProj σ t)) where
  toFun y := (σ (y : G)).restrict
    (range_involutionProj_invariant σ (commute_of_mem_centralizerOf y))
  map_one' := LinearMap.ext fun v => Subtype.ext (by
    simp only [LinearMap.restrict_apply, Module.End.one_apply]
    rw [show ((1 : ↥(centralizerOf t)) : G) = 1 from rfl, map_one]
    rfl)
  map_mul' y z := LinearMap.ext fun v => Subtype.ext (by
    simp only [LinearMap.restrict_apply, Module.End.mul_apply]
    rw [show ((y * z : ↥(centralizerOf t)) : G) = (y : G) * (z : G) from rfl, map_mul]
    rfl)

end Plus

/-! ### Integrality -/

section Integral

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module K V] [Module 𝒪 V]
  [IsScalarTower 𝒪 K V] [FiniteDimensional K V] {t : G}

/-- **The generalized decomposition numbers at an involution are rational integers.**

`χ(t y) = 2 χ_{V₊}(y) − χ(y)` expresses `χ(t ·)` on the `p`-section of `t` as a `ℤ`-combination of
two ordinary characters of `C_G(t)`, each of which is an `ℕ`-combination of `IBr(C_G(t))` on the
`p`-regular classes; uniqueness of the expansion (Navarro (5.1)) then identifies `d^t_{χφ}` as the
difference.

Navarro deduces this from `d^x_{χφ} ∈ ℤ[ζ_{o(x)}]`; the route here needs no roots of unity and no
Schur scalar, only that `2` is invertible in `K`. -/
theorem exists_intCast_generalizedDecompositionNumber (hp : p.Prime) {ω : 𝒪}
    (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf t)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf t)))
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)),
      π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)))
    (σ : Representation K G V) (ht : t * t = 1)
    (hχ : ∀ g h : G, IsConj g h → σ.character g = σ.character h) :
    ∃ n : ι → ℤ, ∀ φ : ι,
      generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) t hp hω' hπ hlin hkerJ σ.character hχ φ
        = (n φ : K) := by
  classical
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  obtain ⟨nplus, hnplus⟩ := exists_nat_character_eq_sum_irreducibleBrauerCharacter (ι := ι)
    (nn := nn) hp hω hω' hπ hlin hkerJ (involutionPlusRepresentation σ t)
  obtain ⟨nall, hnall⟩ := exists_nat_character_eq_sum_irreducibleBrauerCharacter (ι := ι)
    (nn := nn) hp hω hω' hπ hlin hkerJ (σ.comp (centralizerOf t).subtype)
  refine ⟨fun φ => 2 * (nplus φ : ℤ) - (nall φ : ℤ), ?_⟩
  have key : (fun φ => ((2 * (nplus φ : ℤ) - (nall φ : ℤ) : ℤ) : K))
      = generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) t hp hω' hπ hlin hkerJ
          σ.character hχ := by
    refine eq_generalizedDecompositionNumber t hp hω' hπ hlin hkerJ σ.character hχ fun y hy => ?_
    have hsplit := character_involution_mul_eq σ h2 ht (commute_of_mem_centralizerOf y)
    rw [Finset.sum_congr rfl fun φ (_ : φ ∈ Finset.univ) =>
        show ((2 * (nplus φ : ℤ) - (nall φ : ℤ) : ℤ) : K)
              * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y)
            = 2 * ((nplus φ : K)
                * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y))
              - (nall φ : K)
                * algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ y) by
          push_cast; ring,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← hnplus y hy, ← hnall y hy, hsplit]
    rfl
  intro φ
  exact (congrFun key φ).symm

end Integral

/-! ### The intended instantiation

The consumer is the "analysis at `t`", where `σ` is an ordinary irreducible of the ambient group
read off a Wedderburn splitting.  Checking it here keeps the instance chain
(`Module 𝒪 (m i → K)`, `IsScalarTower 𝒪 K (m i → K)`) from silently breaking. -/

section Check

variable {G : Type*} [Group G] [Finite G] {t : G}
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

example (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf t)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf t)))
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)),
      π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)))
    (eG : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K) (i : ι') (ht : t * t = 1) :
    ∃ n : ι → ℤ, ∀ φ : ι,
      generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) t hp hω' hπ hlin hkerJ
          (wedderburnRepresentation eG i).character
          (fun _ _ h => character_eq_of_isConj (wedderburnRepresentation eG i) h) φ
        = (n φ : K) :=
  exists_intCast_generalizedDecompositionNumber hp hω hω' hπ hlin hkerJ
    (wedderburnRepresentation eG i) ht _

end Check

end OddOrder.RepresentationTheory.Modular
