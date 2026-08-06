/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Localization.Integer
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanInverse

/-!
# The irreducible Brauer characters are a basis of the `p`-regular class functions

`|IBr(G)| = #cl(G°)` (`card_eq_card_pRegularClass`) and the irreducible Brauer characters are
linearly independent on the `p`-regular classes
(`eq_zero_of_sum_irreducibleBrauerCharacter_ringHom`).  So their table on the `p`-regular class
representatives is a *square* matrix with independent rows, hence invertible; consequently
**every** function on the `p`-regular elements that is constant on conjugacy classes is uniquely
a combination `∑_φ d_φ φ`.

Independence is proved over `𝒪`; over the fraction field `K` it follows by clearing denominators
(`IsLocalization.exist_integer_multiples_of_finite`), which is done here.

This is exactly what Navarro (5.1) needs: for a `p`-element `x` and `H = C_G(x)`, the function
`y ↦ χ(xy)` is a class function of `H`, so on the `p`-regular elements of `H` it expands uniquely
in `IBr(H)` — the coefficients being the generalized decomposition numbers `d^x_{χφ}`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.brauerCharacterMatrix` — the table `φ(x_j)`

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_isConj_pRegularRep`
* `OddOrder.RepresentationTheory.Modular.isUnit_det_brauerCharacterMatrix`
* `OddOrder.RepresentationTheory.Modular.existsUnique_coeff_irreducibleBrauerCharacter`
* `OddOrder.RepresentationTheory.Modular.eq_zero_of_vecMul_map` — a vanishing left kernel is
  inherited by a field extension
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

/-! ### Left kernels survive a field extension

A matrix with entries in `F` whose rows are independent over `F` has rows independent over any
field extension `K`: expand a `K`-relation in an `F`-basis of `K` and read off the coefficients.

This is what will let the coefficient field of the modular theory be an *arbitrary* extension of
`Frac 𝒪` — in particular an algebraic closure, for which the Wedderburn splitting of `K[G]` is
free — rather than `Frac 𝒪` itself (issue 9506). -/

/-- **A vanishing left kernel is inherited by a field extension.** -/
theorem eq_zero_of_vecMul_map {F L ι' κ : Type*} [Field F] [Field L] [Algebra F L]
    [Fintype ι'] {M : Matrix ι' κ F}
    (hF : ∀ c : ι' → F, c ᵥ* M = 0 → c = 0)
    {d : ι' → L} (hd : d ᵥ* M.map (algebraMap F L) = 0) : d = 0 := by
  classical
  set b := Module.Basis.ofVectorSpace F L with hb
  have hzero : ∀ j : Module.Basis.ofVectorSpaceIndex F L, (fun i => b.repr (d i) j) ᵥ* M = 0 := by
    intro j
    funext x
    have hx := congrFun hd x
    have hrepr : b.repr ((d ᵥ* M.map (algebraMap F L)) x) j
        = ((fun i => b.repr (d i) j) ᵥ* M) x := by
      simp only [Matrix.vecMul, dotProduct, map_sum, Finsupp.coe_finsetSum,
        Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.map_apply, show d i * algebraMap F L (M i x) = M i x • d i by
        rw [Algebra.smul_def]; ring, map_smul]
      simp [mul_comm]
    rw [← hrepr, hx]
    simp
  funext i
  have := fun j => congrFun (hF _ (hzero j)) i
  refine b.repr.injective ?_
  ext j
  simpa using this j

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Finite ι] [Fintype ι] [DecidableEq ι]
  [∀ i, Nonempty (nn i)]
variable (hp : p.Prime) {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))

omit [IsDomain 𝒪] [ValuationRing 𝒪] [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
  [Fintype ι] [DecidableEq ι] in
include hp hπ hlin hkerJ in
/-- Every `p`-regular element is conjugate to one of the chosen class representatives. -/
theorem exists_isConj_pRegularRep {g : G} (hg : IsPRegular p g) :
    ∃ j : ι, IsConj g (pRegularRep hp hπ hlin hkerJ j) := by
  set C : {C : ConjClasses G // IsPRegularClass p C} :=
    ⟨ConjClasses.mk g, isPRegularClass_mk.mpr hg⟩ with hC
  refine ⟨(equivPRegularClass hp hπ hlin hkerJ).symm C, ?_⟩
  rw [← ConjClasses.mk_eq_mk_iff_isConj, mk_pRegularRep]
  exact congrArg Subtype.val
    ((equivPRegularClass hp hπ hlin hkerJ).apply_symm_apply C).symm

/-- **The Brauer character table** `M_{φ,j} = φ(x_j)` on the `p`-regular class representatives. -/
noncomputable def brauerCharacterMatrix : Matrix ι ι K := fun φ j =>
  algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ
    (pRegularRep hp hπ hlin hkerJ j))

omit [DecidableEq ι] in
include hp hω hπ hlin hkerJ in
/-- **The rows of the Brauer character table are independent over `K`.**  Independence over `𝒪` is
`eq_zero_of_sum_irreducibleBrauerCharacter_ringHom`; a relation over `K` becomes one over `𝒪`
after multiplying by a common denominator. -/
theorem eq_zero_of_vecMul_brauerCharacterMatrix {d : ι → K}
    (hd : d ᵥ* brauerCharacterMatrix (K := K) hp hπ hlin hkerJ = 0) : d = 0 := by
  classical
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪) d
  simp only [IsLocalization.IsInteger] at hb
  choose c hc using hb
  -- `hc i : algebraMap 𝒪 K (c i) = (b : 𝒪) • d i`
  have hrel : ∀ g : G, IsPRegular p g →
      ∑ i, c i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g = 0 := by
    intro g hg
    obtain ⟨j, hj⟩ := exists_isConj_pRegularRep hp hπ hlin hkerJ hg
    refine hinj ?_
    rw [map_sum, map_zero]
    have hterm : ∀ i : ι, algebraMap 𝒪 K
        (c i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g)
        = algebraMap 𝒪 K (b : 𝒪) *
          (d i * brauerCharacterMatrix (K := K) hp hπ hlin hkerJ i j) := by
      intro i
      rw [map_mul, hc i, Algebra.smul_def, brauerCharacterMatrix,
        irreducibleBrauerCharacter_eq_of_isConj (𝒪 := 𝒪) i hj]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
    have hzero : ∑ i, d i * brauerCharacterMatrix (K := K) hp hπ hlin hkerJ i j = 0 :=
      congrFun hd j
    rw [hzero, mul_zero]
  have hc0 := eq_zero_of_sum_irreducibleBrauerCharacter_ringHom hp hω hπ hlin hkerJ c hrel
  funext i
  have hi := hc i
  rw [hc0] at hi
  rw [Pi.zero_apply, map_zero, Algebra.smul_def] at hi
  have hbne : algebraMap 𝒪 K (b : 𝒪) ≠ 0 := fun h =>
    (nonZeroDivisors.coe_ne_zero b) (hinj (by rw [h, map_zero]))
  exact (mul_eq_zero.mp hi.symm).resolve_left hbne

include hp hω hπ hlin hkerJ in
/-- **The Brauer character table is invertible**: it is square (`|IBr(G)| = #cl(G°)`) with
independent rows. -/
theorem isUnit_det_brauerCharacterMatrix :
    IsUnit (brauerCharacterMatrix (K := K) hp hπ hlin hkerJ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  exact hv0 (eq_zero_of_vecMul_brauerCharacterMatrix hp hω hπ hlin hkerJ hv)

omit [DecidableEq ι] in
include hp hω hπ hlin hkerJ in
/-- **The irreducible Brauer characters are a basis of the `p`-regular class functions.**  A
function `f : G → K` constant on conjugacy classes is, on the `p`-regular elements, uniquely a
`K`-combination of the `φ_i`.

Only the values of `f` on `p`-regular elements matter; conjugacy-invariance is asked for
everywhere merely because that is how class functions occur in practice. -/
theorem existsUnique_coeff_irreducibleBrauerCharacter (f : G → K)
    (hf : ∀ g h : G, IsConj g h → f g = f h) :
    ∃! d : ι → K, ∀ g : G, IsPRegular p g →
      ∑ φ, d φ * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g) = f g := by
  classical
  set M := brauerCharacterMatrix (K := K) hp hπ hlin hkerJ with hM
  have hdet : IsUnit M.det := isUnit_det_brauerCharacterMatrix hp hω hπ hlin hkerJ
  set fv : ι → K := fun j => f (pRegularRep hp hπ hlin hkerJ j) with hfv
  -- the statement at the representatives is a `vecMul` equation, and `M` is invertible
  have hkey : ∀ d : ι → K, (∀ g : G, IsPRegular p g →
      ∑ φ, d φ * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g) = f g) ↔ d ᵥ* M = fv := by
    intro d
    constructor
    · intro h
      funext j
      exact h _ (isPRegular_pRegularRep hp hπ hlin hkerJ j)
    · intro h g hg
      obtain ⟨j, hj⟩ := exists_isConj_pRegularRep hp hπ hlin hkerJ hg
      have hval : ∑ i, d i * M i j = fv j := congrFun h j
      have hterm : ∀ φ : ι, d φ * algebraMap 𝒪 K
          (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g) = d φ * M φ j := fun φ => by
        have hb : irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g
            = irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ
              (pRegularRep hp hπ hlin hkerJ j) :=
          irreducibleBrauerCharacter_eq_of_isConj (𝒪 := 𝒪) φ hj
        rw [hb, hM]
        rfl
      rw [Finset.sum_congr rfl fun φ _ => hterm φ, hval, hfv]
      exact (hf _ _ hj).symm
  refine ⟨fv ᵥ* M⁻¹, (hkey _).mpr ?_, fun d hd => ?_⟩
  · rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  · calc d = d ᵥ* (1 : Matrix ι ι K) := (Matrix.vecMul_one d).symm
      _ = d ᵥ* (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet]
      _ = (d ᵥ* M) ᵥ* M⁻¹ := (Matrix.vecMul_vecMul d M M⁻¹).symm
      _ = fv ᵥ* M⁻¹ := by rw [(hkey d).mp hd]

omit [DecidableEq ι] in
include hp hω hπ hlin hkerJ in
/-- **Linear independence of `IBr(G)`**: a combination vanishing on the `p`-regular elements has
zero coefficients.  This is the uniqueness half of
`existsUnique_coeff_irreducibleBrauerCharacter` applied to the zero class function. -/
theorem eq_zero_of_sum_irreducibleBrauerCharacter_eq_zero (a : ι → K)
    (ha : ∀ g : G, IsPRegular p g →
      ∑ φ, a φ * algebraMap 𝒪 K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ g) = 0) :
    a = 0 := by
  classical
  exact (existsUnique_coeff_irreducibleBrauerCharacter hp hω hπ hlin hkerJ (fun _ => (0 : K))
    (fun _ _ _ => rfl)).unique ha (fun _ _ => by simp)

end OddOrder.RepresentationTheory.Modular
