/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Ring.Subring.Basic
import OddOrder.Algebra.PiMatrixSimpleModules

/-!
# Central characters of the blocks

A central element of `A` acts on each block of a surjection `π : A ↠ ∏_j M_{n_j}(k)` by a
scalar: its image is central in the matrix algebra, and the centre of a matrix algebra over a
commutative ring consists of the scalar matrices (`Matrix.center_eq_range`).  The resulting map

`ω_i : Z(A) →+* k`

is the **central character** of the `i`-th block.  Two blocks lie in the same *block* of `A` (in
the sense of block theory) exactly when their central characters agree, so this is the entry
point to the block decomposition.

## Main results

* `OddOrder.MatrixModule.exists_scalar_of_mem_center`
* `OddOrder.MatrixModule.exists_smul_id_of_commute_blockAction` — the commutant of a block is `k`
* `OddOrder.MatrixModule.centralCharacter`
* `OddOrder.MatrixModule.centralCharacterPi_eq_zero_iff`
* `OddOrder.MatrixModule.SameBlock`
-/

namespace OddOrder.MatrixModule

open Matrix

variable {k ι : Type*} [Field k] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
variable {A : Type*} [Ring A]

/-- **A central element acts on each block by a scalar matrix.** -/
theorem exists_scalar_of_mem_center {π : A →+* ∀ j, Matrix (nn j) (nn j) k}
    (hπ : Function.Surjective π) {z : A} (hz : z ∈ Set.center A) (i : ι) :
    ∃ c : k, π z i = Matrix.scalar (nn i) c := by
  classical
  have hmem : π z i ∈ Set.center (Matrix (nn i) (nn i) k) := by
    rw [Semigroup.mem_center_iff]
    intro M
    obtain ⟨x, hx⟩ := hπ (Pi.single i M)
    have h := congrArg π (Semigroup.mem_center_iff.mp hz x)
    rw [map_mul, map_mul, hx] at h
    simpa using congrFun h i
  rw [Matrix.center_eq_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

/-- **The commutant of a block is the scalars.**  A `k`-endomorphism of `nn i → k` commuting with
the whole image of `A` commutes with every matrix, because `π` is onto; hence it is a scalar.

This is absolute irreducibility of the `i`-th block, in the form
`LatticeCentralCharacter.centralCharacter` asks for. -/
theorem exists_smul_id_of_commute_blockAction {π : A →+* ∀ j, Matrix (nn j) (nn j) k}
    (hπ : Function.Surjective π) (i : ι) (E : (nn i → k) →ₗ[k] (nn i → k))
    (hE : ∀ (a : A) (v : nn i → k), E (π a i *ᵥ v) = π a i *ᵥ E v) :
    ∃ c : k, E = c • LinearMap.id := by
  classical
  have hcomm : ∀ M : Matrix (nn i) (nn i) k, ∀ v, E (M *ᵥ v) = M *ᵥ E v := by
    intro M v
    obtain ⟨a, ha⟩ := hπ (Pi.single i M)
    have hM : π a i = M := by rw [ha]; simp
    rw [← hM]; exact hE a v
  have hmem : LinearMap.toMatrix' E ∈ Set.center (Matrix (nn i) (nn i) k) := by
    rw [Semigroup.mem_center_iff]
    intro M
    refine Matrix.toLin'.injective ?_
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply]
    exact (hcomm M v).symm
  rw [Matrix.center_eq_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  have hE' := congrArg Matrix.toLin' hc
  rw [Matrix.toLin'_toMatrix'] at hE'
  refine LinearMap.ext fun v => ?_
  rw [← hE']
  refine funext fun j => ?_
  simp [Matrix.toLin'_apply, Matrix.scalar, Matrix.mulVec_diagonal]

variable (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (i : ι) [Nonempty (nn i)]

open Classical in
/-- The scalar by which a central element acts on the `i`-th block, read off a diagonal entry. -/
noncomputable def centralScalar (z : A) : k :=
  π z i (Classical.arbitrary (nn i)) (Classical.arbitrary (nn i))

/-- **`centralScalar` is additive on finite sums.**  It is a matrix entry of `π z`, and `π` is a
ring homomorphism, so the sum passes through. -/
theorem centralScalar_finsetSum {S : Type*} (s : Finset S) (g : S → A) :
    centralScalar π i (∑ x ∈ s, g x) = ∑ x ∈ s, centralScalar π i (g x) := by
  simp only [centralScalar, map_sum, Finset.sum_apply, Matrix.sum_apply]

theorem scalar_centralScalar (hπ : Function.Surjective π) {z : A} (hz : z ∈ Set.center A) :
    π z i = Matrix.scalar (nn i) (centralScalar π i z) := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hπ hz i
  rw [hc, centralScalar, hc]
  simp

/-- **The central character of the `i`-th block**: a ring homomorphism from the centre of `A` to
the coefficient field. -/
noncomputable def centralCharacter (hπ : Function.Surjective π) :
    Subring.center A →+* k where
  toFun z := centralScalar π i (z : A)
  map_one' := by
    have h1 : π (1 : A) i = 1 := by rw [map_one]; rfl
    simp [centralScalar, h1]
  map_mul' z w := by
    have hzw : π ((z : A) * w) i
        = Matrix.scalar (nn i) (centralScalar π i z) *
          Matrix.scalar (nn i) (centralScalar π i w) := by
      rw [map_mul, Pi.mul_apply, scalar_centralScalar π i hπ z.2,
        scalar_centralScalar π i hπ w.2]
    simp [centralScalar, hzw]
  map_zero' := by simp [centralScalar]
  map_add' z w := by simp [centralScalar]

@[simp]
theorem centralCharacter_apply (hπ : Function.Surjective π) (z : Subring.center A) :
    centralCharacter π i hπ z = centralScalar π i (z : A) := rfl

/-- **The central character is the scalar by which the centre acts on the block.**  This is the
representation-theoretic content of the definition: it is why two blocks with the same central
character cannot be separated by the centre. -/
theorem centralScalar_smul (hπ : Function.Surjective π) {z : A} (hz : z ∈ Set.center A)
    (v : nn i → k) :
    letI := blockModule nn π i
    z • v = centralScalar π i z • v := by
  letI := blockModule nn π i
  change π z i *ᵥ v = _
  rw [scalar_centralScalar π i hπ hz, Matrix.scalar_apply]
  funext j
  simp [Matrix.mulVec, Matrix.diagonal, dotProduct]

/-- **The central character is *the* scalar**: any scalar by which a central element acts on the
`i`-th block is its central-character value.

This is the last step of the bridge from an ordinary character to its block.  The reduction of an
absolutely irreducible `𝒪`-lattice has the centre acting by `λ_χ`
(`Modular.baseChange_apply_center` plus `Modular.asAlgebraHom_reduction_mapRingHom`); if a
constituent of that reduction is the `i`-th block, this identifies `λ_χ` with
`centralCharacter π i`, i.e. tells us which block `χ` lies in. -/
theorem eq_centralScalar_of_forall_smul_eq (hπ : Function.Surjective π) {z : A}
    (hz : z ∈ Set.center A) {c : k}
    (h : letI := blockModule nn π i; ∀ v : nn i → k, z • v = c • v) :
    c = centralScalar π i z := by
  classical
  letI := blockModule nn π i
  set a := Classical.arbitrary (nn i) with ha
  have hv : (c : k) • (Pi.single a 1 : nn i → k)
      = centralScalar π i z • (Pi.single a 1 : nn i → k) := by
    rw [← h (Pi.single a 1), centralScalar_smul π i hπ hz]
  have := congrFun hv a
  simpa using this

/-! ### The centre as a `k`-algebra -/

section Alg

variable [Algebra k A]

theorem mem_center_of_mem_centerSubalgebra {z : Subalgebra.center k A} :
    (z : A) ∈ Set.center A :=
  Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp z.2)

/-- **The central character as a `k`-algebra homomorphism** on the centre.  The extra hypothesis
is that the splitting surjection is `k`-linear, which is what makes it fix the scalars. -/
noncomputable def centralCharacterAlg (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : A), π (c • a) = c • π a) :
    Subalgebra.center k A →ₐ[k] k where
  toFun z := centralScalar π i (z : A)
  map_one' := by
    have h1 : π (1 : A) i = 1 := by rw [map_one]; rfl
    simp [centralScalar, h1]
  map_mul' z w := by
    have hzw : π ((z : A) * w) i
        = Matrix.scalar (nn i) (centralScalar π i z) *
          Matrix.scalar (nn i) (centralScalar π i w) := by
      rw [map_mul, Pi.mul_apply,
        scalar_centralScalar π i hπ (mem_center_of_mem_centerSubalgebra (z := z)),
        scalar_centralScalar π i hπ (mem_center_of_mem_centerSubalgebra (z := w))]
    simp [centralScalar, hzw]
  map_zero' := by simp [centralScalar]
  map_add' z w := by simp [centralScalar]
  commutes' r := by
    have hr : π (algebraMap k A r) i = Matrix.scalar (nn i) r := by
      rw [Algebra.algebraMap_eq_smul_one, hlin, Pi.smul_apply, map_one]
      ext a b
      by_cases h : a = b
      · subst h; simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]
    simp [centralScalar, hr, Matrix.scalar_apply]

/-- **The algebra-homomorphism form of `eq_centralScalar_of_forall_smul_eq`.**  This is the shape
the block partition is stated in (`blockSetoid` compares `centralCharacterAlg`), so it is the
form in which "χ lies in block `i`" gets proved. -/
theorem eq_centralCharacterAlg_of_forall_smul_eq (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : A), π (c • a) = c • π a)
    {z : Subalgebra.center k A} {c : k}
    (h : letI := blockModule nn π i; ∀ v : nn i → k, (z : A) • v = c • v) :
    c = centralCharacterAlg π i hπ hlin z :=
  eq_centralScalar_of_forall_smul_eq π i hπ mem_center_of_mem_centerSubalgebra h

end Alg

/-! ### Blocks -/

section Blocks

variable [∀ i, Nonempty (nn i)]

variable (nn) in
/-- The tuple of central characters. -/
noncomputable def centralCharacterPi (π : A →+* ∀ j, Matrix (nn j) (nn j) k)
    (hπ : Function.Surjective π) : Subring.center A →+* (ι → k) :=
  RingHom.pi fun i => centralCharacter π i hπ

/-- **The central characters see exactly `Z(A)` modulo the kernel of the splitting.**  For
`A = kG` the kernel is `J(kG)`, so `Z(kG) ⧸ (Z(kG) ∩ J)` embeds in `∏_i k`; this is what makes
the block decomposition a decomposition of the centre. -/
theorem centralCharacterPi_eq_zero_iff (π : A →+* ∀ j, Matrix (nn j) (nn j) k)
    (hπ : Function.Surjective π) (z : Subring.center A) :
    centralCharacterPi nn π hπ z = 0 ↔ π (z : A) = 0 := by
  constructor
  · intro h
    funext j
    have hj : centralScalar π j (z : A) = 0 := congrFun h j
    rw [scalar_centralScalar π j hπ z.2, hj]
    simp
  · intro h
    funext j
    have hj : π (z : A) j = 0 := by rw [h]; rfl
    simp [centralCharacterPi, RingHom.pi, centralScalar, hj]

variable (nn) in
/-- **Two blocks lie in the same block of `A`** when their central characters agree.  This is
the standard definition of the block partition. -/
def SameBlock (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π) (i j : ι) :
    Prop :=
  centralCharacter π i hπ = centralCharacter π j hπ

theorem sameBlock_equivalence (π : A →+* ∀ j, Matrix (nn j) (nn j) k)
    (hπ : Function.Surjective π) : Equivalence (SameBlock nn π hπ) where
  refl _ := rfl
  symm h := h.symm
  trans h h' := h.trans h'

end Blocks

end OddOrder.MatrixModule
