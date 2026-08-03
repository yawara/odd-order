/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import OddOrder.Algebra.CommutatorSpanHom
import OddOrder.Algebra.CommutatorSpanPi
import OddOrder.Algebra.MatrixCommutator

/-!
# `dim (A ⧸ T')` counts the blocks of a split semisimple quotient

Assemble the three previous steps.  Let `A` be an algebra over a field `k` of characteristic `p`
admitting a surjection `π : A ↠ B` with uniformly nilpotent kernel (for a finite-dimensional
algebra, `B = A ⧸ J(A)`), and suppose `B` is *split semisimple*, i.e. Artin–Wedderburn puts it in
the form `∏_{i ∈ ι} M_{n_i}(k)`.  Then

`dim_k (A ⧸ T') = #ι`,

where `T' = {x : ∃ m, x ^ (p ^ m) ∈ [A, A]}`.  The proof exhibits a single surjection
`A → (ι → k)`, namely "reduce, split, take the trace of each block", and identifies its kernel
with `T'` by walking back through the three steps:

* the trace-tuple map has kernel `[C, C]` (`MatrixCommutator` + `CommutatorSpanPi`);
* on `C` the `p`-radical collapses, `T'(C) = [C, C]` (trace of a `p`-power);
* `T'` is preserved by the splitting isomorphism and is the preimage of `T'` along `π`
  (`CommutatorSpanHom`).

Applied to `A = kG` this is the second half of Brauer's count: combined with
`finrank_quotient_commutatorRadical` (`dim (kG ⧸ T') = #{p`-regular classes`}`) it says the
number of matrix blocks of `kG ⧸ J(kG)` is the number of `p`-regular classes.  (That the blocks
are in bijection with the irreducible `kG`-modules is the uniqueness half of Artin–Wedderburn
and is *not* proved here.)

## Main results

* `OddOrder.ker_traceTuple`
* `OddOrder.commutatorRadical_matrixPi_eq`
* `OddOrder.finrank_quotient_commutatorRadical_eq_card`
-/

namespace OddOrder

open Matrix

variable {k ι : Type*} [Field k] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]

variable (k nn) in
/-- The trace of each block of a tuple of matrices. -/
noncomputable def traceTuple : (∀ i, Matrix (nn i) (nn i) k) →ₗ[k] (ι → k) where
  toFun x i := (x i).trace
  map_add' x y := by funext i; simp
  map_smul' c x := by funext i; simp

omit [∀ i, DecidableEq (nn i)] in
@[simp]
theorem traceTuple_apply (x : ∀ i, Matrix (nn i) (nn i) k) (i : ι) :
    traceTuple k nn x i = (x i).trace := rfl

omit [∀ i, DecidableEq (nn i)] in
theorem surjective_traceTuple [∀ i, Nonempty (nn i)] :
    Function.Surjective (traceTuple k nn) := fun c => by
  classical
  refine ⟨fun i => single (Classical.arbitrary (nn i)) (Classical.arbitrary (nn i)) (c i), ?_⟩
  funext i
  simp

/-- **The trace-tuple map has the commutator span as its kernel.** -/
theorem ker_traceTuple [Finite ι] [∀ i, Nonempty (nn i)] :
    LinearMap.ker (traceTuple k nn) = commutatorSpan k (∀ i, Matrix (nn i) (nn i) k) := by
  rw [commutatorSpan_pi]
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ, forall_const,
    mem_commutatorSpan_matrix_iff]
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

variable {p : ℕ}

omit [∀ i, Fintype (nn i)] in
/-- Characteristic `p` passes to a tuple of matrix algebras. -/
theorem natCast_matrixPi_eq_zero (hk : (p : k) = 0) :
    ((p : ℕ) : ∀ i, Matrix (nn i) (nn i) k) = 0 := by
  funext i
  exact natCast_matrix_eq_zero hk

/-- **A split semisimple algebra has no `p`-radical.** -/
theorem commutatorRadical_matrixPi_eq [Finite ι] [∀ i, Nonempty (nn i)] (hp : p.Prime)
    (hk : (p : k) = 0) :
    commutatorRadical (k := k) hp (natCast_matrixPi_eq_zero (nn := nn) hk)
      = commutatorSpan k (∀ i, Matrix (nn i) (nn i) k) :=
  commutatorRadical_pi_eq hp (fun _ => natCast_matrix_eq_zero hk) _
    fun _ => commutatorRadical_matrix_eq hp hk

/-! ### Descent along a surjection with nilpotent kernel -/

variable {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- **`dim_k (A ⧸ T')` is the number of blocks of the split semisimple quotient.**

`π : A ↠ B` is the reduction modulo a uniformly nilpotent ideal (for a finite-dimensional
algebra: modulo `J(A)`), and `e` is the Artin–Wedderburn splitting of `B`. -/
theorem finrank_quotient_commutatorRadical_eq_card [Finite ι] [∀ i, Nonempty (nn i)]
    (hp : p.Prime) (hk : (p : k) = 0) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (π : A →ₐ[k] B) (hπ : Function.Surjective π) {N : ℕ} (hker : ∀ y : A, π y = 0 → y ^ N = 0)
    (e : B ≃ₐ[k] ∀ i, Matrix (nn i) (nn i) k) :
    Module.finrank k (A ⧸ commutatorRadical (k := k) hp hA) = Nat.card ι := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  set hC := natCast_matrixPi_eq_zero (k := k) (nn := nn) hk with hCdef
  -- the composite "reduce, split, take block traces"
  set Ψ : A →ₗ[k] (ι → k) :=
    (traceTuple k nn).comp ((e.toAlgHom.toLinearMap).comp π.toLinearMap) with hΨ
  have hsurj : Function.Surjective Ψ :=
    surjective_traceTuple.comp (e.surjective.comp hπ)
  -- its kernel is exactly the `p`-radical
  have hkerΨ : LinearMap.ker Ψ = commutatorRadical (k := k) hp hA := by
    ext x
    rw [LinearMap.mem_ker]
    have hmem : Ψ x = 0 ↔ e (π x) ∈ commutatorSpan k (∀ i, Matrix (nn i) (nn i) k) := by
      rw [← ker_traceTuple (k := k) (nn := nn), LinearMap.mem_ker]
      rfl
    rw [hmem, ← commutatorRadical_matrixPi_eq hp hk]
    constructor
    · intro h
      refine mem_commutatorRadical_of_map_mem π hπ hp hA hB hker ?_
      have := map_mem_commutatorRadical e.symm.toAlgHom hp hC hB h
      simpa using this
    · intro h
      exact map_mem_commutatorRadical e.toAlgHom hp hB hC
        (map_mem_commutatorRadical π hp hA hB h)
  rw [← hkerΨ, (Ψ.quotKerEquivOfSurjective hsurj).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end OddOrder
