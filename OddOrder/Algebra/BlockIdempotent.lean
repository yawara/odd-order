/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Idempotents
import OddOrder.Algebra.CentralCharacter
import OddOrder.Algebra.SeparatingSubalgebra

/-!
# Block idempotents

The blocks of `A` are the classes of indices that the centre cannot separate
(`CentralCharacter`).  Passing to the quotient, the central characters give an algebra map

`Φ : Z(A) →ₐ[k] (blocks → k)`,

which is *surjective*: its image separates the blocks by construction, and a separating
subalgebra of a finite product of copies of a field is everything
(`Subalgebra.eq_top_of_separates`).  Since the kernel of the splitting is nil — for `A = kG` it
is `J(kG)` — the indicator of a block lifts uniquely to an idempotent of `Z(A)`: the **block
idempotent** `e_B`.

## Main results

* `OddOrder.MatrixModule.surjective_blockCharacterPi`
* `OddOrder.MatrixModule.existsUnique_blockIdempotent`
* `OddOrder.MatrixModule.blockIdempotent_ne_zero`
* `OddOrder.MatrixModule.eq_zero_or_eq_of_mul_eq_of_isIdempotentElem` — `e_B` is primitive
* `OddOrder.MatrixModule.exists_completeOrthogonalIdempotents_block`
* `OddOrder.MatrixModule.blockRingEquiv` — `A` is the product of its blocks
* `OddOrder.MatrixModule.existsUnique_block_smul_eq_self`
-/

namespace OddOrder.MatrixModule

open Matrix

variable {k ι : Type*} [Field k] [Finite ι] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable {A : Type*} [Ring A] [Algebra k A]
variable (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : A), π (c • a) = c • π a)

/-- **The block partition**: two indices are in the same block when the centre acts on them by
the same character. -/
def blockSetoid : Setoid ι where
  r i j := centralCharacterAlg π i hπ hlin = centralCharacterAlg π j hπ hlin
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The set of blocks of `A`. -/
abbrev Block : Type _ := Quotient (blockSetoid π hπ hlin)

/-- The central character of a block. -/
noncomputable def blockCharacter (c : Block π hπ hlin) : Subalgebra.center k A →ₐ[k] k :=
  Quotient.liftOn c (fun i => centralCharacterAlg π i hπ hlin) fun _ _ h => h

omit [Finite ι] in
@[simp]
theorem blockCharacter_mk (i : ι) :
    blockCharacter π hπ hlin (Quotient.mk (blockSetoid π hπ hlin) i)
      = centralCharacterAlg π i hπ hlin := rfl

/-- The central characters of all blocks, assembled. -/
noncomputable def blockCharacterPi :
    Subalgebra.center k A →ₐ[k] (Block π hπ hlin → k) :=
  Pi.algHom _ _ fun c => blockCharacter π hπ hlin c

omit [Finite ι] in
@[simp]
theorem blockCharacterPi_apply (z : Subalgebra.center k A) (c : Block π hπ hlin) :
    blockCharacterPi π hπ hlin z c = blockCharacter π hπ hlin c z := rfl

/-- **The central characters realise every function on the blocks.**  The image separates the
blocks by construction, and a separating subalgebra of `blocks → k` is everything. -/
theorem surjective_blockCharacterPi : Function.Surjective (blockCharacterPi π hπ hlin) := by
  haveI : Finite (Block π hπ hlin) := Quotient.finite _
  rw [← AlgHom.range_eq_top]
  refine Subalgebra.eq_top_of_separates fun c c' hcc => ?_
  induction c using Quotient.ind with | _ i =>
  induction c' using Quotient.ind with | _ j =>
  have hne : centralCharacterAlg π i hπ hlin ≠ centralCharacterAlg π j hπ hlin := fun h =>
    hcc (Quotient.sound h)
  obtain ⟨z, hz⟩ : ∃ z : Subalgebra.center k A,
      centralCharacterAlg π i hπ hlin z ≠ centralCharacterAlg π j hπ hlin z := by
    by_contra hcon
    push Not at hcon
    exact hne (AlgHom.ext hcon)
  exact ⟨blockCharacterPi π hπ hlin z, ⟨z, rfl⟩, hz⟩

omit [Finite ι] in
/-- **A central element is killed by all block characters exactly when the splitting kills it.**
So the nil-kernel hypothesis of `existsUnique_blockIdempotent` is implied by nilness of
`RingHom.ker π`, which is what `exists_algHom_pi_matrix_of_isAlgClosed` supplies. -/
theorem blockCharacterPi_eq_zero_iff {z : Subalgebra.center k A} :
    blockCharacterPi π hπ hlin z = 0 ↔ π (z : A) = 0 := by
  rw [← centralCharacterPi_eq_zero_iff π hπ ⟨(z : A), mem_center_of_mem_centerSubalgebra⟩]
  constructor
  · intro h
    funext i
    exact congrFun h (Quotient.mk (blockSetoid π hπ hlin) i)
  · intro h
    funext c
    induction c using Quotient.ind with | _ i =>
    exact congrFun h i

/-- **The block idempotents.**  If the kernel of the splitting is nil — for `A = kG` it is the
Jacobson radical — then the indicator of each block lifts uniquely to a central idempotent. -/
theorem existsUnique_blockIdempotent
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x)
    [DecidableEq (Block π hπ hlin)] (c : Block π hπ hlin) :
    ∃! e : Subalgebra.center k A,
      IsIdempotentElem e ∧ blockCharacterPi π hπ hlin e = Pi.single c 1 := by
  classical
  set f : Subalgebra.center k A →+* (Block π hπ hlin → k) :=
    (blockCharacterPi π hπ hlin).toRingHom with hf
  have hsurj : Function.Surjective f := surjective_blockCharacterPi π hπ hlin
  have hidem : IsIdempotentElem (Pi.single c 1 : Block π hπ hlin → k) := by
    funext d
    by_cases h : c = d
    · subst h; simp
    · simp [Pi.single_eq_of_ne (Ne.symm h)]
  exact existsUnique_isIdempotentElem_eq_of_ker_isNilpotent f
    (fun x hx => hnil x (RingHom.mem_ker.mp hx)) _ (hsurj _) hidem

omit [Finite ι] in
/-- **A block idempotent is nonzero**, since its central character on its own block is `1`. -/
theorem blockIdempotent_ne_zero [DecidableEq (Block π hπ hlin)] {c : Block π hπ hlin}
    {e : Subalgebra.center k A} (hec : blockCharacterPi π hπ hlin e = Pi.single c 1) :
    e ≠ 0 := by
  intro h
  rw [h, map_zero] at hec
  have hcc := congrFun hec c
  rw [Pi.single_eq_same] at hcc
  exact one_ne_zero hcc.symm

/-- **Block idempotents are primitive in the centre.**  A central idempotent `u` with
`e_B u = u` — a piece split off the block `B` — is either `0` or `e_B` itself.

The central characters see `u` as an idempotent of `blocks → k`, that is as an indicator
function, and `e_B u = u` confines its support to `B`.  So `Φ u` is `0` or the indicator of `B`;
in the first case `u` lies in the nil kernel and an idempotent there is `0`, in the second
uniqueness of the block idempotent gives `u = e_B`.

This is the primitivity hypothesis of `GroupAlgebra.exists_conj_eq_of_isDefectGroup`: it is what
makes the defect groups of a block a single conjugacy class. -/
theorem eq_zero_or_eq_of_mul_eq_of_isIdempotentElem
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x)
    [DecidableEq (Block π hπ hlin)] {c : Block π hπ hlin} {e : Subalgebra.center k A}
    (he : IsIdempotentElem e) (hec : blockCharacterPi π hπ hlin e = Pi.single c 1)
    {u : Subalgebra.center k A} (hu : IsIdempotentElem u) (heu : e * u = u) :
    u = 0 ∨ u = e := by
  classical
  -- `Φ u` is supported at `c`, because `Φ e = Pi.single c 1` kills every other coordinate.
  have hsupp : ∀ d, d ≠ c → blockCharacterPi π hπ hlin u d = 0 := by
    intro d hd
    have hmul : blockCharacterPi π hπ hlin e * blockCharacterPi π hπ hlin u
        = blockCharacterPi π hπ hlin u := by rw [← map_mul, heu]
    have := congrFun hmul d
    rwa [hec, Pi.mul_apply, Pi.single_eq_of_ne hd, zero_mul, eq_comm] at this
  -- And its value at `c` is an idempotent of the field `k`.
  have hidem : IsIdempotentElem (blockCharacterPi π hπ hlin u c) := by
    have h : blockCharacterPi π hπ hlin u * blockCharacterPi π hπ hlin u
        = blockCharacterPi π hπ hlin u := by rw [← map_mul, hu.eq]
    exact congrFun h c
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h0 | h1
  · refine Or.inl (eq_of_isNilpotent_sub_of_isIdempotentElem hu .zero ?_)
    refine (sub_zero u).symm ▸ hnil u (funext fun d => ?_)
    by_cases hd : d = c
    · subst hd; exact h0
    · exact hsupp d hd
  · refine Or.inr ((existsUnique_blockIdempotent π hπ hlin hnil c).unique ⟨hu, ?_⟩ ⟨he, hec⟩)
    funext d
    by_cases hd : d = c
    · subst hd; rw [h1, Pi.single_eq_same]
    · rw [hsupp d hd, Pi.single_eq_of_ne hd]

/-- **The block idempotents are a complete orthogonal family**: `∑_B e_B = 1` and
`e_B e_{B'} = 0` for `B ≠ B'`.  This is the block decomposition of the centre, and through it of
`A` itself. -/
theorem exists_completeOrthogonalIdempotents_block
    [Fintype (Block π hπ hlin)] [DecidableEq (Block π hπ hlin)]
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x) :
    ∃ e : Block π hπ hlin → Subalgebra.center k A,
      CompleteOrthogonalIdempotents e ∧
      ∀ c, blockCharacterPi π hπ hlin (e c) = Pi.single c 1 := by
  set f : Subalgebra.center k A →+* (Block π hπ hlin → k) :=
    (blockCharacterPi π hπ hlin).toRingHom with hf
  have hsurj : Function.Surjective f := surjective_blockCharacterPi π hπ hlin
  obtain ⟨e, he, hfe⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker f
    (fun x hx => hnil x (RingHom.mem_ker.mp hx))
    (CompleteOrthogonalIdempotents.single fun _ : Block π hπ hlin => k)
    (fun c => hsurj _)
  exact ⟨e, he, fun c => congrFun hfe c⟩

omit [Finite ι] in
/-- The block idempotents, viewed inside `A`. -/
theorem completeOrthogonalIdempotents_val [Fintype (Block π hπ hlin)]
    {ee : Block π hπ hlin → Subalgebra.center k A}
    (hee : CompleteOrthogonalIdempotents ee) :
    CompleteOrthogonalIdempotents fun c => (ee c : A) :=
  hee.map ((Subalgebra.center k A).val : Subalgebra.center k A →ₐ[k] A).toRingHom

omit [Finite ι] in
/-- **The block decomposition of `A`**: the algebra is the direct product of its blocks
`e_B A e_B`.  This is what makes block theory a genuine reduction — every question about
`A`-modules splits into independent questions, one per block. -/
noncomputable def blockRingEquiv [Fintype (Block π hπ hlin)]
    {ee : Block π hπ hlin → Subalgebra.center k A}
    (hee : CompleteOrthogonalIdempotents ee) :
    A ≃+* ∀ c : Block π hπ hlin,
      ((completeOrthogonalIdempotents_val π hπ hlin hee).idem c).Corner :=
  (completeOrthogonalIdempotents_val π hπ hlin hee).ringEquivOfIsMulCentral fun _ =>
    Set.mem_center_iff.mp mem_center_of_mem_centerSubalgebra

omit [Finite ι] in
/-- **Every simple `A`-module belongs to exactly one block**: exactly one block idempotent acts
on it as the identity, and the others act as zero. -/
theorem existsUnique_block_smul_eq_self [Fintype (Block π hπ hlin)]
    {ee : Block π hπ hlin → Subalgebra.center k A}
    (hee : CompleteOrthogonalIdempotents ee)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    ∃! c : Block π hπ hlin, ∀ s : M, (ee c : A) • s = s :=
  OddOrder.exists_unique_smul_eq_self_of_completeOrthogonal
    (hee.map ((Subalgebra.center k A).val : Subalgebra.center k A →ₐ[k] A).toRingHom)
    fun _ => mem_center_of_mem_centerSubalgebra

end OddOrder.MatrixModule
