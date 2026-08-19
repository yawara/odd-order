/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockIdempotent

/-!
# An algebra map on the centre is the character of a unique block

**Navarro (3.11).**  Every `k`-algebra homomorphism `λ : Z(A) →ₐ[k] k` is the central character
`blockCharacter c` of exactly one block `c`.

This is what makes the Brauer correspondence a map *between blocks*: the induced central
character `λ_b^G` of `TruncClassSum`, when it happens to be an algebra homomorphism, singles out
a block `b^G` of `G`.

The proof is the block decomposition of the identity.  The block idempotents `e_c` are a complete
orthogonal family, so their images `λ(e_c)` are orthogonal idempotents of the field `k` summing to
`1`: exactly one is `1`.  For that block `c₀` and any central `z`, the element
`z - ∑_c (blockCharacter c z) • e_c` is killed by every block character, hence nilpotent, hence
killed by `λ`; expanding gives `λ z = blockCharacter c₀ z`.

## Main results

* `OddOrder.MatrixModule.existsUnique_blockCharacter_eq`
* `OddOrder.MatrixModule.blockOfCentralCharacter` — the block it singles out
-/

namespace OddOrder.MatrixModule

open Matrix

variable {k ι : Type*} [Field k] [Finite ι] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable {A : Type*} [Ring A] [Algebra k A]
variable (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
  (hlin : ∀ (c : k) (a : A), π (c • a) = c • π a)

section

variable [Fintype (Block π hπ hlin)]

omit [Finite ι] in
/-- **Exactly one block idempotent survives an algebra map to `k`.**  The `λ(e_c)` are idempotents
of a field, pairwise annihilating and summing to `1`. -/
theorem existsUnique_blockIdempotent_map_eq_one
    {ee : Block π hπ hlin → Subalgebra.center k A} (hee : CompleteOrthogonalIdempotents ee)
    (lam : Subalgebra.center k A →ₐ[k] k) :
    ∃! c : Block π hπ hlin, lam (ee c) = 1 := by
  classical
  have hsum : ∑ c : Block π hπ hlin, lam (ee c) = 1 := by
    rw [← map_sum, hee.complete, map_one]
  obtain ⟨c₀, -, hc₀⟩ : ∃ c₀ ∈ Finset.univ, lam (ee c₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_congr rfl fun c hc => hcon c hc, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  have hone : lam (ee c₀) = 1 :=
    mul_right_cancel₀ hc₀ (by rw [← map_mul, hee.idem c₀, one_mul])
  refine ⟨c₀, hone, fun c hc => ?_⟩
  by_contra hne
  have hz := congrArg lam (hee.ortho hne)
  rw [map_mul, hc, hone, one_mul, map_zero] at hz
  exact one_ne_zero hz

end

/-- **Navarro (3.11)**: an algebra homomorphism `Z(A) →ₐ[k] k` is the central character of a
unique block. -/
theorem existsUnique_blockCharacter_eq
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x)
    (lam : Subalgebra.center k A →ₐ[k] k) :
    ∃! c : Block π hπ hlin, blockCharacter π hπ hlin c = lam := by
  classical
  have : Finite (Block π hπ hlin) := Quotient.finite _
  have : Fintype (Block π hπ hlin) := Fintype.ofFinite _
  obtain ⟨ee, hee, hval⟩ := exists_completeOrthogonalIdempotents_block π hπ hlin hnil
  obtain ⟨c₀, hc₀, hc₀uniq⟩ := existsUnique_blockIdempotent_map_eq_one π hπ hlin hee lam
  have hzero : ∀ c, c ≠ c₀ → lam (ee c) = 0 := fun c hc => by
    have hz := congrArg lam (hee.ortho hc)
    rwa [map_mul, hc₀, mul_one, map_zero] at hz
  have hlam : ∀ z : Subalgebra.center k A, lam z = blockCharacter π hπ hlin c₀ z := by
    intro z
    set w : Subalgebra.center k A := ∑ c, blockCharacter π hπ hlin c z • ee c with hw
    have hΦw : blockCharacterPi π hπ hlin w = blockCharacterPi π hπ hlin z := by
      funext c'
      rw [hw, map_sum]
      simp only [Finset.sum_apply, map_smul, hval, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ c' (fun c => blockCharacter π hπ hlin c z),
        if_pos (Finset.mem_univ _), blockCharacterPi_apply]
    have hlamzw : lam (z - w) = 0 := ((hnil _ (by rw [map_sub, hΦw, sub_self])).map lam).eq_zero
    have hlamw : lam w = blockCharacter π hπ hlin c₀ z := by
      rw [hw, map_sum]
      have hterm : ∀ c : Block π hπ hlin,
          lam (blockCharacter π hπ hlin c z • ee c)
            = if c = c₀ then blockCharacter π hπ hlin c₀ z else 0 := by
        intro c
        rw [map_smul, smul_eq_mul]
        by_cases h : c = c₀
        · rw [h, hc₀, mul_one, if_pos rfl]
        · rw [hzero c h, mul_zero, if_neg h]
      rw [Finset.sum_congr rfl fun c _ => hterm c,
        Finset.sum_ite_eq' Finset.univ c₀ (fun _ => blockCharacter π hπ hlin c₀ z),
        if_pos (Finset.mem_univ _)]
    have hsub : lam z - lam w = 0 := by rw [← map_sub]; exact hlamzw
    rw [sub_eq_zero.mp hsub]
    exact hlamw
  refine ⟨c₀, AlgHom.ext fun z => (hlam z).symm, fun c hc => ?_⟩
  have hcc : blockCharacter π hπ hlin c (ee c) = 1 := by
    rw [← blockCharacterPi_apply, hval c, Pi.single_eq_same]
  exact hc₀uniq c (hc ▸ hcc)

/-- **The block with a given central character.**  Well defined by
`existsUnique_blockCharacter_eq`. -/
noncomputable def blockOfCentralCharacter
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x)
    (lam : Subalgebra.center k A →ₐ[k] k) : Block π hπ hlin :=
  (existsUnique_blockCharacter_eq π hπ hlin hnil lam).choose

@[simp]
theorem blockCharacter_blockOfCentralCharacter
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x)
    (lam : Subalgebra.center k A →ₐ[k] k) :
    blockCharacter π hπ hlin (blockOfCentralCharacter π hπ hlin hnil lam) = lam :=
  (existsUnique_blockCharacter_eq π hπ hlin hnil lam).choose_spec.1

theorem eq_blockOfCentralCharacter
    (hnil : ∀ x : Subalgebra.center k A,
      blockCharacterPi π hπ hlin x = 0 → IsNilpotent x)
    {lam : Subalgebra.center k A →ₐ[k] k} {c : Block π hπ hlin}
    (hc : blockCharacter π hπ hlin c = lam) : c = blockOfCentralCharacter π hπ hlin hnil lam :=
  (existsUnique_blockCharacter_eq π hπ hlin hnil lam).choose_spec.2 c hc

end OddOrder.MatrixModule
