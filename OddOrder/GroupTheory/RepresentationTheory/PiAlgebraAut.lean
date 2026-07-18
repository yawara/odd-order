/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Algebra automorphisms of `ι → k` permute the standard idempotents

For Peterfalvi (9.1)'s orbit-count Brauer lemma, the automorphism `σ` of `Z(𝔽̄_p[U]) ≅ 𝔽̄_p^N`
must permute the primitive-idempotent basis.  After transporting through the splitting
`Z ≅ (Fin N → k)`, this reduces to the **basis-free** fact proved here: any `k`-algebra
automorphism of `ι → k` (`ι` finite, `k` a field) sends each standard idempotent `Pi.single i 1`
to another, `Pi.single (π i) 1`, for a permutation `π` of `ι`.

The images `ε i := ψ (Pi.single i 1)` form a complete family of orthogonal idempotents.  Over a
field each coordinate is `0` or `1`; **orthogonality** (not the column sum, which is unreliable in
characteristic `p`) forces the supports to be pairwise disjoint, and they cover `ι` because the
family sums to `1`.  `|ι|` nonempty disjoint subsets covering an `|ι|`-set are all singletons, so
each `ε i` is a single standard idempotent.
-/

namespace OddOrder.GroupTheory.PiAlgebraAut

variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]

set_option linter.unusedFintypeInType false in
/-- **A `k`-algebra automorphism of `ι → k` permutes the standard idempotents.**  There is a
permutation `π` with `ψ (Pi.single i 1) = Pi.single (π i) 1` for every `i`. -/
theorem algEquiv_permutes_single (ψ : (ι → k) ≃ₐ[k] (ι → k)) :
    ∃ π : Equiv.Perm ι, ∀ i, ψ (Pi.single i (1 : k)) = Pi.single (π i) (1 : k) := by
  classical
  set ε : ι → (ι → k) := fun i => ψ (Pi.single i 1) with hε
  -- each `Pi.single i 1` is idempotent, hence so is its image `ε i`
  have hsingle_idem : ∀ i, (Pi.single i (1 : k) : ι → k) * Pi.single i 1 = Pi.single i 1 := by
    intro i; funext j; by_cases h : j = i <;> simp [h]
  have hidem : ∀ i, IsIdempotentElem (ε i) := by
    intro i
    change ψ (Pi.single i 1) * ψ (Pi.single i 1) = ψ (Pi.single i 1)
    rw [← map_mul, hsingle_idem i]
  -- each coordinate is `0` or `1`
  have hcoord : ∀ i j, ε i j = 0 ∨ ε i j = 1 := by
    intro i j
    refine IsIdempotentElem.iff_eq_zero_or_one.mp ?_
    have hj : (ε i * ε i) j = ε i j := congrFun (hidem i) j
    rwa [Pi.mul_apply] at hj
  -- supports
  set S : ι → Finset ι := fun i => Finset.univ.filter (fun j => ε i j = 1) with hS
  have hmem : ∀ i j, j ∈ S i ↔ ε i j = 1 := by
    intro i j; rw [hS]; simp
  -- nonzero ⟹ nonempty support
  have hsingle_ne : ∀ i, (Pi.single i (1 : k) : ι → k) ≠ 0 := by
    intro i hcon
    have h10 : (1 : k) = 0 := by simpa [Pi.single_apply] using congrFun hcon i
    exact one_ne_zero h10
  have hne : ∀ i, (S i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hz : ε i = 0 := by
      funext j
      rcases hcoord i j with h0 | h1
      · exact h0
      · exact absurd ((hmem i j).mpr h1) (hemp ▸ Finset.notMem_empty j)
    exact hsingle_ne i (ψ.injective (show ψ (Pi.single i (1 : k)) = ψ 0 by rw [map_zero]; exact hz))
  -- orthogonality ⟹ pairwise-disjoint supports
  have hortho : ∀ i i', i ≠ i' → ε i * ε i' = 0 := by
    intro i i' h
    change ψ (Pi.single i 1) * ψ (Pi.single i' 1) = 0
    rw [← map_mul]
    have hz : (Pi.single i (1 : k) : ι → k) * Pi.single i' 1 = 0 := by
      funext j; by_cases hj : j = i <;> by_cases hj' : j = i' <;> simp_all
    rw [hz, map_zero]
  have hdisj : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint S := by
    intro i _ i' _ h
    simp only [Function.onFun, Finset.disjoint_left]
    intro j hji hji'
    have hz := congrFun (hortho i i' h) j
    rw [Pi.mul_apply, (hmem i j).mp hji, (hmem i' j).mp hji', one_mul] at hz
    exact one_ne_zero hz
  -- sums to one ⟹ supports cover `ι`
  have hone : ∑ i, Pi.single i (1 : k) = (1 : ι → k) := by
    funext j; rw [Finset.sum_apply]; simp [Pi.single_apply, Finset.sum_ite_eq]
  have hsum : ∑ i, ε i = 1 := by
    change ∑ i, ψ (Pi.single i 1) = 1
    rw [← map_sum, hone, map_one]
  have hcover : (Finset.univ : Finset ι).biUnion S = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    rw [Finset.mem_biUnion]
    by_contra h
    have hnotin : ∀ i, j ∉ S i := fun i hi => h ⟨i, Finset.mem_univ i, hi⟩
    have hz : (∑ i, ε i) j = 0 := by
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hcoord i j with h0 | h1
      · exact h0
      · exact absurd ((hmem i j).mpr h1) (hnotin i)
    rw [hsum, Pi.one_apply] at hz
    exact one_ne_zero hz
  -- `|ι|` nonempty disjoint sets covering `ι` are singletons
  have hcard : ∑ i, (S i).card = Fintype.card ι := by
    rw [← Finset.card_biUnion hdisj, hcover, Finset.card_univ]
  have hge : ∀ i ∈ (Finset.univ : Finset ι), 1 ≤ (S i).card := fun i _ => (hne i).card_pos
  have hcard1 : ∀ i, (S i).card = 1 := by
    intro i₀
    by_contra h
    have hlt : (1 : ℕ) < (S i₀).card := by have := hge i₀ (Finset.mem_univ i₀); omega
    have hlt2 : (∑ _i : ι, (1 : ℕ)) < ∑ i, (S i).card :=
      Finset.sum_lt_sum hge ⟨i₀, Finset.mem_univ i₀, hlt⟩
    rw [hcard] at hlt2
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hlt2
    exact lt_irrefl _ hlt2
  -- read off the permutation
  choose π hπ using fun i => Finset.card_eq_one.mp (hcard1 i)
  have hπeq : ∀ i, ε i = Pi.single (π i) (1 : k) := by
    intro i; funext j
    by_cases hj : j = π i
    · have hjS : j ∈ S i := by rw [hπ i]; exact Finset.mem_singleton.mpr hj
      rw [(hmem i j).mp hjS, hj, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj]
      rcases hcoord i j with h0 | h1
      · exact h0
      · exact absurd ((hmem i j).mpr h1) (by rw [hπ i, Finset.mem_singleton]; exact hj)
  have hinj : Function.Injective π := by
    intro i i' h
    by_contra hii
    have hd : Disjoint (S i) (S i') := hdisj (Finset.mem_univ i) (Finset.mem_univ i') hii
    rw [hπ i, hπ i', h, Finset.disjoint_singleton] at hd
    exact hd rfl
  exact ⟨Equiv.ofBijective π ⟨hinj, Finite.surjective_of_injective hinj⟩, fun i => hπeq i⟩

omit [Fintype ι] in
/-- Standard idempotents in `ι → k` are determined by their index. -/
theorem single_one_inj {i j : ι} (h : (Pi.single i (1 : k) : ι → k) = Pi.single j 1) : i = j := by
  by_contra hij
  have hc := congrFun h i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at hc
  exact one_ne_zero hc

open scoped Classical in
/-- The coordinate permutation underlying an algebra automorphism of `ι → k`, as a **monoid
homomorphism** `((ι → k) ≃ₐ[k] (ι → k)) →* Equiv.Perm ι`.  The underlying permutation is the
(unique)
`π` with `ψ (Pi.single i 1) = Pi.single (π i) 1`; multiplicativity is forced by that uniqueness.
This makes `MulAut`-actions on the index set (the simples of a group algebra) genuine group actions. -/
noncomputable def algAutPerm : ((ι → k) ≃ₐ[k] (ι → k)) →* Equiv.Perm ι where
  toFun ψ := Classical.choose (algEquiv_permutes_single ψ)
  map_one' := by
    ext i
    refine single_one_inj (k := k) ?_
    rw [← Classical.choose_spec (algEquiv_permutes_single (1 : (ι → k) ≃ₐ[k] (ι → k))) i,
      AlgEquiv.one_apply, Equiv.Perm.one_apply]
  map_mul' ψ₁ ψ₂ := by
    ext i
    refine single_one_inj (k := k) ?_
    rw [← Classical.choose_spec (algEquiv_permutes_single (ψ₁ * ψ₂)) i, AlgEquiv.mul_apply,
      Classical.choose_spec (algEquiv_permutes_single ψ₂) i,
      Classical.choose_spec (algEquiv_permutes_single ψ₁) _, Equiv.Perm.mul_apply]

/-- Defining property of `algAutPerm`: `ψ` sends `Pi.single i 1` to `Pi.single (algAutPerm ψ i) 1`. -/
theorem algAutPerm_apply_single (ψ : (ι → k) ≃ₐ[k] (ι → k)) (i : ι) :
    ψ (Pi.single i (1 : k)) = Pi.single (algAutPerm ψ i) 1 := by
  classical exact Classical.choose_spec (algEquiv_permutes_single ψ) i

/-- The standard idempotents `Pi.single i 1` expand the identity: `∑ i, Pi.single i 1 = 1`. -/
theorem sum_single_one : ∑ i, Pi.single i (1 : k) = (1 : ι → k) := by
  funext j; rw [Finset.sum_apply]; simp [Pi.single_apply, Finset.sum_ite_eq]

/-- A vector is the sum of standard idempotents weighted by its own coordinates. -/
theorem eq_sum_smul_single (v : ι → k) : v = ∑ i, v i • (Pi.single i 1 : ι → k) := by
  funext j
  rw [Finset.sum_apply,
    Finset.sum_eq_single j (fun i _ hij => by simp [Pi.single_eq_of_ne (Ne.symm hij)]) fun h =>
      absurd (Finset.mem_univ j) h]
  simp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **A `k`-algebra homomorphism `(ι → k) →ₐ[k] k` is evaluation at a single index.**  The images
`f (Pi.single i 1)` form orthogonal `0/1` idempotents summing to `1` (over a field), so exactly one
is `1`; `f` then reads off that coordinate.  (For Peterfalvi (9.1): the central character of the
trivial module is such an evaluation, fixed by every automorphism — the trivial simple.) -/
theorem algHom_pi_eq_eval (f : (ι → k) →ₐ[k] k) : ∃ i₀, ∀ v : ι → k, f v = v i₀ := by
  classical
  -- `eᵢ := f (Pi.single i 1)` is idempotent in `k`, hence `0` or `1`.
  have h01 : ∀ i, f (Pi.single i (1 : k)) = 0 ∨ f (Pi.single i 1) = 1 := by
    intro i
    refine IsIdempotentElem.iff_eq_zero_or_one.mp ?_
    rw [IsIdempotentElem, ← map_mul]
    congr 1
    funext j; by_cases h : j = i <;> simp [h]
  -- distinct ones are orthogonal.
  have hortho : ∀ i j, i ≠ j → f (Pi.single i (1 : k)) * f (Pi.single j 1) = 0 := by
    intro i j hij
    rw [← map_mul, show (Pi.single i 1 : ι → k) * Pi.single j 1 = 0 from ?_, map_zero]
    funext l
    simp only [Pi.mul_apply, Pi.single_apply]
    by_cases hi : l = i <;> by_cases hj : l = j <;> simp_all
  -- they sum to `1`.
  have hsum : ∑ i, f (Pi.single i (1 : k)) = 1 := by
    rw [← map_sum, sum_single_one, map_one]
  -- some index has value `1` (else the sum would be `0`).
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, f (Pi.single i₀ (1 : k)) = 1 := by
    by_contra h
    have hall : ∀ i, f (Pi.single i (1 : k)) = 0 :=
      fun i => (h01 i).resolve_right fun hi => h ⟨i, hi⟩
    rw [Finset.sum_congr rfl fun i _ => hall i, Finset.sum_const_zero] at hsum
    exact one_ne_zero hsum.symm
  -- every other index has value `0` (orthogonal to the `1`).
  have hzero : ∀ j, j ≠ i₀ → f (Pi.single j (1 : k)) = 0 := by
    intro j hj
    have := hortho i₀ j (Ne.symm hj)
    rwa [hi₀, one_mul] at this
  refine ⟨i₀, fun v => ?_⟩
  have hfv : f v = ∑ i, v i * f (Pi.single i (1 : k)) := by
    conv_lhs => rw [eq_sum_smul_single v]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
  rw [hfv,
    Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)
      (fun j _ hj => by rw [hzero j hj, mul_zero]),
    hi₀, mul_one]

end OddOrder.GroupTheory.PiAlgebraAut
