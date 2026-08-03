/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import OddOrder.Algebra.SplitSemisimpleCount
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularCount

/-!
# Brauer's count: as many blocks as `p`-regular classes

Put the two halves together.  For a finite group `G` and a field `k` of characteristic `p`:

* `dim_k (kG ⧸ T') = #{p`-regular classes of `G}` — the `p`-regular classes are a basis of the
  quotient (`PRegularCount`);
* `dim_k (A ⧸ T') = #ι` whenever `A` has a split semisimple quotient `∏_{i ∈ ι} M_{n_i}(k)`
  reached by a surjection with uniformly nilpotent kernel (`SplitSemisimpleCount`).

Hence the number of matrix blocks of the split semisimple quotient of `kG` is the number of
`p`-regular classes of `G`.  This is **Brauer's theorem** `|IBr(G)| = #{p`-regular classes`}`,
modulo the (unformalised) uniqueness half of Artin–Wedderburn identifying blocks with
irreducible modules.

Over an *algebraically closed* `k` the splitting datum is produced here rather than assumed:
`kG` is finite-dimensional hence Artinian hence semiprimary, so `J(kG)` is nilpotent and
`kG ⧸ J(kG)` is semisimple, and Artin–Wedderburn splits the latter into matrix algebras over
finite-dimensional division algebras — which over an algebraically closed field are `k` itself.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_split_blocks_eq_card_pRegularClass` — the count
  from an abstract splitting datum
* `OddOrder.RepresentationTheory.Modular.exists_wedderburn_pi_matrix_card_eq` — the datum,
  and hence the count, for an algebraically closed `k`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.GroupTheory

variable {k G : Type*} [Field k] [Group G] [Finite G] {p : ℕ}

/-- **Brauer's count.**  If the group algebra `kG` (characteristic `p`) admits a surjection onto
a split semisimple algebra `∏_{i ∈ ι} M_{n_i}(k)` whose kernel is uniformly nilpotent — for
`k` a splitting field this is the reduction modulo `J(kG)` — then there are exactly as many
blocks as `p`-regular classes of `G`. -/
theorem card_split_blocks_eq_card_pRegularClass (hp : p.Prime) (hk : (p : k) = 0)
    {B : Type*} [Ring B] [Algebra k B] {ι : Type*} [Finite ι] {nn : ι → Type*}
    [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
    (π : MonoidAlgebra k G →ₐ[k] B) (hπ : Function.Surjective π)
    {N : ℕ} (hker : ∀ y : MonoidAlgebra k G, π y = 0 → y ^ N = 0)
    (e : B ≃ₐ[k] ∀ i, Matrix (nn i) (nn i) k) :
    Nat.card ι = Nat.card {C : ConjClasses G // IsPRegularClass p C} := by
  have hchar : ((p : ℕ) : MonoidAlgebra k G) = 0 := by
    rw [← map_natCast (algebraMap k (MonoidAlgebra k G)) p, hk, map_zero]
  have hB : ((p : ℕ) : B) = 0 := by rw [← map_natCast π p, hchar, map_zero]
  rw [← OddOrder.finrank_quotient_commutatorRadical_eq_card hp hk hchar hB π hπ hker e,
    finrank_quotient_commutatorRadical hp hchar]

/-! ### The splitting datum, over an algebraically closed field

Over an algebraically closed `k` the hypotheses of `card_split_blocks_eq_card_pRegularClass` are
automatic: `kG` is finite-dimensional, hence Artinian, hence semiprimary — so `J(kG)` is
nilpotent and `kG ⧸ J(kG)` is semisimple — and Artin–Wedderburn writes the latter as a product
of matrix algebras over finite-dimensional division algebras, each of which is `k` itself.
-/

/-- **Brauer's theorem.**  Over an algebraically closed field of characteristic `p`, the
semisimple quotient `kG ⧸ J(kG)` is a product of exactly `#{p`-regular classes of `G}` matrix
algebras over `k`.

By the uniqueness half of Artin–Wedderburn (not formalised here) the blocks correspond to the
irreducible `kG`-modules, so this is `|IBr(G)| = #{p`-regular classes`}`. -/
theorem exists_wedderburn_pi_matrix_card_eq [IsAlgClosed k] (hp : p.Prime) (hk : (p : k) = 0) :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty ((MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G))
        ≃ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k) ∧
      n = Nat.card {C : ConjClasses G // IsPRegularClass p C} := by
  classical
  haveI : IsArtinianRing (MonoidAlgebra k G) := isArtinian_of_tower k inferInstance
  haveI : Module.Finite k (MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective k _)
  obtain ⟨n, D, d, _, _, _, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite (R₀ := k)
      (R := MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G))
  -- a finite-dimensional division algebra over an algebraically closed field is the field
  have hDk : ∀ i, D i ≃ₐ[k] k := fun i =>
    (AlgEquiv.ofBijective (Algebra.ofId k (D i))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := D i))).symm
  have e' : (MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G))
      ≃ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k :=
    e.trans (AlgEquiv.piCongrRight fun i => (hDk i).mapMatrix)
  refine ⟨n, d, hd, ⟨e'⟩, ?_⟩
  -- the Jacobson radical is nilpotent, uniformly on elements
  obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := MonoidAlgebra k G)
  have hker : ∀ y : MonoidAlgebra k G,
      Ideal.Quotient.mkₐ k (Ring.jacobson (MonoidAlgebra k G)) y = 0 → y ^ N = 0 := by
    intro y hy
    have hyJ : y ∈ Ring.jacobson (MonoidAlgebra k G) := by
      rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
    have hpow := Ideal.pow_mem_pow hyJ N
    rw [hN] at hpow
    simpa using hpow
  haveI : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (hd i).out⟩⟩
  have hcount := card_split_blocks_eq_card_pRegularClass (k := k) (G := G) hp hk
    (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _) hker e'
  simpa using hcount

end OddOrder.RepresentationTheory.Modular
