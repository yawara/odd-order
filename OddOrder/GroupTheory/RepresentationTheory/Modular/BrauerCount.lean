/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import OddOrder.Algebra.BlockIdempotent
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
`p`-regular classes of `G`.  Since the blocks *are* the simple `kG`-modules
(`Algebra/PiMatrixSimpleModules`, via `J(kG)` annihilating them), this is **Brauer's theorem**
`|IBr(G)| = #{p`-regular classes`}`.

Over an *algebraically closed* `k` the splitting datum is produced here rather than assumed:
`kG` is finite-dimensional hence Artinian hence semiprimary, so `J(kG)` is nilpotent and
`kG ⧸ J(kG)` is semisimple, and mathlib's Artin–Wedderburn over an algebraically closed field
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`) splits the latter into matrix
algebras over `k`.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_split_blocks_eq_card_pRegularClass` — the count
  from an abstract splitting datum
* `OddOrder.RepresentationTheory.Modular.exists_wedderburn_pi_matrix_card_eq` — the datum,
  and hence the count, for an algebraically closed `k`
* `OddOrder.RepresentationTheory.Modular.exists_splitting_datum` — the full datum `hπ`/`hlin`/
  `hkerJ`/`hnil` that the block theory carries
* `OddOrder.RepresentationTheory.Modular.exists_surjective_blocks_card_eq` — the same, packaged
  as a surjection of `kG` with kernel `J(kG)`, which is the form the module classification of
  `Algebra/PiMatrixSimpleModules` consumes
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
of matrix algebras over `k` (`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`).
-/

/-- **Brauer's theorem.**  Over an algebraically closed field of characteristic `p`, the
semisimple quotient `kG ⧸ J(kG)` is a product of exactly `#{p`-regular classes of `G}` matrix
algebras over `k`.

The blocks correspond to the irreducible `kG`-modules — see
`exists_surjective_blocks_card_eq` for the packaging that makes that correspondence usable —
so this is `|IBr(G)| = #{p`-regular classes`}`. -/
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
  obtain ⟨n, d, hd, ⟨e'⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k
      (MonoidAlgebra k G ⧸ Ring.jacobson (MonoidAlgebra k G))
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

/-- **The full modular splitting datum** of `kG` over an algebraically closed field of
characteristic `p`: a surjective, `k`-linear ring map onto a product of `n` matrix algebras whose
kernel is exactly `J(kG)` and whose block character detects nilpotence, with `n` the number of
`p`-regular classes.

These are precisely the four hypotheses `hπ`, `hlin`, `hkerJ`, `hnil` that the block theory
carries everywhere.  Linearity comes from taking the quotient map as an *algebra* map
(`Ideal.Quotient.mkₐ`), and `hnil` from the nilpotence of `J(kG)` (`kG` is semiprimary): a central
element with vanishing block character lies in `ker π = J(kG)`, hence is nilpotent. -/
theorem exists_splitting_datum [IsAlgClosed k] (hp : p.Prime) (hk : (p : k) = 0) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i))
      (π : MonoidAlgebra k G →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k)
      (hπ : Function.Surjective π)
      (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a),
      RingHom.ker π = Ring.jacobson (MonoidAlgebra k G) ∧
      n = Nat.card {C : ConjClasses G // IsPRegularClass p C} ∧
      ∀ z : Subalgebra.center k (MonoidAlgebra k G),
        OddOrder.MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z := by
  classical
  haveI : IsArtinianRing (MonoidAlgebra k G) := isArtinian_of_tower k inferInstance
  obtain ⟨n, d, hd, ⟨e⟩, hn⟩ := exists_wedderburn_pi_matrix_card_eq (k := k) (G := G) hp hk
  haveI : ∀ i, NeZero (d i) := hd
  haveI : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (hd i).out⟩⟩
  set π : MonoidAlgebra k G →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k :=
    e.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra k G)))
    with hπdef
  have hπ : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a := by
    intro c a
    change e (Ideal.Quotient.mk _ (c • a)) = c • e (Ideal.Quotient.mk _ a)
    rw [show Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra k G)) (c • a)
        = c • Ideal.Quotient.mk (Ring.jacobson (MonoidAlgebra k G)) a from
      map_smul (Ideal.Quotient.mkₐ k (Ring.jacobson (MonoidAlgebra k G))) c a,
      map_smul]
  have hker : RingHom.ker π = Ring.jacobson (MonoidAlgebra k G) := by
    ext a
    simp only [hπdef, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨fun ha => e.injective (by simpa using ha), fun ha => by rw [ha]; simp⟩
  refine ⟨n, d, hd, π, hπ, hlin, hker, hn, ?_⟩
  intro z hz
  obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := MonoidAlgebra k G)
  have hz0 : (z : MonoidAlgebra k G) ∈ RingHom.ker π :=
    RingHom.mem_ker.mpr ((OddOrder.MatrixModule.blockCharacterPi_eq_zero_iff π hπ hlin).mp hz)
  rw [hker] at hz0
  have hpow := Ideal.pow_mem_pow hz0 N
  rw [hN] at hpow
  exact ⟨N, Subtype.ext (by simpa using hpow)⟩

/-- **Brauer's theorem, module form.**  Over an algebraically closed field of characteristic `p`
there is a surjection of `kG` onto a product of `n` matrix algebras whose kernel is exactly
`J(kG)`, with `n` the number of `p`-regular classes of `G`.

Since `J(kG)` annihilates every simple `kG`-module
(`IsSemisimpleModule.jacobson_le_annihilator`), the blocks of this surjection *are* the simple
`kG`-modules: each is simple (`MatrixModule.isSimpleModule_blockModule`), every simple module is
one of them (`MatrixModule.exists_linearEquiv_blockModule`), and no two coincide
(`PiModule.exists_unique_idem_smul_eq_self`).  So this is `|IBr(G)| = #{p`-regular classes`}`. -/
theorem exists_surjective_blocks_card_eq [IsAlgClosed k] (hp : p.Prime) (hk : (p : k) = 0) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i))
      (π : MonoidAlgebra k G →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k),
      Function.Surjective π ∧ RingHom.ker π = Ring.jacobson (MonoidAlgebra k G) ∧
      n = Nat.card {C : ConjClasses G // IsPRegularClass p C} := by
  obtain ⟨n, d, hd, π, hπ, -, hker, hn, -⟩ := exists_splitting_datum (k := k) (G := G) hp hk
  exact ⟨n, d, hd, π, hπ, hker, hn⟩

end OddOrder.RepresentationTheory.Modular
