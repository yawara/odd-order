/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Splitting a finite-dimensional algebra over an algebraically closed field

The block theory of `BlockIdempotent` — central characters, block idempotents, the block
decomposition — takes as its input a surjection

`π : A →ₐ[k] ∏_i M_{d_i}(k)` with nil kernel.

Over an algebraically closed field this input is free: a finite-dimensional algebra is Artinian,
so its Jacobson radical `J(A)` is nilpotent and `A / J(A)` is semisimple, and Wedderburn–Artin
over an algebraically closed field writes `A / J(A)` as a product of matrix algebras over `k`.

For `A = k[G]` with `G` finite this is exactly the setting of modular representation theory in
characteristic `p`, with `k` a large enough field: `k = 𝔽̄_p` is the residue field of the
`p`-modular system `𝕎(𝔽̄_p)`.

Over a merely *splitting* field — one where every simple module has endomorphism algebra `k` —
the same conclusion holds, but that needs Brauer's splitting field theorem to be checked for a
given `k`, so it is left as a hypothesis where it is needed.

## Main results

* `OddOrder.exists_algHom_pi_matrix_of_isAlgClosed`
-/

namespace OddOrder

/-- **A finite-dimensional algebra over an algebraically closed field surjects onto a product of
matrix algebras, with kernel exactly the Jacobson radical.**

This is the splitting datum that `BlockIdempotent` takes as a hypothesis, so it is what makes the
block decomposition — and with it Brauer's theorem on defect groups — unconditional over an
algebraically closed field.

The kernel is identified with `J(A)` and not merely shown to be nil, because the modular theory
asks for it in that exact form (`hkerJ`): the decomposition matrix and Navarro (5.11) are stated
relative to `RingHom.ker π = Ring.jacobson _`.  Nilness then follows, `J(A)` being nilpotent in an
Artinian ring. -/
theorem exists_algHom_pi_matrix_of_isAlgClosed (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i))
      (π : A →ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k),
      Function.Surjective π ∧
        RingHom.ker (π : A →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k) = Ring.jacobson A ∧
        ∀ x ∈ RingHom.ker (π : A →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k), IsNilpotent x := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨m, hm⟩ : IsNilpotent (Ring.jacobson A) := IsSemiprimaryRing.isNilpotent
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ Ring.jacobson A)
  -- The kernel is `J(A)` because `e` is injective.
  have hker : RingHom.ker ((e.toAlgHom.comp (Ideal.Quotient.mkₐ k (Ring.jacobson A)) :
      A →ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k) :
      A →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k) = Ring.jacobson A := by
    ext x
    constructor
    · intro hx
      have h0 : e (Ideal.Quotient.mk (Ring.jacobson A) x) = 0 := hx
      exact (Ideal.Quotient.eq_zero_iff_mem).mp (e.injective (by rw [h0, map_zero]))
    · intro hx
      change e (Ideal.Quotient.mk (Ring.jacobson A) x) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hx, map_zero]
  refine ⟨n, d, hd, e.toAlgHom.comp (Ideal.Quotient.mkₐ k (Ring.jacobson A)), ?_, hker, ?_⟩
  · exact e.surjective.comp Ideal.Quotient.mk_surjective
  · intro x hx
    -- `J(A) ^ m = ⊥`
    refine ⟨m, ?_⟩
    have hpow := Ideal.pow_mem_pow (hker ▸ hx) m
    rw [hm] at hpow
    simpa using hpow

end OddOrder
