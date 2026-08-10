/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.FieldTheory.Finite.Trace

/-!
# Independence of power monomials on the unit group of a field

For a field `F` and an exponent `d`, the map `Fˣ → F`, `a ↦ aᵈ`, is a monoid homomorphism.
Dedekind's independence of characters therefore makes *distinct* power maps linearly independent
over `F`: a vanishing linear combination has zero coefficients.

Over a **finite** field this is the tool that converts "a polynomial function vanishes on `Fˣ`"
into "all its coefficients vanish", once the exponents involved are known to be pairwise
incongruent modulo `|Fˣ|`.  It is used for BG Appendix C, Problem 1 (issue 0180): the relation
lattice `L_e ≤ V³` spanned by the triples `(s, s^e, s^{e²})` is everything exactly when no
non-zero `(λ, μ, ν)` satisfies `Tr(λa + μa^e + νa^{e²}) = 0` for all `a`, and expanding the trace
turns that into a vanishing combination of the power monomials `a ↦ a^{d·3ʲ}` with
`d ∈ {1, e, e²}`.  Those exponents fall into three cosets of `⟨3⟩` in `(ZMod (|F| - 1))ˣ`, which
are pairwise disjoint precisely when `e ∉ ⟨3⟩` — whence all coefficients die.

## Main results

* `powHom` — the `d`-th power map `Fˣ →* F`.
* `powHom_ne_of_apply_ne` — a witness separating two exponents separates the two homomorphisms.
* `eq_zero_of_sum_powHom_eq_zero` — **the independence statement**.
-/

namespace OddOrder.PowerMonomial

variable {F : Type*} [Field F]

/-- The `d`-th power map on the units of `F`, viewed as a monoid homomorphism into `F`. -/
def powHom (F : Type*) [Field F] (d : ℕ) : Fˣ →* F :=
  (Units.coeHom F).comp (powMonoidHom d)

@[simp]
theorem powHom_apply (d : ℕ) (a : Fˣ) : powHom F d a = (a : F) ^ d := rfl

/-- Two power maps are different as soon as one unit separates the two exponents.  In practice one
takes `a` to be a generator of the (cyclic) unit group of a finite field, so that the criterion
becomes "the exponents are incongruent modulo `|Fˣ|`". -/
theorem powHom_ne_of_apply_ne {d d' : ℕ} (a : Fˣ) (h : (a : F) ^ d ≠ (a : F) ^ d') :
    powHom F d ≠ powHom F d' := fun hEq => h (by
  have := congrArg (fun f : Fˣ →* F => f a) hEq
  simpa using this)

/-- A single unit that separates the exponents separates the power maps.  Over a finite field one
takes `a` to be a generator of `Fˣ`, so the hypothesis says exactly that the exponents are
pairwise incongruent modulo `|Fˣ|`. -/
theorem injective_powHom_of_apply_injective {ι : Type*} (D : ι → ℕ) (a : Fˣ)
    (h : Function.Injective fun i => (a : F) ^ D i) :
    Function.Injective fun i => powHom F (D i) := fun i j hij => by
  refine h ?_
  have := congrArg (fun f : Fˣ →* F => f a) hij
  simpa using this

/-- **Independence of power monomials.**  Let `D : ι → ℕ` be a finite family of exponents whose
power maps are pairwise distinct.  If an `F`-linear combination of the corresponding monomials
vanishes at every unit of `F`, then every coefficient vanishes.

This is Dedekind's linear independence of characters (`linearIndependent_monoidHom`) applied to
the monoid homomorphisms `powHom F (D i) : Fˣ →* F`. -/
theorem eq_zero_of_sum_powHom_eq_zero {ι : Type*} [Fintype ι] (D : ι → ℕ)
    (hD : Function.Injective fun i => powHom F (D i)) (c : ι → F)
    (h : ∀ a : Fˣ, ∑ i, c i * (a : F) ^ D i = 0) : ∀ i, c i = 0 := by
  have hli : LinearIndependent F fun i => ⇑(powHom F (D i)) :=
    (linearIndependent_monoidHom Fˣ F).comp _ hD
  refine Fintype.linearIndependent_iff.mp hli c ?_
  funext a
  simpa [Finset.sum_apply] using h a

/-! ## Trace forms -/

section Trace

open Finset

variable {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F]

/-- **Lemma D, analytic core.**  Let `F / K` be an extension of finite fields, let `d : ι → ℕ` be
exponents and `c : ι → F` coefficients, and suppose the `K`-trace form

`a ↦ ∑ i, Tr_{F/K} (c i · a ^ d i)`

vanishes on every unit of `F`.  If the *expanded* exponent family `d i · |K| ^ j`
(`j < [F : K]`) consists of pairwise distinct power maps, then every coefficient `c i` is zero.

Expanding the trace as `Tr(x) = ∑_{j < [F:K]} x ^ (|K| ^ j)`
(`FiniteField.algebraMap_trace_eq_sum_pow`) turns the hypothesis into a vanishing `F`-linear
combination of the power monomials
`a ↦ a ^ (d i · |K| ^ j)`, and `eq_zero_of_sum_powHom_eq_zero` kills all of its coefficients
`c i ^ (|K| ^ j)`; the case `j = 0` is the conclusion.

For BG Appendix C, Problem 1 (issue 0180) this is applied with `K = 𝔽₃`, `ι = Fin 3`,
`d = ![1, e, e²]`: the expanded exponents are then the three cosets `⟨3⟩`, `e⟨3⟩`, `e²⟨3⟩` in
`(ZMod (|F| - 1))ˣ`, which are pairwise disjoint exactly when `e ∉ ⟨3⟩`. -/
theorem eq_zero_of_forall_trace_sum_eq_zero {ι : Type*} [Fintype ι] (d : ι → ℕ) (c : ι → F)
    (hD : Function.Injective fun x : ι × Fin (Module.finrank K F) =>
      powHom F (d x.1 * Nat.card K ^ (x.2 : ℕ)))
    (h : ∀ a : Fˣ, ∑ i, Algebra.trace K F (c i * (a : F) ^ d i) = 0) :
    ∀ i, c i = 0 := by
  have hfin : Module.Finite K F := Module.Finite.of_finite
  have hrpos : 0 < Module.finrank K F := Module.finrank_pos
  have key : ∀ a : Fˣ, ∑ x : ι × Fin (Module.finrank K F),
      c x.1 ^ (Nat.card K ^ (x.2 : ℕ)) * (a : F) ^ (d x.1 * Nat.card K ^ (x.2 : ℕ)) = 0 := by
    intro a
    have h0 := congrArg (algebraMap K F) (h a)
    rw [map_sum, map_zero] at h0
    rw [Fintype.sum_prod_type]
    refine h0 ▸ Finset.sum_congr rfl fun i _ => ?_
    rw [FiniteField.algebraMap_trace_eq_sum_pow, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_pow, ← pow_mul]
  intro i
  have h0 := eq_zero_of_sum_powHom_eq_zero _ hD _ key (i, ⟨0, hrpos⟩)
  simpa using h0

end Trace

end OddOrder.PowerMonomial
