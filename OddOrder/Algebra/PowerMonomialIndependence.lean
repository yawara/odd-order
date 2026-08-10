/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

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

end OddOrder.PowerMonomial
