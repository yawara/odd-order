/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import Mathlib.RepresentationTheory.Basic

/-!
# Reducibility of a faithful non-cyclic commutative representation over `𝔽_p`

`SingerField.isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible` says that a commutative
group acting faithfully and *irreducibly* on a finite `𝔽_p`-module is cyclic — it embeds in the
multiplicative group of the Singer field, which is cyclic.  Read contrapositively, a **non-cyclic**
commutative group cannot act faithfully and irreducibly:

* `Representation.faithful_asModule_of_injective` — the faithfulness bridge, turning
  `Function.Injective ρ` into the `MonoidAlgebra`-scalar form the Singer theorem consumes;
* `Representation.not_isSimpleModule_asModule_of_not_isCyclic` — the contrapositive itself.

Over an algebraically closed field this direction is Schur's lemma (a commutative group acts by
scalars, so an irreducible module is a line and *every* commutative group qualifies); over `𝔽_p`
it is genuinely a statement about `𝔽_{p^n}^×` being cyclic, which is why the Singer field is
needed.

The intended consumer is **BG Lemma 2.7** (`(ℤ/q)²` acting faithfully on `(ℤ/p)²`, `p ≠ q`): the
acting group is elementary abelian of rank `2`, hence non-cyclic, so the `2`-dimensional module
splits as a sum of two lines — the starting point of the eigenvalue analysis that produces
`q ∣ p - 1` and the power-map automorphism (issue 0150).
-/

namespace OddOrder.RepresentationTheory

open scoped MonoidAlgebra

universe u

variable {p : ℕ} [Fact p.Prime] {M : Type u} [AddCommGroup M] [Module (ZMod p) M] [Finite M]
variable {Q : Type u} [CommGroup Q] [Finite Q]

omit [Finite M] [Finite Q] in
/-- **Faithfulness bridge for the Singer theorems.**  An injective representation
`ρ : Representation (ZMod p) Q M` is faithful in the `MonoidAlgebra`-scalar sense used by
`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`: if `c` acts as the identity on
`ρ.asModule`, then `c = 1`.

`ρ.asModule` is a type synonym for `M` carrying the `MonoidAlgebra (ZMod p) Q`-action, and
`Representation.asModuleEquiv_symm_map_rho` identifies the scalar action of `of c` with applying
`ρ c`; injectivity of the equivalence then turns the fixed-point hypothesis into `ρ c = 1`. -/
theorem Representation.faithful_asModule_of_injective (ρ : Representation (ZMod p) Q M)
    (hfaith : Function.Injective ρ) :
    ∀ c : Q, (∀ x : ρ.asModule, (MonoidAlgebra.of (ZMod p) Q) c • x = x) → c = 1 := by
  intro c hc
  apply hfaith
  ext x
  have h := hc (ρ.asModuleEquiv.symm x)
  rw [← Representation.asModuleEquiv_symm_map_rho] at h
  have hx : (ρ c) x = x := ρ.asModuleEquiv.symm.injective h
  rw [hx, map_one]
  rfl

omit [Finite Q] in
/-- **A faithful representation of a non-cyclic commutative group over `𝔽_p` is reducible.**

Contrapositive of the Singer order bound
(`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`): were `ρ.asModule` simple, the
Singer field realization would embed `Q` into the cyclic group `𝔽_{p^n}^×`, forcing `Q` cyclic.

This is the reducibility input of BG Lemma 2.7 (issue 0150), where `Q ≅ (ℤ/q)²` is elementary
abelian of rank `2`. -/
theorem Representation.not_isSimpleModule_asModule_of_not_isCyclic
    (ρ : Representation (ZMod p) Q M) (hfaith : Function.Injective ρ) (hQ : ¬ IsCyclic Q) :
    ¬ IsSimpleModule (MonoidAlgebra (ZMod p) Q) ρ.asModule := by
  intro hsimple
  haveI : Finite ρ.asModule := inferInstanceAs (Finite M)
  exact hQ (isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible
    (p := p) (C := Q) (M := ρ.asModule)
    (Representation.faithful_asModule_of_injective ρ hfaith)).1

omit [Finite Q] in
/-- **A group of prime-square order and prime exponent is not cyclic.**  If `x ^ q = 1` for every
`x` in a group of order `q²` (`q` prime), no element can generate: a generator would have order
`q²`, but the exponent hypothesis bounds every order by `q`.

This is the rank-`2` elementary abelian hypothesis of BG Lemma 2.7 in the form
`Representation.not_isSimpleModule_asModule_of_not_isCyclic` consumes. -/
theorem not_isCyclic_of_exponent_of_card_sq {q : ℕ} (hq : q.Prime)
    (hQexp : ∀ x : Q, x ^ q = 1) (hQcard : Nat.card Q = q ^ 2) :
    ¬ IsCyclic Q := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have hdvd : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one (hQexp g)
  rw [hg, hQcard] at hdvd
  have hle := Nat.le_of_dvd hq.pos hdvd
  nlinarith [hq.two_le]

end OddOrder.RepresentationTheory
