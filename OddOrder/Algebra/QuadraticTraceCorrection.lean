/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.QuadraticFrobenius
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The relative trace of `𝐅_{q²}/𝐅_q`, and correcting a bilinear form into `𝐅_q`

For `E = 𝐅_{q²}` of characteristic `2` with fixed subfield `F = 𝐅_q` of the
`q`-power Frobenius, the relative trace is `Tr z = z + z^q`.  Its kernel is
exactly `F` (in characteristic `2`, `z + z^q = 0` says `z^q = z`) and its image
lies in `F`.

The point of this file is the *correction* lemma: a bilinear form
`φ : E × E → E` whose **diagonal** already takes values in `F` can be altered,
without changing that diagonal, into one taking **all** its values in `F`.  The
correction is `ψ = φ + u · (Tr ∘ φ)` for any `u` with `Tr u = 1`:

* `Tr ψ = Tr φ + Tr(u · Tr φ) = Tr φ + (Tr φ)(Tr u) = 0`, using that `Tr φ` lies
  in `F` and `Tr` is `F`-linear;
* on the diagonal `Tr (φ x x) = 0`, so nothing changes.

This is what makes the model of Peterfalvi Part II, Ch. III §3, p. 120 available:
the book's `S₁` is `E × F` with a cocycle `φ : E × E → F`, and the cocycle
produced by the Appendix III Lemma 2(c) expansion of `χ` is a priori only
`E`-valued.  The book instead reads `F`-valuedness off a symmetry of the
expansion coefficients (`λ_{μ̄ν̄} = λ̄_{μν}`); the correction below avoids that.

Crucially the correction preserves `F`-semilinearity: if
`φ (a x) (b y) = a b^θ φ x y` for `a, b ∈ F`, then `a b^θ` is fixed by the
Frobenius, so it passes through `Tr` and `ψ` obeys the same law.

## Main results

* `frobTrace` — the relative trace `z ↦ z + z^q`, as a `ZMod 2`-linear map.
* `frobTrace_eq_zero_iff` — its kernel is `F`; `frobTrace_mem` — its image is in `F`.
* `exists_frobTrace_eq_one` — `Tr` is nonzero, so some `u` has `Tr u = 1`.
* `exists_bilinear_frobFixed_of_diag` — the correction lemma.
-/

set_option autoImplicit false

namespace OddOrder.FiniteField

open Module

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E] (m : ℕ)

/-- The subfield `F = {x : x^q = x}` carries a `ZMod 2`-algebra structure, just as
`E` does.  Not derivable by instance search because `ZMod.algebra` is deliberately
a `def`; registered here so that `QuadraticMap (ZMod 2) E ↥F` and bilinear forms
into `F` can be written down. -/
noncomputable instance instAlgebraZModTwoFrobFixed {E' : Type*} [Field E'] [Finite E']
    [CharP E' 2] (n : ℕ) :
    Algebra (ZMod 2) ↥(frobFixedSubfield E' 2 n) :=
  ZMod.algebra _ 2

/-! ## The relative trace -/

/-- **The relative trace `Tr : E → E` of `E = 𝐅_{q²}` over `F = 𝐅_q`**, `z ↦ z + z^q`
(`q = 2^m`).  Additivity is free: `z ↦ z^q` is the ring automorphism `qFrobenius`. -/
noncomputable def frobTraceHom : E →+ E :=
  AddMonoidHom.id E + ((OddOrder.FiniteField.qFrobenius E 2 m).toRingHom : E →+* E).toAddMonoidHom

/-- The relative trace as a `ZMod 2`-linear map (every additive map between
`ZMod 2`-modules is linear). -/
noncomputable def frobTrace : E →ₗ[ZMod 2] E :=
  (frobTraceHom (E := E) m).toZModLinearMap 2

@[simp] theorem frobTrace_apply (z : E) : frobTrace (E := E) m z = z + z ^ 2 ^ m :=
  rfl

/-- **The kernel of the relative trace is `F`.**  In characteristic `2`,
`z + z^q = 0` says `z^q = z`. -/
theorem frobTrace_eq_zero_iff (z : E) :
    frobTrace (E := E) m z = 0 ↔ z ∈ OddOrder.FiniteField.frobFixedSubfield E 2 m := by
  rw [OddOrder.FiniteField.mem_frobFixedSubfield, frobTrace_apply]
  constructor
  · intro h
    have := (sub_eq_zero (a := z) (b := z ^ 2 ^ m)).mp (by rwa [CharTwo.sub_eq_add])
    exact this.symm
  · intro h
    rw [h]
    exact CharTwo.add_self_eq_zero z

/-- **The relative trace is `F`-linear**: an element of `F` pulls out. -/
theorem frobTrace_mul_of_mem {c : E}
    (hc : c ∈ OddOrder.FiniteField.frobFixedSubfield E 2 m) (z : E) :
    frobTrace (E := E) m (c * z) = c * frobTrace (E := E) m z := by
  have hcq : c ^ 2 ^ m = c := OddOrder.FiniteField.mem_frobFixedSubfield.mp hc
  simp only [frobTrace_apply, mul_pow, hcq]
  ring

/-- **The relative trace takes values in `F`**: `(z + z^q)^q = z^q + z^{q²} = z^q + z`,
using `z^{q²} = z` for `|E| = q²`. -/
theorem frobTrace_mem (hcard : Nat.card E = (2 ^ m) ^ 2) (z : E) :
    frobTrace (E := E) m z ∈ OddOrder.FiniteField.frobFixedSubfield E 2 m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype E := Fintype.ofFinite E
  have hcardF : Fintype.card E = 2 ^ (m + m) := by
    rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul]
    congr 1
    omega
  have hfull : ∀ w : E, w ^ 2 ^ (m + m) = w := by
    intro w
    rw [← hcardF]
    exact FiniteField.pow_card w
  rw [OddOrder.FiniteField.mem_frobFixedSubfield, frobTrace_apply,
    add_pow_char_pow, ← pow_mul, ← pow_add, hfull z]
  exact add_comm _ _

/-- **The relative trace is onto `F`**, in the only form needed: some `u` has
`Tr u = 1`.  If `Tr` vanished identically then every element of `E` would lie in
`F`, contradicting `|F| = q < q² = |E|`; rescaling a witness by the inverse of its
(nonzero, `F`-valued) trace normalizes it. -/
theorem exists_frobTrace_eq_one (hm : m ≠ 0) (hcard : Nat.card E = (2 ^ m) ^ 2) :
    ∃ u : E, frobTrace (E := E) m u = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ : ∃ e : E, frobTrace (E := E) m e ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ e : E, e ∈ OddOrder.FiniteField.frobFixedSubfield E 2 m := fun e =>
      (frobTrace_eq_zero_iff m e).mp (hcon e)
    have hcards : Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield E 2 m) = Nat.card E :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [OddOrder.FiniteField.natCard_frobFixedSubfield hcard hm, hcard] at hcards
    have h2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (Nat.pos_of_ne_zero hm)
    nlinarith [hcards, h2]
  have hmem := frobTrace_mem m hcard e
  refine ⟨(frobTrace (E := E) m e)⁻¹ * e, ?_⟩
  rw [frobTrace_mul_of_mem m (Subfield.inv_mem _ hmem) e]
  exact inv_mul_cancel₀ he

/-- **Corestrict an `F`-valued bilinear form on `E` to a bilinear form into `F`.**

Needed because the model `S₁` of Peterfalvi Part II, Ch. III §3 has kernel `F`, so
its cocycle must be typed as a form into `F`, while the correction above produces
one typed into `E` that happens to take values in `F`. -/
noncomputable def bilinCodRestrict (ψ : LinearMap.BilinMap (ZMod 2) E E)
    (h : ∀ x y : E, ψ x y ∈ OddOrder.FiniteField.frobFixedSubfield E 2 m) :
    LinearMap.BilinMap (ZMod 2) E ↥(OddOrder.FiniteField.frobFixedSubfield E 2 m) where
  toFun x :=
    { toFun := fun y => ⟨ψ x y, h x y⟩
      map_add' := fun y y' => Subtype.ext (by simp)
      map_smul' := fun c y => by
        refine Subtype.ext ?_
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with hc | hc <;> subst hc <;> simp }
  map_add' x x' := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    simp
  map_smul' c x := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with hc | hc <;> subst hc <;> simp

@[simp] theorem bilinCodRestrict_apply (ψ : LinearMap.BilinMap (ZMod 2) E E)
    (h : ∀ x y : E, ψ x y ∈ OddOrder.FiniteField.frobFixedSubfield E 2 m) (x y : E) :
    ((bilinCodRestrict m ψ h x y :
      ↥(OddOrder.FiniteField.frobFixedSubfield E 2 m)) : E) = ψ x y :=
  rfl

/-! ## Correcting a bilinear form into `F` -/

/-- **A bilinear form whose diagonal lies in `F` can be corrected to be `F`-valued**,
without changing the diagonal.

The correction is `ψ = φ + u · (Tr ∘ φ)` with `Tr u = 1`.  The explicit formula is
part of the conclusion because the consumer needs it: any scaling law
`φ (a x) (b y) = c · φ x y` with `c ∈ F` is inherited by `ψ`, since `c` then passes
through `Tr`.

Peterfalvi Part II, Ch. III §3, p. 121, step (3): this turns the `E`-valued
bilinear lift of `χ` coming from the Appendix III Lemma 2(c) expansion into the
`F`-valued cocycle `φ` of the Proposition, whose model `S₁` has kernel `F`. -/
theorem exists_bilinear_frobFixed_of_diag (hm : m ≠ 0) (hcard : Nat.card E = (2 ^ m) ^ 2)
    (φ : LinearMap.BilinMap (ZMod 2) E E)
    (hdiag : ∀ x : E, φ x x ∈ OddOrder.FiniteField.frobFixedSubfield E 2 m) :
    ∃ (u : E) (ψ : LinearMap.BilinMap (ZMod 2) E E),
      (∀ x y : E, ψ x y = φ x y + u * frobTrace (E := E) m (φ x y)) ∧
      (∀ x y : E, ψ x y ∈ OddOrder.FiniteField.frobFixedSubfield E 2 m) ∧
      ∀ x : E, ψ x x = φ x x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : SMulCommClass E (ZMod 2) E := SMulCommClass.symm _ _ _
  obtain ⟨u, hu⟩ := exists_frobTrace_eq_one (E := E) m hm hcard
  refine ⟨u, φ + u • φ.compr₂ (frobTrace (E := E) m), fun x y => ?_, fun x y => ?_, fun x => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compr₂_apply,
      smul_eq_mul]
  · -- `Tr ψ = Tr φ + (Tr φ) · (Tr u) = 0`
    have hval : (φ + u • φ.compr₂ (frobTrace (E := E) m)) x y
        = φ x y + u * frobTrace (E := E) m (φ x y) := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compr₂_apply,
        smul_eq_mul]
    rw [← frobTrace_eq_zero_iff, hval, map_add]
    rw [mul_comm u (frobTrace (E := E) m (φ x y)),
      frobTrace_mul_of_mem m (frobTrace_mem m hcard (φ x y)) u, hu, mul_one]
    exact CharTwo.add_self_eq_zero _
  · have hval : (φ + u • φ.compr₂ (frobTrace (E := E) m)) x x
        = φ x x + u * frobTrace (E := E) m (φ x x) := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compr₂_apply,
        smul_eq_mul]
    rw [hval, (frobTrace_eq_zero_iff m (φ x x)).mpr (hdiag x), mul_zero, add_zero]

end OddOrder.FiniteField
