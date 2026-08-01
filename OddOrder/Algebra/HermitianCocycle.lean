/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AnisotropicNormForm

/-!
# The Hermitian cocycle of a quadratic extension, corrected into the subfield

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, pp. 130–131.

For `E = 𝐅_{q²}` of characteristic `2` with subfield `F = 𝐅_q`, the unitary
coordinates of `PSU(3, q)` present the unipotent group as pairs `(a, b)` of elements of
`E` with `Tr b = a ā`, multiplying by `(a, b)(c, d) = (a + c, b + d + a c̄)`.  The
cocycle `a c̄` is `E`-valued, whereas Chapter III §3's model has a cocycle valued in
`F`.  The dictionary between the two corrects the second coordinate by the norm:

  `b ↦ b + u a ā` (`Tr u = 1`),

which lands in `F` and turns the `E`-valued cocycle `a c̄` into `a c̄ + u Tr(a c̄)`.

This file develops that over an arbitrary quadratic extension; the case
`E = ProjectiveUnitary.Field n` is
`OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.rootBilin`, where `x ↦ x^q` is
written `star`.

## Main results

* `OddOrder.FiniteField.frobPow_frobPow` — `x^{q²} = x`.
* `OddOrder.FiniteField.norm_mem_frobFixed` — the Hermitian norm `a ā` lies in `F`.
* `OddOrder.FiniteField.norm_cocycle` — the coboundary of `a ↦ u a ā` is `u Tr(a c̄)`.
* `OddOrder.FiniteField.hermitianCocycle` — the corrected cocycle `x ȳ + u Tr(x ȳ)`,
  as an `F`-valued bilinear map, with diagonal the norm
  (`hermitianCocycle_diag`).
-/

set_option autoImplicit false

namespace OddOrder.FiniteField

section HermitianCocycle

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E] (m : ℕ)

omit [Algebra (ZMod 2) E] in
/-- **The `q`-power map is an involution** on a field of order `q²`. -/
theorem frobPow_frobPow (hcard : Nat.card E = (2 ^ m) ^ 2) (x : E) :
    (x ^ 2 ^ m) ^ 2 ^ m = x := by
  have h := congrFun (congrArg (fun σ : RingAut E => (σ : E → E)) (qFrobenius_sq hcard)) x
  simpa only [RingAut.mul_apply, qFrobenius_apply, RingAut.one_apply] using
    (by
      have h2 : (qFrobenius E 2 m ^ 2) x = x := by
        rw [qFrobenius_sq hcard]; rfl
      rw [pow_two, RingAut.mul_apply, qFrobenius_apply, qFrobenius_apply] at h2
      exact h2)

omit [Algebra (ZMod 2) E] in
/-- **The Hermitian norm lands in `F`**: `(a ā)^q = ā a`. -/
theorem norm_mem_frobFixed (hcard : Nat.card E = (2 ^ m) ^ 2) (a : E) :
    a * a ^ 2 ^ m ∈ frobFixedSubfield E 2 m := by
  rw [mem_frobFixedSubfield, mul_pow, frobPow_frobPow m hcard]
  ring

/-- **The coboundary of `a ↦ u a ā` is the trace term**: expanding `(a+c)(ā+c̄)` leaves
`a c̄ + c ā = Tr (a c̄)`.  This is what turns the `E`-valued Hermitian cocycle into an
`F`-valued one. -/
theorem norm_cocycle (hcard : Nat.card E = (2 ^ m) ^ 2) (u a c : E) :
    u * (a * a ^ 2 ^ m) + u * (c * c ^ 2 ^ m)
        + u * ((a + c) * (a + c) ^ 2 ^ m)
      = u * frobTrace (E := E) m (a * c ^ 2 ^ m) := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hadd : (a + c) ^ 2 ^ m = a ^ 2 ^ m + c ^ 2 ^ m := by rw [add_pow_char_pow]
  rw [frobTrace_apply, hadd, mul_pow, frobPow_frobPow m hcard]
  linear_combination (u * (a * a ^ 2 ^ m) + u * (c * c ^ 2 ^ m)) * h2

/-! ## The corrected cocycle -/

/-- The Hermitian cocycle `(x, y) ↦ x ȳ`, as a `ZMod 2`-bilinear map. -/
noncomputable def hermitianBilin (m : ℕ) :
    LinearMap.BilinMap (ZMod 2) E E where
  toFun x :=
    { toFun := fun y => x * y ^ 2 ^ m
      map_add' := fun y y' => by rw [add_pow_char_pow, mul_add]
      map_smul' := fun c y => by
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with hc | hc <;> subst hc <;>
          simp }
  map_add' x x' := LinearMap.ext fun y => by simp [add_mul]
  map_smul' c x := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with hc | hc <;> subst hc <;>
      exact LinearMap.ext fun y => by simp

omit [Finite E] in
@[simp] theorem hermitianBilin_apply (x y : E) :
    hermitianBilin (E := E) m x y = x * y ^ 2 ^ m := rfl

/-- The trace correction `x ȳ + u Tr(x ȳ)` of the Hermitian cocycle: it has the same
diagonal and, when `Tr u = 1`, takes its values in `F`. -/
noncomputable def correctedBilin (m : ℕ) (u : E) :
    LinearMap.BilinMap (ZMod 2) E E :=
  hermitianBilin m + u • (hermitianBilin m).compr₂ (frobTrace (E := E) m)

@[simp] theorem correctedBilin_apply (u x y : E) :
    correctedBilin m u x y
      = x * y ^ 2 ^ m + u * frobTrace (E := E) m (x * y ^ 2 ^ m) := by
  simp only [correctedBilin, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.compr₂_apply, hermitianBilin_apply, smul_eq_mul]

/-- **The corrected cocycle is `F`-valued** when `Tr u = 1`. -/
theorem correctedBilin_mem (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (x y : E) :
    correctedBilin m u x y ∈ frobFixedSubfield E 2 m := by
  rw [← frobTrace_eq_zero_iff, correctedBilin_apply, map_add,
    mul_comm u (frobTrace (E := E) m (x * y ^ 2 ^ m)),
    frobTrace_mul_of_mem m (frobTrace_mem m hcard (x * y ^ 2 ^ m)) u, hu, mul_one]
  exact CharTwo.add_self_eq_zero _

/-- **The Hermitian cocycle of `E / F`**, corrected to take its values in `F`: the
cocycle of the unitary coordinates of `PSU(3, q)` in the shape that
`BilinearTwistedProduct` consumes. -/
noncomputable def hermitianCocycle (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) :
    LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m) :=
  bilinCodRestrict m (correctedBilin m u) (correctedBilin_mem m hcard hu)

@[simp] theorem hermitianCocycle_apply (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (x y : E) :
    ((hermitianCocycle m hcard hu x y : ↥(frobFixedSubfield E 2 m)) : E)
      = x * y ^ 2 ^ m + u * frobTrace (E := E) m (x * y ^ 2 ^ m) := by
  rw [hermitianCocycle]
  change correctedBilin m u x y = _
  rw [correctedBilin_apply]

/-- **The diagonal of the Hermitian cocycle is the norm**: the correction vanishes
there, since `a ā` already lies in `F`. -/
@[simp] theorem hermitianCocycle_diag (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (x : E) :
    ((hermitianCocycle m hcard hu x x : ↥(frobFixedSubfield E 2 m)) : E)
      = x * x ^ 2 ^ m := by
  rw [hermitianCocycle_apply,
    (frobTrace_eq_zero_iff m (x * x ^ 2 ^ m)).mpr (norm_mem_frobFixed m hcard x),
    mul_zero, add_zero]

/-- **The Hermitian cocycle scales by the norm**: `φ (d x) (d y) = d^{1+q} φ x y`.

This is the action of the torus of `PSU(3, q)` on the unipotent group,
`(x, y)^d = (d x, d^{1+q} y)`; the scalar `d^{1+q}` lies in `F`, which is why it passes
through the trace correction unchanged. -/
theorem hermitianCocycle_smul (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1) (d x y : E) :
    ((hermitianCocycle m hcard hu (d * x) (d * y) :
      ↥(frobFixedSubfield E 2 m)) : E)
      = d * d ^ 2 ^ m * ((hermitianCocycle m hcard hu x y :
        ↥(frobFixedSubfield E 2 m)) : E) := by
  have hsplit : (d * x) * (d * y) ^ 2 ^ m = (d * d ^ 2 ^ m) * (x * y ^ 2 ^ m) := by
    rw [mul_pow]
    ring
  rw [hermitianCocycle_apply, hermitianCocycle_apply, hsplit,
    frobTrace_mul_of_mem m (norm_mem_frobFixed m hcard d)]
  ring

/-! ## An anisotropic cocycle *is* the Hermitian one -/

/-- **A cocycle whose diagonal is a multiple of the norm is that multiple of the
Hermitian cocycle, for a suitable `u`** (Peterfalvi Part II, Ch. IV §3, p. 130).

This is sharper than matching the diagonals: it identifies the cocycles themselves, so
the comparison isomorphism is `congrEquiv` — a rescaling of the quotient coordinate
that leaves the centre alone and commutes with the scalar action.  Matching only the
diagonals would leave the freedom of an automorphism inducing the identity on both
ends, which does *not* commute with the scalar action.

The proof: `D x y := φ x y + c x ȳ` is `F`-bilinear with `D x x = 0`, hence alternating
and — in characteristic two — symmetric.  On the `F`-basis `1, w` given by an element
of trace one it therefore agrees with `β · Tr(x ȳ)`, where `β := D 1 w`.  Since `φ` is
`F`-valued, `Tr β = c`, so `u := β / c` has trace one. -/
theorem exists_hermitianCocycle_eq (hm : m ≠ 0) (hcard : Nat.card E = (2 ^ m) ^ 2)
    (φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m))
    (hsemi : ∀ a ∈ frobFixedSubfield E 2 m, ∀ b ∈ frobFixedSubfield E 2 m, ∀ x y : E,
      ((φ (a * x) (b * y) : ↥(frobFixedSubfield E 2 m)) : E)
        = a * b * ((φ x y : ↥(frobFixedSubfield E 2 m)) : E))
    (hc : ((φ 1 1 : ↥(frobFixedSubfield E 2 m)) : E) ≠ 0)
    (hdiag : ∀ x : E, ((φ x x : ↥(frobFixedSubfield E 2 m)) : E)
      = ((φ 1 1 : ↥(frobFixedSubfield E 2 m)) : E) * x ^ (2 ^ m + 1)) :
    ∃ u : E, frobTrace (E := E) m u = 1 ∧
      ∀ x y : E, ((φ x y : ↥(frobFixedSubfield E 2 m)) : E)
        = ((φ 1 1 : ↥(frobFixedSubfield E 2 m)) : E)
          * (x * y ^ 2 ^ m + u * frobTrace (E := E) m (x * y ^ 2 ^ m)) := by
  classical
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  set c : E := ((φ 1 1 : ↥(frobFixedSubfield E 2 m)) : E) with hcdef
  have hcF : c ∈ frobFixedSubfield E 2 m := (φ 1 1).2
  set D : E → E → E := fun x y => ((φ x y : ↥(frobFixedSubfield E 2 m)) : E)
    + c * (x * y ^ 2 ^ m) with hD
  set T : E → E → E := fun x y => frobTrace (E := E) m (x * y ^ 2 ^ m) with hT
  -- ### both pairings are `F`-bilinear
  have hDadd₁ : ∀ x x' y : E, D (x + x') y = D x y + D x' y := by
    intro x x' y
    simp only [hD, map_add, LinearMap.add_apply]
    push_cast
    ring
  have hDadd₂ : ∀ x y y' : E, D x (y + y') = D x y + D x y' := by
    intro x y y'
    have hpow : (y + y') ^ 2 ^ m = y ^ 2 ^ m + y' ^ 2 ^ m := by rw [add_pow_char_pow]
    simp only [hD, map_add, hpow]
    push_cast
    ring
  have hDsmul₁ : ∀ a ∈ frobFixedSubfield E 2 m, ∀ x y : E,
      D (a * x) y = a * D x y := by
    intro a ha x y
    have h := hsemi a ha 1 (one_mem _) x y
    rw [one_mul] at h
    simp only [hD, h]
    ring
  have hDsmul₂ : ∀ b ∈ frobFixedSubfield E 2 m, ∀ x y : E,
      D x (b * y) = b * D x y := by
    intro b hb x y
    have h := hsemi 1 (one_mem _) b hb x y
    rw [one_mul] at h
    have hbq : b ^ 2 ^ m = b := mem_frobFixedSubfield.mp hb
    simp only [hD, h, mul_pow, hbq]
    ring
  have hTadd₁ : ∀ x x' y : E, T (x + x') y = T x y + T x' y := by
    intro x x' y
    simp only [hT, add_mul, map_add]
  have hTadd₂ : ∀ x y y' : E, T x (y + y') = T x y + T x y' := by
    intro x y y'
    have hpow : (y + y') ^ 2 ^ m = y ^ 2 ^ m + y' ^ 2 ^ m := by rw [add_pow_char_pow]
    simp only [hT, hpow, mul_add, map_add]
  have hTsmul₁ : ∀ a ∈ frobFixedSubfield E 2 m, ∀ x y : E,
      T (a * x) y = a * T x y := by
    intro a ha x y
    simp only [hT, mul_assoc]
    exact frobTrace_mul_of_mem m ha _
  have hTsmul₂ : ∀ b ∈ frobFixedSubfield E 2 m, ∀ x y : E,
      T x (b * y) = b * T x y := by
    intro b hb x y
    have hbq : b ^ 2 ^ m = b := mem_frobFixedSubfield.mp hb
    have hval : x * (b * y) ^ 2 ^ m = b * (x * y ^ 2 ^ m) := by
      rw [mul_pow, hbq]
      ring
    simp only [hT, hval]
    exact frobTrace_mul_of_mem m hb _
  -- ### `D` is alternating, hence symmetric
  have hDself : ∀ x : E, D x x = 0 := by
    intro x
    simp only [hD, hdiag x, pow_succ]
    linear_combination (c * (x ^ 2 ^ m * x)) * h2
  have hDsymm : ∀ x y : E, D x y = D y x := by
    intro x y
    have h := hDself (x + y)
    rw [hDadd₁, hDadd₂, hDadd₂, hDself, hDself] at h
    linear_combination h - D y x * h2
  -- ### an element of trace one gives the `F`-basis `1, w`
  obtain ⟨w, hw⟩ := exists_frobTrace_eq_one (E := E) m hm hcard
  have hwq : w ^ 2 ^ m = w + 1 := by
    rw [frobTrace_apply] at hw
    linear_combination hw - w * h2
  have hwF : w ∉ frobFixedSubfield E 2 m := by
    intro hmem
    have hfix : w ^ 2 ^ m = w := mem_frobFixedSubfield.mp hmem
    rw [hfix] at hwq
    exact one_ne_zero (α := E) (by linear_combination -hwq)
  have hind : ∀ a b : E, a ∈ frobFixedSubfield E 2 m →
      b ∈ frobFixedSubfield E 2 m → a * 1 + b * w = 0 → a = 0 ∧ b = 0 := by
    intro a b ha hb hab
    by_cases hb0 : b = 0
    · subst hb0
      refine ⟨?_, rfl⟩
      simpa using hab
    · exfalso
      refine hwF ?_
      have hbw : b * w = a := by linear_combination hab - a * h2
      have hweq : w = b⁻¹ * a := by
        rw [← hbw, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
      rw [hweq]
      exact Subfield.mul_mem _ (Subfield.inv_mem _ hb) ha
  -- ### expansion of an `F`-bilinear pairing in these coordinates
  have expand : ∀ B : E → E → E,
      (∀ x x' y : E, B (x + x') y = B x y + B x' y) →
      (∀ x y y' : E, B x (y + y') = B x y + B x y') →
      (∀ a ∈ frobFixedSubfield E 2 m, ∀ x y : E, B (a * x) y = a * B x y) →
      (∀ b ∈ frobFixedSubfield E 2 m, ∀ x y : E, B x (b * y) = b * B x y) →
      ∀ a b a' b' : E, a ∈ frobFixedSubfield E 2 m → b ∈ frobFixedSubfield E 2 m →
        a' ∈ frobFixedSubfield E 2 m → b' ∈ frobFixedSubfield E 2 m →
        B (a * 1 + b * w) (a' * 1 + b' * w)
          = a * a' * B 1 1 + a * b' * B 1 w + b * a' * B w 1 + b * b' * B w w := by
    intro B hadd1 hadd2 hs1 hs2 a b a' b' ha hb ha' hb'
    have e1 : B (a * 1 + b * w) (a' * 1 + b' * w)
        = B (a * 1) (a' * 1) + B (a * 1) (b' * w)
          + (B (b * w) (a' * 1) + B (b * w) (b' * w)) := by
      rw [hadd1, hadd2, hadd2]
    have e2 : B (a * 1) (a' * 1) = a * a' * B 1 1 := by
      rw [hs1 a ha, hs2 a' ha']
      ring
    have e3 : B (a * 1) (b' * w) = a * b' * B 1 w := by
      rw [hs1 a ha, hs2 b' hb']
      ring
    have e4 : B (b * w) (a' * 1) = b * a' * B w 1 := by
      rw [hs1 b hb, hs2 a' ha']
      ring
    have e5 : B (b * w) (b' * w) = b * b' * B w w := by
      rw [hs1 b hb, hs2 b' hb']
      ring
    rw [e1, e2, e3, e4, e5]
    ring
  -- ### the four basis values
  have hwtr : w + w ^ 2 ^ m = 1 := by
    rw [frobTrace_apply] at hw
    exact hw
  have hTrwq : frobTrace (E := E) m (w ^ 2 ^ m) = 1 := by
    rw [frobTrace_apply, frobPow_frobPow m hcard]
    linear_combination hwtr
  have hT11 : T 1 1 = 0 := by
    simp only [hT, one_pow, mul_one, frobTrace_apply]
    linear_combination h2
  have hT1w : T 1 w = 1 := by
    simp only [hT, one_mul]
    exact hTrwq
  have hTw1 : T w 1 = 1 := by
    simp only [hT, one_pow, mul_one]
    exact hw
  have hTww : T w w = 0 := by
    simp only [hT]
    exact (frobTrace_eq_zero_iff m _).mpr (norm_mem_frobFixed m hcard w)
  set β : E := D 1 w with hβ
  have hDw1 : D w 1 = β := (hDsymm w 1).trans hβ.symm
  -- ### the two pairings agree
  have hkey : ∀ x y : E, D x y = β * T x y := by
    intro x y
    obtain ⟨p, hp⟩ := (frobCoordEquiv m hm hcard hind).surjective x
    obtain ⟨q, hq⟩ := (frobCoordEquiv m hm hcard hind).surjective y
    have hpval : (p.1 : E) * 1 + (p.2 : E) * w = x := hp
    have hqval : (q.1 : E) * 1 + (q.2 : E) * w = y := hq
    rw [← hpval, ← hqval,
      expand D hDadd₁ hDadd₂ hDsmul₁ hDsmul₂ _ _ _ _ p.1.2 p.2.2 q.1.2 q.2.2,
      expand T hTadd₁ hTadd₂ hTsmul₁ hTsmul₂ _ _ _ _ p.1.2 p.2.2 q.1.2 q.2.2,
      hDself 1, hDself w, hDw1, hT11, hT1w, hTw1, hTww]
    ring
  -- ### the trace of `β`
  have hTrβ : frobTrace (E := E) m β = c := by
    have hsplit : frobTrace (E := E) m β
        = frobTrace (E := E) m ((φ 1 w : ↥(frobFixedSubfield E 2 m)) : E)
          + frobTrace (E := E) m (c * (1 * w ^ 2 ^ m)) := by
      rw [hβ, hD]
      exact map_add _ _ _
    rw [hsplit, (frobTrace_eq_zero_iff m _).mpr (φ 1 w).2, zero_add, one_mul,
      frobTrace_mul_of_mem m hcF, hTrwq, mul_one]
  -- ### the parameter
  refine ⟨β * c⁻¹, ?_, fun x y => ?_⟩
  · rw [mul_comm, frobTrace_mul_of_mem m (Subfield.inv_mem _ hcF), hTrβ,
      inv_mul_cancel₀ hc]
  · have hval := hkey x y
    rw [hD] at hval
    have hβc : β = c * (β * c⁻¹) := by
      field_simp
    rw [hβc] at hval
    simp only [hT] at hval
    linear_combination hval - (c * (x * y ^ 2 ^ m)) * h2

end HermitianCocycle

end OddOrder.FiniteField
