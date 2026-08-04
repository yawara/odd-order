/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.CharP.Lemmas
import OddOrder.GroupTheory.RepresentationTheory.Modular.ConjugationLayers

/-!
# The twisted layer sum `s = ∑ ω^{-i} w_i`

**Navarro (5.7), the eigenvector.**  Once the witness `w` of (5.6) has been split into `p` layers
cyclically permuted by `h` (`ConjugationLayers`), Navarro forms

`s = ∑_{i=1}^p ω^{-i} w_i`,

where `ω` is a primitive `p`-th root of unity, and observes two things:

* `s^h = ω s` — so right multiplication by `s` shifts the `h`-eigenspaces of a module by `ω`;
* `s* = w*` — because `ω* = 1` in the residue field, whose characteristic is `p`.

Both are recorded here for an arbitrary family `v : ZMod p → R[G]` with `h • v i = v (i+1)`, so
that the family can be either the raw layers or their `f_b`-corners `f_b w_i f_b` (Navarro
replaces the former by the latter, which is what `twistedSum_corner` and `sum_corner` are for).

## Main results

* `OddOrder.GroupTheory.eq_one_of_pow_eq_one_expChar` — `ω* = 1`
* `OddOrder.GroupTheory.conj_smul_twistedSum` — `s^h = ω s`
* `OddOrder.GroupTheory.mapRingHom_twistedSum` — `s* = (∑ v i)*`
* `OddOrder.GroupTheory.sum_corner`, `OddOrder.GroupTheory.conj_smul_corner` — passing to
  `f · v i · f`
* `OddOrder.GroupTheory.exists_conj_eigen_corner` — the assembly: all three properties of `s`
-/

namespace OddOrder.GroupTheory

open scoped OddOrder.Conjugation

/-! ### `p`-th roots of unity in characteristic `p` -/

section RootOfUnity

variable {p : ℕ}

/-- **A `p`-th root of unity is `1` in characteristic `p`.**  Frobenius gives `(a - 1)^p = 0`, and
a field has no nilpotents.  This is Navarro's `ω* = 1`. -/
theorem eq_one_of_pow_eq_one_expChar {F : Type*} [Field F] [ExpChar F p] {a : F}
    (ha : a ^ p = 1) : a = 1 := by
  have hp0 : p ≠ 0 := (expChar_pos F p).ne'
  have h : (a - 1) ^ p = 0 := by rw [sub_pow_expChar, ha, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff hp0 |>.mp h)

variable {R : Type*} [CommRing R] {ζ : R}

/-- The exponent of a `p`-th root of unity only matters modulo `p`. -/
theorem pow_mod_eq_pow (hζ : ζ ^ p = 1) (a : ℕ) : ζ ^ (a % p) = ζ ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a p]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

/-- A `p`-th root of unity is exponentiated by `ZMod p`. -/
theorem pow_val_add [NeZero p] (hζ : ζ ^ p = 1) (i j : ZMod p) :
    ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val := by
  rw [ZMod.val_add, pow_mod_eq_pow hζ, pow_add]

end RootOfUnity

/-! ### The twisted sum -/

section TwistedSum

variable {R G : Type*} [CommRing R] [Group G] {p : ℕ} [NeZero p]

/-- **Navarro's `s = ∑_i ω^{-i} w_i`.** -/
noncomputable def twistedSum (p : ℕ) [NeZero p] (ζ : R) (v : ZMod p → MonoidAlgebra R G) :
    MonoidAlgebra R G :=
  ∑ i : ZMod p, ζ ^ (-i).val • v i

/-- **`s^h = ω s`.**  Conjugation shifts the family by one, which the twist turns into
multiplication by `ω`. -/
theorem conj_smul_twistedSum (hp : 1 < p) {ζ : R} (hζ : ζ ^ p = 1) {h : G}
    {v : ZMod p → MonoidAlgebra R G} (hv : ∀ i, h • v i = v (i + 1)) :
    h • twistedSum p ζ v = ζ • twistedSum p ζ v := by
  haveI : Fact (1 < p) := ⟨hp⟩
  rw [twistedSum, Finset.smul_sum, Finset.smul_sum]
  have hshift : ∀ i : ZMod p, h • (ζ ^ (-i).val • v i) = ζ ^ (-i).val • v (i + 1) := fun i => by
    rw [OddOrder.GroupAlgebra.conj_smul_smul, hv]
  rw [Finset.sum_congr rfl fun i _ => hshift i]
  refine (Fintype.sum_equiv (Equiv.addRight (1 : ZMod p))
    (fun i : ZMod p => ζ ^ (-i).val • v (i + 1))
    (fun j : ZMod p => ζ • (ζ ^ (-j).val • v j)) fun i => ?_)
  have hscal : ζ ^ (-i).val = ζ * ζ ^ (-(i + 1) : ZMod p).val := by
    have hidx : (-i : ZMod p) = 1 + (-(i + 1)) := by ring
    rw [hidx, pow_val_add hζ, ZMod.val_one, pow_one]
  simp only [Equiv.coe_addRight]
  rw [hscal, smul_smul]

/-- **`s* = (∑ v i)*`.**  Any coefficient map killing the twist — for `ω` a `p`-th root of unity
and the residue field of characteristic `p`, that is every one — collapses `s` to the plain sum. -/
theorem mapRingHom_twistedSum {F : Type*} [CommRing F] (φ : R →+* F) {ζ : R} (hφζ : φ ζ = 1)
    (v : ZMod p → MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G φ (twistedSum p ζ v)
      = MonoidAlgebra.mapRingHom G φ (∑ i : ZMod p, v i) := by
  have hsmul : ∀ (r : R) (x : MonoidAlgebra R G),
      MonoidAlgebra.mapRingHom G φ (r • x) = φ r • MonoidAlgebra.mapRingHom G φ x := by
    intro r x
    refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
    rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul_apply,
      MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_mapRingHom, smul_eq_mul, smul_eq_mul,
      map_mul]
  rw [twistedSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul, map_pow, hφζ, one_pow, one_smul]

/-! ### Passing to the corner `f · − · f` -/

variable {f : MonoidAlgebra R G} {v : ZMod p → MonoidAlgebra R G}

/-- The corners still add up to the corner of the sum. -/
theorem sum_corner : ∑ i : ZMod p, f * v i * f = f * (∑ i : ZMod p, v i) * f := by
  rw [Finset.mul_sum, Finset.sum_mul]

omit [NeZero p] in
/-- The corners are still shifted by conjugation, provided `f` is fixed. -/
theorem conj_smul_corner {h : G} (hf : h • f = f) (hv : ∀ i, h • v i = v (i + 1)) (i : ZMod p) :
    h • (f * v i * f) = f * v (i + 1) * f := by
  rw [smul_mul', smul_mul', hf, hv]

omit [NeZero p] in
/-- Each corner is its own corner. -/
theorem corner_idem (hf : f * f = f) (i : ZMod p) :
    f * (f * v i * f) * f = f * v i * f := by
  rw [← mul_assoc, ← mul_assoc, hf, mul_assoc, mul_assoc, hf, ← mul_assoc]

/-- **The twisted sum of the corners is a corner.**  This is Navarro's `f_b s f_b = s`, which is
what makes `(1 - f_B) s` land in the corner ring where (5.4) applies. -/
theorem corner_twistedSum (hf : f * f = f) (ζ : R) :
    f * twistedSum p ζ (fun i => f * v i * f) * f = twistedSum p ζ (fun i => f * v i * f) := by
  rw [twistedSum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, corner_idem hf]

end TwistedSum

/-! ### Assembly

Everything the algebraic half of Navarro (5.7) has to produce, in one statement. -/

section Assembly

variable {R G : Type*} [CommRing R] [Group G] [Fintype G] {p : ℕ} [NeZero p]

-- `Fintype G` is consumed by the layer decomposition inside the proof.
set_option linter.unusedFintypeInType false in
/-- **Navarro (5.7), the algebraic half.**  Let `h` be an element of finite order, `f` an
idempotent fixed by `h`, and `w` an element fixed by `h`, equal to its own `f`-corner, and
supported off `C_G(h_p)`.  Let `ζ` be a `p`-th root of unity whose residue is `1`.  Then there is
an `s` with

* `s^h = ζ s` — the eigenvector property, which shifts `h`-eigenspaces by `ζ`;
* `f s f = s` — so `s` lives in the corner ring where (5.4) applies;
* `s* = w*` — so (5.6.a) transfers to `s`, which is what makes `s` invertible enough to be
  injective on the module.

This is Navarro's `s = ∑_i ω^{-i} w_i` together with the three facts he checks about it. -/
theorem exists_conj_eigen_corner (hp : p.Prime) {ζ : R} (hζ : ζ ^ p = 1)
    {h : G} (hh : IsOfFinOrder h) {f w : MonoidAlgebra R G} (hf : f * f = f) (hfh : h • f = f)
    (hw : h • w = w) (hfw : f * w * f = w)
    (hsupp : ∀ x : G, w.coeff x ≠ 0 → ¬ Commute (pPart p h) x)
    {F : Type*} [CommRing F] (φ : R →+* F) (hφζ : φ ζ = 1) :
    ∃ s : MonoidAlgebra R G,
      h • s = ζ • s ∧ f * s * f = s ∧
        MonoidAlgebra.mapRingHom G φ s = MonoidAlgebra.mapRingHom G φ w := by
  classical
  refine ⟨twistedSum p ζ fun i => f * conjLayer p h w i * f, ?_, corner_twistedSum hf ζ, ?_⟩
  · exact conj_smul_twistedSum hp.one_lt hζ fun i =>
      conj_smul_corner hfh (fun j => conjLayer_conj_smul hp hh hw hsupp j) i
  · rw [mapRingHom_twistedSum φ hφζ, sum_corner, sum_conjLayer, hfw]

end Assembly

end OddOrder.GroupTheory
