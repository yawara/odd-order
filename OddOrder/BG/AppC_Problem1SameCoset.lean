/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.InverseClosedSubgroup
import OddOrder.BG.AppC_Problem1Trace

/-!
# BG Appendix C, Problem 1: the same-coset obstruction

`false_of_collisionPair_trace` refutes hypothesis (B) from a single collision whose normalised
values have a non-zero trace.  This file prepares the *trace-free* refutation available when the
two Paley points of the collision lie in one coset of the fixed subgroup of `z ↦ z ^ e`.

In that situation `K(p) = K(r)`, so the two normalised values coincide, `S = S'`, and relation (4)
degenerates from a conjugacy into a **commutation**

`[a(t), b(S t^e)] = 1`.

The set of `S` for which that holds for every `t` is an additive subgroup `commSubgroup` of
`𝔽_{3^q}`, and — this is the point — it is closed under `s ↦ (s ^ e)⁻¹`: conjugating the
commutation by `g²` turns the first layer into the third, and the factorisation
`d(u) = a(-u^e) · b(-u^{e²})` of `layerFieldHom_two_eq` cancels the first-layer factor because the
first layer is abelian.  Iterating three times (`e³ = 1` on the norm-one units) gives closure
under `s ↦ s⁻¹`, at which point `OddOrder.InverseClosed.pow_four_eq_one_or_forall_mem` applies.

## Main results

* `conjGen_pow_three` — `g³ = 1`.
* `conj_layerFieldHom_zero` / `conj_layerFieldHom_one` — conjugating by `g²` shifts layers.
* `commSubgroup` — the additive subgroup of admissible twists `s`.
* `mem_commSubgroup_inv_pow` — closure under `s ↦ (s ^ e)⁻¹`.
* `inv_mem_commSubgroup` — closure under inversion, the hypothesis of
  `OddOrder.InverseClosed.pow_four_eq_one_or_forall_mem`.
-/

namespace OddOrder.BG.AppC.Problem1

section SameCoset

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- `g = x^y` has order dividing three, because `x` does. -/
theorem conjGen_pow_three (data : FieldNormalizerData p q G) (hp : p = 3) :
    conjGen data ^ 3 = 1 := by
  have hx3 : data.s ^ 3 = 1 := by
    rw [← hp, FieldNormalizerData.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  rw [conjGen_def, ← map_pow, hx3, map_one]

/-- Conjugation preserves commutation. -/
private theorem commute_conj {H : Type*} [Group H] {a b : H} (h : Commute a b) (c : H) :
    Commute (c⁻¹ * a * c) (c⁻¹ * b * c) := by
  have e1 : (c⁻¹ * a * c) * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c := by group
  have e2 : (c⁻¹ * b * c) * (c⁻¹ * a * c) = c⁻¹ * (b * a) * c := by group
  unfold Commute SemiconjBy
  rw [e1, e2, h.eq]

/-- Conjugating the zeroth layer by `g²` gives the second. -/
theorem conj_layerFieldHom_zero (data : FieldNormalizerData p q G)
    (t : Multiplicative (GaloisField p q)) :
    (conjGen data ^ 2)⁻¹ * layerFieldHom data 0 t * conjGen data ^ 2
      = layerFieldHom data 2 t := by
  simp only [layerFieldHom_apply, pow_zero, inv_one, one_mul, mul_one]

/-- Conjugating the first layer by `g²` gives the zeroth, because `g³ = 1`. -/
theorem conj_layerFieldHom_one (data : FieldNormalizerData p q G) (hp : p = 3)
    (t : Multiplicative (GaloisField p q)) :
    (conjGen data ^ 2)⁻¹ * layerFieldHom data 1 t * conjGen data ^ 2
      = layerFieldHom data 0 t := by
  have h3 := conjGen_pow_three data hp
  simp only [layerFieldHom_apply, pow_zero, inv_one, one_mul, mul_one, pow_one]
  calc (conjGen data ^ 2)⁻¹ * ((conjGen data)⁻¹ * fieldHom data t * conjGen data)
        * conjGen data ^ 2
      = (conjGen data ^ 3)⁻¹ * fieldHom data t * conjGen data ^ 3 := by group
    _ = fieldHom data t := by rw [h3, inv_one, one_mul, mul_one]

/-- **The admissible twists.**  `s` belongs to this set when the first layer commutes with the
`s`-twisted second layer, `[a(t), b(s t^e)] = 1`, for *every* `t`. -/
def commSubgroup (data : FieldNormalizerData p q G) (e : ℕ) : AddSubgroup (GaloisField p q) where
  carrier := {s | ∀ t : GaloisField p q,
    Commute (layerFieldHom data 0 (Multiplicative.ofAdd t))
      (layerFieldHom data 1 (Multiplicative.ofAdd (s * t ^ e)))}
  zero_mem' := by
    intro t
    simp only [zero_mul, ofAdd_zero, map_one]
    exact Commute.one_right _
  add_mem' := by
    intro s s' hs hs' t
    have hsplit : (s + s') * t ^ e = s * t ^ e + s' * t ^ e := by ring
    rw [hsplit, ofAdd_add, map_mul]
    exact (hs t).mul_right (hs' t)
  neg_mem' := by
    intro s hs t
    have hneg : -s * t ^ e = -(s * t ^ e) := by ring
    rw [hneg, ofAdd_neg, map_inv]
    exact (hs t).inv_right

@[simp]
theorem mem_commSubgroup (data : FieldNormalizerData p q G) (e : ℕ) {s : GaloisField p q} :
    s ∈ commSubgroup data e ↔ ∀ t : GaloisField p q,
      Commute (layerFieldHom data 0 (Multiplicative.ofAdd t))
        (layerFieldHom data 1 (Multiplicative.ofAdd (s * t ^ e))) := Iff.rfl

/-- **Conjugating the commutation by `g²`.**  The first layer becomes the third and the second
becomes the first, so an admissible twist `s` also makes the *third* layer commute with the
`s`-twisted *first* layer. -/
theorem commute_two_zero_of_mem (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) (t : GaloisField p q) :
    Commute (layerFieldHom data 2 (Multiplicative.ofAdd t))
      (layerFieldHom data 0 (Multiplicative.ofAdd (s * t ^ e))) := by
  have hmap := commute_conj (hs t) (conjGen data ^ 2)
  rwa [conj_layerFieldHom_zero data, conj_layerFieldHom_one data hp] at hmap

/-- Cancellation for commutation: if `x * y` and `x` both commute with `z`, so does `y`. -/
private theorem commute_of_mul_left {H : Type*} [Group H] {x y z : H} (hxy : Commute (x * y) z)
    (hx : Commute x z) : Commute y z := by
  have h := hx.inv_left.mul_left hxy
  rwa [inv_mul_cancel_left] at h

/-- The zeroth layer is abelian, being the image of an abelian group. -/
private theorem commute_zero_zero (data : FieldNormalizerData p q G)
    (x y : Multiplicative (GaloisField p q)) :
    Commute (layerFieldHom data 0 x) (layerFieldHom data 0 y) :=
  (Commute.all x y).map _

/-- **The relation for twists supported on the norm-one classes.**  Conjugating the commutation by
`g²` and cancelling the abelian first-layer factor of `d(u) = a(-u^e) · b(-u^{e²})` turns an
admissible twist `s` into the twist `(s ^ e)⁻¹`, on the arguments `t = s · u^e`. -/
theorem commute_inv_pow_of_normOne (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) (u : NormSet.normOneUnits p q) :
    Commute (layerFieldHom data 0 (Multiplicative.ofAdd (s * normOneVal u ^ e)))
      (layerFieldHom data 1 (Multiplicative.ofAdd (normOneVal u ^ (e * e)))) := by
  have h2 := commute_two_zero_of_mem data hp hs (normOneVal u)
  rw [layerFieldHom_two_eq data hp hexp u] at h2
  simp only [normOneVal_pow] at h2
  have hcancel := commute_of_mul_left h2 (commute_zero_zero data _ _).inv_left
  have hfinal : Commute (layerFieldHom data 1
      (Multiplicative.ofAdd (normOneVal u ^ (e * e))))
      (layerFieldHom data 0 (Multiplicative.ofAdd (s * normOneVal u ^ e))) := by
    simpa using hcancel.inv_left
  exact hfinal.symm

/-- **Closure of the admissible twists under `s ↦ (s ^ e)⁻¹`.**

Every non-zero `t` is `± s · u^e` for a norm-one `u` (because `-1` is a non-square and `z ↦ z^e`
permutes the norm-one units), and on those arguments the previous lemma supplies exactly the
required commutation; the sign is absorbed because `e` is odd. -/
theorem mem_commSubgroup_inv_pow (data : FieldNormalizerData p q G) (hp : p = 3) (hq : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) (hs0 : s ≠ 0) :
    (s ^ e)⁻¹ ∈ commSubgroup data e := by
  classical
  subst hp
  letI : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  haveI : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have hcard : Fintype.card (GaloisField 3 q) = 3 ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 q hq
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  have h4 : Fintype.card (GaloisField 3 q) % 4 = 3 := by
    rw [hcard]
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    have hk : q = 2 * (q / 2) + 1 := by omega
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  -- the statement to be proved, at a single argument
  have hkey : ∀ v : GaloisField 3 q, IsSquare v → v ≠ 0 →
      Commute (layerFieldHom data 0 (Multiplicative.ofAdd (s * v)))
        (layerFieldHom data 1
          (Multiplicative.ofAdd ((s ^ e)⁻¹ * (s * v) ^ e))) := by
    intro v hvsq hv0
    -- `v` is norm-one, and `z ↦ z ^ e` is onto the norm-one units
    obtain ⟨u0, hu0⟩ : ∃ u0 : NormSet.normOneUnits 3 q, normOneVal u0 = v :=
      ⟨⟨Units.mk0 v hv0, (mem_normOneUnits_iff_isSquare rfl hq _).mpr (by simpa using hvsq)⟩, rfl⟩
    have hcube : normOneVal u0 ^ (e * e * e) = normOneVal u0 := by
      have hu := normOneUnits_pow_cube data rfl hexp u0
      calc normOneVal u0 ^ (e * e * e) = normOneVal (u0 ^ (e * e * e)) := by rw [normOneVal_pow]
        _ = normOneVal u0 := by rw [hu]
    have hue : normOneVal (u0 ^ (e * e)) ^ e = v := by
      rw [normOneVal_pow, ← pow_mul, hcube, hu0]
    have hue2 : normOneVal (u0 ^ (e * e)) ^ (e * e) = v ^ e := by
      have hexp4 : e * e * (e * e) = e * e * e * e := by ring
      rw [normOneVal_pow, ← pow_mul, hexp4, pow_mul, hcube, hu0]
    have hres := commute_inv_pow_of_normOne data rfl hexp hs (u0 ^ (e * e))
    rw [hue, hue2] at hres
    have harg : (s ^ e)⁻¹ * (s * v) ^ e = v ^ e := by
      rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hs0), one_mul]
    rw [harg]
    exact hres
  -- now every argument, by the square-class dichotomy
  have he0 : e ≠ 0 := by
    have := Nat.odd_iff.mp he
    omega
  intro t
  rcases eq_or_ne t 0 with rfl | ht0
  · simp [zero_pow he0]
  have hz0 : t * s⁻¹ ≠ 0 := mul_ne_zero ht0 (inv_ne_zero hs0)
  rcases Paley.isSquare_or_isSquare_neg hchar2 h4 hz0 with hsq | hnsq
  · have hv : s * (t * s⁻¹) = t := by
      rw [mul_comm t, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    have hcm := hkey (t * s⁻¹) hsq hz0
    rwa [hv] at hcm
  · have hv : s * -(t * s⁻¹) = -t := by
      rw [mul_neg, mul_comm t, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    have hcm := hkey (-(t * s⁻¹)) hnsq (neg_ne_zero.mpr hz0)
    rw [hv] at hcm
    have hb : (s ^ e)⁻¹ * (-t) ^ e = -((s ^ e)⁻¹ * t ^ e) := by
      rw [he.neg_pow]
      ring
    rw [hb, ofAdd_neg, map_inv, ofAdd_neg, map_inv] at hcm
    simpa using hcm.inv_inv

/-- **The admissible twists are closed under inversion.**  Iterating `s ↦ (s ^ e)⁻¹` three times
is `s ↦ (s ^ (e³))⁻¹ = s⁻¹`, since `e³` acts as the identity on the field.

This is the hypothesis of `OddOrder.InverseClosed.pow_four_eq_one_or_forall_mem`. -/
theorem inv_mem_commSubgroup (data : FieldNormalizerData p q G) (hp : p = 3) (hq : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) : s⁻¹ ∈ commSubgroup data e := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  have h1 := mem_commSubgroup_inv_pow data hp hq hqodd he hexp hs hs0
  have h1ne : (s ^ e)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hs0)
  have h2 := mem_commSubgroup_inv_pow data hp hq hqodd he hexp h1 h1ne
  have hx2 : (((s ^ e)⁻¹) ^ e)⁻¹ = s ^ (e * e) := by
    rw [inv_pow, inv_inv, ← pow_mul]
  rw [hx2] at h2
  have h2ne : s ^ (e * e) ≠ 0 := pow_ne_zero _ hs0
  have h3 := mem_commSubgroup_inv_pow data hp hq hqodd he hexp h2 h2ne
  have hx3 : ((s ^ (e * e)) ^ e)⁻¹ = s⁻¹ := by
    rw [← pow_mul, hcube]
  rwa [hx3] at h3

end SameCoset

end OddOrder.BG.AppC.Problem1
