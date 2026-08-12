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
* `mem_commSubgroup_of_square` — one square class of arguments suffices.
* `mem_commSubgroup_inv_pow` — closure under `s ↦ (s ^ e)⁻¹`.
* `inv_mem_commSubgroup` — closure under inversion, the hypothesis of
  `OddOrder.InverseClosed.pow_four_eq_one_or_forall_mem`.
* `mem_commSubgroup_of_collisionPair` — a collision with `S = S'` is an admissible twist.
* `false_of_collisionPair_self` — **Theorem B**: such a collision refutes hypothesis (B), with no
  assumption on the trace.
* `false_of_sameCoset_pair` — **the certificate form**: two distinct Paley points scaled by one and
  the same factor under `z ↦ z ^ e` refute hypothesis (B).
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

/-- **One square class suffices.**  If the defining commutation of `commSubgroup` holds at every
argument `c * v` with `v` a non-zero square, it holds everywhere: every non-zero `t` is `c * v` or
`-(c * v)` for such a `v` (as `-1` is a non-square), and the sign is absorbed because `e` is odd. -/
theorem mem_commSubgroup_of_square (data : FieldNormalizerData p q G) (hp : p = 3) (hq : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (he : Odd e) {c s : GaloisField p q} (hc0 : c ≠ 0)
    (hkey : ∀ v : GaloisField p q, IsSquare v → v ≠ 0 →
      Commute (layerFieldHom data 0 (Multiplicative.ofAdd (c * v)))
        (layerFieldHom data 1 (Multiplicative.ofAdd (s * (c * v) ^ e)))) :
    s ∈ commSubgroup data e := by
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
  have he0 : e ≠ 0 := by
    have := Nat.odd_iff.mp he
    omega
  intro t
  rcases eq_or_ne t 0 with rfl | ht0
  · simp [zero_pow he0]
  have hz0 : t * c⁻¹ ≠ 0 := mul_ne_zero ht0 (inv_ne_zero hc0)
  rcases Paley.isSquare_or_isSquare_neg hchar2 h4 hz0 with hsq | hnsq
  · have hv : c * (t * c⁻¹) = t := by
      rw [mul_comm t, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hcm := hkey (t * c⁻¹) hsq hz0
    rwa [hv] at hcm
  · have hv : c * -(t * c⁻¹) = -t := by
      rw [mul_neg, mul_comm t, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hcm := hkey (-(t * c⁻¹)) hnsq (neg_ne_zero.mpr hz0)
    rw [hv] at hcm
    have hb : s * (-t) ^ e = -(s * t ^ e) := by
      rw [he.neg_pow]
      ring
    rw [hb, ofAdd_neg, map_inv, ofAdd_neg, map_inv] at hcm
    simpa using hcm.inv_inv

/-- **Closure of the admissible twists under `s ↦ (s ^ e)⁻¹`.**

On the arguments `t = s · u^e` with `u` norm-one this is `commute_inv_pow_of_normOne`; the previous
lemma extends it to every `t`. -/
theorem mem_commSubgroup_inv_pow (data : FieldNormalizerData p q G) (hp : p = 3) (hq : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) (hs0 : s ≠ 0) :
    (s ^ e)⁻¹ ∈ commSubgroup data e := by
  refine mem_commSubgroup_of_square data hp hq hqodd he hs0 ?_
  intro v hvsq hv0
  subst hp
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

/-- **A collision with equal normalised values is an admissible twist.**

When `S = S'` — equivalently `K(p) = K(r)`, which is what "the two Paley points lie in one coset
of the fixed subgroup" gives — relation (4) of `layerFieldHom_one_conj` says that `a(δ z^e)`
*commutes with* `b(K z^{e²})` instead of merely conjugating one second-layer element to another.
Since `S · δ^e = K`, that is exactly the defining condition of `commSubgroup` at the arguments
`δ v` with `v` a non-zero square. -/
theorem mem_commSubgroup_of_collisionPair (data : FieldNormalizerData p q G) (hp : p = 3)
    (hq : q ≠ 0) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S : GaloisField p q} (hpair : CollisionPair p q e S S) : S ∈ commSubgroup data e := by
  obtain ⟨p₀, p₁, r₀, r₁, d₀, hpp, hrr, hcoll, hd, hS, hS'⟩ := hpair
  set Z : GaloisField p q := normOneVal (d₀⁻¹ ^ (e * e)) ^ (e * e) with hZ
  have hZ0 : Z ≠ 0 := by
    rw [hZ]
    exact pow_ne_zero _ (Units.ne_zero _)
  have hKeq : normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)
      = normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e) :=
    mul_right_cancel₀ hZ0 (hS.symm.trans hS')
  have hd0 : normOneVal d₀ ≠ 0 := Units.ne_zero _
  refine mem_commSubgroup_of_square data hp hq hqodd he hd0 ?_
  intro v hvsq hv0
  subst hp
  obtain ⟨u0, hu0⟩ : ∃ u0 : NormSet.normOneUnits 3 q, normOneVal u0 = v :=
    ⟨⟨Units.mk0 v hv0, (mem_normOneUnits_iff_isSquare rfl hq _).mpr (by simpa using hvsq)⟩, rfl⟩
  have hcubev : normOneVal u0 ^ (e * e * e) = normOneVal u0 := by
    have hu := normOneUnits_pow_cube data rfl hexp u0
    calc normOneVal u0 ^ (e * e * e) = normOneVal (u0 ^ (e * e * e)) := by rw [normOneVal_pow]
      _ = normOneVal u0 := by rw [hu]
  have hue : normOneVal (u0 ^ (e * e)) ^ e = v := by
    rw [normOneVal_pow, ← pow_mul, hcubev, hu0]
  have hue2 : normOneVal (u0 ^ (e * e)) ^ (e * e) = v ^ e := by
    have hexp4 : e * e * (e * e) = e * e * e * e := by ring
    rw [normOneVal_pow, ← pow_mul, hexp4, pow_mul, hcubev, hu0]
  -- `S · δ^e = K`
  have hdcube : normOneVal d₀ ^ (e * e * e) = normOneVal d₀ := by
    have hu := normOneUnits_pow_cube data rfl hexp d₀
    calc normOneVal d₀ ^ (e * e * e) = normOneVal (d₀ ^ (e * e * e)) := by rw [normOneVal_pow]
      _ = normOneVal d₀ := by rw [hu]
  have hZval : Z * normOneVal d₀ ^ e = 1 := by
    have hexp4 : e * e * (e * e) = e * e * e * e := by ring
    rw [hZ, normOneVal_pow, normOneVal_inv, ← pow_mul, inv_pow, hexp4, pow_mul, hdcube]
    exact inv_mul_cancel₀ (pow_ne_zero _ hd0)
  have hSd : S * normOneVal d₀ ^ e
      = normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e) := by
    rw [hS, mul_assoc, hZval, mul_one]
  -- relation (4) at the norm-one argument `u0 ^ (e * e)`
  have hrel := layerFieldHom_one_conj data rfl hexp p₀ p₁ r₀ r₁ (u0 ^ (e * e)) hpp hrr hcoll
  rw [hue, hue2, ← hd, ← hKeq] at hrel
  -- rewrite the goal into the same shape
  have hgoal : S * (normOneVal d₀ * v) ^ e
      = (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * v ^ e := by
    rw [mul_pow, ← mul_assoc, hSd]
  rw [hgoal]
  -- and read the commutation off relation (4)
  have hinv : layerFieldHom data 0
      (Multiplicative.ofAdd (-(normOneVal d₀ * v)))
      = (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal d₀ * v)))⁻¹ := by
    rw [ofAdd_neg, map_inv]
  rw [hinv] at hrel
  exact mul_inv_eq_iff_eq_mul.mp hrel.symm

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

/-- **Theorem B: the same-coset obstruction.**  A collision whose two normalised values *coincide*
refutes hypothesis (B), with **no** assumption on the trace.

`S = S'` turns relation (4) into a commutation, so `S` is an admissible twist; the twists form an
inversion-closed additive subgroup, hence — `q` being prime — either all of `𝔽_{3^q}` or a copy of
the prime field.  In the first case `x` centralises the whole second layer, so the two layers
commute and `N` is abelian, which `false_of_s_normalizes_layerOne` refutes.  In the second case
`S ^ 4 = 1`, and `-1` is a non-square, so `S = ±1`; then `Tr S = ±q ≠ 0` and the trace obstruction
applies. -/
theorem false_of_collisionPair_self (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) (hqne : q ≠ 3) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j))
    {S : GaloisField p q} (hpair : CollisionPair p q e S S) : False := by
  classical
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hmem := mem_commSubgroup_of_collisionPair data hp hq0 hqodd he hexp hpair
  -- `S ≠ 0`, because `z ↦ z ^ (e * e)` is injective and `p₀ ≠ p₁`
  have hS0 : S ≠ 0 := by
    obtain ⟨p₀, p₁, r₀, r₁, d₀, hpp, -, -, -, hS, -⟩ := hpair
    rw [hS]
    refine mul_ne_zero ?_ (pow_ne_zero _ (Units.ne_zero _))
    intro hzero
    have hEq : normOneVal p₁ ^ (e * e) = normOneVal p₀ ^ (e * e) := by
      linear_combination hzero
    have hinj : normOneVal p₁ = normOneVal p₀ := by
      have h1 := hcube (normOneVal p₁)
      have h2 := hcube (normOneVal p₀)
      calc normOneVal p₁ = (normOneVal p₁ ^ (e * e)) ^ e := by rw [← pow_mul, h1]
        _ = (normOneVal p₀ ^ (e * e)) ^ e := by rw [hEq]
        _ = normOneVal p₀ := by rw [← pow_mul, h2]
    rw [hpp] at hinj
    exact one_ne_zero (by linear_combination -hinj)
  subst hp
  letI : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  haveI : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have hcard : Fintype.card (GaloisField 3 q) = 3 ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 q hq0
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  have h4card : Fintype.card (GaloisField 3 q) % 4 = 3 := by
    rw [hcard]
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    have hk : q = 2 * (q / 2) + 1 := by omega
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hinvW : ∀ w ∈ commSubgroup data e, w⁻¹ ∈ commSubgroup data e := fun w hw =>
    inv_mem_commSubgroup data rfl hq0 hqodd he hcube hexp hw
  rcases InverseClosed.pow_four_eq_one_or_forall_mem (commSubgroup data e) hinvW rfl hqprime
      hcard hmem hS0 with hfour | hall
  · -- `S = ±1`, so its trace is `±q ≠ 0`
    have hnegsq : ¬ IsSquare (-1 : GaloisField 3 q) := Paley.not_isSquare_neg_one hchar2 h4card
    have hsq : S ^ 2 = 1 := by
      have hfac : (S ^ 2 - 1) * (S ^ 2 + 1) = 0 := by linear_combination hfour
      rcases mul_eq_zero.mp hfac with h | h
      · linear_combination h
      · exact absurd ⟨S, by linear_combination -h⟩ hnegsq
    have hcast : ((q : ℕ) : GaloisField 3 q) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (GaloisField 3 q) 3]
      intro hdvd
      exact hqne ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hqprime).mp hdvd).symm
    have htr : fieldTrace 3 q S ≠ 0 := by
      have hfac : (S - 1) * (S + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h | h
      · have hS1 : S = 1 := by linear_combination h
        rw [hS1, fieldTrace]
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        exact hcast
      · have hS1 : S = -1 := by linear_combination h
        rw [hS1, fieldTrace]
        have hodd : ∀ j : ℕ, ((-1 : GaloisField 3 q)) ^ (3 : ℕ) ^ j = -1 := fun j =>
          (Odd.pow (by decide)).neg_one_pow
        simp only [hodd, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg_one]
        exact neg_ne_zero.mpr hcast
    exact false_of_collisionPair_trace_ne_zero data rfl hq0 hexp hpair htr
  · -- the two layers centralise each other
    refine false_of_s_normalizes_layerOne data rfl hexp hnotfrob ?_
    have ha1 : layerFieldHom data 0 (Multiplicative.ofAdd (1 : GaloisField 3 q)) = data.s := by
      simp only [layerFieldHom_apply, pow_zero, inv_one, one_mul, mul_one]
      rfl
    have hfixS : ∀ n ∈ ((layerOne data : Subgroup G) : Set G),
        data.s * n * (data.s)⁻¹ = n := by
      intro n hn
      rw [coe_layerOne_eq_range] at hn
      obtain ⟨w, rfl⟩ := hn
      have hx := hall (Multiplicative.toAdd w) 1
      rw [one_pow, mul_one, ha1] at hx
      have hwo : Multiplicative.ofAdd (Multiplicative.toAdd w) = w := rfl
      rw [hwo] at hx
      exact mul_inv_eq_iff_eq_mul.mpr hx.eq
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hfixS n hn]
      exact hn
    · intro hn
      have h3 := hfixS _ hn
      have h2 : data.s * n * (data.s)⁻¹ = n := by
        calc data.s * n * (data.s)⁻¹
            = (data.s)⁻¹ * (data.s * (data.s * n * (data.s)⁻¹) * (data.s)⁻¹) * data.s := by group
          _ = (data.s)⁻¹ * (data.s * n * (data.s)⁻¹) * data.s := by rw [h3]
          _ = n := by group
      rw [← h2]
      exact hn

/-! ### The certificate form

What a computation actually produces is two Paley points lying in one coset of the fixed subgroup,
i.e. two points `a ≠ b` with `a ^ e = lam · a`, `(a+1) ^ e = lam · (a+1)` and the same for `b`,
with a *common* multiplier `lam`.  The two lemmas below turn that data into a `CollisionPair` with
equal normalised values, and hence into a refutation of hypothesis (B). -/

/-- **A collision with equal `K`-values yields a `CollisionPair` with `S = S'`.**  As in
`exists_collisionPair_of_sub_ne_zero`, exactly one of the two orderings has square difference; both
give the same normalised value because the two `K`-values agree. -/
theorem exists_collisionPair_self_of_K_eq (hp : p = 3) (hq : q ≠ 0) (hqodd : Odd q) {e : ℕ}
    (p₀ p₁ r₀ r₁ : NormSet.normOneUnits p q)
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hcoll : normOneVal p₀ ^ e - normOneVal p₁ ^ e = normOneVal r₀ ^ e - normOneVal r₁ ^ e)
    (hK : normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)
        = normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
    (hd : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0) :
    ∃ S : GaloisField p q, CollisionPair p q e S S := by
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
  rcases Paley.isSquare_or_isSquare_neg hchar2 h4 hd with hsq | hnsq
  · exact ⟨_, p₀, p₁, r₀, r₁,
      ⟨Units.mk0 _ hd, (mem_normOneUnits_iff_isSquare rfl hq _).mpr hsq⟩,
      hpp, hrr, hcoll, rfl, rfl, by rw [hK]⟩
  · have hd' : normOneVal p₀ ^ e - normOneVal r₀ ^ e ≠ 0 := by
      intro h
      exact hd (by linear_combination -h)
    have hsq' : IsSquare (normOneVal p₀ ^ e - normOneVal r₀ ^ e) := by
      have hrw : normOneVal p₀ ^ e - normOneVal r₀ ^ e
          = -(normOneVal r₀ ^ e - normOneVal p₀ ^ e) := by ring
      rw [hrw]
      exact hnsq
    exact ⟨_, r₀, r₁, p₀, p₁,
      ⟨Units.mk0 _ hd', (mem_normOneUnits_iff_isSquare rfl hq _).mpr hsq'⟩,
      hrr, hpp, hcoll.symm, rfl, rfl, by rw [hK]⟩

/-- **The certificate.**  Two distinct Paley points whose coordinates are scaled by *one and the
same* factor `lam` under `z ↦ z ^ e` refute hypothesis (B).

This is the computable form of the same-coset obstruction: `lam` is the coset of the fixed subgroup
of `z ↦ z ^ e` shared by `a`, `a+1`, `b`, `b+1`, the common collision value is `lam` itself
(`Paley.powDiff_eq_of_pow_eq_mul`), and the two `K`-values are both `-lam^{e+1}`, so the collision
has `S = S'` and `false_of_collisionPair_self` applies — with no hypothesis on any trace. -/
theorem false_of_sameCoset_pair (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) (hqne : q ≠ 3) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j))
    {a b lam : GaloisField p q}
    (ha : a ∈ Paley.paleySet (GaloisField p q)) (hb : b ∈ Paley.paleySet (GaloisField p q))
    (hab : a ≠ b) (hae : a ^ e = lam * a) (hae1 : (a + 1) ^ e = lam * (a + 1))
    (hbe : b ^ e = lam * b) (hbe1 : (b + 1) ^ e = lam * (b + 1)) : False := by
  obtain ⟨ha0, hasq, ha10, ha1sq⟩ := ha
  obtain ⟨hb0, hbsq, hb10, hb1sq⟩ := hb
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hlam0 : lam ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hae
    exact (pow_ne_zero _ ha0) hae
  -- the four Paley coordinates as norm-one units
  have hmk : ∀ z : GaloisField p q, z ≠ 0 → IsSquare z → ∃ u : NormSet.normOneUnits p q,
      normOneVal u = z := fun z hz0 hzsq =>
    ⟨⟨Units.mk0 z hz0, (mem_normOneUnits_iff_isSquare hp hq0 _).mpr (by simpa using hzsq)⟩, rfl⟩
  obtain ⟨p₁, hp₁⟩ := hmk a ha0 hasq
  obtain ⟨p₀, hp₀⟩ := hmk (a + 1) ha10 ha1sq
  obtain ⟨r₁, hr₁⟩ := hmk b hb0 hbsq
  obtain ⟨r₀, hr₀⟩ := hmk (b + 1) hb10 hb1sq
  -- the second-power multiplier is `lam ^ (e + 1)`
  have hsq2 : ∀ z : GaloisField p q, z ^ e = lam * z → z ^ (e * e) = lam ^ (e + 1) * z := by
    intro z hz
    calc z ^ (e * e) = (z ^ e) ^ e := by rw [pow_mul]
      _ = (lam * z) ^ e := by rw [hz]
      _ = lam ^ e * z ^ e := by rw [mul_pow]
      _ = lam ^ e * (lam * z) := by rw [hz]
      _ = lam ^ (e + 1) * z := by rw [pow_succ]; ring
  have hpp : normOneVal p₀ = normOneVal p₁ + 1 := by rw [hp₀, hp₁]
  have hrr : normOneVal r₀ = normOneVal r₁ + 1 := by rw [hr₀, hr₁]
  have hcoll : normOneVal p₀ ^ e - normOneVal p₁ ^ e
      = normOneVal r₀ ^ e - normOneVal r₁ ^ e := by
    rw [hp₀, hp₁, hr₀, hr₁, hae, hae1, hbe, hbe1]
    ring
  have hK : normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)
      = normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e) := by
    rw [hp₀, hp₁, hr₀, hr₁, hsq2 a hae, hsq2 (a + 1) hae1, hsq2 b hbe, hsq2 (b + 1) hbe1]
    ring
  have hd : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0 := by
    rw [hr₀, hp₀, hae1, hbe1]
    intro hzero
    refine hab ?_
    have hstep : lam * (b - a) = 0 := by linear_combination hzero
    rcases mul_eq_zero.mp hstep with h | h
    · exact absurd h hlam0
    · linear_combination -h
  obtain ⟨S, hpair⟩ :=
    exists_collisionPair_self_of_K_eq hp hq0 hqodd p₀ p₁ r₀ r₁ hpp hrr hcoll hK hd
  exact false_of_collisionPair_self data hp hqprime hqodd hqne he hcube hexp hnotfrob hpair

end SameCoset

end OddOrder.BG.AppC.Problem1
