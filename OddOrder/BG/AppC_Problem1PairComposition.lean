/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.FrobeniusCyclicModule
import OddOrder.BG.AppC_Problem1SameCoset

/-!
# BG Appendix C, Problem 1: the pair-composition calculus

The trace-free refutations of `AppC_Problem1SameCoset` treat a collision whose two normalised
values coincide (`S = S'`).  This file handles the *general* collision by working with the full
conjugation relation (3′)

`a(v) · b(S v^e) · a(v)⁻¹ = b(S' v^e)`   (for every non-zero square `v`),

packaged as `ConjPair S S'`.  These pairs form the graph of an injective additive map (`add`,
`left_eq_zero`), and — the central discovery — they **compose**: from `ConjPair s s'` and
`ConjPair t t'` one manufactures a new pair whose ratio is the product `(s'/s)·(t'/t)` (or its
inverse), by conjugating the first relation by a first-layer element chosen so that its
`t`-relation consumes the output line of the `s`-relation.  The composition is *total*: the
apparent degenerate case `1 + η = 0` would force `-1` to be a square.  A flipped variant
(`composeFlip_key`) uses the second pair backwards and realises the ratio *quotient*; it
degenerates only at `t' = ±s'`.

Any pair with ratio `1` — a non-zero fixed point — lands in `commSubgroup` and is fatal by the
fixed-point principle `false_of_mem_commSubgroup_ne_zero`.  Consequences:

* `false_of_collisionPair_neg` — a collision with `S' = -S` refutes hypothesis (B): conjugating
  twice gives `a(v)² = a(-v)` fixing `b(S v^e)`, so `S ∈ commSubgroup`.  No trace hypothesis.
* `false_of_collisionPair_ratio_eq` — **two** collisions with equal ratios `S₁'/S₁ = S₂'/S₂` and
  `S₂' ≠ ±S₁'` refute hypothesis (B): the flipped composition realises ratio `1`.
* `false_of_collisionPair_frobCombo` — a Frobenius combination `∑ kⱼ S^{3^j} = ∑ kⱼ S'^{3^j} ≠ 0`
  refutes hypothesis (B): pairs are closed under addition and under the Frobenius twist *of the
  underlying collision* (`CollisionPair.frobenius`), and the combination is a fixed point.

Mathematical record: `notes/bg/appC_problem1_pair_composition.md` (issue 0180).  This is the
"closure theorem depending on the projective ratio `S'/S`" that the fourth ChatGPT consultation
left open (`notes/bg/appC_problem1_chatgpt_answer_b1.md` §III.2).
-/

namespace OddOrder.BG.AppC.Problem1

section PairComposition

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **A conjugation pair.**  `ConjPair data e s s'` says that conjugation by the zeroth-layer
element `a(v)` carries the `s`-twisted second-layer line to the `s'`-twisted one, coherently over
every non-zero square argument `v`.  Relation (3′) of a collision is exactly this shape. -/
def ConjPair (data : FieldNormalizerData p q G) (e : ℕ) (s s' : GaloisField p q) : Prop :=
  ∀ v : GaloisField p q, IsSquare v → v ≠ 0 →
    layerFieldHom data 0 (Multiplicative.ofAdd v) *
        layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹
      = layerFieldHom data 1 (Multiplicative.ofAdd (s' * v ^ e))

/-- Conjugation distributes over a product. -/
private theorem conj_mul {H : Type*} [Group H] {x b₁ b₂ c₁ c₂ : H}
    (h₁ : x * b₁ * x⁻¹ = c₁) (h₂ : x * b₂ * x⁻¹ = c₂) : x * (b₁ * b₂) * x⁻¹ = c₁ * c₂ := by
  rw [← h₁, ← h₂]; group

/-- Conjugation commutes with inversion. -/
private theorem conj_inv {H : Type*} [Group H] {x b c : H}
    (h : x * b * x⁻¹ = c) : x * b⁻¹ * x⁻¹ = c⁻¹ := by
  rw [← h]; group

namespace ConjPair

variable {data : FieldNormalizerData p q G} {e : ℕ}

/-- The layers split additive arguments into products. -/
private theorem layer_split (data : FieldNormalizerData p q G) (i : ℕ)
    {x y z : GaloisField p q} (h : x = y + z) :
    layerFieldHom data i (Multiplicative.ofAdd x)
      = layerFieldHom data i (Multiplicative.ofAdd y) *
        layerFieldHom data i (Multiplicative.ofAdd z) := by
  subst h
  rw [ofAdd_add]
  exact map_mul _ _ _

/-- The layers turn negated arguments into inverses. -/
private theorem layer_neg (data : FieldNormalizerData p q G) (i : ℕ)
    {x y : GaloisField p q} (h : x = -y) :
    layerFieldHom data i (Multiplicative.ofAdd x)
      = (layerFieldHom data i (Multiplicative.ofAdd y))⁻¹ := by
  subst h
  rw [ofAdd_neg]
  exact map_inv _ _

/-- Pairs add componentwise: the second layer is abelian and conjugation is a homomorphism. -/
theorem add {s₁ s₁' s₂ s₂' : GaloisField p q} (h₁ : ConjPair data e s₁ s₁')
    (h₂ : ConjPair data e s₂ s₂') : ConjPair data e (s₁ + s₂) (s₁' + s₂') := by
  intro v hv hv0
  rw [layer_split data 1 (show (s₁ + s₂) * v ^ e = s₁ * v ^ e + s₂ * v ^ e by ring),
    layer_split data 1 (show (s₁' + s₂') * v ^ e = s₁' * v ^ e + s₂' * v ^ e by ring)]
  exact conj_mul (h₁ v hv hv0) (h₂ v hv hv0)

/-- The trivial pair. -/
theorem zero (data : FieldNormalizerData p q G) (e : ℕ) : ConjPair data e 0 0 := by
  intro v hv hv0
  have h0 : layerFieldHom data 1 (Multiplicative.ofAdd ((0 : GaloisField p q) * v ^ e)) = 1 := by
    have harg : Multiplicative.ofAdd ((0 : GaloisField p q) * v ^ e) = 1 := by
      rw [zero_mul]
      exact ofAdd_zero
    rw [harg]
    exact map_one _
  rw [h0, mul_one]
  exact mul_inv_cancel _

/-- Pairs negate componentwise. -/
theorem neg {s s' : GaloisField p q} (h : ConjPair data e s s') :
    ConjPair data e (-s) (-s') := by
  intro v hv hv0
  rw [layer_neg data 1 (show -s * v ^ e = -(s * v ^ e) by ring),
    layer_neg data 1 (show -s' * v ^ e = -(s' * v ^ e) by ring)]
  exact conj_inv (h v hv hv0)

/-- Pairs scale by natural numbers. -/
theorem nsmul {s s' : GaloisField p q} (h : ConjPair data e s s') (k : ℕ) :
    ConjPair data e (k • s) (k • s') := by
  induction k with
  | zero => simpa using ConjPair.zero data e
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      exact ih.add h

/-- Pairs sum over finite index sets. -/
theorem sum {ι : Type*} (f g : ι → GaloisField p q) (T : Finset ι)
    (h : ∀ i ∈ T, ConjPair data e (f i) (g i)) :
    ConjPair data e (∑ i ∈ T, f i) (∑ i ∈ T, g i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using ConjPair.zero data e
  | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a T)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The graph property.**  A pair with vanishing second component has vanishing first
component: the second layer is a faithful copy of the field. -/
theorem left_eq_zero {s : GaloisField p q} (h : ConjPair data e s 0) : s = 0 := by
  have h1 := h 1 ⟨1, (mul_one 1).symm⟩ one_ne_zero
  have h0 : layerFieldHom data 1 (Multiplicative.ofAdd ((0 : GaloisField p q) * 1 ^ e)) = 1 := by
    have harg : Multiplicative.ofAdd ((0 : GaloisField p q) * 1 ^ e) = 1 := by
      rw [zero_mul]
      exact ofAdd_zero
    rw [harg]
    exact map_one _
  rw [h0] at h1
  -- `x · B · x⁻¹ = 1` forces `B = 1`
  have hB : layerFieldHom data 1 (Multiplicative.ofAdd (s * 1 ^ e)) = 1 :=
    mul_left_cancel (a := layerFieldHom data 0 (Multiplicative.ofAdd (1 : GaloisField p q)))
      (by rw [mul_one]; exact mul_inv_eq_one.mp h1)
  have h0' : layerFieldHom data 1 (Multiplicative.ofAdd (0 : GaloisField p q)) = 1 := by
    rw [ofAdd_zero]
    exact map_one _
  have harg := layerFieldHom_injective data 1 (hB.trans h0'.symm)
  have hval : s * 1 ^ e = 0 := by
    have := congrArg Multiplicative.toAdd harg
    simpa using this
  simpa using hval

/-- The second component of a pair with non-zero first component is non-zero. -/
theorem right_ne_zero {s s' : GaloisField p q} (h : ConjPair data e s s') (hs : s ≠ 0) :
    s' ≠ 0 := fun h0 => hs (left_eq_zero (h0 ▸ h))

/-- **The graph property, other direction.**  A pair with vanishing first component has vanishing
second component: `a(v) · 1 · a(v)⁻¹ = 1`.  A violation — the kill condition "K2" of the closure
computation — therefore refutes hypothesis (B) outright. -/
theorem right_eq_zero {s' : GaloisField p q} (h : ConjPair data e 0 s') : s' = 0 := by
  have h1 := h 1 ⟨1, (mul_one 1).symm⟩ one_ne_zero
  have h0 : layerFieldHom data 1 (Multiplicative.ofAdd ((0 : GaloisField p q) * 1 ^ e)) = 1 := by
    have harg : Multiplicative.ofAdd ((0 : GaloisField p q) * 1 ^ e) = 1 := by
      rw [zero_mul]
      exact ofAdd_zero
    rw [harg]
    exact map_one _
  rw [h0, mul_one, mul_inv_cancel] at h1
  have h0' : layerFieldHom data 1 (Multiplicative.ofAdd (0 : GaloisField p q)) = 1 := by
    rw [ofAdd_zero]
    exact map_one _
  have harg := layerFieldHom_injective data 1 (h0'.trans h1)
  have hval : (0 : GaloisField p q) = s' * 1 ^ e := by
    have := congrArg Multiplicative.toAdd harg
    simpa using this
  simpa using hval.symm

end ConjPair

/-- **Relation (3′): a collision is a conjugation pair.**  The normalisation `v := δ z^e` of
relation (3) (`layerFieldHom_one_conj`); as `z` sweeps the norm-one units so does `v`, because the
oriented difference `δ` is a square and `z ↦ z^e` is invertible on squares. -/
theorem ConjPair.of_collisionPair (data : FieldNormalizerData p q G) (hp : p = 3) (hq : q ≠ 0)
    {e : ℕ} (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S S' : GaloisField p q} (hpair : CollisionPair p q e S S') : ConjPair data e S S' := by
  obtain ⟨p₀, p₁, r₀, r₁, d₀, hpp, hrr, hcoll, hd, hS, hS'⟩ := hpair
  have hd0 : normOneVal d₀ ≠ 0 := Units.ne_zero _
  have hdcube : normOneVal d₀ ^ (e * e * e) = normOneVal d₀ := by
    have hu := normOneUnits_pow_cube data hp hexp d₀
    calc normOneVal d₀ ^ (e * e * e) = normOneVal (d₀ ^ (e * e * e)) := by rw [normOneVal_pow]
      _ = normOneVal d₀ := by rw [hu]
  have hZval : normOneVal (d₀⁻¹ ^ (e * e)) ^ (e * e) * normOneVal d₀ ^ e = 1 := by
    have hexp4 : e * e * (e * e) = e * e * e * e := by ring
    rw [normOneVal_pow, normOneVal_inv, ← pow_mul, inv_pow, hexp4, pow_mul, hdcube]
    exact inv_mul_cancel₀ (pow_ne_zero _ hd0)
  have hSd : S * normOneVal d₀ ^ e
      = normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e) := by
    rw [hS, mul_assoc, hZval, mul_one]
  have hS'd : S' * normOneVal d₀ ^ e
      = normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e) := by
    rw [hS', mul_assoc, hZval, mul_one]
  have hdsq : IsSquare (normOneVal d₀) := by
    have := (mem_normOneUnits_iff_isSquare hp hq (d₀ : (GaloisField p q)ˣ)).mp d₀.2
    simpa [normOneVal] using this
  intro w hw hw0
  -- normalise the argument: `w = δ · v` with `v` a non-zero square
  have hv_sq : IsSquare ((normOneVal d₀)⁻¹ * w) := hdsq.inv.mul hw
  have hv0 : (normOneVal d₀)⁻¹ * w ≠ 0 := mul_ne_zero (inv_ne_zero hd0) hw0
  obtain ⟨u0, hu0⟩ : ∃ u0 : NormSet.normOneUnits p q,
      normOneVal u0 = (normOneVal d₀)⁻¹ * w :=
    ⟨⟨Units.mk0 _ hv0, (mem_normOneUnits_iff_isSquare hp hq _).mpr (by simpa using hv_sq)⟩, rfl⟩
  have hcubev : normOneVal u0 ^ (e * e * e) = normOneVal u0 := by
    have hu := normOneUnits_pow_cube data hp hexp u0
    calc normOneVal u0 ^ (e * e * e) = normOneVal (u0 ^ (e * e * e)) := by rw [normOneVal_pow]
      _ = normOneVal u0 := by rw [hu]
  have hue : normOneVal (u0 ^ (e * e)) ^ e = (normOneVal d₀)⁻¹ * w := by
    rw [normOneVal_pow, ← pow_mul, hcubev, hu0]
  have hue2 : normOneVal (u0 ^ (e * e)) ^ (e * e) = ((normOneVal d₀)⁻¹ * w) ^ e := by
    have hexp4 : e * e * (e * e) = e * e * e * e := by ring
    rw [normOneVal_pow, ← pow_mul, hexp4, pow_mul, hcubev, hu0]
  have hrel := layerFieldHom_one_conj data hp hexp p₀ p₁ r₀ r₁ (u0 ^ (e * e)) hpp hrr hcoll
  rw [hue, hue2, ← hd] at hrel
  have hw' : normOneVal d₀ * ((normOneVal d₀)⁻¹ * w) = w := by
    rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
  have hcancel : ∀ X : GaloisField p q,
      X * normOneVal d₀ ^ e * ((normOneVal d₀)⁻¹ * w) ^ e = X * w ^ e := by
    intro X
    rw [mul_pow, inv_pow]
    calc X * normOneVal d₀ ^ e * ((normOneVal d₀ ^ e)⁻¹ * w ^ e)
        = X * (normOneVal d₀ ^ e * (normOneVal d₀ ^ e)⁻¹) * w ^ e := by ring
      _ = X * w ^ e := by rw [mul_inv_cancel₀ (pow_ne_zero _ hd0)]; ring
  have hbS : (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) *
      ((normOneVal d₀)⁻¹ * w) ^ e = S * w ^ e := by
    rw [← hSd]; exact hcancel S
  have hbS' : (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) *
      ((normOneVal d₀)⁻¹ * w) ^ e = S' * w ^ e := by
    rw [← hS'd]; exact hcancel S'
  rw [hw', hbS, hbS'] at hrel
  rw [ConjPair.layer_neg data 0 (rfl : -w = -w)] at hrel
  exact hrel.symm

/-- **A non-zero fixed point of the pair relation is fatal.**  `ConjPair m m` says that `a(v)`
commutes with `b(m v^e)` on every square argument, so `m` is a non-zero admissible twist and the
fixed-point principle applies. -/
theorem false_of_conjPair_self (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {m : GaloisField p q} (h : ConjPair data e m m) (hm0 : m ≠ 0) : False := by
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hmem : m ∈ commSubgroup data e := by
    refine mem_commSubgroup_of_square data hp hq0 hqodd he one_ne_zero ?_
    intro v hv hv0
    have h1 := h v hv hv0
    simp only [one_mul]
    exact (commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp h1)
  exact false_of_mem_commSubgroup_ne_zero data hp hqprime hqodd he hcube hexp hmem hm0

/-- The first normalised value of a collision is non-zero: `z ↦ z^{e²}` is injective and the two
Paley coordinates differ by `1`. -/
theorem CollisionPair.left_ne_zero {e : ℕ}
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {S S' : GaloisField p q} (hpair : CollisionPair p q e S S') : S ≠ 0 := by
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

/-! ### Theorem N1: a collision with `S' = -S` is fatal

Conjugating the pair relation twice by the same `a(v)` and using `a(v)² = a(-v)` (characteristic
three) shows that `a(v)⁻¹` fixes `b(S v^e)`, i.e. `S` is an admissible twist. -/

/-- **A collision whose normalised values are negatives of each other refutes hypothesis (B)** —
with no trace hypothesis. -/
theorem false_of_collisionPair_neg (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S : GaloisField p q} (hpair : CollisionPair p q e S (-S)) : False := by
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hS0 : S ≠ 0 := CollisionPair.left_ne_zero hcube hpair
  have hcp := ConjPair.of_collisionPair data hp hq0 hexp hpair
  have hcpneg : ConjPair data e (-S) S := by
    have := hcp.neg
    rwa [neg_neg] at this
  subst hp
  haveI : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have hmem : S ∈ commSubgroup data e := by
    refine mem_commSubgroup_of_square data rfl hq0 hqodd he one_ne_zero ?_
    intro v hv hv0
    have h1 := hcp v hv hv0
    have h2 := hcpneg v hv hv0
    have hdouble : layerFieldHom data 0 (Multiplicative.ofAdd (v + v)) *
        layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (v + v)))⁻¹
        = layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) := by
      rw [ConjPair.layer_split data 0 (rfl : v + v = v + v)]
      calc (layerFieldHom data 0 (Multiplicative.ofAdd v) *
            layerFieldHom data 0 (Multiplicative.ofAdd v)) *
            layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) *
            (layerFieldHom data 0 (Multiplicative.ofAdd v) *
              layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹
          = layerFieldHom data 0 (Multiplicative.ofAdd v) *
            (layerFieldHom data 0 (Multiplicative.ofAdd v) *
              layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) *
              (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹) *
            (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹ := by group
        _ = layerFieldHom data 0 (Multiplicative.ofAdd v) *
            layerFieldHom data 1 (Multiplicative.ofAdd (-S * v ^ e)) *
            (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹ := by rw [h1]
        _ = _ := h2
    have hvv : v + v = -v := by
      have h3 : (3 : GaloisField 3 q) = 0 := by
        exact_mod_cast CharP.cast_eq_zero (GaloisField 3 q) 3
      linear_combination v * h3
    rw [hvv, ConjPair.layer_neg data 0 (rfl : -v = -v), inv_inv] at hdouble
    -- `a(v)⁻¹ · B · a(v) = B`, hence `a(v)` and `B` commute
    have hBX : layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) *
        layerFieldHom data 0 (Multiplicative.ofAdd v)
        = layerFieldHom data 0 (Multiplicative.ofAdd v) *
          layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) := by
      have h5 : layerFieldHom data 0 (Multiplicative.ofAdd v) *
          ((layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹ *
            layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) *
            layerFieldHom data 0 (Multiplicative.ofAdd v))
          = layerFieldHom data 0 (Multiplicative.ofAdd v) *
            layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) := by rw [hdouble]
      calc layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) *
            layerFieldHom data 0 (Multiplicative.ofAdd v)
          = layerFieldHom data 0 (Multiplicative.ofAdd v) *
            ((layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹ *
              layerFieldHom data 1 (Multiplicative.ofAdd (S * v ^ e)) *
              layerFieldHom data 0 (Multiplicative.ofAdd v)) := by group
        _ = _ := h5
    simp only [one_mul]
    exact (commute_iff_eq _ _).mpr hBX.symm
  exact false_of_mem_commSubgroup_ne_zero data rfl hqprime hqodd he hcube hexp hmem hS0

/-! ### Chain reversal

Two pairs sharing a middle value close into a *reversed* pair.  Unlike the composition calculus
below, no sign analysis and no `e`-th powers appear: both relations are instantiated at the *same*
argument `v`, and `a(v)² = a(2v) = a(-v) = a(v)⁻¹` (characteristic three) turns the double
conjugation into a conjugation by `a(v)⁻¹`. -/

/-- **Chain reversal.**  `ConjPair s s'` and `ConjPair s' s''` imply `ConjPair s'' s`: conjugating
the first relation by `a(v)` and consuming it with the second gives
`a(v)² · b(s v^e) · a(v)⁻² = b(s'' v^e)`, and `a(v)² = a(v)⁻¹` in characteristic three. -/
theorem ConjPair.chain (data : FieldNormalizerData p q G) (hp : p = 3)
    {e : ℕ} {s s' s'' : GaloisField p q}
    (h₁ : ConjPair data e s s') (h₂ : ConjPair data e s' s'') :
    ConjPair data e s'' s := by
  subst hp
  haveI : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  intro v hv hv0
  have h1 := h₁ v hv hv0
  have h2 := h₂ v hv hv0
  have hdouble : layerFieldHom data 0 (Multiplicative.ofAdd (v + v)) *
      layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
      (layerFieldHom data 0 (Multiplicative.ofAdd (v + v)))⁻¹
      = layerFieldHom data 1 (Multiplicative.ofAdd (s'' * v ^ e)) := by
    rw [ConjPair.layer_split data 0 (rfl : v + v = v + v)]
    calc (layerFieldHom data 0 (Multiplicative.ofAdd v) *
          layerFieldHom data 0 (Multiplicative.ofAdd v)) *
          layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v) *
            layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹
        = layerFieldHom data 0 (Multiplicative.ofAdd v) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v) *
            layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
            (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹ := by group
      _ = layerFieldHom data 0 (Multiplicative.ofAdd v) *
          layerFieldHom data 1 (Multiplicative.ofAdd (s' * v ^ e)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹ := by rw [h1]
      _ = _ := h2
  have hvv : v + v = -v := by
    have h3 : (3 : GaloisField 3 q) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (GaloisField 3 q) 3
    linear_combination v * h3
  rw [hvv, ConjPair.layer_neg data 0 (rfl : -v = -v), inv_inv] at hdouble
  rw [← hdouble]
  group

/-! ### The composition calculus

From two pairs one manufactures a third whose ratio is the product (straight) or the quotient
(flipped) of the two ratios.  The conjugator is `a(η v + v)` where `η = (c·s'/t)^{e²}` is chosen —
via the sign `c ∈ {±1}` — to be a *square*, so that the `t`-relation applies at `η v`; and
`1 + η ≠ 0` because `-1` is a non-square.  The flipped variant uses the `t`-relation backwards and
degenerates only when `t' = ±s'`. -/

/-- Pairs scale by the signs `±1`. -/
theorem ConjPair.smul_sign {data : FieldNormalizerData p q G} {e : ℕ}
    {s s' c : GaloisField p q} (h : ConjPair data e s s') (hcc : c = 1 ∨ c = -1) :
    ConjPair data e (c * s) (c * s') := by
  rcases hcc with rfl | rfl
  · simpa only [one_mul] using h
  · simpa only [neg_one_mul] using h.neg

/-- The square dichotomy and the non-squareness of `-1`, packaged for `𝔽_{3^q}`, `q` odd. -/
private theorem square_dichotomy (hp : p = 3) (hq0 : q ≠ 0) (hqodd : Odd q) :
    (∀ a : GaloisField p q, a ≠ 0 → IsSquare a ∨ IsSquare (-a)) ∧
      ¬ IsSquare (-1 : GaloisField p q) := by
  classical
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
  exact ⟨fun a ha => Paley.isSquare_or_isSquare_neg hchar2 h4card ha,
    Paley.not_isSquare_neg_one hchar2 h4card⟩

/-- **The straight composition, unnormalised.**  Conjugation by `a(η v + v)` carries the
`s`-twisted line to the `(s'·t'/t)`-twisted one: the inner `a(v)` produces the `s'`-line, and the
outer `a(η v)` consumes it through the `c`-scaled `t`-relation, since `(c t)·(η v)^e = s' v^e`. -/
private theorem compose_key (data : FieldNormalizerData p q G) {e : ℕ}
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {s s' t t' c : GaloisField p q} (hst : ConjPair data e s s') (htt : ConjPair data e t t')
    (hc2 : c * c = 1) (ht0 : t ≠ 0) (hs'0 : s' ≠ 0) (hcsq : IsSquare (c * s' / t)) :
    ∀ v : GaloisField p q, IsSquare v → v ≠ 0 →
      layerFieldHom data 0 (Multiplicative.ofAdd ((1 + (c * s' / t) ^ (e * e)) * v)) *
          layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd ((1 + (c * s' / t) ^ (e * e)) * v)))⁻¹
        = layerFieldHom data 1 (Multiplicative.ofAdd (s' * t' / t * v ^ e)) := by
  intro v hv hv0
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc2
    exact zero_ne_one hc2
  have hr0 : c * s' / t ≠ 0 := div_ne_zero (mul_ne_zero hc0 hs'0) ht0
  have hcc : c = 1 ∨ c = -1 := by
    have hfac : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  have hu_sq : IsSquare ((c * s' / t) ^ (e * e) * v) := (hcsq.pow _).mul hv
  have hu0 : (c * s' / t) ^ (e * e) * v ≠ 0 := mul_ne_zero (pow_ne_zero _ hr0) hv0
  have hηe : ((c * s' / t) ^ (e * e)) ^ e = c * s' / t := by
    rw [← pow_mul]
    exact hcube _
  -- the `c`-scaled `t`-relation at `η v`, with both arguments rewritten
  have h2 := (htt.smul_sign hcc) ((c * s' / t) ^ (e * e) * v) hu_sq hu0
  have hargeq : c * t * ((c * s' / t) ^ (e * e) * v) ^ e = s' * v ^ e := by
    rw [mul_pow, hηe]
    calc c * t * (c * s' / t * v ^ e) = c * c * s' * (t * t⁻¹) * v ^ e := by ring
      _ = s' * v ^ e := by rw [mul_inv_cancel₀ ht0, hc2]; ring
  have hvaleq : c * t' * ((c * s' / t) ^ (e * e) * v) ^ e = s' * t' / t * v ^ e := by
    rw [mul_pow, hηe]
    calc c * t' * (c * s' / t * v ^ e) = c * c * (s' * t' / t) * v ^ e := by ring
      _ = s' * t' / t * v ^ e := by rw [hc2]; ring
  rw [hargeq, hvaleq] at h2
  -- chain the two conjugations
  have h1 := hst v hv hv0
  rw [ConjPair.layer_split data 0
    (show (1 + (c * s' / t) ^ (e * e)) * v = (c * s' / t) ^ (e * e) * v + v by ring)]
  calc (layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t) ^ (e * e) * v)) *
        layerFieldHom data 0 (Multiplicative.ofAdd v)) *
        layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t) ^ (e * e) * v)) *
          layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹
      = layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t) ^ (e * e) * v)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd v) *
          layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹) *
        (layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t) ^ (e * e) * v)))⁻¹ := by
        group
    _ = layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t) ^ (e * e) * v)) *
        layerFieldHom data 1 (Multiplicative.ofAdd (s' * v ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t) ^ (e * e) * v)))⁻¹ := by
        rw [h1]
    _ = _ := h2

/-- **The flipped composition, unnormalised.**  The `t`-relation is used backwards: the conjugator
is `a(-η v + v)` with `η = (c·s'/t')^{e²}` a square, and the ratio comes out as the *quotient*
`s'·t/(t'·s)` instead of the product. -/
private theorem composeFlip_key (data : FieldNormalizerData p q G) {e : ℕ}
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {s s' t t' c : GaloisField p q} (hst : ConjPair data e s s') (htt : ConjPair data e t t')
    (hc2 : c * c = 1) (ht'0 : t' ≠ 0) (hs'0 : s' ≠ 0) (hcsq : IsSquare (c * s' / t')) :
    ∀ v : GaloisField p q, IsSquare v → v ≠ 0 →
      layerFieldHom data 0 (Multiplicative.ofAdd ((1 - (c * s' / t') ^ (e * e)) * v)) *
          layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd ((1 - (c * s' / t') ^ (e * e)) * v)))⁻¹
        = layerFieldHom data 1 (Multiplicative.ofAdd (s' * t / t' * v ^ e)) := by
  intro v hv hv0
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc2
    exact zero_ne_one hc2
  have hr0 : c * s' / t' ≠ 0 := div_ne_zero (mul_ne_zero hc0 hs'0) ht'0
  have hcc : c = 1 ∨ c = -1 := by
    have hfac : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  have hu_sq : IsSquare ((c * s' / t') ^ (e * e) * v) := (hcsq.pow _).mul hv
  have hu0 : (c * s' / t') ^ (e * e) * v ≠ 0 := mul_ne_zero (pow_ne_zero _ hr0) hv0
  have hηe : ((c * s' / t') ^ (e * e)) ^ e = c * s' / t' := by
    rw [← pow_mul]
    exact hcube _
  have h2 := (htt.smul_sign hcc) ((c * s' / t') ^ (e * e) * v) hu_sq hu0
  have hargeq : c * t' * ((c * s' / t') ^ (e * e) * v) ^ e = s' * v ^ e := by
    rw [mul_pow, hηe]
    calc c * t' * (c * s' / t' * v ^ e) = c * c * s' * (t' * t'⁻¹) * v ^ e := by ring
      _ = s' * v ^ e := by rw [mul_inv_cancel₀ ht'0, hc2]; ring
  have hvaleq : c * t * ((c * s' / t') ^ (e * e) * v) ^ e = s' * t / t' * v ^ e := by
    rw [mul_pow, hηe]
    calc c * t * (c * s' / t' * v ^ e) = c * c * (s' * t / t') * v ^ e := by ring
      _ = s' * t / t' * v ^ e := by rw [hc2]; ring
  rw [hvaleq, hargeq] at h2
  -- h2 : a(ηv) · b((s'·t/t')·v^e) · a(ηv)⁻¹ = b(s'·v^e); invert it
  have h2' : (layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t') ^ (e * e) * v)))⁻¹ *
      layerFieldHom data 1 (Multiplicative.ofAdd (s' * v ^ e)) *
      layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t') ^ (e * e) * v))
      = layerFieldHom data 1 (Multiplicative.ofAdd (s' * t / t' * v ^ e)) := by
    rw [← h2]
    group
  have h1 := hst v hv hv0
  rw [ConjPair.layer_split data 0
    (show (1 - (c * s' / t') ^ (e * e)) * v = -((c * s' / t') ^ (e * e) * v) + v by ring),
    ConjPair.layer_neg data 0
      (rfl : -((c * s' / t') ^ (e * e) * v) = -((c * s' / t') ^ (e * e) * v))]
  calc ((layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t') ^ (e * e) * v)))⁻¹ *
        layerFieldHom data 0 (Multiplicative.ofAdd v)) *
        layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
        ((layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t') ^ (e * e) * v)))⁻¹ *
          layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹
      = (layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t') ^ (e * e) * v)))⁻¹ *
        (layerFieldHom data 0 (Multiplicative.ofAdd v) *
          layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹) *
        layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t') ^ (e * e) * v)) := by
        group
    _ = (layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t') ^ (e * e) * v)))⁻¹ *
        layerFieldHom data 1 (Multiplicative.ofAdd (s' * v ^ e)) *
        layerFieldHom data 0 (Multiplicative.ofAdd ((c * s' / t') ^ (e * e) * v)) := by
        rw [h1]
    _ = _ := h2'

/-- **Theorem C1 (straight composition).**  From pairs `(s, s')` and `(t, t')`, both non-zero,
one obtains a non-zero pair realising the *product* ratio `r = (s'/s)·(t'/t)` — as `(m, r·m)` or
as `(r·m, m)`, according to the square class of `1 + η`.  There is **no** degenerate case. -/
theorem ConjPair.compose (data : FieldNormalizerData p q G) (hp : p = 3) (hq0 : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {s s' t t' : GaloisField p q} (hst : ConjPair data e s s') (htt : ConjPair data e t t')
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    ∃ m : GaloisField p q, m ≠ 0 ∧
      (ConjPair data e m (s' * t' / (t * s) * m) ∨
        ConjPair data e (s' * t' / (t * s) * m) m) := by
  obtain ⟨hdich, hneg1⟩ := square_dichotomy hp hq0 hqodd
  have hs'0 : s' ≠ 0 := hst.right_ne_zero hs0
  obtain ⟨c, hc2, hcsq⟩ : ∃ c : GaloisField p q, c * c = 1 ∧ IsSquare (c * s' / t) := by
    rcases hdich _ (div_ne_zero hs'0 ht0) with hsq | hnsq
    · exact ⟨1, by ring, by rwa [one_mul]⟩
    · refine ⟨-1, by ring, ?_⟩
      have hrw : -1 * s' / t = -(s' / t) := by ring
      rwa [hrw]
  have hkey := compose_key data hcube hst htt hc2 ht0 hs'0 hcsq
  obtain ⟨τ, hτdef⟩ : ∃ τ : GaloisField p q, τ = 1 + (c * s' / t) ^ (e * e) := ⟨_, rfl⟩
  rw [← hτdef] at hkey
  have hτ0 : τ ≠ 0 := by
    intro h
    have hη : (c * s' / t) ^ (e * e) = -1 := by linear_combination h - hτdef
    have hηsq : IsSquare ((c * s' / t) ^ (e * e)) := hcsq.pow _
    rw [hη] at hηsq
    exact hneg1 hηsq
  rcases hdich τ hτ0 with hτsq | hτnsq
  · -- `τ` a square: the straight pair `(s·τ^{-e}, r·s·τ^{-e})`
    refine ⟨s * (τ ^ e)⁻¹, mul_ne_zero hs0 (inv_ne_zero (pow_ne_zero _ hτ0)), Or.inl ?_⟩
    intro w hw hw0
    have h := hkey (τ⁻¹ * w) (hτsq.inv.mul hw) (mul_ne_zero (inv_ne_zero hτ0) hw0)
    have ha : τ * (τ⁻¹ * w) = w := by
      rw [← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
    have hb : s * (τ⁻¹ * w) ^ e = s * (τ ^ e)⁻¹ * w ^ e := by
      rw [mul_pow, inv_pow]
      ring
    have hval : s' * t' / t * (τ⁻¹ * w) ^ e
        = s' * t' / (t * s) * (s * (τ ^ e)⁻¹) * w ^ e := by
      rw [mul_pow, inv_pow]
      have hss : s' * t' / (t * s) * s = s' * t' / t := by
        field_simp
      rw [← hss]
      ring
    rw [ha, hb, hval] at h
    exact h
  · -- `-τ` a square: the flipped pair
    refine ⟨s * ((-τ) ^ e)⁻¹,
      mul_ne_zero hs0 (inv_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hτ0))), Or.inr ?_⟩
    intro w hw hw0
    have h := hkey ((-τ)⁻¹ * w) (hτnsq.inv.mul hw)
      (mul_ne_zero (inv_ne_zero (neg_ne_zero.mpr hτ0)) hw0)
    have ha : τ * ((-τ)⁻¹ * w) = -w := by
      rw [inv_neg]
      field_simp
    have hb : s * ((-τ)⁻¹ * w) ^ e = s * ((-τ) ^ e)⁻¹ * w ^ e := by
      rw [mul_pow, inv_pow]
      ring
    have hval : s' * t' / t * ((-τ)⁻¹ * w) ^ e
        = s' * t' / (t * s) * (s * ((-τ) ^ e)⁻¹) * w ^ e := by
      rw [mul_pow, inv_pow]
      have hss : s' * t' / (t * s) * s = s' * t' / t := by
        field_simp
      rw [← hss]
      ring
    rw [ha, hb, hval, ConjPair.layer_neg data 0 (rfl : -w = -w), inv_inv] at h
    rw [← h]
    group

/-- **Theorem C2 (flipped composition).**  From pairs `(s, s')` and `(t, t')` with `t' ≠ ±s'`,
one obtains a non-zero pair realising the *quotient* ratio `(s'/s)·(t/t')` — the only degenerate
case of the calculus, excluded by `t' ≠ ±s'`. -/
theorem ConjPair.composeFlip (data : FieldNormalizerData p q G) (hp : p = 3) (hq0 : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {s s' t t' : GaloisField p q} (hst : ConjPair data e s s') (htt : ConjPair data e t t')
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hne1 : t' ≠ s') (hne2 : t' ≠ -s') :
    ∃ m : GaloisField p q, m ≠ 0 ∧
      (ConjPair data e m (s' * t / (t' * s) * m) ∨
        ConjPair data e (s' * t / (t' * s) * m) m) := by
  obtain ⟨hdich, hneg1⟩ := square_dichotomy hp hq0 hqodd
  have hs'0 : s' ≠ 0 := hst.right_ne_zero hs0
  have ht'0 : t' ≠ 0 := htt.right_ne_zero ht0
  obtain ⟨c, hc2, hcsq, hcne⟩ : ∃ c : GaloisField p q,
      c * c = 1 ∧ IsSquare (c * s' / t') ∧ c * s' / t' ≠ 1 := by
    rcases hdich _ (div_ne_zero hs'0 ht'0) with hsq | hnsq
    · refine ⟨1, by ring, by rwa [one_mul], ?_⟩
      rw [one_mul]
      intro h
      exact hne1 ((div_eq_one_iff_eq ht'0).mp h).symm
    · refine ⟨-1, by ring, ?_, ?_⟩
      · have hrw : -1 * s' / t' = -(s' / t') := by ring
        rwa [hrw]
      · intro h
        have h' : -1 * s' = t' := (div_eq_one_iff_eq ht'0).mp h
        exact hne2 (by linear_combination -h')
  have hkey := composeFlip_key data hcube hst htt hc2 ht'0 hs'0 hcsq
  obtain ⟨τ, hτdef⟩ : ∃ τ : GaloisField p q, τ = 1 - (c * s' / t') ^ (e * e) := ⟨_, rfl⟩
  rw [← hτdef] at hkey
  have hτ0 : τ ≠ 0 := by
    intro h
    have hη1 : (c * s' / t') ^ (e * e) = 1 := by linear_combination hτdef - h
    have hone : c * s' / t' = 1 := by
      calc c * s' / t' = (c * s' / t') ^ (e * e * e) := (hcube _).symm
        _ = ((c * s' / t') ^ (e * e)) ^ e := by rw [pow_mul]
        _ = 1 := by rw [hη1, one_pow]
    exact hcne hone
  rcases hdich τ hτ0 with hτsq | hτnsq
  · refine ⟨s * (τ ^ e)⁻¹, mul_ne_zero hs0 (inv_ne_zero (pow_ne_zero _ hτ0)), Or.inl ?_⟩
    intro w hw hw0
    have h := hkey (τ⁻¹ * w) (hτsq.inv.mul hw) (mul_ne_zero (inv_ne_zero hτ0) hw0)
    have ha : τ * (τ⁻¹ * w) = w := by
      rw [← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
    have hb : s * (τ⁻¹ * w) ^ e = s * (τ ^ e)⁻¹ * w ^ e := by
      rw [mul_pow, inv_pow]
      ring
    have hval : s' * t / t' * (τ⁻¹ * w) ^ e
        = s' * t / (t' * s) * (s * (τ ^ e)⁻¹) * w ^ e := by
      rw [mul_pow, inv_pow]
      have hss : s' * t / (t' * s) * s = s' * t / t' := by
        field_simp
      rw [← hss]
      ring
    rw [ha, hb, hval] at h
    exact h
  · refine ⟨s * ((-τ) ^ e)⁻¹,
      mul_ne_zero hs0 (inv_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hτ0))), Or.inr ?_⟩
    intro w hw hw0
    have h := hkey ((-τ)⁻¹ * w) (hτnsq.inv.mul hw)
      (mul_ne_zero (inv_ne_zero (neg_ne_zero.mpr hτ0)) hw0)
    have ha : τ * ((-τ)⁻¹ * w) = -w := by
      rw [inv_neg]
      field_simp
    have hb : s * ((-τ)⁻¹ * w) ^ e = s * ((-τ) ^ e)⁻¹ * w ^ e := by
      rw [mul_pow, inv_pow]
      ring
    have hval : s' * t / t' * ((-τ)⁻¹ * w) ^ e
        = s' * t / (t' * s) * (s * ((-τ) ^ e)⁻¹) * w ^ e := by
      rw [mul_pow, inv_pow]
      have hss : s' * t / (t' * s) * s = s' * t / t' := by
        field_simp
      rw [← hss]
      ring
    rw [ha, hb, hval, ConjPair.layer_neg data 0 (rfl : -w = -w), inv_inv] at h
    rw [← h]
    group

/-! ### The K3 endpoint: a spanning family of pairs -/

/-- **A spanning family of conjugation pairs refutes hypothesis (B).**  If the first components
of a family of conjugation pairs generate `(𝔽_{3^q}, +)`, then conjugation by `x = a(1)` maps the
(finite) second layer into itself — evaluate each pair at `v = 1` — so `x` normalizes the layer
and `false_of_s_normalizes_layerOne` applies.

This is the endpoint "K3" of the closure computation of
`notes/bg/appC_problem1_pair_composition.md` §7: the pair space of an escape collision is forced
into the trace-zero Frobenius module, and a single composition already breaks out of it, so its
first components span and this theorem fires. -/
theorem false_of_conjPair_spanning (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j))
    {D : Set (GaloisField p q)} (hD : ∀ s ∈ D, ∃ s', ConjPair data e s s')
    (hspan : AddSubgroup.closure D = ⊤) : False := by
  classical
  haveI : Finite (layerOne data) := by
    have hfin : ((layerOne data : Subgroup G) : Set G).Finite := by
      rw [coe_layerOne_eq_range data]
      exact Set.finite_range _
    exact hfin.to_subtype
  have ha1 : layerFieldHom data 0 (Multiplicative.ofAdd (1 : GaloisField p q)) = data.s := by
    simp only [layerFieldHom_apply, pow_zero, inv_one, one_mul, mul_one]
    rfl
  -- conjugation by `x` maps the second layer into itself
  have hmapsto : ∀ z ∈ layerOne data, data.s * z * (data.s)⁻¹ ∈ layerOne data := by
    have hJ : ∀ t : GaloisField p q,
        data.s * layerFieldHom data 1 (Multiplicative.ofAdd t) * (data.s)⁻¹ ∈ layerOne data := by
      have hsub : D ⊆ {t : GaloisField p q |
          data.s * layerFieldHom data 1 (Multiplicative.ofAdd t) * (data.s)⁻¹ ∈ layerOne data} := by
        intro t ht
        obtain ⟨t', hpair⟩ := hD t ht
        have h1 := hpair 1 ⟨1, (mul_one 1).symm⟩ one_ne_zero
        rw [one_pow, mul_one, mul_one, ha1] at h1
        rw [Set.mem_setOf_eq, h1, ← SetLike.mem_coe, coe_layerOne_eq_range data]
        exact ⟨_, rfl⟩
      have hgrp : AddSubgroup.closure D ≤
          { carrier := {t : GaloisField p q |
              data.s * layerFieldHom data 1 (Multiplicative.ofAdd t) * (data.s)⁻¹ ∈ layerOne data}
            zero_mem' := by
              simp only [Set.mem_setOf_eq, ofAdd_zero, map_one, mul_one, mul_inv_cancel]
              exact (layerOne data).one_mem
            add_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq, ofAdd_add, map_mul] at *
              have hsplit : data.s * (layerFieldHom data 1 (Multiplicative.ofAdd a) *
                  layerFieldHom data 1 (Multiplicative.ofAdd b)) * (data.s)⁻¹ =
                  (data.s * layerFieldHom data 1 (Multiplicative.ofAdd a) * (data.s)⁻¹) *
                  (data.s * layerFieldHom data 1 (Multiplicative.ofAdd b) * (data.s)⁻¹) := by
                group
              rw [hsplit]
              exact (layerOne data).mul_mem ha hb
            neg_mem' := fun {a} ha => by
              simp only [Set.mem_setOf_eq, ofAdd_neg, map_inv] at *
              have hinv : data.s * (layerFieldHom data 1 (Multiplicative.ofAdd a))⁻¹ *
                  (data.s)⁻¹ =
                  (data.s * layerFieldHom data 1 (Multiplicative.ofAdd a) * (data.s)⁻¹)⁻¹ := by
                group
              rw [hinv]
              exact (layerOne data).inv_mem ha } :=
        (AddSubgroup.closure_le _).mpr hsub
      intro t
      exact hgrp (by rw [hspan]; trivial : t ∈ AddSubgroup.closure D)
    intro z hz
    rw [← SetLike.mem_coe, coe_layerOne_eq_range data] at hz
    obtain ⟨t, rfl⟩ := hz
    exact hJ (Multiplicative.toAdd t)
  -- finiteness upgrades this to normalizing
  have hmap_le : (layerOne data).map (MulAut.conj data.s : G →* G) ≤ layerOne data := by
    rintro _ ⟨z, hz, rfl⟩
    exact hmapsto z hz
  have hcard : Nat.card ((layerOne data).map (MulAut.conj data.s : G →* G))
      = Nat.card (layerOne data) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj data.s : G →* G))
      (MulAut.conj data.s).injective
  exact false_of_s_normalizes_layerOne data hp hexp hnotfrob
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)))

/-! ### Theorems N2 and N3 -/

/-- **Theorem N2: two collisions with equal ratios refute hypothesis (B)** — with no trace
hypothesis.  If `S₁'/S₁ = S₂'/S₂` (stated multiplicatively) and `S₂' ≠ ±S₁'`, the flipped
composition of the two collision pairs realises ratio `1`, i.e. a non-zero fixed point. -/
theorem false_of_collisionPair_ratio_eq (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S₁ S₁' S₂ S₂' : GaloisField p q}
    (h₁ : CollisionPair p q e S₁ S₁') (h₂ : CollisionPair p q e S₂ S₂')
    (hratio : S₁' * S₂ = S₂' * S₁) (hne : S₂' ≠ S₁') (hne' : S₂' ≠ -S₁') : False := by
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hS₁0 : S₁ ≠ 0 := CollisionPair.left_ne_zero hcube h₁
  have hS₂0 : S₂ ≠ 0 := CollisionPair.left_ne_zero hcube h₂
  have cp₁ := ConjPair.of_collisionPair data hp hq0 hexp h₁
  have cp₂ := ConjPair.of_collisionPair data hp hq0 hexp h₂
  have hS₂'0 : S₂' ≠ 0 := cp₂.right_ne_zero hS₂0
  obtain ⟨m, hm0, hcase⟩ :=
    cp₁.composeFlip data hp hq0 hqodd hcube cp₂ hS₁0 hS₂0 hne hne'
  have hr1 : S₁' * S₂ / (S₂' * S₁) = 1 :=
    (div_eq_one_iff_eq (mul_ne_zero hS₂'0 hS₁0)).mpr hratio
  rw [hr1, one_mul] at hcase
  rcases hcase with h | h
  · exact false_of_conjPair_self data hp hqprime hqodd he hcube hexp h hm0
  · exact false_of_conjPair_self data hp hqprime hqodd he hcube hexp h hm0

/-- **Theorem N3: a Frobenius combination refutes hypothesis (B).**  Conjugation pairs are closed
under addition and under the Frobenius twist of the underlying collision, so a non-trivial
`𝔽₃[Frob]`-relation `∑ kⱼ S^{3^j} = ∑ kⱼ S'^{3^j} ≠ 0` produces a non-zero fixed point.
(The instance `k = (1,…,1)` recovers trace information; the other components of `x^q - 1` give
genuinely new certificates.) -/
theorem false_of_collisionPair_frobCombo (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S S' : GaloisField p q} (hpair : CollisionPair p q e S S') (k : ℕ → ℕ) (n : ℕ)
    (heq : ∑ j ∈ Finset.range n, k j • S ^ p ^ j = ∑ j ∈ Finset.range n, k j • S' ^ p ^ j)
    (hne : ∑ j ∈ Finset.range n, k j • S ^ p ^ j ≠ 0) : False := by
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hsum : ConjPair data e (∑ j ∈ Finset.range n, k j • S ^ p ^ j)
      (∑ j ∈ Finset.range n, k j • S' ^ p ^ j) := by
    refine ConjPair.sum _ _ _ ?_
    intro j hj
    exact (ConjPair.of_collisionPair data hp hq0 hexp (hpair.frobenius_iterate j)).nsmul (k j)
  rw [heq] at hsum
  exact false_of_conjPair_self data hp hqprime hqodd he hcube hexp hsum (heq ▸ hne)

/-! ### (B2) eliminated: any collision refutes hypothesis (B)

`ConjPair.chain` closes the polynomial family `{(c • S, c • S') : c ∈ (ZMod 3)[X]}` of pairs
into a 3-cycle, and the cyclicity of the Frobenius module
(`OddOrder.Algebra.FrobeniusCyclicModule`) converts the closure into `S' = S`:

* the graph property forces the annihilator inclusion `Ann(S) ⊆ Ann(S')`, so `S' = a₀ • S`
  for some polynomial `a₀` (`exists_aeval_frobEnd_eq_of_forall_imp`);
* chaining `(S, S') → (S', a₀² • S)` and subtracting the `a₀²`-pair forces `a₀³ • S = S`;
* in characteristic three `a₀³ - 1 = (a₀ - 1)³`, and `X ^ q - 1` is squarefree for `q ≠ 3`,
  so the annihilator is radical and `a₀ • S = S`, i.e. `S' = S` — fatal by
  `false_of_collisionPair_self`.

No trace hypothesis, no spanning hypothesis, no Frobenius-exoticity of the exponent: **one
collision kills the witness**.  (For `q = 3` no exotic exponent exists — every solution of
`e³ ≡ 1 mod n`, `n ∣ 26`, lies in `⟨3⟩` — so `false_of_centralizing` already covers that case
and nothing is lost.) -/

open Polynomial in
/-- Polynomial multiples of a Frobenius-closed pair family are conjugation pairs: the
`(ZMod p)[X]`-module action through the Frobenius endomorphism preserves the family. -/
theorem conjPair_aeval_of_frobenius_family (data : FieldNormalizerData p q G) {e : ℕ}
    {S S' : GaloisField p q}
    (hfam : ∀ j : ℕ, ConjPair data e (S ^ p ^ j) (S' ^ p ^ j)) (c : (ZMod p)[X]) :
    ConjPair data e (aeval (frobEnd p q) c S) (aeval (frobEnd p q) c S') := by
  rw [aeval_frobEnd_apply, aeval_frobEnd_apply]
  exact ConjPair.sum _ _ _ fun j _ => (hfam j).nsmul _

open Polynomial in
/-- Polynomial multiples of a collision are conjugation pairs: the `(ZMod p)[X]`-module
action through the Frobenius endomorphism preserves the pair family. -/
theorem conjPair_aeval_of_collisionPair (data : FieldNormalizerData p q G) (hp : p = 3)
    (hq0 : q ≠ 0) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S S' : GaloisField p q} (hpair : CollisionPair p q e S S') (c : (ZMod p)[X]) :
    ConjPair data e (aeval (frobEnd p q) c S) (aeval (frobEnd p q) c S') :=
  conjPair_aeval_of_frobenius_family data
    (fun j => ConjPair.of_collisionPair data hp hq0 hexp (hpair.frobenius_iterate j)) c

open Polynomial in
/-- **The chain-reversal engine, for pair families of any provenance.**  A Frobenius-closed
conjugation-pair family with non-zero seed refutes hypothesis (B) — no collision needed.
Chain reversal (`ConjPair.chain`) plus the cyclicity of the Frobenius module force `S' = S`,
which is fatal by the fixed-point principle `false_of_conjPair_self`.  (Closed loops of the
collision-free skew-pair calculus provide such families; a collision provides one via
`ConjPair.of_collisionPair` and `CollisionPair.frobenius_iterate`.) -/
theorem false_of_conjPair_frobenius_family (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S S' : GaloisField p q} (hS0 : S ≠ 0)
    (hfam : ∀ j : ℕ, ConjPair data e (S ^ p ^ j) (S' ^ p ^ j)) : False := by
  subst hp
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hcp : ∀ c : (ZMod 3)[X],
      ConjPair data e (aeval (frobEnd 3 q) c S) (aeval (frobEnd 3 q) c S') :=
    conjPair_aeval_of_frobenius_family data hfam
  have haux : ∀ y : GaloisField 3 q, ∀ a b : (ZMod 3)[X],
      aeval (frobEnd 3 q) (a * b) y
        = aeval (frobEnd 3 q) a (aeval (frobEnd 3 q) b y) := by
    intro y a b
    rw [map_mul, Module.End.mul_apply]
  -- the graph property forces the annihilator inclusion
  have hann : ∀ c : (ZMod 3)[X],
      aeval (frobEnd 3 q) c S = 0 → aeval (frobEnd 3 q) c S' = 0 := by
    intro c h0
    have h := hcp c
    rw [h0] at h
    exact ConjPair.right_eq_zero h
  obtain ⟨a₀, ha₀⟩ := exists_aeval_frobEnd_eq_of_forall_imp 3 q hq0 hann
  -- chain reversal at the pair `(S, S')` and its `a₀`-translate
  have h1 : ConjPair data e S S' := by
    have h := hcp 1
    simpa using h
  have h2 : ConjPair data e S' (aeval (frobEnd 3 q) a₀ S') := by
    have h := hcp a₀
    rwa [ha₀] at h
  have h3 := ConjPair.chain data rfl h1 h2
  have hsq2 : aeval (frobEnd 3 q) a₀ S' = aeval (frobEnd 3 q) (a₀ * a₀) S := by
    rw [haux S a₀ a₀, ha₀]
  rw [hsq2] at h3
  -- subtract the `a₀²`-pair: the graph forces `a₀³ • S = S`
  have h5 := (hcp (a₀ * a₀)).add h3.neg
  rw [add_neg_cancel] at h5
  have h6 : aeval (frobEnd 3 q) (a₀ * a₀) S' = S :=
    add_neg_eq_zero.mp (ConjPair.right_eq_zero h5)
  -- `(a₀³ - 1) • S = 0`, and `(a₀ - 1)³ = a₀³ - 1` in characteristic three
  have h33 : aeval (frobEnd 3 q) (a₀ ^ 3) S = S := by
    have hpow : a₀ ^ 3 = (a₀ * a₀) * a₀ := by ring
    rw [hpow, haux S (a₀ * a₀) a₀, ha₀]
    exact h6
  have h7 : aeval (frobEnd 3 q) (a₀ ^ 3 - 1) S = 0 := by
    rw [map_sub, LinearMap.sub_apply, h33, map_one, Module.End.one_apply, sub_self]
  haveI : CharP ((ZMod 3)[X]) 3 :=
    charP_of_injective_ringHom (C_injective (R := ZMod 3)) 3
  haveI : ExpChar ((ZMod 3)[X]) 3 := .prime Nat.prime_three
  have hchar : (a₀ - 1) ^ 3 = a₀ ^ 3 - 1 := by
    rw [sub_pow_expChar, one_pow]
  have h8 : aeval (frobEnd 3 q) ((a₀ - 1) ^ 3) S = 0 := by
    rw [hchar]
    exact h7
  have hpq : ¬ (3 : ℕ) ∣ q := fun hdvd =>
    hq3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hqprime).mp hdvd).symm)
  have h9 := aeval_frobEnd_eq_zero_of_pow 3 q hq0 hpq (by norm_num : (3 : ℕ) ≠ 0) h8
  rw [map_sub, LinearMap.sub_apply, map_one, Module.End.one_apply] at h9
  have hSS : S' = S := by
    rw [← ha₀]
    exact sub_eq_zero.mp h9
  have hself : ConjPair data e S S := by
    have h := h1
    rwa [hSS] at h
  exact false_of_conjPair_self data rfl hqprime hqodd he hcube hexp hself hS0

open Polynomial in
/-- **(B2) is eliminated: a single collision refutes hypothesis (B)** — with no trace
hypothesis, no spanning hypothesis, and no condition on the exponent beyond the standing
ones.  Special case of `false_of_conjPair_frobenius_family` with the family supplied by the
Frobenius twists of the collision. -/
theorem false_of_collisionPair (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S S' : GaloisField p q} (hpair : CollisionPair p q e S S') : False :=
  false_of_conjPair_frobenius_family data hp hqprime hq3 hqodd he hcube hexp
    (CollisionPair.left_ne_zero hcube hpair)
    (fun j => ConjPair.of_collisionPair data hp hqprime.ne_zero hexp
      (hpair.frobenius_iterate j))

end PairComposition

end OddOrder.BG.AppC.Problem1
