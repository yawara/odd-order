/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_Problem1PairComposition

/-!
# BG Appendix C, Problem 1: the skew-pair calculus

The collision-free attack on hypothesis (B) (`notes/bg/appC_problem1_resolution.md` §3,
issue 0181).  A **skew pair** `SkewPair data e A B X Y` is the relation

`a(A w) · b(X wᵉ) · a(B w)⁻¹ = b(Y wᵉ)`   (for every non-zero square `w`),

where `a`, `b` are the zeroth and first layers.  Eliminating the third-layer factorisations
`layerFieldHom_two_factor` of two Paley points `p ≠ r` against each other produces the
**skew edge** `skewPair_edge`, a skew pair with data

`(A, B; X, Y) = (δ₀, δ₁; K(p), K(r))`,  `δ₀ = rᵉ - pᵉ`,  `δ₁ = (r-1)ᵉ - (p-1)ᵉ`,

with **no collision hypothesis**: a collision is exactly the degenerate edge with `A = B`.

Design note (layer convention).  The mathematical record builds the calculus one layer up,
with conjugating layer `b` and line layer `d`; the two versions are `conjGen`-conjugate and
carry the same edge data.  Building on layers `(0, 1)` instead makes a closed loop (`A = B`)
*literally* a conjugation pair after the substitution `v := A w` (`conjPair_of_self`), so the
chain-reversal engine `false_of_conjPair_frobenius_family` applies with no conjugation step.

The calculus:

* `SkewPair.rev`, `SkewPair.comp`, `SkewPair.rescale` — the groupoid operations: reversal
  `(B, A; -X, -Y)`, composition along a matching inner parameter `(A, C; X₁+X₂, Y₁+Y₂)`, and
  rescaling by a non-zero square `(As, Bs; Xsᵉ, Ysᵉ)`.
* `SkewPair.self_symm` / `self_left_eq_zero` / `self_right_eq_zero` — closed-loop reversal
  and the graph property: in a closed loop the two weights vanish together.
* `SkewPair.conjPair_of_self` / `conjPair_of_self_neg` — a closed loop whose parameter is a
  square (resp. non-square) is a conjugation pair with seed `X A⁻ᵉ` (resp. `-Y (-A)⁻ᵉ`,
  read backwards).
* `false_of_skewPair_self_frobenius_family` — **loop ⟹ kill**: a Frobenius-closed family of
  closed loops with a non-vanishing weight refutes hypothesis (B), through the family capstone
  `false_of_conjPair_frobenius_family`.

Mathematical record: `notes/bg/appC_problem1_resolution.md` §3 (issues 0180/0181).
-/

namespace OddOrder.BG.AppC.Problem1

section SkewCalculus

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **A skew pair.**  `SkewPair data e A B X Y` says that multiplying by the zeroth-layer
elements `a(A w)`, `a(B w)⁻¹` carries the `X`-twisted first-layer line to the `Y`-twisted one,
coherently over every non-zero square height `w`.  For `A = B` this is conjugation; the general
shape is what the elimination of the third layer between two Paley points actually produces. -/
def SkewPair (data : FieldNormalizerData p q G) (e : ℕ) (A B X Y : GaloisField p q) : Prop :=
  ∀ w : GaloisField p q, IsSquare w → w ≠ 0 →
    layerFieldHom data 0 (Multiplicative.ofAdd (A * w)) *
        layerFieldHom data 1 (Multiplicative.ofAdd (X * w ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (B * w)))⁻¹
      = layerFieldHom data 1 (Multiplicative.ofAdd (Y * w ^ e))

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

namespace SkewPair

variable {data : FieldNormalizerData p q G} {e : ℕ}

/-- A conjugation pair is exactly a skew pair with both parameters `1`. -/
theorem one_one_iff {s s' : GaloisField p q} :
    SkewPair data e 1 1 s s' ↔ ConjPair data e s s' := by
  unfold SkewPair ConjPair
  simp only [one_mul]

/-- **Reversal.**  Inverting the relation swaps the two parameters and negates the weights. -/
theorem rev {A B X Y : GaloisField p q} (h : SkewPair data e A B X Y) :
    SkewPair data e B A (-X) (-Y) := by
  intro w hw hw0
  rw [layer_neg data 1 (show -X * w ^ e = -(X * w ^ e) by ring),
    layer_neg data 1 (show -Y * w ^ e = -(Y * w ^ e) by ring), ← h w hw hw0]
  group

/-- **Composition.**  When the inner parameters match, the zeroth-layer factors cancel and the
weights add. -/
theorem comp {A B C X₁ Y₁ X₂ Y₂ : GaloisField p q} (h₁ : SkewPair data e A B X₁ Y₁)
    (h₂ : SkewPair data e B C X₂ Y₂) : SkewPair data e A C (X₁ + X₂) (Y₁ + Y₂) := by
  intro w hw hw0
  rw [layer_split data 1 (show (X₁ + X₂) * w ^ e = X₁ * w ^ e + X₂ * w ^ e by ring),
    layer_split data 1 (show (Y₁ + Y₂) * w ^ e = Y₁ * w ^ e + Y₂ * w ^ e by ring),
    ← h₁ w hw hw0, ← h₂ w hw hw0]
  group

/-- **Rescaling.**  Substituting `w ↦ s w` for a non-zero square `s` rescales the parameters by
`s` and the weights by `sᵉ`. -/
theorem rescale {A B X Y : GaloisField p q} (h : SkewPair data e A B X Y)
    {s : GaloisField p q} (hs : IsSquare s) (hs0 : s ≠ 0) :
    SkewPair data e (A * s) (B * s) (X * s ^ e) (Y * s ^ e) := by
  intro w hw hw0
  have g := h (s * w) (hs.mul hw) (mul_ne_zero hs0 hw0)
  rw [show A * (s * w) = A * s * w by ring, show B * (s * w) = B * s * w by ring,
    show X * (s * w) ^ e = X * s ^ e * w ^ e by rw [mul_pow]; ring,
    show Y * (s * w) ^ e = Y * s ^ e * w ^ e by rw [mul_pow]; ring] at g
  exact g

/-- **Closed-loop reversal.**  A closed loop (`A = B`) is a conjugation relation; reading it
backwards negates the parameter and swaps the weights. -/
theorem self_symm {A X Y : GaloisField p q} (h : SkewPair data e A A X Y) :
    SkewPair data e (-A) (-A) Y X := by
  intro w hw hw0
  rw [layer_neg data 0 (show -A * w = -(A * w) by ring), ← h w hw hw0]
  group

/-- **The graph property for closed loops.**  A closed loop with vanishing left weight has
vanishing right weight: the first layer is a faithful copy of the field. -/
theorem self_right_eq_zero {A Y : GaloisField p q} (h : SkewPair data e A A 0 Y) : Y = 0 := by
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
  have hval : (0 : GaloisField p q) = Y * 1 ^ e := by
    have := congrArg Multiplicative.toAdd harg
    simpa using this
  simpa using hval.symm

/-- **The graph property, other direction.**  A closed loop with vanishing right weight has
vanishing left weight. -/
theorem self_left_eq_zero {A X : GaloisField p q} (h : SkewPair data e A A X 0) : X = 0 :=
  self_right_eq_zero h.self_symm

/-- **A closed loop with square parameter is a conjugation pair.**  Substituting `v := A w`
(a bijection of the non-zero squares) turns `a(Aw) · b(Xwᵉ) · a(Aw)⁻¹ = b(Ywᵉ)` into the
standard pair relation with seed ratio `(X A⁻ᵉ, Y A⁻ᵉ)`. -/
theorem conjPair_of_self {A X Y : GaloisField p q} (h : SkewPair data e A A X Y)
    (hA : IsSquare A) (hA0 : A ≠ 0) :
    ConjPair data e (X * (A ^ e)⁻¹) (Y * (A ^ e)⁻¹) := by
  intro v hv hv0
  have g := h (A⁻¹ * v) (hA.inv.mul hv) (mul_ne_zero (inv_ne_zero hA0) hv0)
  rw [show A * (A⁻¹ * v) = v by rw [← mul_assoc, mul_inv_cancel₀ hA0, one_mul],
    show X * (A⁻¹ * v) ^ e = X * (A ^ e)⁻¹ * v ^ e by rw [mul_pow, inv_pow]; ring,
    show Y * (A⁻¹ * v) ^ e = Y * (A ^ e)⁻¹ * v ^ e by rw [mul_pow, inv_pow]; ring] at g
  exact g

/-- **A closed loop with non-square parameter is a conjugation pair read backwards.**  `-A` is
then a square (`-1` is a non-square), and reversing the conjugation swaps the two weights. -/
theorem conjPair_of_self_neg {A X Y : GaloisField p q} (h : SkewPair data e A A X Y)
    (hA : IsSquare (-A)) (hA0 : A ≠ 0) :
    ConjPair data e (Y * ((-A) ^ e)⁻¹) (X * ((-A) ^ e)⁻¹) :=
  conjPair_of_self h.self_symm hA (neg_ne_zero.mpr hA0)

end SkewPair

/-- **The skew edge.**  Eliminating the third layer between the factorisations
`layerFieldHom_two_factor` of two Paley points `(p₀, p₁)` and `(r₀, r₁)` yields the skew pair

`(δ₀, δ₁; K(p), K(r))`,  `δ₀ = r₀ᵉ - p₀ᵉ`,  `δ₁ = r₁ᵉ - p₁ᵉ`,

with no collision hypothesis (`δ₀ = δ₁` is precisely a collision). -/
theorem skewPair_edge (data : FieldNormalizerData p q G) (hp : p = 3) (hq : q ≠ 0) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (p₀ p₁ r₀ r₁ : NormSet.normOneUnits p q)
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1) :
    SkewPair data e (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
      (normOneVal r₁ ^ e - normOneVal p₁ ^ e)
      (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
      (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) := by
  intro w hw hw0
  obtain ⟨u, hu⟩ : ∃ u : NormSet.normOneUnits p q, normOneVal u = w :=
    ⟨⟨Units.mk0 w hw0, (mem_normOneUnits_iff_isSquare hp hq _).mpr (by simpa using hw)⟩, rfl⟩
  -- the auxiliary height `z := u^{e²}` satisfies `zᵉ = u` and `z^{e²} = uᵉ`
  have hz1 : (u ^ (e * e)) ^ e = u := by
    rw [← pow_mul]
    exact normOneUnits_pow_cube data hp hexp u
  have hz2 : (u ^ (e * e)) ^ (e * e) = u ^ e := by
    rw [← pow_mul, show e * e * (e * e) = e * e * e * e by ring, pow_mul,
      normOneUnits_pow_cube data hp hexp u]
  have hP := layerFieldHom_two_factor data hp hexp p₀ p₁ (u ^ (e * e)) hpp
  have hR := layerFieldHom_two_factor data hp hexp r₀ r₁ (u ^ (e * e)) hrr
  rw [hz1, hz2] at hP hR
  simp only [normOneVal_mul, normOneVal_pow, hu] at hP hR
  have hEq := hP.symm.trans hR
  rw [layer_split data 0 (show (normOneVal r₀ ^ e - normOneVal p₀ ^ e) * w
        = normOneVal r₀ ^ e * w + -(normOneVal p₀ ^ e * w) by ring),
    layer_neg data 0 (rfl : -(normOneVal p₀ ^ e * w) = -(normOneVal p₀ ^ e * w)),
    layer_split data 0 (show (normOneVal r₁ ^ e - normOneVal p₁ ^ e) * w
        = normOneVal r₁ ^ e * w + -(normOneVal p₁ ^ e * w) by ring),
    layer_neg data 0 (rfl : -(normOneVal p₁ ^ e * w) = -(normOneVal p₁ ^ e * w))]
  calc layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * w)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₀ ^ e * w)))⁻¹ *
        layerFieldHom data 1 (Multiplicative.ofAdd
          ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * w ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * w)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₁ ^ e * w)))⁻¹)⁻¹
      = layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * w)) *
          ((layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₀ ^ e * w)))⁻¹ *
            layerFieldHom data 1 (Multiplicative.ofAdd
              ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * w ^ e)) *
            layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₁ ^ e * w))) *
          (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * w)))⁻¹ := by
        group
    _ = layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * w)) *
          ((layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * w)))⁻¹ *
            layerFieldHom data 1 (Multiplicative.ofAdd
              ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * w ^ e)) *
            layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * w))) *
          (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * w)))⁻¹ := by
        rw [hEq]
    _ = layerFieldHom data 1 (Multiplicative.ofAdd
          ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * w ^ e)) := by
        group

/-- The left edge parameter `δ₀ = r₀ᵉ - p₀ᵉ` is non-zero for distinct Paley points. -/
theorem skewPair_edge_left_ne_zero {e : ℕ}
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {p₀ r₀ : NormSet.normOneUnits p q} (hne : normOneVal p₀ ≠ normOneVal r₀) :
    normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0 := by
  intro h0
  exact hne (Paley.pow_injective_of_cube hcube (sub_eq_zero.mp h0)).symm

/-- The weight `K(p) = (p-1)^{e²} - p^{e²}` of an edge is non-zero: the `e²`-power map is
injective and the two Paley coordinates differ by `1`. -/
theorem skewPair_edge_weight_ne_zero {e : ℕ}
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {p₀ p₁ : NormSet.normOneUnits p q} (hpp : normOneVal p₀ = normOneVal p₁ + 1) :
    normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e) ≠ 0 := by
  intro h0
  have hpow : (normOneVal p₁ ^ e) ^ e = (normOneVal p₀ ^ e) ^ e := by
    rw [← pow_mul, ← pow_mul]
    exact sub_eq_zero.mp h0
  have h1 : normOneVal p₁ = normOneVal p₀ :=
    Paley.pow_injective_of_cube hcube (Paley.pow_injective_of_cube hcube hpow)
  rw [h1] at hpp
  simp at hpp

/-- **Loop ⟹ kill.**  A Frobenius-closed family of closed loops whose weight pair does not
vanish refutes hypothesis (B).  If one weight vanishes the graph property kills the loop
directly; otherwise the loop is a conjugation pair with non-zero seed — forwards when the loop
parameter is a square, backwards when it is not (the square class is Frobenius-stable, so the
orientation is uniform in the family) — and the chain-reversal engine
`false_of_conjPair_frobenius_family` applies. -/
theorem false_of_skewPair_self_frobenius_family (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {A X Y : GaloisField p q} (hA0 : A ≠ 0) (hXY : ¬(X = 0 ∧ Y = 0))
    (hfam : ∀ j : ℕ, SkewPair data e (A ^ p ^ j) (A ^ p ^ j) (X ^ p ^ j) (Y ^ p ^ j)) :
    False := by
  subst hp
  have h00 : SkewPair data e A A X Y := by simpa using hfam 0
  -- the two weights vanish together, so both are non-zero
  have hX0 : X ≠ 0 := by
    intro h0
    exact hXY ⟨h0, SkewPair.self_right_eq_zero (by rwa [h0] at h00)⟩
  have hY0 : Y ≠ 0 := by
    intro h0
    exact hXY ⟨SkewPair.self_left_eq_zero (by rwa [h0] at h00), h0⟩
  -- `±A` is a square
  letI : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  haveI : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have hcard : Fintype.card (GaloisField 3 q) = 3 ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 q hqprime.ne_zero
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  have h4 : Fintype.card (GaloisField 3 q) % 4 = 3 := by
    rw [hcard]
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    have hk : q = 2 * (q / 2) + 1 := by omega
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rcases Paley.isSquare_or_isSquare_neg hchar2 h4 hA0 with hsq | hnsq
  · -- forward orientation: seed `X A⁻ᵉ`
    have hfam' : ∀ j : ℕ,
        ConjPair data e ((X * (A ^ e)⁻¹) ^ 3 ^ j) ((Y * (A ^ e)⁻¹) ^ 3 ^ j) := by
      intro j
      have h := SkewPair.conjPair_of_self (hfam j) (hsq.pow _) (pow_ne_zero _ hA0)
      rw [show (X * (A ^ e)⁻¹) ^ 3 ^ j = X ^ 3 ^ j * ((A ^ 3 ^ j) ^ e)⁻¹ by
          rw [mul_pow, inv_pow, pow_right_comm],
        show (Y * (A ^ e)⁻¹) ^ 3 ^ j = Y ^ 3 ^ j * ((A ^ 3 ^ j) ^ e)⁻¹ by
          rw [mul_pow, inv_pow, pow_right_comm]]
      exact h
    exact false_of_conjPair_frobenius_family data rfl hqprime hq3 hqodd he hcube hexp
      (mul_ne_zero hX0 (inv_ne_zero (pow_ne_zero _ hA0))) hfam'
  · -- backward orientation: seed `Y (-A)⁻ᵉ`
    have hfam' : ∀ j : ℕ,
        ConjPair data e ((Y * ((-A) ^ e)⁻¹) ^ 3 ^ j) ((X * ((-A) ^ e)⁻¹) ^ 3 ^ j) := by
      intro j
      have hodd3j : Odd (3 ^ j : ℕ) := (by decide : Odd (3 : ℕ)).pow
      have hAneg : (-A) ^ 3 ^ j = -(A ^ 3 ^ j) := hodd3j.neg_pow A
      have hAj : IsSquare (-(A ^ 3 ^ j)) := by
        rw [← hAneg]
        exact hnsq.pow _
      have h := SkewPair.conjPair_of_self_neg (hfam j) hAj (pow_ne_zero _ hA0)
      rw [show (Y * ((-A) ^ e)⁻¹) ^ 3 ^ j = Y ^ 3 ^ j * ((-(A ^ 3 ^ j)) ^ e)⁻¹ by
          rw [mul_pow, inv_pow, pow_right_comm, hAneg],
        show (X * ((-A) ^ e)⁻¹) ^ 3 ^ j = X ^ 3 ^ j * ((-(A ^ 3 ^ j)) ^ e)⁻¹ by
          rw [mul_pow, inv_pow, pow_right_comm, hAneg]]
      exact h
    exact false_of_conjPair_frobenius_family data rfl hqprime hq3 hqodd he hcube hexp
      (mul_ne_zero hY0 (inv_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hA0)))) hfam'

/-! ### The same-slot two-loop: proportional edges have proportional weights

Two edges whose parameters are proportional by a non-zero square `s` (`δ₀ = δ₀'·s`,
`δ₁ = δ₁'·s` — in slot language: the same ratio class and the same sign component) compose
into the closed loop `e ∘ rev(e'·s)` with weights `(K(p) - K(p')sᵉ, K(r) - K(r')sᵉ)`,
uniformly in the Frobenius twist.  The kill lemma forces both weights to vanish, i.e.
`κ := K δ₁⁻ᵉ` is constant on each slot (stated multiplied-out, with no division).  This is
step 3 of the case tree of `notes/bg/appC_problem1_resolution.md` §5. -/

/-- A Paley pair is Frobenius-stable: `p₀ = p₁ + 1` gives `p₀^{pʲ} = p₁^{pʲ} + 1`. -/
theorem paley_frobenius_iterate {p₀ p₁ : NormSet.normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (j : ℕ) :
    normOneVal (p₀ ^ p ^ j) = normOneVal (p₁ ^ p ^ j) + 1 := by
  simp only [normOneVal_pow]
  rw [hpp, add_pow_char_pow, one_pow]

/-- Frobenius twists of the edge data: differences of `e`-th (or `e²`-th) powers of norm-one
values twist by `x ↦ x^{pʲ}` componentwise. -/
private theorem normOneVal_sub_pow_frobenius (j k : ℕ) (x y : NormSet.normOneUnits p q) :
    normOneVal (x ^ p ^ j) ^ k - normOneVal (y ^ p ^ j) ^ k
      = (normOneVal x ^ k - normOneVal y ^ k) ^ p ^ j := by
  rw [normOneVal_pow, normOneVal_pow, pow_right_comm (normOneVal x) (p ^ j) k,
    pow_right_comm (normOneVal y) (p ^ j) k, ← sub_pow_char_pow]

/-- **The same-slot two-loop kill.**  Two edges with parameters proportional by a non-zero
square `s` compose into a closed loop; if either component of its weight
`(K(p) - K(p')sᵉ, K(r) - K(r')sᵉ)` does not vanish, hypothesis (B) is refuted.  The loop
family is supplied by the Frobenius twists of the two Paley pairs, whose proportionality
constants are the twists of `s`. -/
theorem false_of_proportional_edges (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ p₀' p₁' r₀' r₁' : NormSet.normOneUnits p q} {s : GaloisField p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hpp' : normOneVal p₀' = normOneVal p₁' + 1) (hrr' : normOneVal r₀' = normOneVal r₁' + 1)
    (hne : normOneVal p₀ ≠ normOneVal r₀) (hs : IsSquare s) (hs0 : s ≠ 0)
    (houter : normOneVal r₀ ^ e - normOneVal p₀ ^ e
      = (normOneVal r₀' ^ e - normOneVal p₀' ^ e) * s)
    (hinner : normOneVal r₁ ^ e - normOneVal p₁ ^ e
      = (normOneVal r₁' ^ e - normOneVal p₁' ^ e) * s)
    (hW : ¬(normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)
          = (normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e)) * s ^ e ∧
        normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)
          = (normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e)) * s ^ e)) : False := by
  subst hp
  have hq0 : q ≠ 0 := hqprime.ne_zero
  refine false_of_skewPair_self_frobenius_family data rfl hqprime hq3 hqodd he hcube hexp
    (A := normOneVal r₀ ^ e - normOneVal p₀ ^ e)
    (X := (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
      - (normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e)) * s ^ e)
    (Y := (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
      - (normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e)) * s ^ e)
    (skewPair_edge_left_ne_zero hcube hne) ?_ ?_
  · rintro ⟨hX0, hY0⟩
    exact hW ⟨sub_eq_zero.mp hX0, sub_eq_zero.mp hY0⟩
  · intro j
    have hppj := paley_frobenius_iterate hpp j
    have hrrj := paley_frobenius_iterate hrr j
    have hppj' := paley_frobenius_iterate hpp' j
    have hrrj' := paley_frobenius_iterate hrr' j
    have he₁ := skewPair_edge data rfl hq0 hexp _ _ _ _ hppj hrrj
    have he₂ := skewPair_edge data rfl hq0 hexp _ _ _ _ hppj' hrrj'
    rw [normOneVal_sub_pow_frobenius j e r₀ p₀, normOneVal_sub_pow_frobenius j e r₁ p₁,
      normOneVal_sub_pow_frobenius j (e * e) p₁ p₀,
      normOneVal_sub_pow_frobenius j (e * e) r₁ r₀] at he₁
    rw [normOneVal_sub_pow_frobenius j e r₀' p₀', normOneVal_sub_pow_frobenius j e r₁' p₁',
      normOneVal_sub_pow_frobenius j (e * e) p₁' p₀',
      normOneVal_sub_pow_frobenius j (e * e) r₁' r₀'] at he₂
    have he₂' := (he₂.rev).rescale (s := s ^ 3 ^ j) (hs.pow _) (pow_ne_zero _ hs0)
    have hin_j : (normOneVal r₁' ^ e - normOneVal p₁' ^ e) ^ 3 ^ j * s ^ 3 ^ j
        = (normOneVal r₁ ^ e - normOneVal p₁ ^ e) ^ 3 ^ j := by
      rw [← mul_pow, ← hinner]
    have hout_j : (normOneVal r₀' ^ e - normOneVal p₀' ^ e) ^ 3 ^ j * s ^ 3 ^ j
        = (normOneVal r₀ ^ e - normOneVal p₀ ^ e) ^ 3 ^ j := by
      rw [← mul_pow, ← houter]
    rw [hin_j, hout_j] at he₂'
    have hcomp := he₁.comp he₂'
    have hXj : (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) ^ 3 ^ j +
        -((normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e)) ^ 3 ^ j) * (s ^ 3 ^ j) ^ e
        = ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
            - (normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e)) * s ^ e) ^ 3 ^ j := by
      conv_rhs => rw [sub_pow_char_pow, mul_pow, pow_right_comm s e (3 ^ j)]
      ring
    have hYj : (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) ^ 3 ^ j +
        -((normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e)) ^ 3 ^ j) * (s ^ 3 ^ j) ^ e
        = ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
            - (normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e)) * s ^ e) ^ 3 ^ j := by
      conv_rhs => rw [sub_pow_char_pow, mul_pow, pow_right_comm s e (3 ^ j)]
      ring
    rw [hXj, hYj] at hcomp
    exact hcomp

/-- **Same-slot κ-constancy.**  Proportional edges have proportional weights: both components
of the two-loop weight vanish, i.e. `K(p) = K(p')sᵉ` and `K(r) = K(r')sᵉ`.  In slot language
`κ = K δ₁⁻ᵉ` (equivalently `κ̂ = K δ₀⁻ᵉ`) is well defined on each slot.  Step 3 of the case
tree. -/
theorem weights_proportional_of_proportional_edges (data : FieldNormalizerData p q G)
    (hp : p = 3) (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ p₀' p₁' r₀' r₁' : NormSet.normOneUnits p q} {s : GaloisField p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hpp' : normOneVal p₀' = normOneVal p₁' + 1) (hrr' : normOneVal r₀' = normOneVal r₁' + 1)
    (hne : normOneVal p₀ ≠ normOneVal r₀) (hs : IsSquare s) (hs0 : s ≠ 0)
    (houter : normOneVal r₀ ^ e - normOneVal p₀ ^ e
      = (normOneVal r₀' ^ e - normOneVal p₀' ^ e) * s)
    (hinner : normOneVal r₁ ^ e - normOneVal p₁ ^ e
      = (normOneVal r₁' ^ e - normOneVal p₁' ^ e) * s) :
    normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)
        = (normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e)) * s ^ e ∧
      normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)
        = (normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e)) * s ^ e := by
  by_contra hW
  exact false_of_proportional_edges data hp hqprime hq3 hqodd he hcube hexp hpp hrr hpp' hrr'
    hne hs hs0 houter hinner hW

end SkewCalculus

end OddOrder.BG.AppC.Problem1
