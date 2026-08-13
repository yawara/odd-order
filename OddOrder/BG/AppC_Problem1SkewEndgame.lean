/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_Problem1SkewCalculus
import OddOrder.BG.AppC_Problem1Exponent

/-!
# BG Appendix C, Problem 1: the endgame — the κ-conspiracy refuted

The case tree of `notes/bg/appC_problem1_resolution.md` §5, built on the skew-pair calculus
(`AppC_Problem1SkewCalculus`).  A witness surviving Part I (no collision) and Part II (every
closed loop has vanishing weight — *conspiracy*) is walked through the population branches:

* **Step 4** (`false_of_three_antipodal`): three distinct Paley points whose pairwise ratios
  are all `-1` force `K ≡ 0` through the antipodal relations `K(p) = -K(r)` — contradicting
  `K ≠ 0`.  This kills the singleton-`{-1}` population.
* Steps 5–7 (the exchange relation, the master formula and its branches) follow.

Mathematical record: `notes/bg/appC_problem1_resolution.md` §4–§5 (issues 0180/0181).
-/

namespace OddOrder.BG.AppC.Problem1

section SkewEndgame

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **Step 4: the singleton-`{-1}` population dies.**  If the three ordered pairs among three
distinct Paley points all have ratio `-1` (`δ₁ = -δ₀`), the antipodal relations give
`K(a) + K(b) = K(a) + K(c) = K(b) + K(c) = 0`, hence `2·K(c) = 0`; since `2 = -1` is
invertible in characteristic three this forces `K(c) = 0`, contradicting the non-vanishing of
the edge weight. -/
theorem false_of_three_antipodal (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {a₀ a₁ b₀ b₁ c₀ c₁ : NormSet.normOneUnits p q}
    (haa : normOneVal a₀ = normOneVal a₁ + 1) (hbb : normOneVal b₀ = normOneVal b₁ + 1)
    (hcc : normOneVal c₀ = normOneVal c₁ + 1)
    (hab : normOneVal a₀ ≠ normOneVal b₀) (hac : normOneVal a₀ ≠ normOneVal c₀)
    (hbc : normOneVal b₀ ≠ normOneVal c₀)
    (hoppab : normOneVal b₁ ^ e - normOneVal a₁ ^ e
      = -(normOneVal b₀ ^ e - normOneVal a₀ ^ e))
    (hoppac : normOneVal c₁ ^ e - normOneVal a₁ ^ e
      = -(normOneVal c₀ ^ e - normOneVal a₀ ^ e))
    (hoppbc : normOneVal c₁ ^ e - normOneVal b₁ ^ e
      = -(normOneVal c₀ ^ e - normOneVal b₀ ^ e)) : False := by
  have hKab := weight_sum_eq_zero_of_antipodal_edge data hp hqprime hq3 hqodd he hcube hexp
    haa hbb hab hoppab
  have hKac := weight_sum_eq_zero_of_antipodal_edge data hp hqprime hq3 hqodd he hcube hexp
    haa hcc hac hoppac
  have hKbc := weight_sum_eq_zero_of_antipodal_edge data hp hqprime hq3 hqodd he hcube hexp
    hbb hcc hbc hoppbc
  subst hp
  have h30 : (3 : GaloisField 3 q) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 3 q) 3
  have h2 : (2 : GaloisField 3 q)
      * (normOneVal c₁ ^ (e * e) - normOneVal c₀ ^ (e * e)) = 0 := by
    linear_combination hKac + hKbc - hKab
  have h2ne : (2 : GaloisField 3 q) ≠ 0 := by
    intro h20
    exact one_ne_zero (by linear_combination h30 - h20 : (1 : GaloisField 3 q) = 0)
  exact skewPair_edge_weight_ne_zero hcube hcc
    ((mul_eq_zero.mp h2).resolve_left h2ne)

/-! ### Step 5: the commutator loop and the exchange relation (EX)

For two Paley pairs `(p, r)` and `(p', r')` with ratios `ρ = δ₁/δ₀`, `σ = δ₁'/δ₀'`, the
commutator loop climbs `δ₀ → δ₁ → δ₁σ` by the edge itself and a `σ`-leg, and descends
`δ₁σ → δ₀σ → δ₀` by a backwards `ρ`-leg and a backwards `σ`-leg.  The chaining and closure
conditions hold identically (`ρσ = σρ`), each leg exists in exactly one orientation
(`leg_resolved`), and conspiracy forces both weight components to vanish — the exchange
relation (EX).  The Booleans `b₂ b₃ b₄` record the forced orientations; the loop for the
opposite entry component `-δ₀` is this relation applied to the swapped pair `(r, p)`. -/

/-- **The exchange relation (EX).**  Conspiracy on the commutator loop of two Paley pairs, in
sign-resolved form: for any orientation sector `(b₂, b₃, b₄)` matching the square classes of
`δ₁/δ₀'`, `δ₁'/δ₀'` and `δ₀/δ₀'`, both weight components of the loop vanish.  Step 5 of the
case tree. -/
theorem exchange_relation (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ p₀' p₁' r₀' r₁' : NormSet.normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hpp' : normOneVal p₀' = normOneVal p₁' + 1) (hrr' : normOneVal r₀' = normOneVal r₁' + 1)
    (hne : normOneVal p₀ ≠ normOneVal r₀) (hne' : normOneVal p₀' ≠ normOneVal r₀')
    (b₂ b₃ b₄ : Bool)
    (hs₂ : cond b₂
      (IsSquare ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹))
      (IsSquare (-((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹))))
    (hs₃ : cond b₃
      (IsSquare ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
        * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹))
      (IsSquare (-((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
        * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹))))
    (hs₄ : cond b₄
      (IsSquare ((normOneVal r₀ ^ e - normOneVal p₀ ^ e)
        * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹))
      (IsSquare (-((normOneVal r₀ ^ e - normOneVal p₀ ^ e)
        * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹)))) :
    (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
        + legWeight (normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e))
            (normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e)) b₂
          * ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
            * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹) ^ e
        - legWeight (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
            (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) b₃
          * ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
            * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹) ^ e
        - legWeight (normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e))
            (normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e)) b₄
          * ((normOneVal r₀ ^ e - normOneVal p₀ ^ e)
            * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹) ^ e = 0
    ∧ (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
        + legWeight (normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e))
            (normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e)) b₂
          * ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
            * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹) ^ e
        - legWeight (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
            (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) b₃
          * ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
            * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹) ^ e
        - legWeight (normOneVal r₁' ^ (e * e) - normOneVal r₀' ^ (e * e))
            (normOneVal p₁' ^ (e * e) - normOneVal p₀' ^ (e * e)) b₄
          * ((normOneVal r₀ ^ e - normOneVal p₀ ^ e)
            * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹) ^ e = 0 := by
  subst hp
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hD0 : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne
  have hD0' : normOneVal r₀' ^ e - normOneVal p₀' ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne'
  have hne₁ : normOneVal p₁ ≠ normOneVal r₁ := fun h => hne (by linear_combination hpp - hrr + h)
  have hD1 : normOneVal r₁ ^ e - normOneVal p₁ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne₁
  have hne₁' : normOneVal p₁' ≠ normOneVal r₁' :=
    fun h => hne' (by linear_combination hpp' - hrr' + h)
  have hD1' : normOneVal r₁' ^ e - normOneVal p₁' ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne₁'
  -- the entry height of the backwards `ρ`-leg
  have hent0 : (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
      * ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
        * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹) ≠ 0 :=
    mul_ne_zero hD0 (mul_ne_zero hD1' (inv_ne_zero hD0'))
  have hent : (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
        * ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
          * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹
      = (normOneVal r₁' ^ e - normOneVal p₁' ^ e)
        * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹ := by
    field_simp
  -- the four legs
  have h₁ := FrobFam.edge data rfl hq0 hexp hpp hrr
  have h₂ := FrobFam.leg_resolved data rfl hq0 he hexp hpp' hrr' hD0' hD1 b₂ hs₂
  have hs₃' : cond b₃
      (IsSquare ((normOneVal r₀ ^ e - normOneVal p₀ ^ e)
        * ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
          * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹))
      (IsSquare (-((normOneVal r₀ ^ e - normOneVal p₀ ^ e)
        * ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
          * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹))) := by
    rw [hent]
    exact hs₃
  have h₃ := FrobFam.leg_resolved data rfl hq0 he hexp hpp hrr hD0 hent0 b₃ hs₃'
  rw [hent] at h₃
  rw [show (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
        * ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
          * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹)
        * ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
          * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)
      = (normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * ((normOneVal r₁' ^ e - normOneVal p₁' ^ e)
          * (normOneVal r₀' ^ e - normOneVal p₀' ^ e)⁻¹) by
      field_simp] at h₃
  have h₄ := FrobFam.leg_resolved data rfl hq0 he hexp hpp' hrr' hD0' hD0 b₄ hs₄
  exact weights_eq_zero_of_four_loop data rfl hqprime hq3 hqodd he hcube hexp
    h₁ h₂ h₃ h₄ hD0

/-! ### The master formula

`MasterFormula e λ₊ λ₋` is the collapsed form of the conspiracy:
`K(p) = λ_{χ(δ₀)}·δ₀ᵉ - λ_{χ(δ₁)}·δ₁ᵉ` for every ordered pair of distinct Paley points.
The anchor argument (`notes/bg/appC_problem1_resolution.md` §4.3) derives it from the
exchange relation; the population branches feed different anchors. -/

open scoped Classical in
/-- The coefficient `λ_{χ(x)}`: `lamP` on squares, `lamM` on non-squares. -/
noncomputable def sqSelect (x lamP lamM : GaloisField p q) : GaloisField p q :=
  if IsSquare x then lamP else lamM

theorem sqSelect_of_isSquare {x lamP lamM : GaloisField p q} (h : IsSquare x) :
    sqSelect x lamP lamM = lamP := if_pos h

theorem sqSelect_of_not_isSquare {x lamP lamM : GaloisField p q} (h : ¬IsSquare x) :
    sqSelect x lamP lamM = lamM := if_neg h

open scoped Classical in
/-- Evaluating `sqSelect` with values branched on the sign of a reference `A₀`, at an element
whose ratio to `A₀` is a square: the sign of `x` agrees with the sign of `A₀`, so the selector
returns `vS`. -/
private theorem sqSelect_ite_same {A₀ x vS vO : GaloisField p q} (hA₀ : A₀ ≠ 0)
    (hx0 : x ≠ 0) (hxs : IsSquare (x * A₀⁻¹)) :
    sqSelect x (if IsSquare A₀ then vS else vO) (if IsSquare A₀ then vO else vS) = vS := by
  by_cases hA : IsSquare A₀
  · have hxsq : IsSquare x := by
      rw [show x = x * A₀⁻¹ * A₀ by field_simp]
      exact hxs.mul hA
    rw [sqSelect_of_isSquare hxsq, if_pos hA]
  · have hxsq : ¬IsSquare x := by
      intro hxq
      exact hA (by rw [show A₀ = x * (x * A₀⁻¹)⁻¹ by field_simp]; exact hxq.mul hxs.inv)
    rw [sqSelect_of_not_isSquare hxsq, if_neg hA]

open scoped Classical in
/-- Evaluating `sqSelect` with values branched on the sign of a reference `A₀`, at an element
whose ratio to `A₀` has square negative: the signs disagree, so the selector returns `vO`. -/
private theorem sqSelect_ite_opp {A₀ x vS vO : GaloisField p q}
    (hneg1 : ¬IsSquare (-1 : GaloisField p q))
    (hdichA : IsSquare A₀ ∨ IsSquare (-A₀)) (hA₀ : A₀ ≠ 0) (hx0 : x ≠ 0)
    (hxs : IsSquare (-(x * A₀⁻¹))) :
    sqSelect x (if IsSquare A₀ then vS else vO) (if IsSquare A₀ then vO else vS) = vO := by
  by_cases hA : IsSquare A₀
  · have hxsq : ¬IsSquare x := by
      refine not_isSquare_of_isSquare_neg hneg1 hx0 ?_
      rw [show -x = -(x * A₀⁻¹) * A₀ by field_simp]
      exact hxs.mul hA
    rw [sqSelect_of_not_isSquare hxsq, if_pos hA]
  · have hAneg : IsSquare (-A₀) := hdichA.resolve_left hA
    have hxsq : IsSquare x := by
      rw [show x = -(x * A₀⁻¹) * -A₀ by field_simp]
      exact hxs.mul hAneg
    rw [sqSelect_of_isSquare hxsq, if_neg hA]

/-- **The master formula**: `K(p) = λ_{χ(δ₀)}·δ₀ᵉ - λ_{χ(δ₁)}·δ₁ᵉ` for every ordered pair
of distinct Paley points.  (The pair `(r, p)` recovers the `K(r)`-equation, so one component
suffices.) -/
def MasterFormula (e : ℕ) (lamP lamM : GaloisField p q) : Prop :=
  ∀ p₀ p₁ r₀ r₁ : NormSet.normOneUnits p q,
    normOneVal p₀ = normOneVal p₁ + 1 → normOneVal r₀ = normOneVal r₁ + 1 →
    normOneVal p₀ ≠ normOneVal r₀ →
    normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)
      = sqSelect (normOneVal r₀ ^ e - normOneVal p₀ ^ e) lamP lamM
          * (normOneVal r₀ ^ e - normOneVal p₀ ^ e) ^ e
        - sqSelect (normOneVal r₁ ^ e - normOneVal p₁ ^ e) lamP lamM
          * (normOneVal r₁ ^ e - normOneVal p₁ ^ e) ^ e

/-- Clearing the anchor denominator in an exchange relation with `b₃ = true`: the target
weight is pinned against the anchor data. -/
private theorem pin_of_exchange {e : ℕ} {Kp W₂ W₄ D₀ D₁ d₀ d₁ : GaloisField p q}
    (hD₀ : D₀ ≠ 0)
    (h : Kp + W₂ * (d₁ * D₀⁻¹) ^ e - Kp * (D₁ * D₀⁻¹) ^ e - W₄ * (d₀ * D₀⁻¹) ^ e = 0) :
    Kp * (D₀ ^ e - D₁ ^ e) = W₄ * d₀ ^ e - W₂ * d₁ ^ e := by
  have hcancel : (D₀⁻¹) ^ e * D₀ ^ e = 1 := by
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ hD₀)
  linear_combination D₀ ^ e * h + (Kp * D₁ ^ e + W₄ * d₀ ^ e - W₂ * d₁ ^ e) * hcancel

/-- **The anchor argument, case `χ(ρ₀) = +1`.**  A single anchor pair whose ratio is a square
pins every pair of the master formula: the exchange relation of any target pair against the
anchor has `b₃ = true`, and its first component solves for the target weight with the
anchor-side coefficients `λ = ±K·(Δ₀ᵉ - Δ₁ᵉ)⁻¹`.  No population hypotheses beyond the anchor
are needed. -/
theorem exists_masterFormula_of_plus_anchor (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {a₀ a₁ b₀ b₁ : NormSet.normOneUnits p q}
    (haa : normOneVal a₀ = normOneVal a₁ + 1) (hbb : normOneVal b₀ = normOneVal b₁ + 1)
    (hneA : normOneVal a₀ ≠ normOneVal b₀)
    (hcollA : normOneVal b₀ ^ e - normOneVal a₀ ^ e
      ≠ normOneVal b₁ ^ e - normOneVal a₁ ^ e)
    (hanchor : IsSquare ((normOneVal b₁ ^ e - normOneVal a₁ ^ e)
      * (normOneVal b₀ ^ e - normOneVal a₀ ^ e)⁻¹)) :
    ∃ lamP lamM : GaloisField p q, MasterFormula e lamP lamM := by
  subst hp
  classical
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hneg1 := not_isSquare_neg_one_galois rfl hq0 hqodd
  have hDA0 : normOneVal b₀ ^ e - normOneVal a₀ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hneA
  have hdichA := isSquare_or_isSquare_neg_galois rfl hq0 hqodd hDA0
  have hD : (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
      - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e ≠ 0 := by
    intro h0
    exact hcollA (Paley.pow_injective_of_cube hcube (sub_eq_zero.mp h0))
  -- the two anchor-side coefficients
  refine ⟨if IsSquare (normOneVal b₀ ^ e - normOneVal a₀ ^ e) then
      (normOneVal a₁ ^ (e * e) - normOneVal a₀ ^ (e * e))
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)⁻¹
    else
      -(normOneVal b₁ ^ (e * e) - normOneVal b₀ ^ (e * e))
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)⁻¹,
    if IsSquare (normOneVal b₀ ^ e - normOneVal a₀ ^ e) then
      -(normOneVal b₁ ^ (e * e) - normOneVal b₀ ^ (e * e))
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)⁻¹
    else
      (normOneVal a₁ ^ (e * e) - normOneVal a₀ ^ (e * e))
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)⁻¹, ?_⟩
  intro p₀ p₁ r₀ r₁ hpp hrr hne
  have hd0 : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne
  have hne₁ : normOneVal p₁ ≠ normOneVal r₁ :=
    fun h => hne (by linear_combination hpp - hrr + h)
  have hd1 : normOneVal r₁ ^ e - normOneVal p₁ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne₁
  have hr₂0 : (normOneVal r₁ ^ e - normOneVal p₁ ^ e)
      * (normOneVal b₀ ^ e - normOneVal a₀ ^ e)⁻¹ ≠ 0 :=
    mul_ne_zero hd1 (inv_ne_zero hDA0)
  have hr₄0 : (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
      * (normOneVal b₀ ^ e - normOneVal a₀ ^ e)⁻¹ ≠ 0 :=
    mul_ne_zero hd0 (inv_ne_zero hDA0)
  rcases isSquare_or_isSquare_neg_galois rfl hq0 hqodd hr₂0 with hb₂ | hb₂ <;>
    rcases isSquare_or_isSquare_neg_galois rfl hq0 hqodd hr₄0 with hb₄ | hb₄
  · -- `(b₂, b₄) = (true, true)`
    have hEX := (exchange_relation data rfl hqprime hq3 hqodd he hcube hexp
      hpp hrr haa hbb hne hneA true true true hb₂ hanchor hb₄).1
    simp only [legWeight_true] at hEX
    have hpin := pin_of_exchange hDA0 hEX
    rw [sqSelect_ite_same hDA0 hd0 hb₄, sqSelect_ite_same hDA0 hd1 hb₂]
    field_simp
    linear_combination hpin
  · -- `(b₂, b₄) = (true, false)`
    have hEX := (exchange_relation data rfl hqprime hq3 hqodd he hcube hexp
      hpp hrr haa hbb hne hneA true true false hb₂ hanchor hb₄).1
    simp only [legWeight_true, legWeight_false] at hEX
    have hpin := pin_of_exchange hDA0 hEX
    rw [sqSelect_ite_opp hneg1 hdichA hDA0 hd0 hb₄, sqSelect_ite_same hDA0 hd1 hb₂]
    field_simp
    linear_combination hpin
  · -- `(b₂, b₄) = (false, true)`
    have hEX := (exchange_relation data rfl hqprime hq3 hqodd he hcube hexp
      hpp hrr haa hbb hne hneA false true true hb₂ hanchor hb₄).1
    simp only [legWeight_true, legWeight_false] at hEX
    have hpin := pin_of_exchange hDA0 hEX
    rw [sqSelect_ite_same hDA0 hd0 hb₄, sqSelect_ite_opp hneg1 hdichA hDA0 hd1 hb₂]
    field_simp
    linear_combination hpin
  · -- `(b₂, b₄) = (false, false)`
    have hEX := (exchange_relation data rfl hqprime hq3 hqodd he hcube hexp
      hpp hrr haa hbb hne hneA false true false hb₂ hanchor hb₄).1
    simp only [legWeight_true, legWeight_false] at hEX
    have hpin := pin_of_exchange hDA0 hEX
    rw [sqSelect_ite_opp hneg1 hdichA hDA0 hd0 hb₄, sqSelect_ite_opp hneg1 hdichA hDA0 hd1 hb₂]
    field_simp
    linear_combination hpin

/-- Dividing a pinned weight by the (non-zero) anchor determinant, distributing over the two
master terms. -/
private theorem master_div {K D A B d₀e d₁e : GaloisField p q} (hD : D ≠ 0)
    (h : K * D = A * d₀e - B * d₁e) : K = A * D⁻¹ * d₀e - B * D⁻¹ * d₁e := by
  have hK : K = (A * d₀e - B * d₁e) * D⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hD, mul_one]
  rw [hK]
  ring

/-- Clearing the anchor denominator in an exchange relation with `b₃ = false`: the two
components couple the two target weights into a `2 × 2` system, solved against the determinant
`D₀^{2e} - D₁^{2e}`. -/
private theorem pin2_of_exchange {e : ℕ} {Kp Kr W₂ V₂ W₄ V₄ D₀ D₁ d₀ d₁ : GaloisField p q}
    (hD₀ : D₀ ≠ 0)
    (h1 : Kp + W₂ * (d₁ * D₀⁻¹) ^ e - -Kr * (D₁ * D₀⁻¹) ^ e - W₄ * (d₀ * D₀⁻¹) ^ e = 0)
    (h2 : Kr + V₂ * (d₁ * D₀⁻¹) ^ e - -Kp * (D₁ * D₀⁻¹) ^ e - V₄ * (d₀ * D₀⁻¹) ^ e = 0) :
    Kp * (D₀ ^ e * D₀ ^ e - D₁ ^ e * D₁ ^ e)
      = (W₄ * D₀ ^ e - V₄ * D₁ ^ e) * d₀ ^ e - (W₂ * D₀ ^ e - V₂ * D₁ ^ e) * d₁ ^ e := by
  have hcancel : (D₀⁻¹) ^ e * D₀ ^ e = 1 := by
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ hD₀)
  linear_combination (D₀ ^ e * D₀ ^ e) * h1 - (D₁ ^ e * D₀ ^ e) * h2
    - (W₂ * d₁ ^ e * D₀ ^ e + Kr * D₁ ^ e * D₀ ^ e - W₄ * d₀ ^ e * D₀ ^ e
      - V₂ * d₁ ^ e * D₁ ^ e - Kp * (D₁ ^ e * D₁ ^ e) + V₄ * d₀ ^ e * D₁ ^ e) * hcancel

/-- **The anchor argument, case `χ(ρ₀) = -1`.**  When the anchor ratio is a non-square with
`ρ₀ ≠ ±1`, the exchange relation of any target pair against the anchor has `b₃ = false` and
couples the two target weights; its two components form a `2 × 2` system with determinant
`Δ₀^{2e} - Δ₁^{2e} ≠ 0`, which pins every pair to the master formula with coefficients
`λ = (K(a)Δ₀ᵉ - K(b)Δ₁ᵉ)/(Δ₀^{2e} - Δ₁^{2e})` (component of `χ(Δ₀)`) and
`λ' = (K(a)Δ₁ᵉ - K(b)Δ₀ᵉ)/(Δ₀^{2e} - Δ₁^{2e})` (opposite component). -/
theorem exists_masterFormula_of_minus_anchor (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {a₀ a₁ b₀ b₁ : NormSet.normOneUnits p q}
    (haa : normOneVal a₀ = normOneVal a₁ + 1) (hbb : normOneVal b₀ = normOneVal b₁ + 1)
    (hneA : normOneVal a₀ ≠ normOneVal b₀)
    (hcollA : normOneVal b₀ ^ e - normOneVal a₀ ^ e
      ≠ normOneVal b₁ ^ e - normOneVal a₁ ^ e)
    (hantiA : normOneVal b₁ ^ e - normOneVal a₁ ^ e
      ≠ -(normOneVal b₀ ^ e - normOneVal a₀ ^ e))
    (hanchor : IsSquare (-((normOneVal b₁ ^ e - normOneVal a₁ ^ e)
      * (normOneVal b₀ ^ e - normOneVal a₀ ^ e)⁻¹))) :
    ∃ lamP lamM : GaloisField p q, MasterFormula e lamP lamM := by
  subst hp
  classical
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hneg1 := not_isSquare_neg_one_galois rfl hq0 hqodd
  have hDA0 : normOneVal b₀ ^ e - normOneVal a₀ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hneA
  have hdichA := isSquare_or_isSquare_neg_galois rfl hq0 hqodd hDA0
  have hD2 : (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
        * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
      - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e
        * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp (show
        ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          + (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e) = 0 by linear_combination h0)
      with h | h
    · exact hcollA (Paley.pow_injective_of_cube hcube (sub_eq_zero.mp h))
    · have h' : (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          = (-(normOneVal b₁ ^ e - normOneVal a₁ ^ e)) ^ e := by
        rw [he.neg_pow]
        linear_combination h
      have hba := Paley.pow_injective_of_cube hcube h'
      exact hantiA (by linear_combination hba)
  refine ⟨if IsSquare (normOneVal b₀ ^ e - normOneVal a₀ ^ e) then
      ((normOneVal a₁ ^ (e * e) - normOneVal a₀ ^ (e * e))
          * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
        - (normOneVal b₁ ^ (e * e) - normOneVal b₀ ^ (e * e))
          * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
            * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e
            * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)⁻¹
    else
      ((normOneVal a₁ ^ (e * e) - normOneVal a₀ ^ (e * e))
          * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e
        - (normOneVal b₁ ^ (e * e) - normOneVal b₀ ^ (e * e))
          * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e)
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
            * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e
            * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)⁻¹,
    if IsSquare (normOneVal b₀ ^ e - normOneVal a₀ ^ e) then
      ((normOneVal a₁ ^ (e * e) - normOneVal a₀ ^ (e * e))
          * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e
        - (normOneVal b₁ ^ (e * e) - normOneVal b₀ ^ (e * e))
          * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e)
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
            * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e
            * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)⁻¹
    else
      ((normOneVal a₁ ^ (e * e) - normOneVal a₀ ^ (e * e))
          * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
        - (normOneVal b₁ ^ (e * e) - normOneVal b₀ ^ (e * e))
          * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
            * (normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e
          - (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e
            * (normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e)⁻¹, ?_⟩
  intro p₀ p₁ r₀ r₁ hpp hrr hne
  have hd0 : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne
  have hne₁ : normOneVal p₁ ≠ normOneVal r₁ :=
    fun h => hne (by linear_combination hpp - hrr + h)
  have hd1 : normOneVal r₁ ^ e - normOneVal p₁ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne₁
  have hr₂0 : (normOneVal r₁ ^ e - normOneVal p₁ ^ e)
      * (normOneVal b₀ ^ e - normOneVal a₀ ^ e)⁻¹ ≠ 0 :=
    mul_ne_zero hd1 (inv_ne_zero hDA0)
  have hr₄0 : (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
      * (normOneVal b₀ ^ e - normOneVal a₀ ^ e)⁻¹ ≠ 0 :=
    mul_ne_zero hd0 (inv_ne_zero hDA0)
  rcases isSquare_or_isSquare_neg_galois rfl hq0 hqodd hr₂0 with hb₂ | hb₂ <;>
    rcases isSquare_or_isSquare_neg_galois rfl hq0 hqodd hr₄0 with hb₄ | hb₄
  · have hEX := exchange_relation data rfl hqprime hq3 hqodd he hcube hexp
      hpp hrr haa hbb hne hneA true false true hb₂ hanchor hb₄
    simp only [legWeight_true, legWeight_false] at hEX
    have hpin := pin2_of_exchange hDA0 hEX.1 hEX.2
    rw [sqSelect_ite_same hDA0 hd0 hb₄, sqSelect_ite_same hDA0 hd1 hb₂]
    linear_combination master_div hD2 hpin
  · have hEX := exchange_relation data rfl hqprime hq3 hqodd he hcube hexp
      hpp hrr haa hbb hne hneA true false false hb₂ hanchor hb₄
    simp only [legWeight_true, legWeight_false] at hEX
    have hpin := pin2_of_exchange hDA0 hEX.1 hEX.2
    rw [sqSelect_ite_opp hneg1 hdichA hDA0 hd0 hb₄, sqSelect_ite_same hDA0 hd1 hb₂]
    linear_combination master_div hD2 hpin
  · have hEX := exchange_relation data rfl hqprime hq3 hqodd he hcube hexp
      hpp hrr haa hbb hne hneA false false true hb₂ hanchor hb₄
    simp only [legWeight_true, legWeight_false] at hEX
    have hpin := pin2_of_exchange hDA0 hEX.1 hEX.2
    rw [sqSelect_ite_same hDA0 hd0 hb₄, sqSelect_ite_opp hneg1 hdichA hDA0 hd1 hb₂]
    linear_combination master_div hD2 hpin
  · have hEX := exchange_relation data rfl hqprime hq3 hqodd he hcube hexp
      hpp hrr haa hbb hne hneA false false false hb₂ hanchor hb₄
    simp only [legWeight_false] at hEX
    have hpin := pin2_of_exchange hDA0 hEX.1 hEX.2
    rw [sqSelect_ite_opp hneg1 hdichA hDA0 hd0 hb₄,
      sqSelect_ite_opp hneg1 hdichA hDA0 hd1 hb₂]
    linear_combination master_div hD2 hpin

/-- **Master or death: the population glue.**  Under conspiracy and no collision, the master
formula holds: some pair has square ratio (case P), or some pair has ratio `≠ -1` — then
non-square, so case M applies — or every ratio is `-1` and the three distinct Paley points
die by step 4.  Steps 3–5 of the case tree, assembled. -/
theorem exists_masterFormula_of_no_collision (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {a₀ a₁ b₀ b₁ c₀ c₁ : NormSet.normOneUnits p q}
    (haa : normOneVal a₀ = normOneVal a₁ + 1) (hbb : normOneVal b₀ = normOneVal b₁ + 1)
    (hcc : normOneVal c₀ = normOneVal c₁ + 1)
    (hab : normOneVal a₀ ≠ normOneVal b₀) (hac : normOneVal a₀ ≠ normOneVal c₀)
    (hbc : normOneVal b₀ ≠ normOneVal c₀)
    (hnocoll : ∀ p₀ p₁ r₀ r₁ : NormSet.normOneUnits p q,
      normOneVal p₀ = normOneVal p₁ + 1 → normOneVal r₀ = normOneVal r₁ + 1 →
      normOneVal p₀ ≠ normOneVal r₀ →
      normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ normOneVal r₁ ^ e - normOneVal p₁ ^ e) :
    ∃ lamP lamM : GaloisField p q, MasterFormula e lamP lamM := by
  classical
  have hq0 : q ≠ 0 := hqprime.ne_zero
  by_cases hplus : ∃ p₀ p₁ r₀ r₁ : NormSet.normOneUnits p q,
      normOneVal p₀ = normOneVal p₁ + 1 ∧ normOneVal r₀ = normOneVal r₁ + 1 ∧
      normOneVal p₀ ≠ normOneVal r₀ ∧
      IsSquare ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)
  · obtain ⟨p₀, p₁, r₀, r₁, hpp, hrr, hne, hsq⟩ := hplus
    exact exists_masterFormula_of_plus_anchor data hp hqprime hq3 hqodd he hcube hexp
      hpp hrr hne (hnocoll p₀ p₁ r₀ r₁ hpp hrr hne) hsq
  · push Not at hplus
    by_cases hgen : ∃ p₀ p₁ r₀ r₁ : NormSet.normOneUnits p q,
        normOneVal p₀ = normOneVal p₁ + 1 ∧ normOneVal r₀ = normOneVal r₁ + 1 ∧
        normOneVal p₀ ≠ normOneVal r₀ ∧
        normOneVal r₁ ^ e - normOneVal p₁ ^ e ≠ -(normOneVal r₀ ^ e - normOneVal p₀ ^ e)
    · obtain ⟨p₀, p₁, r₀, r₁, hpp, hrr, hne, hanti⟩ := hgen
      have hd0 : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0 :=
        skewPair_edge_left_ne_zero hcube hne
      have hne₁ : normOneVal p₁ ≠ normOneVal r₁ :=
        fun h => hne (by linear_combination hpp - hrr + h)
      have hd1 : normOneVal r₁ ^ e - normOneVal p₁ ^ e ≠ 0 :=
        skewPair_edge_left_ne_zero hcube hne₁
      have hr0 : (normOneVal r₁ ^ e - normOneVal p₁ ^ e)
          * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹ ≠ 0 :=
        mul_ne_zero hd1 (inv_ne_zero hd0)
      have hneg : IsSquare (-((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
          * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)) :=
        (isSquare_or_isSquare_neg_galois hp hq0 hqodd hr0).resolve_left
          (hplus p₀ p₁ r₀ r₁ hpp hrr hne)
      exact exists_masterFormula_of_minus_anchor data hp hqprime hq3 hqodd he hcube hexp
        hpp hrr hne (hnocoll p₀ p₁ r₀ r₁ hpp hrr hne) hanti hneg
    · push Not at hgen
      exact (false_of_three_antipodal data hp hqprime hq3 hqodd he hcube hexp
        haa hbb hcc hab hac hbc (hgen a₀ a₁ b₀ b₁ haa hbb hab)
        (hgen a₀ a₁ c₀ c₁ haa hcc hac) (hgen b₀ b₁ c₀ c₁ hbb hcc hbc)).elim

/-! ### Steps 6–7: the branches of the master formula

With the master formula in hand the loops are no longer needed: each parameter branch is pure
field arithmetic.  `Δ = λ₊ - λ₋ = 0` forces antisymmetric weights and dies on three points;
`Σ̄ = λ₊ + λ₋ = 0` forces constant weights and dies through the `e²`-collision bridge back to
Part I. -/

theorem sqSelect_self {x lam : GaloisField p q} : sqSelect x lam lam = lam := ite_self lam

/-- Negating the argument of an antisymmetric selector negates the value (`-1` is a
non-square). -/
private theorem sqSelect_neg_apply (hneg1 : ¬IsSquare (-1 : GaloisField p q))
    {x : GaloisField p q} (hdich : IsSquare x ∨ IsSquare (-x)) (hx0 : x ≠ 0)
    {lam : GaloisField p q} :
    sqSelect (-x) lam (-lam) = -sqSelect x lam (-lam) := by
  by_cases hx : IsSquare x
  · have hnx : ¬IsSquare (-x) :=
      not_isSquare_of_isSquare_neg hneg1 (neg_ne_zero.mpr hx0) (by rwa [neg_neg])
    rw [sqSelect_of_not_isSquare hnx, sqSelect_of_isSquare hx]
  · have hnegx : IsSquare (-x) := hdich.resolve_left hx
    rw [sqSelect_of_isSquare hnegx, sqSelect_of_not_isSquare hx, neg_neg]

/-- Three pairwise-antisymmetric weights with a non-zero member are impossible in
characteristic three (`2 = -1` is invertible). -/
private theorem false_of_antisym_triple (hp : p = 3) {Ka Kb Kc : GaloisField p q}
    (hab : Ka + Kb = 0) (hac : Ka + Kc = 0) (hbc : Kb + Kc = 0) (hc : Kc ≠ 0) : False := by
  subst hp
  have h30 : (3 : GaloisField 3 q) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 3 q) 3
  have h2 : (2 : GaloisField 3 q) * Kc = 0 := by linear_combination hac + hbc - hab
  have h2ne : (2 : GaloisField 3 q) ≠ 0 := fun h20 =>
    one_ne_zero (by linear_combination h30 - h20 : (1 : GaloisField 3 q) = 0)
  exact hc ((mul_eq_zero.mp h2).resolve_left h2ne)

/-- **Branch `Δ = 0`** (`λ₊ = λ₋`).  The master formula becomes sign-free, so the swapped pair
gives `K(p) = -K(r)` for every ordered pair (`e` odd); three distinct Paley points then force
`K = 0`, contradicting the non-vanishing of the weight.  No loops are needed. -/
theorem false_of_masterFormula_delta_zero (hp : p = 3) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {a₀ a₁ b₀ b₁ c₀ c₁ : NormSet.normOneUnits p q}
    (haa : normOneVal a₀ = normOneVal a₁ + 1) (hbb : normOneVal b₀ = normOneVal b₁ + 1)
    (hcc : normOneVal c₀ = normOneVal c₁ + 1)
    (hab : normOneVal a₀ ≠ normOneVal b₀) (hac : normOneVal a₀ ≠ normOneVal c₀)
    (hbc : normOneVal b₀ ≠ normOneVal c₀)
    {lam : GaloisField p q} (hmaster : MasterFormula e lam lam) : False := by
  have key : ∀ x₀ x₁ y₀ y₁ : NormSet.normOneUnits p q,
      normOneVal x₀ = normOneVal x₁ + 1 → normOneVal y₀ = normOneVal y₁ + 1 →
      normOneVal x₀ ≠ normOneVal y₀ →
      (normOneVal x₁ ^ (e * e) - normOneVal x₀ ^ (e * e))
        + (normOneVal y₁ ^ (e * e) - normOneVal y₀ ^ (e * e)) = 0 := by
    intro x₀ x₁ y₀ y₁ hxx hyy hxy
    have h1 := hmaster x₀ x₁ y₀ y₁ hxx hyy hxy
    have h2 := hmaster y₀ y₁ x₀ x₁ hyy hxx hxy.symm
    simp only [sqSelect_self] at h1 h2
    have hnp₀ : (normOneVal x₀ ^ e - normOneVal y₀ ^ e) ^ e
        = -(normOneVal y₀ ^ e - normOneVal x₀ ^ e) ^ e := by
      rw [show normOneVal x₀ ^ e - normOneVal y₀ ^ e
          = -(normOneVal y₀ ^ e - normOneVal x₀ ^ e) by ring, he.neg_pow]
    have hnp₁ : (normOneVal x₁ ^ e - normOneVal y₁ ^ e) ^ e
        = -(normOneVal y₁ ^ e - normOneVal x₁ ^ e) ^ e := by
      rw [show normOneVal x₁ ^ e - normOneVal y₁ ^ e
          = -(normOneVal y₁ ^ e - normOneVal x₁ ^ e) by ring, he.neg_pow]
    linear_combination h1 + h2 + lam * hnp₀ - lam * hnp₁
  exact false_of_antisym_triple hp (key a₀ a₁ b₀ b₁ haa hbb hab)
    (key a₀ a₁ c₀ c₁ haa hcc hac) (key b₀ b₁ c₀ c₁ hbb hcc hbc)
    (skewPair_edge_weight_ne_zero hcube hcc)

/-- **Branch `Σ̄ = 0`** (`λ₋ = -λ₊`).  The selector becomes antisymmetric, so the swapped pair
gives `K(p) = K(r)` for every ordered pair: `K` is constant on the Paley set.  Two distinct
Paley points then produce an `e²`-collision of `powDiff`, the downward conjugation bridge
turns it into an `e`-collision, and Part I kills the witness. -/
theorem false_of_masterFormula_sigma_zero (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {a₀ a₁ b₀ b₁ : NormSet.normOneUnits p q}
    (haa : normOneVal a₀ = normOneVal a₁ + 1) (hbb : normOneVal b₀ = normOneVal b₁ + 1)
    (hab : normOneVal a₀ ≠ normOneVal b₀)
    {lam : GaloisField p q} (hmaster : MasterFormula e lam (-lam)) : False := by
  subst hp
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hneg1 := not_isSquare_neg_one_galois rfl hq0 hqodd
  -- `K` is constant: `K(x) = K(y)` for every ordered pair
  have key : ∀ x₀ x₁ y₀ y₁ : NormSet.normOneUnits 3 q,
      normOneVal x₀ = normOneVal x₁ + 1 → normOneVal y₀ = normOneVal y₁ + 1 →
      normOneVal x₀ ≠ normOneVal y₀ →
      normOneVal x₁ ^ (e * e) - normOneVal x₀ ^ (e * e)
        = normOneVal y₁ ^ (e * e) - normOneVal y₀ ^ (e * e) := by
    intro x₀ x₁ y₀ y₁ hxx hyy hxy
    have hd0 : normOneVal y₀ ^ e - normOneVal x₀ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hxy
    have hne₁ : normOneVal x₁ ≠ normOneVal y₁ :=
      fun h => hxy (by linear_combination hxx - hyy + h)
    have hd1 : normOneVal y₁ ^ e - normOneVal x₁ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hne₁
    have h1 := hmaster x₀ x₁ y₀ y₁ hxx hyy hxy
    have h2 := hmaster y₀ y₁ x₀ x₁ hyy hxx hxy.symm
    rw [show normOneVal x₀ ^ e - normOneVal y₀ ^ e
        = -(normOneVal y₀ ^ e - normOneVal x₀ ^ e) by ring,
      show normOneVal x₁ ^ e - normOneVal y₁ ^ e
        = -(normOneVal y₁ ^ e - normOneVal x₁ ^ e) by ring,
      sqSelect_neg_apply hneg1 (isSquare_or_isSquare_neg_galois rfl hq0 hqodd hd0) hd0,
      sqSelect_neg_apply hneg1 (isSquare_or_isSquare_neg_galois rfl hq0 hqodd hd1) hd1,
      he.neg_pow, he.neg_pow] at h2
    linear_combination h1 - h2
  -- translate to a `powDiff (e²)`-collision on the Paley set
  letI : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  haveI : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  have h4 : Fintype.card (GaloisField 3 q) % 4 = 3 := by
    rw [show Fintype.card (GaloisField 3 q) = 3 ^ q by
      rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 3 q hq0]
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    have hk : q = 2 * (q / 2) + 1 := by omega
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hmem : ∀ x₀ x₁ : NormSet.normOneUnits 3 q,
      normOneVal x₀ = normOneVal x₁ + 1 →
      normOneVal x₁ ∈ Paley.paleySet (GaloisField 3 q) := by
    intro x₀ x₁ hxx
    refine ⟨Units.ne_zero _, ?_, ?_, ?_⟩
    · have := (mem_normOneUnits_iff_isSquare rfl hq0 (x₁ : (GaloisField 3 q)ˣ)).mp x₁.2
      simpa [normOneVal] using this
    · rw [← hxx]
      exact Units.ne_zero _
    · rw [← hxx]
      have := (mem_normOneUnits_iff_isSquare rfl hq0 (x₀ : (GaloisField 3 q)ˣ)).mp x₀.2
      simpa [normOneVal] using this
  have hne₁ : normOneVal a₁ ≠ normOneVal b₁ :=
    fun h => hab (by linear_combination haa - hbb + h)
  have hval : Paley.powDiff (e * e) (normOneVal a₁) = Paley.powDiff (e * e) (normOneVal b₁) := by
    have hKab := key a₀ a₁ b₀ b₁ haa hbb hab
    rw [Paley.powDiff, Paley.powDiff, ← haa, ← hbb]
    linear_combination -hKab
  obtain ⟨c, hcP, d, hdP, hcd, hpd⟩ := Paley.exists_paley_collision_pow_mul_down hchar2 h4
    he hcube (hmem a₀ a₁ haa) (hmem b₀ b₁ hbb) hne₁ hval
  -- package the `e`-collision as a `CollisionPair` and kill it by Part I
  obtain ⟨hc0, hcsq, hc10, hc1sq⟩ := hcP
  obtain ⟨hd0, hdsq, hd10, hd1sq⟩ := hdP
  have hcoll : ∃ S S', CollisionPair 3 q e S S' := by
    refine exists_collisionPair_of_sub_ne_zero rfl hq0 hqodd
      ⟨Units.mk0 (c + 1) hc10, (mem_normOneUnits_iff_isSquare rfl hq0 _).mpr
        (by simpa using hc1sq)⟩
      ⟨Units.mk0 c hc0, (mem_normOneUnits_iff_isSquare rfl hq0 _).mpr (by simpa using hcsq)⟩
      ⟨Units.mk0 (d + 1) hd10, (mem_normOneUnits_iff_isSquare rfl hq0 _).mpr
        (by simpa using hd1sq)⟩
      ⟨Units.mk0 d hd0, (mem_normOneUnits_iff_isSquare rfl hq0 _).mpr (by simpa using hdsq)⟩
      rfl rfl ?_ ?_
    · have := hpd
      rw [Paley.powDiff, Paley.powDiff] at this
      exact this
    · intro h0
      have hd1c1 : (d + 1 : GaloisField 3 q) ^ e = (c + 1) ^ e := by
        have : normOneVal (⟨Units.mk0 (d + 1) hd10, _⟩ : NormSet.normOneUnits 3 q) ^ e
            - normOneVal (⟨Units.mk0 (c + 1) hc10, _⟩ : NormSet.normOneUnits 3 q) ^ e = 0 := h0
        simpa [normOneVal, sub_eq_zero] using this
      exact hcd (by linear_combination (Paley.pow_injective_of_cube hcube hd1c1).symm)
  obtain ⟨S, S', hpair⟩ := hcoll
  exact false_of_collisionPair data rfl hqprime hq3 hqodd he hcube hexp hpair

/-- Negating the argument of the selector swaps its two values (`-1` is a non-square). -/
private theorem sqSelect_neg_swap (hneg1 : ¬IsSquare (-1 : GaloisField p q))
    {x : GaloisField p q} (hdich : IsSquare x ∨ IsSquare (-x)) (hx0 : x ≠ 0)
    {lamP lamM : GaloisField p q} :
    sqSelect (-x) lamP lamM = sqSelect x lamM lamP := by
  by_cases hx : IsSquare x
  · have hnx : ¬IsSquare (-x) :=
      not_isSquare_of_isSquare_neg hneg1 (neg_ne_zero.mpr hx0) (by rwa [neg_neg])
    rw [sqSelect_of_not_isSquare hnx, sqSelect_of_isSquare hx]
  · rw [sqSelect_of_isSquare (hdich.resolve_left hx), sqSelect_of_not_isSquare hx]

/-- The selector and its value-swapped twin sum to the sum of the values. -/
private theorem sqSelect_add_swap {x a b : GaloisField p q} :
    sqSelect x a b + sqSelect x b a = a + b := by
  by_cases hx : IsSquare x
  · rw [sqSelect_of_isSquare hx, sqSelect_of_isSquare hx]
  · rw [sqSelect_of_not_isSquare hx, sqSelect_of_not_isSquare hx, add_comm]

/-- The selector commutes with `λ ↦ λ - λ³`. -/
private theorem sqSelect_sub_cube {x lamP lamM : GaloisField p q} :
    sqSelect x lamP lamM - sqSelect x lamP lamM ^ (3 : ℕ)
      = sqSelect x (lamP - lamP ^ (3 : ℕ)) (lamM - lamM ^ (3 : ℕ)) := by
  by_cases hx : IsSquare x
  · simp only [sqSelect_of_isSquare hx]
  · simp only [sqSelect_of_not_isSquare hx]

/-- The selector is invariant under cubing the argument (`x³ = x·x²` has the sign of `x`). -/
private theorem sqSelect_cube {x lamP lamM : GaloisField p q} (hx0 : x ≠ 0) :
    sqSelect (x ^ (3 : ℕ)) lamP lamM = sqSelect x lamP lamM := by
  by_cases hx : IsSquare x
  · rw [sqSelect_of_isSquare (hx.pow _), sqSelect_of_isSquare hx]
  · have h3 : ¬IsSquare (x ^ (3 : ℕ)) := by
      intro h
      refine hx ?_
      rw [show x = x ^ (3 : ℕ) * (x⁻¹) ^ (2 : ℕ) by field_simp]
      exact h.mul ⟨x⁻¹, pow_two x⁻¹⟩
    rw [sqSelect_of_not_isSquare h3, sqSelect_of_not_isSquare hx]

/-- **Branch `μ ≠ 0`: Frobenius quantisation.**  Comparing the master formula on `(p³, r³)`
with the cube of the master formula on `(p, r)` yields the quantisation identity
`μ_{χ(δ₀)}·δ₀^{3e} = μ_{χ(δ₁)}·δ₁^{3e}` with `μ_c = λ_c - λ_c³`.  Adding it to its swap gives
`(μ₊ + μ₋)(δ₀^{3e} - δ₁^{3e}) = 0`, so `μ₋ = -μ₊` (a collision otherwise); if `μ₊ ≠ 0`,
same-sign pairs are collisions and mixed pairs are antipodal, so *every* pair is antipodal —
the master formula degenerates to `K = Σ̄·δ₀ᵉ` and pins the partner of `a` uniquely,
contradicting two distinct partners.  Hence `λ₊, λ₋ ∈ 𝔽₃`. -/
theorem false_of_masterFormula_mu_ne_zero (hp : p = 3) (hq0 : q ≠ 0) (hqodd : Odd q)
    {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {a₀ a₁ b₀ b₁ c₀ c₁ : NormSet.normOneUnits p q}
    (haa : normOneVal a₀ = normOneVal a₁ + 1) (hbb : normOneVal b₀ = normOneVal b₁ + 1)
    (hcc : normOneVal c₀ = normOneVal c₁ + 1)
    (hab : normOneVal a₀ ≠ normOneVal b₀) (hac : normOneVal a₀ ≠ normOneVal c₀)
    (hbc : normOneVal b₀ ≠ normOneVal c₀)
    (hnocoll : ∀ p₀ p₁ r₀ r₁ : NormSet.normOneUnits p q,
      normOneVal p₀ = normOneVal p₁ + 1 → normOneVal r₀ = normOneVal r₁ + 1 →
      normOneVal p₀ ≠ normOneVal r₀ →
      normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ normOneVal r₁ ^ e - normOneVal p₁ ^ e)
    {lamP lamM : GaloisField p q} (hmaster : MasterFormula e lamP lamM)
    (hSig : lamP + lamM ≠ 0)
    (hμ : ¬(lamP - lamP ^ (3 : ℕ) = 0 ∧ lamM - lamM ^ (3 : ℕ) = 0)) : False := by
  subst hp
  have hneg1 := not_isSquare_neg_one_galois rfl hq0 hqodd
  have hodd3 : Odd (3 : ℕ) := by decide
  have h3inj : ∀ x y : GaloisField 3 q, x ^ (3 : ℕ) = y ^ (3 : ℕ) → x = y := by
    intro x y h
    have h0 : (x - y) ^ (3 : ℕ) = 0 := by rw [sub_pow_char, h, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h0)
  have hfrob : ∀ (x y : NormSet.normOneUnits 3 q) (k : ℕ),
      normOneVal (x ^ (3 : ℕ)) ^ k - normOneVal (y ^ (3 : ℕ)) ^ k
        = (normOneVal x ^ k - normOneVal y ^ k) ^ (3 : ℕ) := by
    intro x y k
    rw [normOneVal_pow, normOneVal_pow, pow_right_comm (normOneVal x) 3 k,
      pow_right_comm (normOneVal y) 3 k, ← sub_pow_char]
  -- the quantisation identity (Q), for every pair
  have hQ : ∀ x₀ x₁ y₀ y₁ : NormSet.normOneUnits 3 q,
      normOneVal x₀ = normOneVal x₁ + 1 → normOneVal y₀ = normOneVal y₁ + 1 →
      normOneVal x₀ ≠ normOneVal y₀ →
      sqSelect (normOneVal y₀ ^ e - normOneVal x₀ ^ e)
          (lamP - lamP ^ (3 : ℕ)) (lamM - lamM ^ (3 : ℕ))
          * ((normOneVal y₀ ^ e - normOneVal x₀ ^ e) ^ e) ^ (3 : ℕ)
        = sqSelect (normOneVal y₁ ^ e - normOneVal x₁ ^ e)
            (lamP - lamP ^ (3 : ℕ)) (lamM - lamM ^ (3 : ℕ))
            * ((normOneVal y₁ ^ e - normOneVal x₁ ^ e) ^ e) ^ (3 : ℕ) := by
    intro x₀ x₁ y₀ y₁ hxx hyy hxy
    have hd0 : normOneVal y₀ ^ e - normOneVal x₀ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hxy
    have hne₁ : normOneVal x₁ ≠ normOneVal y₁ :=
      fun h => hxy (by linear_combination hxx - hyy + h)
    have hd1 : normOneVal y₁ ^ e - normOneVal x₁ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hne₁
    have h1 := hmaster x₀ x₁ y₀ y₁ hxx hyy hxy
    have hxx3 : normOneVal (x₀ ^ (3 : ℕ)) = normOneVal (x₁ ^ (3 : ℕ)) + 1 := by
      simp only [normOneVal_pow]
      rw [hxx, add_pow_char, one_pow]
    have hyy3 : normOneVal (y₀ ^ (3 : ℕ)) = normOneVal (y₁ ^ (3 : ℕ)) + 1 := by
      simp only [normOneVal_pow]
      rw [hyy, add_pow_char, one_pow]
    have hxy3 : normOneVal (x₀ ^ (3 : ℕ)) ≠ normOneVal (y₀ ^ (3 : ℕ)) := by
      intro h
      refine hxy (h3inj _ _ ?_)
      simpa [normOneVal_pow] using h
    have h3 := hmaster (x₀ ^ (3 : ℕ)) (x₁ ^ (3 : ℕ)) (y₀ ^ (3 : ℕ)) (y₁ ^ (3 : ℕ))
      hxx3 hyy3 hxy3
    rw [hfrob y₀ x₀ e, hfrob y₁ x₁ e, hfrob x₁ x₀ (e * e),
      sqSelect_cube hd0, sqSelect_cube hd1,
      pow_right_comm (normOneVal y₀ ^ e - normOneVal x₀ ^ e) 3 e,
      pow_right_comm (normOneVal y₁ ^ e - normOneVal x₁ ^ e) 3 e] at h3
    have hc1 : (normOneVal x₁ ^ (e * e) - normOneVal x₀ ^ (e * e)) ^ (3 : ℕ)
        = sqSelect (normOneVal y₀ ^ e - normOneVal x₀ ^ e) lamP lamM ^ (3 : ℕ)
            * ((normOneVal y₀ ^ e - normOneVal x₀ ^ e) ^ e) ^ (3 : ℕ)
          - sqSelect (normOneVal y₁ ^ e - normOneVal x₁ ^ e) lamP lamM ^ (3 : ℕ)
            * ((normOneVal y₁ ^ e - normOneVal x₁ ^ e) ^ e) ^ (3 : ℕ) := by
      rw [h1, sub_pow_char, mul_pow, mul_pow]
    rw [← sqSelect_sub_cube, ← sqSelect_sub_cube]
    linear_combination hc1 - h3
  -- adding (Q) to its swap forces `μ₋ = -μ₊`
  have hdich : ∀ x : GaloisField 3 q, x ≠ 0 → IsSquare x ∨ IsSquare (-x) :=
    fun x hx => isSquare_or_isSquare_neg_galois rfl hq0 hqodd hx
  have hd0ab : normOneVal b₀ ^ e - normOneVal a₀ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hab
  have hne₁ab : normOneVal a₁ ≠ normOneVal b₁ :=
    fun h => hab (by linear_combination haa - hbb + h)
  have hd1ab : normOneVal b₁ ^ e - normOneVal a₁ ^ e ≠ 0 :=
    skewPair_edge_left_ne_zero hcube hne₁ab
  have hμsum : lamM - lamM ^ (3 : ℕ) = -(lamP - lamP ^ (3 : ℕ)) := by
    by_contra hSigMu
    have hSigMu' : lamP - lamP ^ (3 : ℕ) + (lamM - lamM ^ (3 : ℕ)) ≠ 0 :=
      fun h0 => hSigMu (by linear_combination h0)
    have hq1 := hQ a₀ a₁ b₀ b₁ haa hbb hab
    have hq2 := hQ b₀ b₁ a₀ a₁ hbb haa hab.symm
    rw [show normOneVal a₀ ^ e - normOneVal b₀ ^ e
        = -(normOneVal b₀ ^ e - normOneVal a₀ ^ e) by ring,
      show normOneVal a₁ ^ e - normOneVal b₁ ^ e
        = -(normOneVal b₁ ^ e - normOneVal a₁ ^ e) by ring,
      sqSelect_neg_swap hneg1 (hdich _ hd0ab) hd0ab,
      sqSelect_neg_swap hneg1 (hdich _ hd1ab) hd1ab,
      he.neg_pow, he.neg_pow, hodd3.neg_pow, hodd3.neg_pow] at hq2
    have e₀ := sqSelect_add_swap (x := normOneVal b₀ ^ e - normOneVal a₀ ^ e)
      (a := lamP - lamP ^ (3 : ℕ)) (b := lamM - lamM ^ (3 : ℕ))
    have e₁ := sqSelect_add_swap (x := normOneVal b₁ ^ e - normOneVal a₁ ^ e)
      (a := lamP - lamP ^ (3 : ℕ)) (b := lamM - lamM ^ (3 : ℕ))
    have hsum : (lamP - lamP ^ (3 : ℕ) + (lamM - lamM ^ (3 : ℕ)))
        * ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e) ^ (3 : ℕ)
        = (lamP - lamP ^ (3 : ℕ) + (lamM - lamM ^ (3 : ℕ)))
        * ((normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e) ^ (3 : ℕ) := by
      linear_combination hq1 - hq2
        - ((normOneVal b₀ ^ e - normOneVal a₀ ^ e) ^ e) ^ (3 : ℕ) * e₀
        + ((normOneVal b₁ ^ e - normOneVal a₁ ^ e) ^ e) ^ (3 : ℕ) * e₁
    have hpow := h3inj _ _ (mul_left_cancel₀ hSigMu' hsum)
    exact hnocoll a₀ a₁ b₀ b₁ haa hbb hab
      (Paley.pow_injective_of_cube hcube hpow)
  have hμP : lamP - lamP ^ (3 : ℕ) ≠ 0 := by
    intro h0
    exact hμ ⟨h0, by rw [hμsum, h0, neg_zero]⟩
  -- every pair is antipodal
  have hanti : ∀ x₀ x₁ y₀ y₁ : NormSet.normOneUnits 3 q,
      normOneVal x₀ = normOneVal x₁ + 1 → normOneVal y₀ = normOneVal y₁ + 1 →
      normOneVal x₀ ≠ normOneVal y₀ →
      normOneVal y₁ ^ e - normOneVal x₁ ^ e
        = -(normOneVal y₀ ^ e - normOneVal x₀ ^ e) := by
    intro x₀ x₁ y₀ y₁ hxx hyy hxy
    have hd0 : normOneVal y₀ ^ e - normOneVal x₀ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hxy
    have hne₁ : normOneVal x₁ ≠ normOneVal y₁ :=
      fun h => hxy (by linear_combination hxx - hyy + h)
    have hd1 : normOneVal y₁ ^ e - normOneVal x₁ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hne₁
    have hq1 := hQ x₀ x₁ y₀ y₁ hxx hyy hxy
    rw [hμsum] at hq1
    have hcollx := hnocoll x₀ x₁ y₀ y₁ hxx hyy hxy
    by_cases h₀ : IsSquare (normOneVal y₀ ^ e - normOneVal x₀ ^ e) <;>
      by_cases h₁ : IsSquare (normOneVal y₁ ^ e - normOneVal x₁ ^ e)
    · rw [sqSelect_of_isSquare h₀, sqSelect_of_isSquare h₁] at hq1
      exact absurd (Paley.pow_injective_of_cube hcube
        (h3inj _ _ (mul_left_cancel₀ hμP hq1))) hcollx
    · rw [sqSelect_of_isSquare h₀, sqSelect_of_not_isSquare h₁] at hq1
      have hAB : ((normOneVal y₀ ^ e - normOneVal x₀ ^ e) ^ e) ^ (3 : ℕ)
          = ((-(normOneVal y₁ ^ e - normOneVal x₁ ^ e)) ^ e) ^ (3 : ℕ) := by
        rw [he.neg_pow, hodd3.neg_pow]
        linear_combination mul_left_cancel₀ hμP (by linear_combination hq1 :
          (lamP - lamP ^ (3 : ℕ))
              * ((normOneVal y₀ ^ e - normOneVal x₀ ^ e) ^ e) ^ (3 : ℕ)
            = (lamP - lamP ^ (3 : ℕ))
              * -((normOneVal y₁ ^ e - normOneVal x₁ ^ e) ^ e) ^ (3 : ℕ))
      have := Paley.pow_injective_of_cube hcube (h3inj _ _ hAB)
      linear_combination this
    · rw [sqSelect_of_not_isSquare h₀, sqSelect_of_isSquare h₁] at hq1
      have hAB : ((normOneVal y₀ ^ e - normOneVal x₀ ^ e) ^ e) ^ (3 : ℕ)
          = ((-(normOneVal y₁ ^ e - normOneVal x₁ ^ e)) ^ e) ^ (3 : ℕ) := by
        rw [he.neg_pow, hodd3.neg_pow]
        linear_combination mul_left_cancel₀ hμP (by linear_combination -hq1 :
          (lamP - lamP ^ (3 : ℕ))
              * ((normOneVal y₀ ^ e - normOneVal x₀ ^ e) ^ e) ^ (3 : ℕ)
            = (lamP - lamP ^ (3 : ℕ))
              * -((normOneVal y₁ ^ e - normOneVal x₁ ^ e) ^ e) ^ (3 : ℕ))
      have := Paley.pow_injective_of_cube hcube (h3inj _ _ hAB)
      linear_combination this
    · rw [sqSelect_of_not_isSquare h₀, sqSelect_of_not_isSquare h₁] at hq1
      have hq1' : (lamP - lamP ^ (3 : ℕ))
            * ((normOneVal y₀ ^ e - normOneVal x₀ ^ e) ^ e) ^ (3 : ℕ)
          = (lamP - lamP ^ (3 : ℕ))
            * ((normOneVal y₁ ^ e - normOneVal x₁ ^ e) ^ e) ^ (3 : ℕ) := by
        linear_combination -hq1
      exact absurd (Paley.pow_injective_of_cube hcube
        (h3inj _ _ (mul_left_cancel₀ hμP hq1'))) hcollx
  -- the master formula degenerates to `K = Σ̄·δ₀ᵉ` and pins the partner of `a`
  have hpin : ∀ y₀ y₁ : NormSet.normOneUnits 3 q,
      normOneVal y₀ = normOneVal y₁ + 1 → normOneVal a₀ ≠ normOneVal y₀ →
      normOneVal a₁ ^ (e * e) - normOneVal a₀ ^ (e * e)
        = (lamP + lamM) * (normOneVal y₀ ^ e - normOneVal a₀ ^ e) ^ e := by
    intro y₀ y₁ hyy hay
    have hd0 : normOneVal y₀ ^ e - normOneVal a₀ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hay
    have h1 := hmaster a₀ a₁ y₀ y₁ haa hyy hay
    rw [hanti a₀ a₁ y₀ y₁ haa hyy hay,
      sqSelect_neg_swap hneg1 (hdich _ hd0) hd0, he.neg_pow] at h1
    have hadd := sqSelect_add_swap (x := normOneVal y₀ ^ e - normOneVal a₀ ^ e)
      (a := lamP) (b := lamM)
    linear_combination h1 + (normOneVal y₀ ^ e - normOneVal a₀ ^ e) ^ e * hadd
  have hb := hpin b₀ b₁ hbb hab
  have hc := hpin c₀ c₁ hcc hac
  have hpow := mul_left_cancel₀ hSig (hb.symm.trans hc)
  have h0e := Paley.pow_injective_of_cube hcube hpow
  exact hbc (Paley.pow_injective_of_cube hcube (by linear_combination h0e))

/-- **Branch `λ ∈ 𝔽₃`: the four remaining candidates.**  With `λ₊, λ₋ ∈ 𝔽₃`, `Δ ≠ 0` and
`Σ̄ ≠ 0` force exactly one of `λ₊, λ₋` to vanish.  A same-sign pair then dies: one of its two
orientations reads the vanished coefficient on both terms, so its weight is zero.  Hence all
pairs are mixed, and the master formula pins the partner of `a` through the non-vanished
coefficient — one candidate partner per sign pattern.  Three distinct partners `b, c, d` of
`a` overload the two patterns, and the pinning identifies two of them.  Step 7 of the case
tree. -/
theorem false_of_masterFormula_cubic (hp : p = 3) (hq0 : q ≠ 0) (hqodd : Odd q)
    {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : NormSet.normOneUnits p q}
    (haa : normOneVal a₀ = normOneVal a₁ + 1) (hbb : normOneVal b₀ = normOneVal b₁ + 1)
    (hcc : normOneVal c₀ = normOneVal c₁ + 1) (hdd : normOneVal d₀ = normOneVal d₁ + 1)
    (hab : normOneVal a₀ ≠ normOneVal b₀) (hac : normOneVal a₀ ≠ normOneVal c₀)
    (had : normOneVal a₀ ≠ normOneVal d₀) (hbc : normOneVal b₀ ≠ normOneVal c₀)
    (hbd : normOneVal b₀ ≠ normOneVal d₀) (hcd : normOneVal c₀ ≠ normOneVal d₀)
    {lamP lamM : GaloisField p q} (hmaster : MasterFormula e lamP lamM)
    (hP3 : lamP - lamP ^ (3 : ℕ) = 0) (hM3 : lamM - lamM ^ (3 : ℕ) = 0)
    (hDel : lamP ≠ lamM) (hSig : lamP + lamM ≠ 0) : False := by
  subst hp
  have hneg1 := not_isSquare_neg_one_galois rfl hq0 hqodd
  have hdich : ∀ x : GaloisField 3 q, x ≠ 0 → IsSquare x ∨ IsSquare (-x) :=
    fun x hx => isSquare_or_isSquare_neg_galois rfl hq0 hqodd hx
  -- exactly one of the two coefficients vanishes
  have hval : ∀ x : GaloisField 3 q, x - x ^ (3 : ℕ) = 0 → x = 0 ∨ x = 1 ∨ x = -1 := by
    intro x hx
    have h1 : x * ((x - 1) * (x + 1)) = 0 := by linear_combination -hx
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))
  have hcases : (lamP = 0 ∧ lamM ≠ 0) ∨ (lamM = 0 ∧ lamP ≠ 0) := by
    rcases hval lamP hP3 with hP | hP | hP <;> rcases hval lamM hM3 with hM | hM | hM
    · exact absurd (hP.trans hM.symm) hDel
    · exact Or.inl ⟨hP, by rw [hM]; exact one_ne_zero⟩
    · exact Or.inl ⟨hP, by rw [hM]; exact neg_ne_zero.mpr one_ne_zero⟩
    · exact Or.inr ⟨hM, by rw [hP]; exact one_ne_zero⟩
    · exact absurd (hP.trans hM.symm) hDel
    · exact absurd (by rw [hP, hM]; ring : lamP + lamM = 0) hSig
    · exact Or.inr ⟨hM, by rw [hP]; exact neg_ne_zero.mpr one_ne_zero⟩
    · exact absurd (by rw [hP, hM]; ring : lamP + lamM = 0) hSig
    · exact absurd (hP.trans hM.symm) hDel
  -- a same-sign pair dies: one orientation has weight zero
  have hsame_dead : ∀ x₀ x₁ y₀ y₁ : NormSet.normOneUnits 3 q,
      normOneVal x₀ = normOneVal x₁ + 1 → normOneVal y₀ = normOneVal y₁ + 1 →
      normOneVal x₀ ≠ normOneVal y₀ →
      (IsSquare (normOneVal y₀ ^ e - normOneVal x₀ ^ e)
        ↔ IsSquare (normOneVal y₁ ^ e - normOneVal x₁ ^ e)) → False := by
    intro x₀ x₁ y₀ y₁ hxx hyy hxy hiff
    have hd0 : normOneVal y₀ ^ e - normOneVal x₀ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hxy
    have hne₁ : normOneVal x₁ ≠ normOneVal y₁ :=
      fun h => hxy (by linear_combination hxx - hyy + h)
    have hd1 : normOneVal y₁ ^ e - normOneVal x₁ ^ e ≠ 0 :=
      skewPair_edge_left_ne_zero hcube hne₁
    have h1 := hmaster x₀ x₁ y₀ y₁ hxx hyy hxy
    have h2 := hmaster y₀ y₁ x₀ x₁ hyy hxx hxy.symm
    rw [show normOneVal x₀ ^ e - normOneVal y₀ ^ e
        = -(normOneVal y₀ ^ e - normOneVal x₀ ^ e) by ring,
      show normOneVal x₁ ^ e - normOneVal y₁ ^ e
        = -(normOneVal y₁ ^ e - normOneVal x₁ ^ e) by ring,
      sqSelect_neg_swap hneg1 (hdich _ hd0) hd0,
      sqSelect_neg_swap hneg1 (hdich _ hd1) hd1, he.neg_pow, he.neg_pow] at h2
    by_cases hs : IsSquare (normOneVal y₀ ^ e - normOneVal x₀ ^ e)
    · have hs₁ := hiff.mp hs
      rw [sqSelect_of_isSquare hs, sqSelect_of_isSquare hs₁] at h1
      rw [sqSelect_of_isSquare hs, sqSelect_of_isSquare hs₁] at h2
      rcases hcases with ⟨hP0, hM0⟩ | ⟨hM0, hP0⟩
      · exact skewPair_edge_weight_ne_zero hcube hxx
          (by rw [hP0] at h1; linear_combination h1)
      · exact skewPair_edge_weight_ne_zero hcube hyy
          (by rw [hM0] at h2; linear_combination h2)
    · have hs₁ : ¬IsSquare (normOneVal y₁ ^ e - normOneVal x₁ ^ e) :=
        fun h₁ => hs (hiff.mpr h₁)
      rw [sqSelect_of_not_isSquare hs, sqSelect_of_not_isSquare hs₁] at h1
      rw [sqSelect_of_not_isSquare hs, sqSelect_of_not_isSquare hs₁] at h2
      rcases hcases with ⟨hP0, hM0⟩ | ⟨hM0, hP0⟩
      · exact skewPair_edge_weight_ne_zero hcube hyy
          (by rw [hP0] at h2; linear_combination h2)
      · exact skewPair_edge_weight_ne_zero hcube hxx
          (by rw [hM0] at h1; linear_combination h1)
  have hmixed : ∀ x₀ x₁ y₀ y₁ : NormSet.normOneUnits 3 q,
      normOneVal x₀ = normOneVal x₁ + 1 → normOneVal y₀ = normOneVal y₁ + 1 →
      normOneVal x₀ ≠ normOneVal y₀ →
      ¬(IsSquare (normOneVal y₀ ^ e - normOneVal x₀ ^ e)
        ↔ IsSquare (normOneVal y₁ ^ e - normOneVal x₁ ^ e)) :=
    fun x₀ x₁ y₀ y₁ hxx hyy hxy hiff => hsame_dead x₀ x₁ y₀ y₁ hxx hyy hxy hiff
  -- two partners of `a` with the same sign pattern coincide
  have key : ∀ y₀ y₁ z₀ z₁ : NormSet.normOneUnits 3 q,
      normOneVal y₀ = normOneVal y₁ + 1 → normOneVal z₀ = normOneVal z₁ + 1 →
      normOneVal a₀ ≠ normOneVal y₀ → normOneVal a₀ ≠ normOneVal z₀ →
      normOneVal y₀ ≠ normOneVal z₀ →
      (IsSquare (normOneVal y₀ ^ e - normOneVal a₀ ^ e)
        ↔ IsSquare (normOneVal z₀ ^ e - normOneVal a₀ ^ e)) → False := by
    intro y₀ y₁ z₀ z₁ hyy hzz hay haz hyz hiff
    have h1 := hmaster a₀ a₁ y₀ y₁ haa hyy hay
    have h2 := hmaster a₀ a₁ z₀ z₁ haa hzz haz
    by_cases hsy : IsSquare (normOneVal y₀ ^ e - normOneVal a₀ ^ e)
    · have hsz := hiff.mp hsy
      have hns₁y : ¬IsSquare (normOneVal y₁ ^ e - normOneVal a₁ ^ e) :=
        fun h₁ => hmixed a₀ a₁ y₀ y₁ haa hyy hay (iff_of_true hsy h₁)
      have hns₁z : ¬IsSquare (normOneVal z₁ ^ e - normOneVal a₁ ^ e) :=
        fun h₁ => hmixed a₀ a₁ z₀ z₁ haa hzz haz (iff_of_true hsz h₁)
      rw [sqSelect_of_isSquare hsy, sqSelect_of_not_isSquare hns₁y] at h1
      rw [sqSelect_of_isSquare hsz, sqSelect_of_not_isSquare hns₁z] at h2
      rcases hcases with ⟨hP0, hM0⟩ | ⟨hM0, hP0⟩
      · have h12 : lamM * ((normOneVal y₁ ^ e - normOneVal a₁ ^ e) ^ e)
            = lamM * ((normOneVal z₁ ^ e - normOneVal a₁ ^ e) ^ e) := by
          rw [hP0] at h1 h2
          linear_combination h1 - h2
        have hz1 := Paley.pow_injective_of_cube hcube (mul_left_cancel₀ hM0 h12)
        have hy1 : normOneVal y₁ = normOneVal z₁ :=
          Paley.pow_injective_of_cube hcube (by linear_combination hz1)
        exact hyz (by linear_combination hyy - hzz + hy1)
      · have h12 : lamP * ((normOneVal y₀ ^ e - normOneVal a₀ ^ e) ^ e)
            = lamP * ((normOneVal z₀ ^ e - normOneVal a₀ ^ e) ^ e) := by
          rw [hM0] at h1 h2
          linear_combination h2 - h1
        have hz0 := Paley.pow_injective_of_cube hcube (mul_left_cancel₀ hP0 h12)
        exact hyz (Paley.pow_injective_of_cube hcube (by linear_combination hz0))
    · have hsz : ¬IsSquare (normOneVal z₀ ^ e - normOneVal a₀ ^ e) :=
        fun h => hsy (hiff.mpr h)
      have hs₁y : IsSquare (normOneVal y₁ ^ e - normOneVal a₁ ^ e) := by
        by_contra h₁
        exact hmixed a₀ a₁ y₀ y₁ haa hyy hay (iff_of_false hsy h₁)
      have hs₁z : IsSquare (normOneVal z₁ ^ e - normOneVal a₁ ^ e) := by
        by_contra h₁
        exact hmixed a₀ a₁ z₀ z₁ haa hzz haz (iff_of_false hsz h₁)
      rw [sqSelect_of_not_isSquare hsy, sqSelect_of_isSquare hs₁y] at h1
      rw [sqSelect_of_not_isSquare hsz, sqSelect_of_isSquare hs₁z] at h2
      rcases hcases with ⟨hP0, hM0⟩ | ⟨hM0, hP0⟩
      · have h12 : lamM * ((normOneVal y₀ ^ e - normOneVal a₀ ^ e) ^ e)
            = lamM * ((normOneVal z₀ ^ e - normOneVal a₀ ^ e) ^ e) := by
          rw [hP0] at h1 h2
          linear_combination h2 - h1
        have hz0 := Paley.pow_injective_of_cube hcube (mul_left_cancel₀ hM0 h12)
        exact hyz (Paley.pow_injective_of_cube hcube (by linear_combination hz0))
      · have h12 : lamP * ((normOneVal y₁ ^ e - normOneVal a₁ ^ e) ^ e)
            = lamP * ((normOneVal z₁ ^ e - normOneVal a₁ ^ e) ^ e) := by
          rw [hM0] at h1 h2
          linear_combination h1 - h2
        have hz1 := Paley.pow_injective_of_cube hcube (mul_left_cancel₀ hP0 h12)
        have hy1 : normOneVal y₁ = normOneVal z₁ :=
          Paley.pow_injective_of_cube hcube (by linear_combination hz1)
        exact hyz (by linear_combination hyy - hzz + hy1)
  -- three partners overload the two sign patterns
  by_cases hB : IsSquare (normOneVal b₀ ^ e - normOneVal a₀ ^ e) <;>
    by_cases hC : IsSquare (normOneVal c₀ ^ e - normOneVal a₀ ^ e) <;>
      by_cases hD : IsSquare (normOneVal d₀ ^ e - normOneVal a₀ ^ e)
  · exact key b₀ b₁ c₀ c₁ hbb hcc hab hac hbc (iff_of_true hB hC)
  · exact key b₀ b₁ c₀ c₁ hbb hcc hab hac hbc (iff_of_true hB hC)
  · exact key b₀ b₁ d₀ d₁ hbb hdd hab had hbd (iff_of_true hB hD)
  · exact key c₀ c₁ d₀ d₁ hcc hdd hac had hcd (iff_of_false hC hD)
  · exact key c₀ c₁ d₀ d₁ hcc hdd hac had hcd (iff_of_true hC hD)
  · exact key b₀ b₁ d₀ d₁ hbb hdd hab had hbd (iff_of_false hB hD)
  · exact key b₀ b₁ c₀ c₁ hbb hcc hab hac hbc (iff_of_false hB hC)
  · exact key b₀ b₁ c₀ c₁ hbb hcc hab hac hbc (iff_of_false hB hC)

/-! ### The capstone: no witness for `q ≠ 3` -/

/-- **The case tree, assembled: hypothesis (B) has no witness for `q ≠ 3`.**  Despite the
historical name, no exoticity of the exponent is assumed — the tree kills *every* exponent
(`e` odd with `e³ = 1` on the field, as every witness provides): a collision dies by Part I;
otherwise the conspiracy collapses to the master formula, and its four parameter branches
(`Δ = 0`, `Σ̄ = 0`, `μ ≠ 0`, `λ ∈ 𝔽₃`) all die.  The four distinct Paley points needed by the
branches exist because `|T| ≥ (3^q - 3)/4 ≥ 60` for `q ≥ 5`. -/
theorem false_of_exotic (data : FieldNormalizerData p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) : False := by
  subst hp
  classical
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hneg1 := not_isSquare_neg_one_galois rfl hq0 hqodd
  -- four distinct Paley elements
  letI : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  haveI : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have h30 : (3 : GaloisField 3 q) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 3 q) 3
  set T : Finset (GaloisField 3 q) := {a ∈ Finset.univ | a ∈ Paley.paleySet (GaloisField 3 q)}
    with hTdef
  have hT : ∀ a, a ∈ T ↔ a ∈ Paley.paleySet (GaloisField 3 q) := by
    intro a
    simp [hTdef]
  have hlow := Paley.card_paleySet_lower h30 hneg1 T hT
  have hcard : Fintype.card (GaloisField 3 q) = 3 ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 q hq0
  have hq5 : 5 ≤ q := by
    have h2 := hqprime.two_le
    have hodd := Nat.odd_iff.mp hqodd
    omega
  have hcard5 : 3 ^ 5 ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) hq5
  have hT4 : 4 ≤ T.card := by
    rw [hcard] at hlow
    omega
  obtain ⟨t₁, ht₁⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  obtain ⟨t₂, ht₂⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem ht₁]; omega : 0 < (T.erase t₁).card)
  obtain ⟨t₃, ht₃⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem ht₂, Finset.card_erase_of_mem ht₁]; omega :
      0 < ((T.erase t₁).erase t₂).card)
  obtain ⟨t₄, ht₄⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem ht₃, Finset.card_erase_of_mem ht₂,
        Finset.card_erase_of_mem ht₁]; omega :
      0 < (((T.erase t₁).erase t₂).erase t₃).card)
  have h12 : t₂ ≠ t₁ := Finset.ne_of_mem_erase ht₂
  have h23 : t₃ ≠ t₂ := Finset.ne_of_mem_erase ht₃
  have h13 : t₃ ≠ t₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht₃)
  have h34 : t₄ ≠ t₃ := Finset.ne_of_mem_erase ht₄
  have h24 : t₄ ≠ t₂ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht₄)
  have h14 : t₄ ≠ t₁ :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht₄))
  obtain ⟨hp₁0, hp₁sq, hp₁10, hp₁1sq⟩ := (hT t₁).mp ht₁
  obtain ⟨hp₂0, hp₂sq, hp₂10, hp₂1sq⟩ := (hT t₂).mp (Finset.mem_of_mem_erase ht₂)
  obtain ⟨hp₃0, hp₃sq, hp₃10, hp₃1sq⟩ :=
    (hT t₃).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht₃))
  obtain ⟨hp₄0, hp₄sq, hp₄10, hp₄1sq⟩ := (hT t₄).mp
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht₄)))
  -- lift to Paley pairs of norm-one units
  let mk : ∀ (t : GaloisField 3 q), t ≠ 0 → IsSquare t → NormSet.normOneUnits 3 q :=
    fun t ht0 htsq => ⟨Units.mk0 t ht0,
      (mem_normOneUnits_iff_isSquare rfl hq0 _).mpr (by simpa using htsq)⟩
  have hxx₁ : normOneVal (mk (t₁ + 1) hp₁10 hp₁1sq) = normOneVal (mk t₁ hp₁0 hp₁sq) + 1 := rfl
  have hxx₂ : normOneVal (mk (t₂ + 1) hp₂10 hp₂1sq) = normOneVal (mk t₂ hp₂0 hp₂sq) + 1 := rfl
  have hxx₃ : normOneVal (mk (t₃ + 1) hp₃10 hp₃1sq) = normOneVal (mk t₃ hp₃0 hp₃sq) + 1 := rfl
  have hxx₄ : normOneVal (mk (t₄ + 1) hp₄10 hp₄1sq) = normOneVal (mk t₄ hp₄0 hp₄sq) + 1 := rfl
  have hne₁₂ : normOneVal (mk (t₁ + 1) hp₁10 hp₁1sq)
      ≠ normOneVal (mk (t₂ + 1) hp₂10 hp₂1sq) :=
    fun h => h12.symm (by
      have h' : (t₁ + 1 : GaloisField 3 q) = t₂ + 1 := h
      linear_combination h')
  have hne₁₃ : normOneVal (mk (t₁ + 1) hp₁10 hp₁1sq)
      ≠ normOneVal (mk (t₃ + 1) hp₃10 hp₃1sq) :=
    fun h => h13.symm (by
      have h' : (t₁ + 1 : GaloisField 3 q) = t₃ + 1 := h
      linear_combination h')
  have hne₁₄ : normOneVal (mk (t₁ + 1) hp₁10 hp₁1sq)
      ≠ normOneVal (mk (t₄ + 1) hp₄10 hp₄1sq) :=
    fun h => h14.symm (by
      have h' : (t₁ + 1 : GaloisField 3 q) = t₄ + 1 := h
      linear_combination h')
  have hne₂₃ : normOneVal (mk (t₂ + 1) hp₂10 hp₂1sq)
      ≠ normOneVal (mk (t₃ + 1) hp₃10 hp₃1sq) :=
    fun h => h23.symm (by
      have h' : (t₂ + 1 : GaloisField 3 q) = t₃ + 1 := h
      linear_combination h')
  have hne₂₄ : normOneVal (mk (t₂ + 1) hp₂10 hp₂1sq)
      ≠ normOneVal (mk (t₄ + 1) hp₄10 hp₄1sq) :=
    fun h => h24.symm (by
      have h' : (t₂ + 1 : GaloisField 3 q) = t₄ + 1 := h
      linear_combination h')
  have hne₃₄ : normOneVal (mk (t₃ + 1) hp₃10 hp₃1sq)
      ≠ normOneVal (mk (t₄ + 1) hp₄10 hp₄1sq) :=
    fun h => h34.symm (by
      have h' : (t₃ + 1 : GaloisField 3 q) = t₄ + 1 := h
      linear_combination h')
  -- a collision dies by Part I
  by_cases hcoll : ∃ p₀ p₁ r₀ r₁ : NormSet.normOneUnits 3 q,
      normOneVal p₀ = normOneVal p₁ + 1 ∧ normOneVal r₀ = normOneVal r₁ + 1 ∧
      normOneVal p₀ ≠ normOneVal r₀ ∧
      normOneVal r₀ ^ e - normOneVal p₀ ^ e = normOneVal r₁ ^ e - normOneVal p₁ ^ e
  · obtain ⟨p₀, p₁, r₀, r₁, hpp, hrr, hne, heq⟩ := hcoll
    obtain ⟨S, S', hpair⟩ := exists_collisionPair_of_sub_ne_zero rfl hq0 hqodd p₀ p₁ r₀ r₁
      hpp hrr (by linear_combination -heq) (skewPair_edge_left_ne_zero hcube hne)
    exact false_of_collisionPair data rfl hqprime hq3 hqodd he hcube hexp hpair
  push Not at hcoll
  -- no collision: the conspiracy collapses to the master formula
  obtain ⟨lamP, lamM, hmaster⟩ := exists_masterFormula_of_no_collision data rfl hqprime hq3
    hqodd he hcube hexp hxx₁ hxx₂ hxx₃ hne₁₂ hne₁₃ hne₂₃ hcoll
  by_cases hDel : lamP = lamM
  · rw [hDel] at hmaster
    exact false_of_masterFormula_delta_zero rfl he hcube hxx₁ hxx₂ hxx₃
      hne₁₂ hne₁₃ hne₂₃ hmaster
  by_cases hSig : lamP + lamM = 0
  · have hlamM : lamM = -lamP := by linear_combination hSig
    rw [hlamM] at hmaster
    exact false_of_masterFormula_sigma_zero data rfl hqprime hq3 hqodd he hcube hexp
      hxx₁ hxx₂ hne₁₂ hmaster
  by_cases hmu : lamP - lamP ^ (3 : ℕ) = 0 ∧ lamM - lamM ^ (3 : ℕ) = 0
  · exact false_of_masterFormula_cubic rfl hq0 hqodd he hcube hxx₁ hxx₂ hxx₃ hxx₄
      hne₁₂ hne₁₃ hne₁₄ hne₂₃ hne₂₄ hne₃₄ hmaster hmu.1 hmu.2 hDel hSig
  · exact false_of_masterFormula_mu_ne_zero rfl hq0 hqodd he hcube hxx₁ hxx₂ hxx₃
      hne₁₂ hne₁₃ hne₂₃ hcoll hmaster hSig hmu

/-- **Hypothesis (B) has no witness for `p = 3`, `q ≠ 3`** — from the witness data alone:
`q` is odd by condition (A), the exponent is extracted from the witness
(`exists_odd_cube_exponent`), and the case tree kills it (`false_of_exotic`). -/
theorem false_of_witness (data : FieldNormalizerData p q G) (hp : p = 3) (hq3 : q ≠ 3) :
    False := by
  have hqodd := q_odd_of_conditionA data hp
  obtain ⟨e, he, hcube, hexp⟩ := exists_odd_cube_exponent data hp data.q_prime hqodd
  exact false_of_exotic data hp data.q_prime hq3 hqodd he hcube hexp

/-- **BG Appendix C, Problem 1 (Péterfalvi 1993), resolved: hypothesis (B) has no witness
for `p = 3`.**  The answer to "*Can the hypothesis of Proposition 9 be satisfied for
`p = 3`?*" is **no**, for every `q` and with no finiteness assumption on `G`: for `q ≠ 3` the
collision-free skew calculus kills every exponent (`false_of_witness`), and for `q = 3` every
admissible exponent is a Frobenius power mod `13` and Theorem 1 applies
(`false_of_frobenius_exponent`). -/
theorem hypothesisB_false (data : FieldNormalizerData p q G) (hp : p = 3) : False := by
  by_cases hq3 : q = 3
  · subst hq3
    obtain ⟨e, he, hcube, hexp⟩ :=
      exists_odd_cube_exponent data hp Nat.prime_three (by decide)
    subst hp
    -- the norm-one units have order `13`, so the exponent is `1`, `3` or `9` mod `13`
    have hncard : Nat.card (NormSet.normOneUnits 3 3) = 13 := by
      rw [NormSet.normOneUnits_card 3 3 (by norm_num)]
      norm_num
    have hcubeu : ∀ u : NormSet.normOneUnits 3 3, u ^ (e * e * e) = u := by
      intro u
      have h := hcube (((u : (GaloisField 3 3)ˣ) : GaloisField 3 3))
      refine Subtype.ext (Units.ext ?_)
      simpa using h
    obtain ⟨u₀, hu₀⟩ := IsCyclic.exists_generator (α := NormSet.normOneUnits 3 3)
    have hord : orderOf u₀ = 13 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hu₀, hncard]
    have hmod : e * e * e ≡ 1 [MOD 13] := by
      have h1 : u₀ ^ (e * e * e) = u₀ ^ 1 := by simpa using hcubeu u₀
      have h2 := pow_eq_pow_iff_modEq.mp h1
      rwa [hord] at h2
    have hdec : ∀ r : ℕ, r < 13 → r * r * r % 13 = 1 → r = 1 ∨ r = 3 ∨ r = 9 := by decide
    have hcases := hdec (e % 13) (Nat.mod_lt _ (by norm_num)) (by
      have hself : e ≡ e % 13 [MOD 13] := (Nat.mod_modEq e 13).symm
      have hmm := ((hself.symm.mul hself.symm).mul hself.symm).trans hmod
      simpa [Nat.ModEq] using hmm)
    have hfrobmk : ∀ jj : ℕ, e % 13 = 3 ^ jj % 13 →
        ∀ u : NormSet.normOneUnits 3 3, u ^ e = u ^ 3 ^ jj := by
      intro jj hjj u
      have hdvd : orderOf u ∣ 13 := by
        rw [← hncard]
        exact orderOf_dvd_natCard u
      exact pow_eq_pow_iff_modEq.mpr ((show e ≡ 3 ^ jj [MOD 13] from hjj).of_dvd hdvd)
    rcases hcases with h | h | h
    · exact false_of_frobenius_exponent data rfl hexp (hfrobmk 0 (by rw [h]; norm_num))
    · exact false_of_frobenius_exponent data rfl hexp (hfrobmk 1 (by rw [h]; norm_num))
    · exact false_of_frobenius_exponent data rfl hexp (hfrobmk 2 (by rw [h]; norm_num))
  · exact false_of_witness data hp hq3

end SkewEndgame

end OddOrder.BG.AppC.Problem1
