/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_Problem1SkewCalculus

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

end SkewEndgame

end OddOrder.BG.AppC.Problem1
