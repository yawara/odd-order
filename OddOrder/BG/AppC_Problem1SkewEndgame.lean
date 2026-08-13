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

end SkewEndgame

end OddOrder.BG.AppC.Problem1
