import OddOrder.Peterfalvi.S15_SAndT_Setup.NormEstimates
import OddOrder.Peterfalvi.S13_ElementaryAbelianKernel
import OddOrder.BG.Ch2_Uniqueness.S07_Theorem74

/-!
# Peterfalvi (13.11)-(13.15) — order and divisor determination

Split from the former monolithic `OddOrder.Peterfalvi.S15_SAndT_Setup` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]


/-! ## (13.11)--(13.15): order and divisor determination -/

/-- Lower estimate for the analytic parameter `m` of **Peterfalvi (13.10)**.
Dropping the (positive) last summand and bounding `(q-1)/q^p ≤ 1/q^2` (valid once
`p ≥ 3`) gives `m ≥ 1 - 1/(q-1) - 1/q^2`. -/
theorem m_value_ge_aux {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (1 : ℚ) - 1 / ((q : ℚ) - 1) - 1 / (q : ℚ) ^ 2 ≤
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hXpos : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hX3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hfrac : ((q : ℚ) - 1) / (q : ℚ) ^ p ≤ 1 / (q : ℚ) ^ 2 := by
    rw [div_le_div_iff₀ hXpos (by positivity)]
    have e : (q : ℚ) ^ 3 = ((q : ℚ) - 1) * (q : ℚ) ^ 2 + (q : ℚ) ^ 2 := by ring
    have hsq : (0 : ℚ) ≤ (q : ℚ) ^ 2 := sq_nonneg _
    linarith [hX3, e, hsq]
  have hpos : (0 : ℚ) ≤ 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by positivity
  linarith [hfrac, hpos]

/-- **Peterfalvi (13.11.b)** numeric bound: `q ≥ 5 ⇒ m > 7/10`. -/
theorem m_value_gt_seven_tenths {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (7 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have haux := m_value_ge_aux hq hp
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq5]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11.a)** numeric bound: `q ≥ 7 ⇒ m > 8/10`. -/
theorem m_value_gt_four_fifths {q p : ℕ} (hq : 7 ≤ q) (hp : 3 ≤ p) :
    (8 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : 5 ≤ q := by omega
  have haux := m_value_ge_aux hq5 hp
  have hq7 : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 49 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq7]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11)** numeric core of the `q = 3` branch: once the
Section 16 hypothesis gives `p ≥ 5`, the concrete value of `m` is already
strictly larger than `49/100`. -/
theorem m_value_q_three_gt_49_hundredths {p : ℕ} (hp : 5 ≤ p) :
    (49 : ℚ) / 100 <
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
        1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p) := by
  have h4 : 4 ≤ p - 1 := by omega
  have hpow4 : (3 : ℚ) ^ 4 ≤ (3 : ℚ) ^ (p - 1) :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 3) h4
  norm_num at hpow4
  have hden_gt : (100 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hden_pos : (0 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hsmall : 1 / (2 * (3 : ℚ) ^ (p - 1)) < (1 : ℚ) / 100 := by
    rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℚ) < 100)]
    nlinarith
  have hpow : (3 : ℚ) ^ p = 3 * (3 : ℚ) ^ (p - 1) := by
    have hp_eq : p = (p - 1) + 1 := by omega
    rw [hp_eq, pow_succ]
    rw [show p - 1 + 1 - 1 = p - 1 by omega]
    ring
  have hexpr :
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
          1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p)
        = (1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (p - 1)) := by
    rw [hpow]
    field_simp [hden_pos.ne']
    ring
  rw [hexpr]
  linarith [hsmall]

/-- Exponential estimate used in **Peterfalvi (13.11.c)**: for `n ≥ 5`,
`n² ≤ 3^(n-1)`.  The induction step is `(n+1)² ≤ 3n²`. -/
private theorem sq_le_three_pow_pred_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    n ^ 2 ≤ 3 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep : (n + 1) ^ 2 ≤ 3 * n ^ 2 := by nlinarith
      calc
        (n + 1) ^ 2 ≤ 3 * n ^ 2 := hstep
        _ ≤ 3 * 3 ^ (n - 1) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (n + 1 - 1) := by
          rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
          ring

/-- **Numerical core shared by Peterfalvi (13.12) and (13.15)**: the upper estimate
`m < q·p / ((2q+1)(p-1))` — obtained from `c ≥ 2q+1` (13.12) resp. the divisor `x ≥ 2q+1`
(13.15) together with the analytic inequality (13.10) and `u ≤ (p^q-1)/(p-1)` (13.2.c) — combined
with the (13.11) lower bounds on `m` forces `q = 3`.

Self-contained `ℚ`-arithmetic over an abstract `m` satisfying the (13.11.a,b) lower bounds; `p`, `q`
are odd primes so `p = 3 ∨ p ≥ 5` and `q = 3 ∨ q ≥ 5`, as supplied by the callers.

* `p ≥ 5`: `m < q·p/((2q+1)(p-1)) < (1/2)(5/4) = 5/8 < 7/10`, against `m > 7/10` (13.11.b).
* `p = 3`, `q ≥ 7`: `m < 3q/(2(2q+1)) < 3/4 < 8/10`, against `m > 8/10` (13.11.a).
* `p = 3`, `5 ≤ q < 7`: `m < 3q/(2(2q+1)) < 7/10`, against `m > 7/10` (13.11.b). -/
theorem caseB_numeric_forces_q_three {p q : ℕ} {m : ℚ}
    (hp : p = 3 ∨ 5 ≤ p) (hq : q = 3 ∨ 5 ≤ q)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hbound : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1))) :
    q = 3 := by
  rcases hq with hq3 | hq5
  · exact hq3
  exfalso
  have hqR : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq5
  have hm7over : (7 : ℚ) / 10 < m := hm5 hq5
  rcases hp with rfl | hp5
  · -- `p = 3`
    have hden : (0 : ℚ) < (2 * (q : ℚ) + 1) * (((3 : ℕ) : ℚ) - 1) := by
      rw [show (((3 : ℕ) : ℚ)) = 3 by norm_num]; nlinarith [hqR]
    have hb := (lt_div_iff₀ hden).mp hbound
    rw [show (((3 : ℕ) : ℚ)) = 3 by norm_num] at hb
    by_cases hq7 : 7 ≤ q
    · have h87 : (8 : ℚ) / 10 < m := hm7 hq7
      nlinarith [hb, h87, hqR]
    · have hqlt7 : (q : ℚ) < 7 := by exact_mod_cast (show q < 7 by omega)
      nlinarith [hb, hm7over, hqR, hqlt7]
  · -- `p ≥ 5`
    have hpR5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp5
    have hden : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by nlinarith [hqR, hpR5]
    have hb := (lt_div_iff₀ hden).mp hbound
    nlinarith [hb, hm7over, hqR, hpR5]

/-- Exponential estimate for the case-A branch of **Peterfalvi (13.13)**:
`16n ≤ 5·2^(n-1)` for `n ≥ 5`.  Equivalently, `n/2^(n-1) ≤ 5/16`; this is the
decaying upper bound that contradicts (13.11.b). -/
private theorem sixteen_mul_le_five_mul_two_pow_pred {n : ℕ} (hn : 5 ≤ n) :
    16 * n ≤ 5 * 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        16 * (n + 1) ≤ 2 * (16 * n) := by omega
        _ ≤ 2 * (5 * 2 ^ (n - 1)) := Nat.mul_le_mul_left 2 ih
        _ = 5 * 2 ^ (n + 1 - 1) := by
          rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
          ring

/-- **Peterfalvi (13.13), pure numeric core.**  If `q` is an odd prime, (13.10) holds with
`c = 1`, and the case-A block action gives
`u ∣ ((p - 1) / 2)^(q - 1)`, then the (13.11) lower estimates force
`q = 3` and `u = (p - 1)^2 / 4`.

For `q ≥ 5`, the divisibility bound and `2·((p-1)/2) = p-1 < p` give
`m < q/2^(q-1) ≤ 5/16`, contradicting `m > 7/10`.  At `q = 3`, a proper divisor `u`
of `((p-1)/2)^2` is at most half that square, contradicting (13.11.c). -/
theorem caseA_numeric_parameters {p q u : ℕ} {m : ℚ}
    (hp3 : 3 ≤ p) (hqprime : q.Prime) (hqne2 : q ≠ 2)
    (hpeven : 2 ∣ p - 1)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m)
    (h13c : q = 3 → (((p ^ 2 - 1 : ℕ) : ℚ) / 6) < (u : ℚ))
    (hanalytic : (u : ℚ) >
      m * ((p ^ (q - 1) : ℕ) : ℚ) / (q : ℚ))
    (hdiv : u ∣ ((p - 1) / 2) ^ (q - 1)) :
    q = 3 ∧ u = (p - 1) ^ 2 / 4 := by
  let a := (p - 1) / 2
  have ha_pos : 0 < a := by
    dsimp [a]
    omega
  have hsplit : p - 1 = 2 * a := by
    dsimp [a]
    exact (Nat.mul_div_cancel' hpeven).symm
  have hdiv' : u ∣ a ^ (q - 1) := by simpa [a] using hdiv
  have hu_le : u ≤ a ^ (q - 1) :=
    Nat.le_of_dvd (pow_pos ha_pos _) hdiv'
  have hq3le : 3 ≤ q := by
    have := hqprime.two_le
    omega
  have hq3or5 : q = 3 ∨ 5 ≤ q := by
    by_cases hq3 : q = 3
    · exact Or.inl hq3
    · right
      by_contra hq5
      have hq4 : q = 4 := by omega
      subst q
      norm_num at hqprime
  have hq3 : q = 3 := by
    rcases hq3or5 with hq3 | hq5
    · exact hq3
    · exfalso
      have hqRpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hqprime.pos
      have hpRpos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
      have hpPowRpos : (0 : ℚ) < (p : ℚ) ^ (q - 1) := by positivity
      have huR : (u : ℚ) ≤ (a : ℚ) ^ (q - 1) := by exact_mod_cast hu_le
      have hpowcast : (((p ^ (q - 1) : ℕ) : ℚ)) = (p : ℚ) ^ (q - 1) := by
        push_cast
        ring
      rw [hpowcast] at hanalytic
      have hanalytic' : m * (p : ℚ) ^ (q - 1) / (q : ℚ) < (u : ℚ) := hanalytic
      rw [div_lt_iff₀ hqRpos] at hanalytic'
      have hmp : m * (p : ℚ) ^ (q - 1) < (a : ℚ) ^ (q - 1) * (q : ℚ) :=
        hanalytic'.trans_le (mul_le_mul_of_nonneg_right huR (le_of_lt hqRpos))
      have hp1cast : (((p - 1 : ℕ) : ℚ)) = (p : ℚ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
        rfl
      have hsplitR : (p : ℚ) - 1 = 2 * (a : ℚ) := by
        have h := congrArg (fun n : ℕ => (n : ℚ)) hsplit
        push_cast at h
        rw [hp1cast] at h
        exact h
      have hpred : (p - 1) ^ (q - 1) < p ^ (q - 1) :=
        Nat.pow_lt_pow_left (by omega) (by omega)
      have hpredR : ((p : ℚ) - 1) ^ (q - 1) < (p : ℚ) ^ (q - 1) := by
        have h : (((p - 1) ^ (q - 1) : ℕ) : ℚ) < ((p ^ (q - 1) : ℕ) : ℚ) := by
          exact_mod_cast hpred
        push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at h
        exact h
      have htwoa : (2 : ℚ) ^ (q - 1) * (a : ℚ) ^ (q - 1) =
          ((p : ℚ) - 1) ^ (q - 1) := by
        rw [← mul_pow, ← hsplitR]
      have hmul := mul_lt_mul_of_pos_right hmp
        (show (0 : ℚ) < (2 : ℚ) ^ (q - 1) by positivity)
      have hcancel :
          (m * (2 : ℚ) ^ (q - 1)) * (p : ℚ) ^ (q - 1) <
            (q : ℚ) * (p : ℚ) ^ (q - 1) := by
        calc
          (m * (2 : ℚ) ^ (q - 1)) * (p : ℚ) ^ (q - 1)
              = (m * (p : ℚ) ^ (q - 1)) * (2 : ℚ) ^ (q - 1) := by ring
          _ < ((a : ℚ) ^ (q - 1) * (q : ℚ)) * (2 : ℚ) ^ (q - 1) := hmul
          _ = (q : ℚ) * ((p : ℚ) - 1) ^ (q - 1) := by rw [← htwoa]; ring
          _ < (q : ℚ) * (p : ℚ) ^ (q - 1) :=
            mul_lt_mul_of_pos_left hpredR hqRpos
      have hm2pow : m * (2 : ℚ) ^ (q - 1) < (q : ℚ) :=
        lt_of_mul_lt_mul_right hcancel (le_of_lt hpPowRpos)
      have hmupper : m < (q : ℚ) / (2 : ℚ) ^ (q - 1) :=
        (lt_div_iff₀ (show (0 : ℚ) < (2 : ℚ) ^ (q - 1) by positivity)).mpr hm2pow
      have hnat := sixteen_mul_le_five_mul_two_pow_pred hq5
      have hnatR : (16 : ℚ) * (q : ℚ) ≤ 5 * (2 : ℚ) ^ (q - 1) := by
        exact_mod_cast hnat
      have hratio : (q : ℚ) / (2 : ℚ) ^ (q - 1) ≤ (5 : ℚ) / 16 := by
        rw [div_le_div_iff₀ (show (0 : ℚ) < (2 : ℚ) ^ (q - 1) by positivity)
          (by norm_num : (0 : ℚ) < 16)]
        nlinarith [hnatR]
      linarith [hm5 hq5, hmupper, hratio]
  have hdiv2 : u ∣ a ^ 2 := by simpa [hq3] using hdiv'
  have htarget : (p - 1) ^ 2 / 4 = a ^ 2 := by
    rw [hsplit, mul_pow]
    norm_num
  have hueq : u = a ^ 2 := by
    by_contra hne
    have hule : u ≤ a ^ 2 := Nat.le_of_dvd (pow_pos ha_pos 2) hdiv2
    have hult : u < a ^ 2 := lt_of_le_of_ne hule hne
    obtain ⟨k, hk⟩ := hdiv2
    have hk0 : k ≠ 0 := by
      intro hk0
      subst k
      simp at hk
      omega
    have hk1 : k ≠ 1 := by
      intro hk1
      subst k
      simp at hk
      omega
    have hk2 : 2 ≤ k := by omega
    have hu2 : 2 * u ≤ a ^ 2 := by
      calc
        2 * u = u * 2 := Nat.mul_comm _ _
        _ ≤ u * k := Nat.mul_le_mul_left u hk2
        _ = a ^ 2 := hk.symm
    have hlower := h13c hq3
    have hp2one : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hp2cast : (((p ^ 2 - 1 : ℕ) : ℚ)) = (p : ℚ) ^ 2 - 1 := by
      push_cast [Nat.cast_sub hp2one]
      ring
    rw [hp2cast] at hlower
    have hu2R : (2 : ℚ) * (u : ℚ) ≤ (a : ℚ) ^ 2 := by exact_mod_cast hu2
    have hp1cast : (((p - 1 : ℕ) : ℚ)) = (p : ℚ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      rfl
    have hsplitR : (p : ℚ) - 1 = 2 * (a : ℚ) := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) hsplit
      push_cast at h
      rw [hp1cast] at h
      exact h
    have haR : (a : ℚ) = ((p : ℚ) - 1) / 2 := by linarith [hsplitR]
    rw [haR] at hu2R
    have hp3R : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
    nlinarith [hlower, hu2R, hp3R]
  exact ⟨hq3, hueq.trans htarget.symm⟩
namespace Hypothesis

/-- **Peterfalvi (13.11.a)** at the Section 15 hypothesis level: if `q ≥ 7`,
then the concrete analytic parameter satisfies `m > 8/10`. -/
theorem m_gt_four_fifths_of_seven_le_q (hyp : Hypothesis (G := G))
    (hq7 : 7 ≤ hyp.q) :
    hyp.m > (8 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_four_fifths hq7 hyp.three_le_p

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

/-- **Peterfalvi (13.11)** at the Section 15 hypothesis level: in the `q = 3`
branch, the `m > 49/100` part follows once an external argument supplies
`p ≥ 5`.  Section 16 supplies this from `q < p`. -/
theorem m_gt_49_hundredths_of_q_eq_three_of_five_le_p
    (hyp : Hypothesis (G := G)) (hq3 : hyp.q = 3) (hp5 : 5 ≤ hyp.p) :
    hyp.m > (49 / 100 : ℚ) := by
  rw [hyp.m_eq, hq3]
  exact m_value_q_three_gt_49_hundredths hp5

/-- The `m`-only part of **Peterfalvi (13.11)**.  The full `numeric_bounds`
theorem below also packages the `u/c` inequality in the `q = 3` branch, so it
still waits for the analytic estimate (13.10). -/
theorem numeric_m_bounds (hyp : Hypothesis (G := G)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 → 5 ≤ hyp.p → hyp.m > (49 / 100 : ℚ)) := by
  exact ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q,
    fun hq3 hp5 => hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq3 hp5⟩

end Hypothesis

/-- **Arithmetic bridge for Peterfalvi (13.2.c), non-Galois case**: `(p-1)^(q-1) ≤ (p^q-1)/(p-1)`.

In the non-Galois type-`P` case the Singer/semilinear bound gives `u ≤ (p-1)^(q-1)` (Coq
`FTtypeP_facts`, via `card_mx`), which this relaxes to the uniform (13.2.c) form
`u ≤ (p^q-1)/(p-1)`.  Elementary: `(p-1)^(q-1) ≤ p^(q-1) ≤ (p^q-1)/(p-1)` (the last since
`p^(q-1)·(p-1) = p^q - p^(q-1) ≤ p^q - 1`).  Pure `ℕ` arithmetic, `sorry`-free. -/
theorem pred_pow_le_cyclotomic_quotient {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  refine le_trans (Nat.pow_le_pow_left (Nat.sub_le p 1) (q - 1)) ?_
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have ha : 1 ≤ (d + 1) ^ (q - 1) := Nat.one_le_pow _ _ (by omega)
  have hap' : (d + 1) ^ (q - 1) * d + (d + 1) ^ (q - 1) = (d + 1) ^ q := by
    have h1 : (d + 1) ^ (q - 1) * d + (d + 1) ^ (q - 1) = (d + 1) ^ (q - 1) * (d + 1) := by ring
    rw [h1, ← pow_succ]; congr 1; omega
  omega

/-- **Peterfalvi (8.4.d) restricted to `C`**: `W₁` acts fixed-point-freely on `C ⊆ U` by
conjugation — no `w ∈ W₁ #` centralizes any `c ∈ C #`.  `U W₁` is a Frobenius group with kernel `U`
(`typeP_uW1_frobenius`), and `C = U ⊓ C_G(P) ≤ U`, so the Frobenius fpf condition restricts to `C`.
The fpf input to the (13.12) `c ≡ 1 (mod q)` step (Coq `dv_2q_c1`). -/
theorem Hypothesis.W1_fpf_C [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ w ∈ hyp.W1, w ≠ 1 → ∀ c ∈ hyp.C, c ≠ 1 → w * c * w⁻¹ ≠ c := by
  let setup := hyp.toTypesIIIIIIVSetupS hG
  have hUne := setup.nontrivial.1
  change hyp.Sdata.U ≠ ⊥ at hUne
  have frob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hUne
  rw [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at frob
  have hCU : hyp.C ≤ hyp.U := by rw [hyp.C_eq]; exact inf_le_left
  intro w hw hw1 c hc hc1
  have hwL : w ∈ hyp.U ⊔ hyp.W1 := (le_sup_right : hyp.W1 ≤ _) hw
  have hcL : c ∈ hyp.U ⊔ hyp.W1 := (le_sup_left : hyp.U ≤ _) (hCU hc)
  have hne1 : (⟨w, hwL⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hw1 (by simpa using congrArg Subtype.val h)
  have hnec : (⟨c, hcL⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hc1 (by simpa using congrArg Subtype.val h)
  have hmemw : (⟨w, hwL⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) :=
    Subgroup.mem_subgroupOf.mpr hw
  have hmemc : (⟨c, hcL⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) :=
    Subgroup.mem_subgroupOf.mpr (hCU hc)
  have hconj := frob.conj_frobenius _ hmemw hne1 _ hmemc hnec
  intro heq
  apply hconj
  apply Subtype.ext
  push_cast
  exact heq

/-- `W₁` normalizes `C = U ⊓ C_G(P)`: `W₁ ≤ S ≤ N_G(P)` (so it normalizes `C_G(P)`) and
`W₁ ≤ N_G(U)` (`W1_normalizes_U`), hence it normalizes their intersection.  The `N_G(C)`-input to
the conjugation action of the (13.12) `c ≡ 1 (mod q)` step. -/
theorem Hypothesis.W1_le_normalizer_C (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ Subgroup.normalizer (hyp.C : Set G) := by
  have hW1S : hyp.W1 ≤ hyp.S := by
    have h1 : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have h2 : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
    exact h1.trans h2
  have hSP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  intro w hw
  have hwP := hSP (hW1S hw)
  have hwU := hyp.W1_normalizes_U hw
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  rw [hyp.C_eq]
  simp only [Subgroup.mem_inf, SetLike.mem_coe]
  -- `w` normalizes `U` and `C_G(P)`; combine.
  have hU_iff : x ∈ hyp.U ↔ w * x * w⁻¹ ∈ hyp.U :=
    Subgroup.mem_set_normalizer_iff.mp hwU x
  have hCP_iff : x ∈ Subgroup.centralizer (hyp.P : Set G) ↔
      w * x * w⁻¹ ∈ Subgroup.centralizer (hyp.P : Set G) := by
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : w⁻¹ * p * w ∈ (hyp.P : Set G) := (Subgroup.mem_set_normalizer_iff''.mp hwP p).mp hp
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) _ hp'
      calc p * (w * x * w⁻¹) = w * ((w⁻¹ * p * w) * x) * w⁻¹ := by group
        _ = w * (x * (w⁻¹ * p * w)) * w⁻¹ := by rw [hcomm]
        _ = (w * x * w⁻¹) * p := by group
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : w * p * w⁻¹ ∈ (hyp.P : Set G) := (Subgroup.mem_set_normalizer_iff.mp hwP p).mp hp
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) _ hp'
      calc p * x = w⁻¹ * ((w * p * w⁻¹) * (w * x * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * x * w⁻¹) * (w * p * w⁻¹)) * w := by rw [hcomm]
        _ = x * p := by group
  rw [hU_iff, hCP_iff]

/-- **Peterfalvi (13.12), structural step**: `c ≡ 1 (mod q)`.

The cyclic factor `W₁` (order `q`) acts fixed-point-freely on `C ⊆ U` by conjugation
(`W1_fpf_C`, `W1_le_normalizer_C`).  Since `W₁` is a `q`-group, the class equation
(`IsPGroup.card_modEq_card_fixedPoints`) gives `|C| ≡ |C_C(W₁)| (mod q)`, and the fpf condition
makes `C_C(W₁) = {1}`.  This is the Coq `dv_2q_c1` ingredient (`q ∣ c − 1`) of
`FTtypeP_Ind_Fitting_reg_Fcore`. -/
theorem Hypothesis.c_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.c ≡ 1 [MOD hyp.q] := by
  classical
  haveI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hfpf := hyp.W1_fpf_C hG
  letI : MulAction ↥hyp.W1 ↥hyp.C :=
    MulAction.compHom ↥hyp.C (Subgroup.inclusion hyp.W1_le_normalizer_C)
  have hsmul : ∀ (w : ↥hyp.W1) (x : ↥hyp.C), ((w • x : ↥hyp.C) : G) = (w : G) * (x : G) * (w : G)⁻¹ :=
    fun _ _ => rfl
  have hW1pg : IsPGroup hyp.q ↥hyp.W1 := IsPGroup.of_card (by rw [← hyp.q_eq_card_W1, pow_one])
  have hmod : Nat.card ↥hyp.C ≡ Nat.card ↥(MulAction.fixedPoints ↥hyp.W1 ↥hyp.C) [MOD hyp.q] :=
    hW1pg.card_modEq_card_fixedPoints ↥hyp.C
  -- `W₁ ≠ ⊥`, pick `w₀ ∈ W₁ #`.
  have hW1ne : hyp.W1 ≠ ⊥ := by
    intro h; have h3 := hyp.three_le_q
    rw [hyp.q_eq_card_W1, h, Subgroup.card_bot] at h3; omega
  haveI : Nontrivial ↥hyp.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
  obtain ⟨⟨w₀, hw₀W1⟩, hw₀ne⟩ := exists_ne (1 : ↥hyp.W1)
  have hw₀ne' : w₀ ≠ 1 := by rintro rfl; exact hw₀ne rfl
  -- `C_C(W₁) = {1}`.
  have hfixset : MulAction.fixedPoints ↥hyp.W1 ↥hyp.C = {1} := by
    ext a
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hafix
      by_contra hane
      have hav : (a : G) ≠ 1 := fun h => hane (Subtype.ext h)
      have hc := congrArg (Subtype.val) (hafix ⟨w₀, hw₀W1⟩)
      rw [hsmul] at hc
      exact hfpf w₀ hw₀W1 hw₀ne' (a : G) a.2 hav hc
    · rintro rfl w
      apply Subtype.ext
      rw [hsmul]; simp
  have hfix : Nat.card ↥(MulAction.fixedPoints ↥hyp.W1 ↥hyp.C) = 1 := by
    rw [hfixset]; simp
  rw [hfix, ← hyp.c_eq_card_C] at hmod
  exact hmod

/-- **Peterfalvi (13.12), `dv_2q_c1`**: `2q ∣ c − 1`.  `c ≡ 1 (mod q)` (`c_modEq_one`) and `c` is
odd (`|C| ∣ |G|`, `|G|` odd), so both `q` and `2` divide `c − 1`; coprimality (`q` odd) gives
`2q ∣ c − 1`.  In the `c > 1` branch this forces `c ≥ 2q + 1`, the lower bound Peterfalvi's numeric
elimination contradicts. -/
theorem Hypothesis.two_mul_q_dvd_c_pred [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : 2 * hyp.q ∣ hyp.c - 1 := by
  have hc1 : 1 ≤ hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hq : hyp.q ∣ hyp.c - 1 := (Nat.modEq_iff_dvd' hc1).mp (hyp.c_modEq_one hG).symm
  have hcodd : ¬ 2 ∣ hyp.c := by
    have hcG : hyp.c ∣ Nat.card G := by
      rw [hyp.c_eq_card_C]; exact Subgroup.card_subgroup_dvd_card _
    have hodd : Nat.card G % 2 = 1 := Nat.odd_iff.mp hG.odd
    intro h2c
    have h2G : (2 : ℕ) ∣ Nat.card G := h2c.trans hcG
    omega
  have h2 : 2 ∣ hyp.c - 1 := by omega
  have hcop : Nat.Coprime 2 hyp.q :=
    (Nat.coprime_primes Nat.prime_two hyp.q_prime).mpr (Ne.symm hyp.q_ne_two)
  exact hcop.mul_dvd_of_dvd_of_dvd h2 hq

/-- **Peterfalvi (13.11)**: the elementary numerical bounds for `m`.

The `q ≥ 7` and `q ≥ 5` bounds are the genuine arithmetic estimates
`m_value_gt_four_fifths` / `m_value_gt_seven_tenths` applied through the now
concrete value `m_eq` (they need only `p ≥ 3`, supplied by `three_le_p`).  The
`q = 3` branch uses `p ≠ q` and oddness to get `p ≥ 5`; its `m`-bound is
`m_value_q_three_gt_49_hundredths`, while the `u/c` bound combines the analytic
inequality (13.10) with `p² ≤ 3^(p-1)`. -/
theorem numeric_bounds_of_analytic_inequality [Finite G]
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 →
        hyp.m > (49 / 100 : ℚ) ∧
          (hyp.u : ℚ) / (hyp.c : ℚ) > (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6)) := by
  refine ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q, fun hq3 => ?_⟩
  have hp5 : 5 ≤ hyp.p := by
    have hp3 := hyp.three_le_p
    have hpne3 : hyp.p ≠ 3 := by
      intro hp3eq
      exact hyp.p_ne_q (hp3eq.trans hq3.symm)
    obtain ⟨k, hk⟩ := hyp.p_odd
    omega
  have hm49 := hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq3 hp5
  rw [hq3] at h1310
  norm_num at h1310
  have hpPow : hyp.p ^ 2 ≤ 3 ^ (hyp.p - 1) :=
    sq_le_three_pow_pred_of_five_le hp5
  have hpPowR : (hyp.p : ℚ) ^ 2 ≤ (3 : ℚ) ^ (hyp.p - 1) := by
    exact_mod_cast hpPow
  have hmval := hyp.m_eq
  rw [hq3] at hmval
  norm_num at hmval
  have hmval' : hyp.m = (1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (hyp.p - 1)) := by
    rw [hmval]
    have hpow : (3 : ℚ) ^ hyp.p = 3 * (3 : ℚ) ^ (hyp.p - 1) := by
      conv_lhs => rw [show hyp.p = (hyp.p - 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    field_simp
    ring
  have hden : (0 : ℚ) < (3 : ℚ) ^ (hyp.p - 1) := by positivity
  have hfrac : (hyp.p : ℚ) ^ 2 / (3 : ℚ) ^ (hyp.p - 1) ≤ 1 := by
    rw [div_le_one hden]
    exact hpPowR
  have hlower : (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6) ≤
      hyp.m * (((hyp.p ^ 2 : ℕ) : ℚ)) / 3 := by
    have hp2pos : 1 ≤ hyp.p ^ 2 := Nat.one_le_pow _ _ hyp.p_prime.pos
    rw [hmval']
    push_cast [Nat.cast_sub hp2pos]
    have hid : ((1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (hyp.p - 1))) *
          (hyp.p : ℚ) ^ 2 / 3 =
        ((hyp.p : ℚ) ^ 2 - (hyp.p : ℚ) ^ 2 / (3 : ℚ) ^ (hyp.p - 1)) / 6 := by
      field_simp [hden.ne']
      ring
    rw [hid]
    linarith [hfrac]
  exact ⟨hm49, lt_of_le_of_lt hlower h1310⟩

/-- **Peterfalvi (13.12), numeric elimination** (04.15 p.85): the (13.10)+(13.2.c) upper bound
`m < q(p^q − 1)/(c · p^(q−1) · (p − 1))`, together with the fixed-point-free lower bound `c ≥ 2q+1`
(with `2q ∣ c − 1`) and the (13.11) lower bounds on `m`, forces `p = 5`, `q = 3`, `c = 7`.

This is the `sorry`-free `ℕ/ℚ`-arithmetic heart of (13.12): `q = 3` via
`caseB_numeric_forces_q_three`; the `q = 3` bound `m < 3(p³−1)/(c p²(p−1))` then eliminates `c ≥ 13`
(`< 49/100`, against (13.11.c)) forcing `c = 7`, eliminates `p ≥ 11` (`< 399/847 < 49/100`) forcing
`p < 11`, and eliminates `p = 7` (the exact value `m = ½ − 1/(2·3^{p−1}) = ½ − 1/1458` exceeds the
bound `171/343`) forcing `p = 5`.  Only the final `p = 5, q = 3, c = 7` structural contradiction
(`PC` normal nilpotent Hall ⊋ `P = S_F`) remains, isolated in `c_eq_one_final_case`. -/
theorem c_eq_one_forces_params {p q c : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hc2q1 : 2 * q + 1 ≤ c) (h2q : 2 * q ∣ c - 1)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hm49 : q = 3 → 5 ≤ p → (49 : ℚ) / 100 < m)
    (hmval : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hbound : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))) :
    p = 5 ∧ q = 3 ∧ c = 7 := by
  -- Basic positivity.
  have hpR : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hq3le : 3 ≤ q := by
    rcases hq.two_le.lt_or_eq with h | h
    · omega
    · exact absurd h.symm hq2
  have hqR : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq3le
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hcpos : 0 < c := by omega
  have hcR : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hcpos
  have hc2q1R : (2 * (q : ℚ) + 1) ≤ (c : ℚ) := by
    have : ((2 * q + 1 : ℕ) : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc2q1
    push_cast at this; linarith
  -- Odd prime `≥ 3` is `3` or `≥ 5`.
  have prime_split : ∀ n : ℕ, n.Prime → 3 ≤ n → n = 3 ∨ 5 ≤ n := by
    intro n hn hn3
    by_contra hcon
    rw [not_or, not_le] at hcon
    obtain ⟨hne, hlt⟩ := hcon
    interval_cases n
    · exact hne rfl
    · exact (by norm_num : ¬ Nat.Prime 4) hn
  have hp35 : p = 3 ∨ 5 ≤ p := prime_split p hp hp3
  have hq35 : q = 3 ∨ 5 ≤ q := prime_split q hq hq3le
  -- `p^q = p^(q-1) · p`.
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  -- Step 1: derive `m < q p / ((2q+1)(p-1))`, hence `q = 3`.
  have hbound2q1 : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
    have hden1 : (0 : ℚ) < (c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1) := by positivity
    have hden2 : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by positivity
    have hstep : (q : ℚ) * ((p : ℚ) ^ q - 1) / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))
        < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
      rw [div_lt_div_iff₀ hden1 hden2, hpexp]
      have hkey : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
          < (c : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by
        have hpp : (0 : ℚ) < (p : ℚ) ^ (q - 1) * (p : ℚ) := by positivity
        have e1 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
            < (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by nlinarith [hqR, hpp]
        have e2 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ))
            ≤ (c : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) :=
          mul_le_mul_of_nonneg_right hc2q1R (le_of_lt hpp)
        linarith [e1, e2]
      have hqp1 : (0 : ℚ) < (q : ℚ) * ((p : ℚ) - 1) := by positivity
      nlinarith [mul_lt_mul_of_pos_left hkey hqp1]
    linarith [hbound, hstep]
  have hq3 : q = 3 := caseB_numeric_forces_q_three hp35 hq35 hm5 hm7 hbound2q1
  -- With `q = 3`, `p ≥ 5`.
  have hp5 : 5 ≤ p := by
    rcases hp35 with h | h
    · exact absurd (h.trans hq3.symm) hpq
    · exact h
  have hpR5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp5
  subst hq3
  -- Specialize the bound to `q = 3`.
  have hbound3 : m < (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1)) := by
    have he : (p : ℚ) ^ (3 - 1) = (p : ℚ) ^ 2 := by norm_num
    have hc3 : ((3 : ℕ) : ℚ) = (3 : ℚ) := by norm_num
    rw [he, hc3] at hbound
    exact hbound
  have hm49p : (49 : ℚ) / 100 < m := hm49 rfl hp5
  -- `c ≡ 1 mod 6`, `c ≥ 7`, so `c = 7 ∨ c ≥ 13`.
  have h6 : 6 ∣ c - 1 := by simpa using h2q
  have hc7or13 : c = 7 ∨ 13 ≤ c := by omega
  -- Kill `c ≥ 13`.
  have hc7 : c = 7 := by
    rcases hc7or13 with h | h
    · exact h
    exfalso
    have hcR13 : (13 : ℚ) ≤ (c : ℚ) := by exact_mod_cast h
    have hden : (0 : ℚ) < (c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1) := by positivity
    have hb13 : (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1))
        < (49 : ℚ) / 100 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      nlinarith [hcR13, hpR5, mul_pos hp0 hp1, mul_pos (mul_pos hp0 hp0) hp1, hp0, hp1,
        sq_nonneg ((p : ℚ) - 5)]
    linarith [hbound3, hb13, hm49p]
  subst hc7
  -- Kill `p ≥ 11`.
  have hp_lt_11 : p < 11 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hpR11 : (11 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hcon
    have hden : (0 : ℚ) < (7 : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1) := by positivity
    have hb11 : (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((7 : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1))
        < (49 : ℚ) / 100 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      nlinarith [hpR11, mul_pos hp0 hp1, mul_pos (mul_pos hp0 hp0) hp1, hp0, hp1]
    linarith [hbound3, hb11, hm49p]
  -- Kill `p = 7` via the exact value of `m`.
  have hp_ne_7 : p ≠ 7 := by
    intro h7
    subst h7
    rw [hmval] at hbound3
    norm_num at hbound3
  -- `5 ≤ p < 11`, prime, `≠ 7` ⇒ `p = 5`.
  refine ⟨?_, rfl, rfl⟩
  interval_cases p
  · rfl
  · exact absurd hp (by norm_num)
  · exact absurd rfl hp_ne_7
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)

/-- **Peterfalvi (13.12), the isolated `PC`-Hall obligation**: for the numerically-forced
`p = 5, q = 3, c = 7`, the subgroup `PC = P ⊔ C` is contained in `M_F = maxNilpotentNormalHall S`.

Peterfalvi's argument: `PC` is **abelian** (hence nilpotent) — `P` is elementary abelian, `C ≤ U` is
abelian, and `C` centralizes `P` (`C_eq`); it is **normal** in `S` (type-`P` `W₁`-structure); and it
is a **Hall** subgroup once `gcd(c, u) = 1`, which holds because case (9.7.b) for `S`
(as `p − 1 = 4`
has no odd divisor `≠ 1`) forces `u ∣ (p^q − 1)/(p − 1) = 31` (Singer / `typeP_Galois`), coprime to
`c = 7`.

The Lean proof follows the same dichotomy.  In Clifford case (a), `a ∣ p − 1 = 4` and oddness of
`a` force `a = 1`; the resulting trivial action on the orbit generator `S₀` contradicts
`caseA_fixed_contradiction`.  In case (b), `CliffordCaseBData.u_dvd_norm_quotient` gives
`u ∣ 31`.  The already-proved normality and commutativity of `H = PC`, together with its card/index
formulas, then give the normal nilpotent Hall subgroup absorbed by `le_maxNilpotentNormalHall`. -/
theorem pc_le_maxNilpotentNormalHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hp5 : hyp.p = 5) (hq3 : hyp.q = 3) (hc7 : hyp.c = 7) :
    hyp.P ⊔ hyp.C ≤ maxNilpotentNormalHall hyp.S :=
  by
  haveI := hyp.finiteG
  change hyp.H ≤ maxNilpotentNormalHall hyp.S
  -- The (9.7) dichotomy: case (a) is impossible for `p - 1 = 4`; case (b) gives `u ∣ 31`.
  have hu_dvd_31 : hyp.u ∣ 31 := by
    obtain ⟨chief, -⟩ :=
      OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
    rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
        (hyp.mkSection11CharacterDataS hG chief) with hA | hB
    · obtain ⟨caseA⟩ := hA
      exfalso
      have ha_dvd_4 : caseA.a ∣ 4 := by
        have h := caseA.a_dvd_p_sub_one
        rw [hyp.chiefFactorS_p_eq hG chief, hp5] at h
        norm_num at h ⊢
        exact h
      have ha_cop_4 : Nat.Coprime caseA.a 4 := by
        have h := (Nat.coprime_two_left.mpr
          (OddOrder.Peterfalvi.S11.caseA_a_odd hG caseA)).symm.pow_right 2
        norm_num at h ⊢
        exact h
      have ha_one : caseA.a = 1 :=
        Nat.eq_one_of_dvd_coprimes ha_cop_4 dvd_rfl ha_dvd_4
      have hrange_card : Nat.card
          ↥(OddOrder.Peterfalvi.S11.aInvariantRestrictAut caseA.S0_aInvariant).range = 1 := by
        rw [← caseA.a_eq_card_restrictAut_range, ha_one]
      have hrange_bot :
          (OddOrder.Peterfalvi.S11.aInvariantRestrictAut caseA.S0_aInvariant).range = ⊥ :=
        Subgroup.card_eq_one.mp hrange_card
      let j0 : Fin (hyp.toTypesIIIIIIVSetupS hG).q :=
        ⟨0, (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos⟩
      have hS0card : Nat.card ↥caseA.S0 = chief.p := by
        have h := caseA.Hpart_order j0
        rwa [caseA.Hpart_orbit j0, card_pointwise_smul] at h
      have hS0ne : caseA.S0 ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hS0card
        exact chief.p_prime.one_lt.ne' hS0card.symm
      refine OddOrder.Peterfalvi.S13.caseA_fixed_contradiction chief hS0ne ?_
      intro v s hs
      have hvRange :
          OddOrder.Peterfalvi.S11.aInvariantRestrictAut caseA.S0_aInvariant v ∈
            (OddOrder.Peterfalvi.S11.aInvariantRestrictAut caseA.S0_aInvariant).range :=
        ⟨v, rfl⟩
      rw [hrange_bot, Subgroup.mem_bot] at hvRange
      have happ := congrArg
        (fun f : MulAut ↥caseA.S0 => f ⟨s, hs⟩) hvRange
      have hval := congrArg Subtype.val happ
      change (OddOrder.Peterfalvi.S11.uActionHom (hyp.toTypesIIIIIIVSetupS hG) chief) v s = s
      exact hval
    · obtain ⟨caseB⟩ := hB
      have h := caseB.u_dvd_norm_quotient
      rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
        hyp.chiefFactorS_p_eq hG chief, hyp.toTypesIIIIIIVSetupS_q_eq hG, hp5, hq3] at h
      norm_num at h ⊢
      exact h
  -- `|H| = 5^3·7` and `[S:H] = 3u`, with `u ∣ 31`, are coprime.
  have hcop_u : Nat.Coprime (5 ^ 3 * 7) hyp.u :=
    (show Nat.Coprime (5 ^ 3 * 7) 31 by norm_num).coprime_dvd_right hu_dvd_31
  have hcop_three : Nat.Coprime (5 ^ 3 * 7) 3 := by norm_num
  have hHcop : Nat.Coprime (Nat.card ↥hyp.H) ((hyp.H.subgroupOf hyp.S).index) := by
    rw [hyp.card_H_eq hG, hyp.H_index_eq_uq hG, hp5, hq3, hc7]
    exact Nat.Coprime.mul_right hcop_u hcop_three
  have hHhall := OddOrder.BG.Ch4.S15.isHallSubgroup_primeFactors_of_coprime_index
    hyp.H_le_S hHcop
  haveI hHcomm : IsMulCommutative ↥(hyp.H.subgroupOf hyp.S) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hyp.H_le_S).symm (hyp.H_mulCommutative hG)
  have hHnil : Group.IsNilpotent ↥(hyp.H.subgroupOf hyp.S) := inferInstance
  exact OddOrder.BG.Ch4.S15.le_maxNilpotentNormalHall hyp.H_le_S
    (H_sharp_subgroupOf_normal hyp) hHnil hHhall

/-- **Peterfalvi (13.12), structural residual**: the numerically-forced case
`p = 5, q = 3, c = 7` is impossible.  By `pc_le_maxNilpotentNormalHall`,
`PC = P ⊔ C ≤ M_F = P` (`P_eq_SF`), so `C ≤ P`; but `|C| = c = 7` cannot divide
`|P| = p^q = 125`.  The preceding theorem discharges the Clifford/Singer Hall obligation;
the remaining `C ≤ P ⟹ 7 ∣ 125` maximality contradiction is discharged here. -/
theorem c_eq_one_final_case [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hp5 : hyp.p = 5) (hq3 : hyp.q = 3) (hc7 : hyp.c = 7) : False := by
  -- `C ≤ P ⊔ C ≤ M_F = P`.
  have hCleP : hyp.C ≤ hyp.P := by
    have h := pc_le_maxNilpotentNormalHall hG hyp hp5 hq3 hc7
    rw [← hyp.P_eq_SF] at h
    exact le_trans le_sup_right h
  -- `|C| = 7`, `|P| = p^q = 125`.
  have hCcard : Nat.card ↥hyp.C = 7 := by rw [← hyp.c_eq_card_C, hc7]
  have hPcard : Nat.card ↥hyp.P = 5 ^ 3 := by
    obtain ⟨_, _, _, hcard, _, _⟩ := basic_structure hG hyp
    rw [hcard, hp5, hq3]
  -- `C ≤ P ⟹ |C| ∣ |P|`, i.e. `7 ∣ 125`, false.
  have hdvd : Nat.card ↥hyp.C ∣ Nat.card ↥hyp.P := by
    have hd := Subgroup.card_subgroup_dvd_card (hyp.C.subgroupOf hyp.P)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleP).toEquiv] at hd
  rw [hCcard, hPcard] at hdvd
  norm_num at hdvd

/-- **The analytic core of Peterfalvi (13.12)** (side-agnostic, pure `ℚ`-arithmetic).

From the `(13.10)` analytic inequality `u/c > m·a^(b−1)/b` and the `(13.2.c)` Singer *upper*
bound `u·(a−1) ≤ a^b − 1`, derive the upper bound `m < b·(a^b−1) / (c·a^(b−1)·(a−1))` that
(with the fixed-point-free lower bound `c ≥ 2b+1`) feeds the finite numeric elimination.

Both the `S`-side `c = 1` finish (`c_eq_one`, `a = p, b = q, u = u, c = c`) and the `T`-side
`d = 1` dual (`a = q, b = p, u = v, c = d`) instantiate this same core; extracted per issue
9013 (案A: generalize the §13 estimate so both sides `cite` it).  Uses only the Singer *upper*
bound, so it is ungated (the `T`-side lower-bound gate of the (13.15) `v`-value is a different
consumer — the ratio inequality — and does not enter here). -/
theorem analytic_singer_m_bound {a b u c : ℕ} {m : ℚ}
    (hbR : (0 : ℚ) < b) (hcR : (0 : ℚ) < c) (haR : (1 : ℚ) < a)
    (hanalytic : (u : ℚ) / c > m * (a : ℚ) ^ (b - 1) / b)
    (hsinger : (u : ℚ) * ((a : ℚ) - 1) ≤ (a : ℚ) ^ b - 1) :
    m < (b : ℚ) * ((a : ℚ) ^ b - 1)
      / ((c : ℚ) * (a : ℚ) ^ (b - 1) * ((a : ℚ) - 1)) := by
  have haR0 : (0 : ℚ) < (a : ℚ) := by linarith
  have hp1R : (0 : ℚ) < (a : ℚ) - 1 := by linarith
  -- From (13.10): `m · a^(b-1) · c < u · b`.
  rw [gt_iff_lt, div_lt_div_iff₀ hbR hcR] at hanalytic
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hanalytic hp1R,
    mul_le_mul_of_nonneg_left hsinger (le_of_lt hbR)]

/-- **Peterfalvi (13.12)**: the centralizer parameter `c` is `1`.

The numeric elimination `c_eq_one_forces_params` — fed the (13.10) analytic inequality
(`analytic_inequality`, `u/c > m p^(q-1)/q`), the (13.2.c) Singer bound (`basic_structure`,
`u ≤ (p^q-1)/(p-1)`), the fixed-point-free lower bound `c ≥ 2q+1` (`two_mul_q_dvd_c_pred`), and the
(13.11) `m`-bounds — forces `p = 5, q = 3, c = 7`, ruled out by the isolated structural residual
`c_eq_one_final_case`. -/
theorem c_eq_one_of_analytic_inequality [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ)) :
    hyp.c = 1 := by
  by_contra hne
  -- `c > 1`; with `2q ∣ c − 1` (`two_mul_q_dvd_c_pred`) this forces `c ≥ 2q + 1`.
  have hc1 : 1 ≤ hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hcgt : 1 < hyp.c := lt_of_le_of_ne hc1 (Ne.symm hne)
  have hc_ge : 2 * hyp.q + 1 ≤ hyp.c := by
    have h2q : 2 * hyp.q ≤ hyp.c - 1 := Nat.le_of_dvd (by omega) (hyp.two_mul_q_dvd_c_pred hG)
    omega
  -- (13.10) analytic inequality: `u/c > m · p^(q-1) / q`.
  have hWcast : ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) = (hyp.p : ℚ) ^ (hyp.q - 1) := by push_cast; ring
  rw [hWcast] at h1310
  -- (13.2.c) Singer bound: `u ≤ (p^q - 1)/(p - 1)`, hence `u · (p-1) ≤ p^q - 1`.
  obtain ⟨_, _, _, _, hu_bound, _⟩ := basic_structure hG hyp
  have hp1nat : 1 ≤ hyp.p := hyp.p_prime.one_le
  have hp0nat : 0 < hyp.p - 1 := by have := hyp.three_le_p; omega
  have hpq1 : 1 ≤ hyp.p ^ hyp.q := Nat.one_le_pow _ _ hyp.p_prime.pos
  have huP : hyp.u * (hyp.p - 1) ≤ hyp.p ^ hyp.q - 1 :=
    (Nat.le_div_iff_mul_le hp0nat).mp hu_bound
  have huPR : (hyp.u : ℚ) * ((hyp.p : ℚ) - 1) ≤ (hyp.p : ℚ) ^ hyp.q - 1 := by
    have h1 : ((hyp.u * (hyp.p - 1) : ℕ) : ℚ) ≤ ((hyp.p ^ hyp.q - 1 : ℕ) : ℚ) := by
      exact_mod_cast huP
    have e1 : ((hyp.u * (hyp.p - 1) : ℕ) : ℚ) = (hyp.u : ℚ) * ((hyp.p : ℚ) - 1) := by
      push_cast [Nat.cast_sub hp1nat]; ring
    have e2 : ((hyp.p ^ hyp.q - 1 : ℕ) : ℚ) = (hyp.p : ℚ) ^ hyp.q - 1 := by
      push_cast [Nat.cast_sub hpq1]; ring
    rw [e1, e2] at h1; exact h1
  -- Positivity, then the side-agnostic analytic core (`analytic_singer_m_bound`) assembles the
  -- abstract bound `m < q(p^q-1)/(c p^(q-1)(p-1))` from (13.10) + the Singer bound.
  have hqR : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hcRpos : (0 : ℚ) < (hyp.c : ℚ) := by exact_mod_cast (show 0 < hyp.c by omega)
  have haR : (1 : ℚ) < (hyp.p : ℚ) := by
    have : (3 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hyp.three_le_p
    linarith
  have hbound := analytic_singer_m_bound hqR hcRpos haR h1310 huPR
  -- Numeric elimination forces `p = 5, q = 3, c = 7`.
  obtain ⟨hp5, hq3, hc7⟩ := c_eq_one_forces_params hyp.p_prime hyp.q_prime hyp.three_le_p
    hyp.q_ne_two hyp.p_ne_q hc_ge (hyp.two_mul_q_dvd_c_pred hG)
    (fun h => hyp.m_gt_seven_tenths_of_five_le_q h)
    (fun h => hyp.m_gt_four_fifths_of_seven_le_q h)
    (fun hq hp => hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq hp)
    hyp.m_eq hbound
  exact c_eq_one_final_case hG hyp hp5 hq3 hc7

/-- **Peterfalvi (13.13)**: if case (9.7.a) holds for `S`, then
`q = 3` and `u = (p - 1)^2 / 4`.

The hypothesis is the genuine §11 `CliffordCaseAData` for the `S`-side chief factor.  Its block
decomposition supplies `u ∣ ((p - 1)/2)^(q - 1)`; (13.10), (13.11), and `c = 1` then feed the
pure elimination `caseA_numeric_parameters`. -/
theorem caseA_parameters_of_analytic_inequality [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief)) :
    hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  have hc1 := c_eq_one_of_analytic_inequality hG hyp h1310
  have hdiv := OddOrder.Peterfalvi.S11.caseA_u_dvd_half_pred_pow hG
    (hyp.mkSection11CharacterDataS hG chief) caseA
  rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
    hyp.chiefFactorS_p_eq hG chief, hyp.toTypesIIIIIIVSetupS_q_eq hG] at hdiv
  have hpeven : 2 ∣ hyp.p - 1 := by
    have h := even_iff_two_dvd.mp
      (OddOrder.Peterfalvi.S11.chiefFactor_p_sub_one_even (chief := chief) hG)
    rwa [hyp.chiefFactorS_p_eq hG chief] at h
  have h1310c := h1310
  rw [hc1] at h1310c
  norm_num at h1310c
  have h1310' : (hyp.u : ℚ) >
      hyp.m * (((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ)) / (hyp.q : ℚ) := by
    have hpowcast : (((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ)) =
        (hyp.p : ℚ) ^ (hyp.q - 1) := by
      push_cast
      ring
    rw [hpowcast]
    exact h1310c
  have h13c : hyp.q = 3 →
      (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6) < (hyp.u : ℚ) := by
    intro hq3
    obtain ⟨_, _, hnum⟩ := numeric_bounds_of_analytic_inequality hyp h1310
    have h := (hnum hq3).2
    rw [hc1] at h
    simpa using h
  exact caseA_numeric_parameters hyp.three_le_p hyp.q_prime hyp.q_ne_two hpeven
    hyp.m_gt_seven_tenths_of_five_le_q h13c h1310' hdiv

/-- **Peterfalvi (14.6), sharp-parameter Sylow noncyclicity for the `S`-side `U`.**
At the (13.13) parameters `q = 3` and `u = (p - 1)² / 4`, for every prime
`r ∣ (p - 1) / 2`, every Sylow `r`-subgroup of Peterfalvi's actual subgroup `U` is noncyclic.

The numeric equality is normalized to `u = ((p - 1) / 2)²`; the §11 block-scalar theorem gives
the result for the `S`-instance `U`, and `Sdata_U_eq` transports it to the named subgroup
`hyp.U`. -/
theorem caseA_sylow_U_not_isCyclic_of_parameters [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hq : hyp.q = 3) (hu : hyp.u = (hyp.p - 1) ^ 2 / 4)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R : Sylow r ↥hyp.U) : ¬ IsCyclic ↥(R : Subgroup ↥hyp.U) := by
  have hpeven : 2 ∣ hyp.p - 1 := by
    have h := even_iff_two_dvd.mp
      (OddOrder.Peterfalvi.S11.chiefFactor_p_sub_one_even (chief := chief) hG)
    rwa [hyp.chiefFactorS_p_eq hG chief] at h
  have hhalfSq : (hyp.p - 1) ^ 2 / 4 = ((hyp.p - 1) / 2) ^ 2 := by
    have hsplit : hyp.p - 1 = 2 * ((hyp.p - 1) / 2) :=
      (Nat.mul_div_cancel' hpeven).symm
    rw [hsplit, mul_pow]
    norm_num
  have hqSharp : (hyp.toTypesIIIIIIVSetupS hG).q = 3 := by
    rw [hyp.toTypesIIIIIIVSetupS_q_eq hG]
    exact hq
  have huSharp : (hyp.mkSection11CharacterDataS hG chief).u =
      ((chief.p - 1) / 2) ^ 2 := by
    rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
      hyp.chiefFactorS_p_eq hG chief, hu, hhalfSq]
  have hrhalf' : r ∣ (chief.p - 1) / 2 := by
    rwa [hyp.chiefFactorS_p_eq hG chief]
  let e : ↥hyp.U ≃* ↥(hyp.toTypesIIIIIIVSetupS hG).U :=
    MulEquiv.subgroupCongr hyp.Sdata_U_eq.symm
  let f : ↥hyp.U →* ↥(hyp.toTypesIIIIIIVSetupS hG).U := e.toMonoidHom
  have hf : Function.Surjective f := e.surjective
  letI : Fact r.Prime := ⟨hr⟩
  let Rsetup : Sylow r ↥(hyp.toTypesIIIIIIVSetupS hG).U :=
    R.mapSurjective hf
  have hRsetup := OddOrder.Peterfalvi.S11.caseA_sylow_U_not_isCyclic_of_sharp_order
    hG (hyp.mkSection11CharacterDataS hG chief) caseA hqSharp huSharp hr hrhalf' Rsetup
  intro hR
  letI : IsCyclic ↥(R : Subgroup ↥hyp.U) := hR
  rw [show (Rsetup : Subgroup ↥(hyp.toTypesIIIIIIVSetupS hG).U) =
    (R : Subgroup ↥hyp.U).map f by rfl] at hRsetup
  exact hRsetup <| isCyclic_of_surjective _
    (f.subgroupMap_surjective (R : Subgroup ↥hyp.U))

/-- **Peterfalvi (14.6), BG Prop. 1.16 witness.**  Let `R₀` be a noncyclic Sylow
`r`-subgroup of the `S`-side complement `U`, where `r ∣ (p - 1) / 2`.  Then some
nonidentity `x ∈ R₀` has `C_P(x) ≠ 1`.

The ambient image `B` of `R₀` is abelian because `U` is abelian, normalizes `P` because
`U ≤ S ≤ N_G(P)`, and has order coprime to `|P| = p^q` because `r < p`.  These are exactly
the hypotheses of BG Prop. 1.16(1). -/
theorem exists_sylow_mem_inf_centralizer_ne_bot_of_not_isCyclic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R : Sylow r ↥hyp.U) (hRnc : ¬ IsCyclic ↥(R : Subgroup ↥hyp.U)) :
    ∃ x ∈ (R : Subgroup ↥hyp.U).map hyp.U.subtype, x ≠ (1 : G) ∧
      hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  let B : Subgroup G := (R : Subgroup ↥hyp.U).map hyp.U.subtype
  have hBU : B ≤ hyp.U := by
    simpa only [B] using (Subgroup.map_subtype_le (R : Subgroup ↥hyp.U))
  have hBnc : ¬ IsCyclic ↥B := by
    intro hBcyc
    exact hRnc ((Subgroup.equivMapOfInjective (R : Subgroup ↥hyp.U) hyp.U.subtype
      hyp.U.subtype_injective).isCyclic.mpr (by simpa only [B] using hBcyc))
  letI : IsMulCommutative ↥B := IsMulCommutative.of_comm fun a b => by
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg (fun z : ↥hyp.U => (z : G)) (hyp.S_U_commutative.is_comm.comm
      (⟨(a : G), hBU a.2⟩ : ↥hyp.U) (⟨(b : G), hBU b.2⟩ : ↥hyp.U))
  have hUS : hyp.U ≤ hyp.S := by
    rw [← hyp.Sdata_U_eq]
    exact hyp.Sdata.U_le.trans (Subgroup.map_subtype_le _)
  have hSP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hBP : B ≤ Subgroup.normalizer (hyp.P : Set G) := hBU.trans (hUS.trans hSP)
  have hrltp : r < hyp.p := by
    have hhalfpos : 0 < (hyp.p - 1) / 2 := by have := hyp.three_le_p; omega
    have hrle : r ≤ (hyp.p - 1) / 2 := Nat.le_of_dvd hhalfpos hrhalf
    omega
  have hrne : r ≠ hyp.p := ne_of_lt hrltp
  letI : Fact r.Prime := ⟨hr⟩
  letI : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
  have hBr : IsPGroup r B := by
    simpa only [B] using R.isPGroup'.map hyp.U.subtype
  have hPp : IsPGroup hyp.p hyp.P :=
    IsPGroup.of_card (hyp.card_P_eq hG hyp.Sdata_W2_eq)
  have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥hyp.P) :=
    IsPGroup.coprime_card_of_ne r hyp.p hrne B hyp.P hBr hPp
  have hpdvd : hyp.p ∣ Nat.card ↥hyp.P := by
    rw [hyp.card_P_eq hG hyp.Sdata_W2_eq]
    exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
  have hPne : hyp.P ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot hyp.P).mp <| by
    exact hyp.p_prime.one_lt.trans_le (Nat.le_of_dvd Nat.card_pos hpdvd)
  simpa only [B] using
    (OddOrder.BG.Ch2.S07.exists_mem_inf_centralizer_ne_bot_of_not_isCyclic
      hBP hBnc hcop hPne)

/-- **Peterfalvi (14.6), sharp-parameter centralizer witness.**  The case-(9.7.a)
block-scalar noncyclicity at the explicit (13.13) parameters supplies the noncyclic Sylow
input to `exists_sylow_mem_inf_centralizer_ne_bot_of_not_isCyclic`. -/
theorem caseA_exists_sylow_mem_inf_centralizer_ne_bot_of_parameters [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hq : hyp.q = 3) (hu : hyp.u = (hyp.p - 1) ^ 2 / 4)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R : Sylow r ↥hyp.U) :
    ∃ x ∈ (R : Subgroup ↥hyp.U).map hyp.U.subtype, x ≠ (1 : G) ∧
      hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  apply exists_sylow_mem_inf_centralizer_ne_bot_of_not_isCyclic hG hyp hr hrhalf R
  exact caseA_sylow_U_not_isCyclic_of_parameters hG hyp caseA hq hu hr hrhalf R

/-- **Peterfalvi (14.6), ambient Sylow carrier.**  If `R₀ ∈ Syl_r(U)` is noncyclic and
`U ≤ K`, then there is `R ∈ Syl_r(K)` containing the image of `R₀`; simultaneously retain the
BG Prop. 1.16 witness `x ∈ R₀#` with `P ∩ C_G(x) ≠ 1`.  Taking `K = H = L_F` is the Sylow
selection used before the center argument in (14.6). -/
theorem exists_sylow_over_U_with_centralizer_witness_of_not_isCyclic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R₀ : Sylow r ↥hyp.U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U))
    (K : Subgroup G) (hUK : hyp.U ≤ K) :
    ∃ R : Sylow r ↥K,
      (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK) ≤ R ∧
        ∃ x ∈ (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype, x ≠ (1 : G) ∧
          hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  obtain ⟨x, hxR₀, hx1, hxP⟩ :=
    exists_sylow_mem_inf_centralizer_ne_bot_of_not_isCyclic hG hyp hr hrhalf R₀ hR₀nc
  have hR₀K : IsPGroup r
      ((R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK)) :=
    R₀.isPGroup'.map (Subgroup.inclusion hUK)
  obtain ⟨R, hR₀R⟩ := hR₀K.exists_le_sylow
  exact ⟨R, hR₀R, x, hxR₀, hx1, hxP⟩

/-- The parity calculation behind **Peterfalvi (13.14)**: if `p` is odd, the
geometric sum of its first `q` powers has the same parity as `q`. -/
private theorem sum_range_pow_mod_two_eq {p q : ℕ} (hpodd : Odd p) :
    (∑ k ∈ Finset.range q, p ^ k) % 2 = q % 2 := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hpow : p ^ q % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow]
      omega

/-- The oddness part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_odd {p q : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.odd_iff, sum_range_pow_mod_two_eq hpodd, Nat.odd_iff.mp hqodd]

/-- The `p ≡ 1 [MOD q]` divisibility part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_dvd_of_modEq_one {p q : ℕ} (hp : p.Prime)
    (hpq : p ≡ 1 [MOD q]) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [← Nat.modEq_zero_iff_dvd]
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD q] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpq
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  exact hterms.trans (by simp [hsum_one])

/-- The coprimality part of **Peterfalvi (13.14)** when `p` is not `1 mod q`. -/
theorem cyclotomic_quotient_coprime_of_not_modEq_one {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.coprime_iff_gcd_eq_one]
  have hpmod : p ≡ 1 [MOD p - 1] := Nat.modEq_sub (le_of_lt hp.one_lt)
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD p - 1] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpmod
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  have hmod : (∑ k ∈ Finset.range q, p ^ k) ≡ q [MOD p - 1] := by
    exact hterms.trans (by rw [hsum_one])
  rw [hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp <|
    hq.coprime_iff_not_dvd.mpr fun hdiv => hpq <| by
      exact ((Nat.modEq_iff_dvd'
        (show 1 ≤ p from le_of_lt hp.one_lt)).mpr hdiv).symm

/-- If `p` is not `1 mod q`, then the prime `q` does not divide the
cyclotomic quotient in **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_not_dvd_self_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ¬ q ∣ (p ^ q - 1) / (p - 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hdiv
  rw [← Nat.geomSum_eq hp.two_le q] at hdiv
  have hsum_zero_nat : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hsum_zero_zmod : (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_pow] using hsum_zero_nat
  have hgeom :
      (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) =
        (p : ZMod q) ^ q - 1 :=
    geom_sum_mul (p : ZMod q) q
  have hp_eq_one : (p : ZMod q) = 1 := by
    have hzero :
        (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) = 0 := by
      rw [hsum_zero_zmod, zero_mul]
    rw [hgeom, ZMod.pow_card] at hzero
    exact sub_eq_zero.mp hzero
  exact hpq ((ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hp_eq_one))

/-- Prime divisors of the cyclotomic quotient in the non-`1 mod q` case are
`1 mod q`. -/
theorem cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q])
    (hr : r.Prime) (hrdvd : r ∣ (p ^ q - 1) / (p - 1)) :
    r ≡ 1 [MOD q] := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hr_ne_q : r ≠ q := by
    intro h
    exact cyclotomic_quotient_not_dvd_self_of_not_modEq_one hp hq hpq
      (by simpa [h] using hrdvd)
  have hr_not_dvd_q : ¬ r ∣ q := by
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hr_eq_one | hr_eq_q
    · exact hr.ne_one hr_eq_one
    · exact hr_ne_q hr_eq_q
  haveI : NeZero (q : ZMod r) :=
    NeZero.of_not_dvd (ZMod r) hr_not_dvd_q
  have hrdvd_sum : r ∣ ∑ k ∈ Finset.range q, p ^ k := by
    simpa [Nat.geomSum_eq hp.two_le q] using hrdvd
  have hroot :
      Polynomial.IsRoot (Polynomial.cyclotomic q (ZMod r))
        (Nat.castRingHom (ZMod r) p) := by
    rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime]
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    simpa [Nat.cast_sum, Nat.cast_pow] using
      (ZMod.natCast_eq_zero_iff (∑ k ∈ Finset.range q, p ^ k) r).mpr hrdvd_sum
  have hcop : p.Coprime r :=
    Polynomial.coprime_of_root_cyclotomic hq.pos hroot
  have hnot_r_dvd_p : ¬ r ∣ p :=
    hr.coprime_iff_not_dvd.mp hcop.symm
  have hp_ne_zero : (p : ZMod r) ≠ 0 := by
    intro hzero
    exact hnot_r_dvd_p ((ZMod.natCast_eq_zero_iff p r).mp hzero)
  have horder_dvd : orderOf (p : ZMod r) ∣ r - 1 :=
    ZMod.orderOf_dvd_card_sub_one hp_ne_zero
  have horder_eq : q = orderOf (p : ZMod r) :=
    (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  rw [← horder_eq] at horder_dvd
  exact ((Nat.modEq_iff_dvd' hr.pos).mpr horder_dvd).symm

/-- If every prime factor of `x` is `1 mod q`, then `x` is `1 mod q`. -/
theorem modEq_one_of_forall_primeFactors_modEq_one {x q : ℕ} (hx : x ≠ 0)
    (h : ∀ r ∈ x.primeFactors, r ≡ 1 [MOD q]) :
    x ≡ 1 [MOD q] := by
  rw [Nat.prod_pow_primeFactors_factorization hx]
  have hprod :
      (∏ r ∈ x.primeFactors, r ^ x.factorization r) ≡
        ∏ r ∈ x.primeFactors, 1 [MOD q] :=
    Nat.ModEq.prod fun r hr => by
      simpa using (h r hr).pow (x.factorization r)
  simpa using hprod

/-- The divisor-congruence part of **Peterfalvi (13.14)** when `p` is not
`1 mod q`. -/
theorem cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q] := by
  intro x hx hxdvd
  refine modEq_one_of_forall_primeFactors_modEq_one hx fun r hrx => ?_
  exact cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one hp hq hpq
    (Nat.prime_of_mem_primeFactors hrx)
    ((Nat.dvd_of_mem_primeFactors hrx).trans hxdvd)

/-- **Peterfalvi (13.14)**: divisibility facts for
`(p^q - 1) / (p - 1)`. -/
theorem cyclotomic_divisor_facts {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) ∧
      (p ≡ 1 [MOD q] → q ∣ (p ^ q - 1) / (p - 1)) ∧
      (¬ (p ≡ 1 [MOD q]) →
        Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ∧
          ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q]) := by
  refine ⟨cyclotomic_quotient_odd hp hpodd hqodd, ?_, ?_⟩
  · exact cyclotomic_quotient_dvd_of_modEq_one hp
  · intro hpq
    exact ⟨cyclotomic_quotient_coprime_of_not_modEq_one hp hq hpq,
      cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one hp hq hpq⟩

/-! ## The `(13.18.a)` `S′−P` vanishing input (`hmuD`)

The second pointwise `μ`-value input of the exact `β`-support
`betaGrid_support_sharpP_union_typePV_of_values` (`S16_NonExistenceG/TGapCross`):
`μ_{0j} = 0` on `S′ − P` (Pf p.83, from (13.3.a) and (13.12)).  The chain: `c = 1` collapses
`H = PC` to `P`, so `μ_j = Ind_P^S θ` (`mu_j_isIndPC`) vanishes off the normal `P`; and off the
`W`-conjugates the `(13.1.e)` induction identity forces all rows of a column to agree, so
`q·μ_{0j}(z) = μ_j(z) = 0` on `S′ − P` (which avoids the `W`-conjugates since
`W ∩ S′ = W₂ ≤ P`). -/

/-- **`C = ⊥` from (13.12)** — the subgroup-level form of the regularity `c = 1`
(Coq `FTtypeP_reg_Fcore`).  The explicit input keeps downstream (13.18) consumers independent of
the legacy character-degree carrier. -/
theorem Hypothesis.C_eq_bot_of_c_eq_one [Finite G] (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) : hyp.C = ⊥ :=
  Subgroup.card_eq_one.mp (by rw [← hyp.c_eq_card_C]; exact hc1)

/-- **`H = P` from (13.12)** — with `C = ⊥` the (13.5) subgroup `H = P C` collapses to `P`. -/
theorem Hypothesis.H_eq_P_of_c_eq_one [Finite G] (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) : hyp.H = hyp.P := by
  show hyp.P ⊔ hyp.C = hyp.P
  rw [hyp.C_eq_bot_of_c_eq_one hc1, sup_bot_eq]

/-- **`q ∤ |S′|` from (13.12)**: `|S′| = p^q·(u·c) = p^q·u`, with `q ∤ p^q`
(`p ≠ q`) and `q ∤ u` (`u ≡ 1 (mod q)`, `u_modEq_one`). -/
theorem Hypothesis.not_q_dvd_card_derived_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    ¬ hyp.q ∣ Nat.card ↥(OddOrder.GroupTheory.derivedInG hyp.S) := by
  rw [hyp.card_deriv_S_eq, hyp.card_P_eq hG hyp.Sdata_W2_eq, hyp.card_U_eq_uc,
    hc1, mul_one]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hyp.q_prime).mp hdvd with h | h
  · exact hyp.p_ne_q ((Nat.prime_dvd_prime_iff_eq hyp.q_prime hyp.p_prime).mp
      (hyp.q_prime.dvd_of_dvd_pow h)).symm
  · have hmod : hyp.u % hyp.q = 1 % hyp.q := hyp.u_modEq_one hG
    obtain ⟨k, hk⟩ := h
    have hq2 : 2 ≤ hyp.q := hyp.q_prime.two_le
    have h1q : 1 % hyp.q = 1 := Nat.one_mod_eq_one.mpr (by omega)
    rw [hk, Nat.mul_mod_right, h1q] at hmod
    omega

/-- **`W₁ ⊓ S′ = ⊥` from (13.12)**: an element of the intersection has order dividing both `q`
and `|S′|`; `q ∤ |S′|` with `q` prime forces order `1`. -/
theorem Hypothesis.W1_inf_derived_eq_bot_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    hyp.W1 ⊓ OddOrder.GroupTheory.derivedInG hyp.S = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hord_q : orderOf x ∣ hyp.q := by
    rw [hyp.q_eq_card_W1]
    have h := orderOf_dvd_natCard (⟨x, hx.1⟩ : ↥hyp.W1)
    rwa [← Subgroup.orderOf_coe] at h
  have hord_D : orderOf x ∣ Nat.card ↥(OddOrder.GroupTheory.derivedInG hyp.S) := by
    have h := orderOf_dvd_natCard
      (⟨x, hx.2⟩ : ↥(OddOrder.GroupTheory.derivedInG hyp.S))
    rwa [← Subgroup.orderOf_coe] at h
  rcases (Nat.dvd_prime hyp.q_prime).mp hord_q with h1 | hq
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (hq ▸ hord_D) (hyp.not_q_dvd_card_derived_of_c_eq_one hG hc1)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`supp(μ_j) ⊆ P`** ((13.3.a)+(13.12), the `seqInd_on` step of Coq `PVSbeta`): the column
sum `μ_j = Ind_{H}^S θ` (`mu_j_isIndPC`) with `H = P` (`H_eq_P`), and `P ◁ S` confines the
induced support to `P` (`support_induce_subset_of_normal`). -/
theorem Hypothesis.mu_colSum_support_subset_P_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1)
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ((∑ i : Fin hyp.q, hyp.mu i j) : ClassFunction ↥hyp.S ℂ).support ⊆
      hyp.H.subgroupOf hyp.S := by
  classical
  obtain ⟨θ, _hθirr, _hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG j hj
  haveI hPnorm : (hyp.H.subgroupOf hyp.S).Normal := by
    rw [hyp.H_eq_P_of_c_eq_one hc1]
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer ?_).mpr ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  letI : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hθeq]
  exact ClassFunction.support_induce_subset_of_normal _ θ

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18.a), the `S′−P` vanishing (`hmuD`)**: `μ_{0j}(z) = 0` for
`z ∈ S′ − P`, `j ≠ 0` (Pf p.83 "`μ_{0j}` vanishes on `S′ − P` by (13.3.a) and (13.12)";
Coq `PVSbeta`, PU-branch).

*Proof.*  Off the `W`-conjugates the `(13.1.e)` induction identity `mu_definition` has vanishing
left side, so all rows of column `j` agree at `z`; `z ∈ S′ − P` is indeed off the
`W`-conjugates, since a conjugate `x⁻¹zx ∈ W` would lie in `W ∩ S′` (`S′` is
conjugation-stable in `S`), and `W ∩ S′ ≤ P` (`W₁ ⊓ S′ = ⊥` splits the cyclic `W = W₁W₂`,
`W₂ ≤ P`), forcing `z ∈ P` (`S ≤ N_G(P)`) — contradiction.  Hence
`q·μ_{0j}(z) = ∑ᵢ μ_{ij}(z) = μ_j(z) = 0` (`mu_colSum_support_subset_P` with `H = P`), and
`q ≠ 0` cancels. -/
theorem Hypothesis.mu_row0_apply_eq_zero_of_mem_derived_not_mem_P_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1)
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩)
    (z : ↥hyp.S) (hzD : (z : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S)
    (hzP : (z : G) ∉ hyp.P) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j z = 0 := by
  classical
  -- `z` avoids the `W`-conjugates.
  have hz_notin : (z : ↥hyp.S) ∉
      ClassFunction.conjugatesInto (hyp.W.subgroupOf hyp.S) := by
    rintro ⟨x, hxzx⟩
    set w : ↥hyp.S := x⁻¹ * z * x with hwdef
    have hwW : (w : G) ∈ hyp.W := Subgroup.mem_subgroupOf.mp hxzx
    have hwD : (w : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S := by
      obtain ⟨z', hz', hzz'⟩ := hzD
      have hz'eq : z' = z := Subtype.ext hzz'
      exact ⟨x⁻¹ * z' * x, by
        simpa using Subgroup.Normal.conj_mem inferInstance z' hz' x⁻¹, by
        rw [hz'eq]; rfl⟩
    haveI := hyp.W_cyclic
    letI : CommGroup ↥hyp.W := IsCyclic.commGroup
    have hW1le : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have hW2le : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have htop : (hyp.W1.subgroupOf hyp.W) ⊔ (hyp.W2.subgroupOf hyp.W) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← hyp.W_eq_join, Subgroup.subgroupOf_self]
    have hmem : (⟨(w : G), hwW⟩ : ↥hyp.W) ∈
        (hyp.W1.subgroupOf hyp.W) ⊔ (hyp.W2.subgroupOf hyp.W) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hmem
    have haW1 : (a : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp ha
    have hbW2 : (b : G) ∈ hyp.W2 := Subgroup.mem_subgroupOf.mp hb
    have habG : (a : G) * (b : G) = (w : G) := by
      have := congrArg (fun t : ↥hyp.W => (t : G)) hab
      simpa using this
    have hPle : hyp.P ≤ OddOrder.GroupTheory.derivedInG hyp.S := by
      rw [hyp.S_deriv_eq_PU]; exact le_sup_left
    have haD : (a : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S := by
      have heq : (a : G) = (w : G) * (b : G)⁻¹ := by rw [← habG]; group
      rw [heq]
      exact Subgroup.mul_mem _ hwD (Subgroup.inv_mem _ (hPle (W2_le_P hG hyp hbW2)))
    have ha1 : (a : G) = 1 := by
      have hmem2 : (a : G) ∈ hyp.W1 ⊓ OddOrder.GroupTheory.derivedInG hyp.S := ⟨haW1, haD⟩
      rwa [hyp.W1_inf_derived_eq_bot_of_c_eq_one hG hc1, Subgroup.mem_bot] at hmem2
    have hwP : (w : G) ∈ hyp.P := by
      rw [← habG, ha1, one_mul]
      exact W2_le_P hG hyp hbW2
    apply hzP
    have hzw : (z : G) = (x : G) * (w : G) * (x : G)⁻¹ := by
      rw [hwdef]; push_cast; group
    rw [hzw]
    have hSnorm : hyp.S ≤ Subgroup.normalizer hyp.P := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    exact (Subgroup.mem_normalizer_iff.mp (hSnorm x.2) _).mp hwP
  -- All rows of column `j` agree at `z`.
  have hall : ∀ i : Fin hyp.q, hyp.mu i j z = hyp.mu ⟨0, hyp.q_prime.pos⟩ j z := by
    intro i
    have hdef := congrArg (fun f : ClassFunction ↥hyp.S ℂ => f z) (hyp.mu_definition i j)
    have hLz : ClassFunction.induce (hyp.W.subgroupOf hyp.S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq hyp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (hyp.omega i j - hyp.omega ⟨0, hyp.q_prime.pos⟩ j)) z = 0 := by
      by_contra h
      exact hz_notin
        (ClassFunction.support_induce_subset_conjugatesInto _ _
          (ClassFunction.mem_support.mpr h))
    simp only [hLz, ClassFunction.smul_apply, ClassFunction.sub_apply] at hdef
    have hδ : (hyp.delta j : ℂ) ≠ 0 := by
      rcases hyp.delta_pm_one.1 j with h | h <;> rw [h] <;> norm_num
    have hsub := (mul_eq_zero.mp hdef.symm).resolve_left hδ
    exact sub_eq_zero.mp hsub
  -- The column sum vanishes at `z` (`supp(μ_j) ⊆ H = P`, `z ∉ P`).
  have hsum : (∑ i : Fin hyp.q, hyp.mu i j) z = 0 := by
    by_contra h
    apply hzP
    have hmem := hyp.mu_colSum_support_subset_P_of_c_eq_one hG hc1 j hj
      (ClassFunction.mem_support.mpr h)
    have hmem' : (z : G) ∈ hyp.H := Subgroup.mem_subgroupOf.mp hmem
    rwa [hyp.H_eq_P_of_c_eq_one hc1] at hmem'
  rw [ClassFunction.finset_sum_apply,
    Finset.sum_congr rfl (fun i _ => hall i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hq0 : (hyp.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne'
  exact (mul_eq_zero.mp hsum).resolve_left hq0

end OddOrder.Peterfalvi.S15
