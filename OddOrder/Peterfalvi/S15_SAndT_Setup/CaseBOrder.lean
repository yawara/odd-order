import OddOrder.Peterfalvi.S15_SAndT_Setup.OrderDetermination

/-!
# Peterfalvi (13.15), case-(b) order determination

This file isolates the **`ℕ/ℚ`-arithmetic heart of Peterfalvi (13.15)** — the order determination in
case (9.7.b) — as a side-agnostic engine, mirroring the `(13.12)` engine
`OddOrder.Peterfalvi.S15.c_eq_one_forces_params`.

Peterfalvi (13.15) (04.15 p. 86) states that if case (9.7.b) holds for a type-II maximal subgroup
`M`, then the complement order is the Singer cyclotomic value:
`u = (p^q − 1)/(p − 1)` if `p ≢ 1 (mod q)`, or `u = (p^q − 1)/(q(p − 1))` if `p ≡ 1 (mod q)`.
Peterfalvi states it for `M = S` but *applies it to both `S` and `T`* (04.16 p. 87, deriving
`v = (q^p − 1)/(q − 1)` "by (13.15)"), so the arithmetic is genuinely side-symmetric.

Its proof introduces the cofactor `x` with `u·x = (p^q − 1)/(p − 1)` and shows `x = 1` (resp.
`x = q`)
by ruling out `x ≥ 2q + 1` via the analytic inequality (13.10)+(13.12) and the (13.11) lower bounds
on `m`, exactly as in the `(13.12)` `c`-elimination — **except** that the endgame is purely numeric
(`x ∣ (p² + p + 1) ∈ {31, 57}` with `x ≥ 7` and `u ≠ 1` prime-to-`3`), with *no* structural residual
(contrast `(13.12)`, whose `p = 5, q = 3, c = 7` case bottoms out in the `typeP_Galois`-gated
`pc_le_maxNilpotentNormalHall`).

The genuinely deep character/`σ`-theory content — the value of `m` (Peterfalvi (13.9)) and the
analytic inequality (13.10) with `c = 1`/`d = 1` (which itself needs (13.12), `typeP_Galois`-gated,
issue 9000) — enters this engine **only as explicit hypotheses** (`hmval`-free here; `hanalytic`,
the `m`-lower bounds, `h11c`). Thus this engine is *ungated*: the caller (the `S`-side
`caseB_order_u`
or the `T`-side `v`-value) supplies those char inputs, which bottom out in `typeP_Galois` (issue
9000).
-/

namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

/-- `(p³ − 1)/(p − 1) = p² + p + 1` over `ℕ` (the geometric-sum identity for `q = 3`). -/
theorem cyclotomic_quotient_three {p : ℕ} (hp : 2 ≤ p) :
    (p ^ 3 - 1) / (p - 1) = p ^ 2 + p + 1 := by
  rw [← Nat.geomSum_eq hp 3, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  ring

/-- **Peterfalvi (13.15), the `x ≥ 2q + 1` elimination** (side-agnostic numeric engine).

If the cofactor `x` (with `u·x = (p^q − 1)/(p − 1)`) satisfies `x ≥ 2q + 1`, the analytic inequality
`hanalytic` (from (13.10)+(13.12): `m < q(p^q − 1) / (p^{q−1} · x · (p − 1))`) together with the
(13.11) lower bounds on `m` and the (13.11.c) bound `(p² − 1)/6 < u` are contradictory.

Mirrors `c_eq_one_forces_params`: the `q = 3` reduction (via `caseB_numeric_forces_q_three`) and the
`m < qp/((2q+1)(p−1))` step are identical (with `x` in place of `c`); the endgame differs — here
`p² − 6p − 13 < 0` forces `p ∈ {5, 7}`, and `x ∣ (p² + p + 1) ∈ {31, 57}` with `x ≥ 7`, `u ≠ 1`,
`q ∤ u` is impossible.  All char/`σ`-theory content is supplied by the caller as the hypotheses
`hanalytic`, `hm5`, `hm7`, `h11c`, `hu_cop_q` (⟵ (13.14)). -/
theorem caseB_order_x_absurd_of_ge {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hx : 2 * q + 1 ≤ x)
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    False := by
  -- Positivity / prime facts (mirroring `c_eq_one_forces_params`).
  have hpR : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hq3le : 3 ≤ q := by
    rcases hq.two_le.lt_or_eq with h | h
    · omega
    · exact absurd h.symm hq2
  have hqR : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq3le
  have hq0 : (0 : ℚ) < (q : ℚ) := by linarith
  have hx2q1R : (2 * (q : ℚ) + 1) ≤ (x : ℚ) := by
    have h : ((2 * q + 1 : ℕ) : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
    push_cast at h; linarith
  have hxR : (0 : ℚ) < (x : ℚ) := by linarith
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
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  -- Step 1: `m < qp/((2q+1)(p-1))`, hence `q = 3` (identical to `c_eq_one_forces_params`, `x` for
  -- `c`).
  have hbound2q1 : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
    have hden1 : (0 : ℚ) < (p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1) := by positivity
    have hden2 : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by positivity
    have hstep : (q : ℚ) * ((p : ℚ) ^ q - 1) / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))
        < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
      rw [div_lt_div_iff₀ hden1 hden2, hpexp]
      have hpp : (0 : ℚ) < (p : ℚ) ^ (q - 1) * (p : ℚ) := by positivity
      have hkey : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
          < (x : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by
        have e1 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
            < (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by nlinarith [hqR, hpp]
        have e2 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ))
            ≤ (x : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) :=
          mul_le_mul_of_nonneg_right hx2q1R (le_of_lt hpp)
        linarith [e1, e2]
      have hqp1 : (0 : ℚ) < (q : ℚ) * ((p : ℚ) - 1) := by positivity
      nlinarith [mul_lt_mul_of_pos_left hkey hqp1]
    linarith [hanalytic, hstep]
  have hq3 : q = 3 := caseB_numeric_forces_q_three hp35 hq35 hm5 hm7 hbound2q1
  have hp5 : 5 ≤ p := by
    rcases hp35 with h | h
    · exact absurd (h.trans hq3.symm) hpq
    · exact h
  subst hq3
  -- `q = 3`: `u·x = p² + p + 1`, `x ≥ 7`, so `x ∣ p² + p + 1` and `7u ≤ p² + p + 1`.
  have hval : (p ^ 3 - 1) / (p - 1) = p ^ 2 + p + 1 := cyclotomic_quotient_three hp.two_le
  rw [hval] at hux
  have hx7 : 7 ≤ x := by omega
  have hu_le7 : 7 * u ≤ p ^ 2 + p + 1 := by
    have h : 7 * u ≤ x * u := by gcongr
    rw [mul_comm x u, hux] at h
    exact h
  -- (13.11.c): `(p² − 1)/6 < u`; with `7u ≤ p² + p + 1` this forces `p ∈ {5, 7}`.
  have hu_le7R : (7 : ℚ) * (u : ℚ) ≤ (p : ℚ) ^ 2 + (p : ℚ) + 1 := by
    have h : ((7 * u : ℕ) : ℚ) ≤ ((p ^ 2 + p + 1 : ℕ) : ℚ) := by exact_mod_cast hu_le7
    push_cast at h; linarith
  have hp_lt_8 : p < 8 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hpR8 : (8 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hcon
    have h6u : (p : ℚ) ^ 2 - 1 < 6 * (u : ℚ) := by
      have h := h11c rfl
      rw [div_lt_iff₀ (by norm_num : (0 : ℚ) < 6)] at h
      linarith
    have hprod : (0 : ℚ) ≤ ((p : ℚ) - 8) * ((p : ℚ) + 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h6u, hu_le7R, hprod]
  -- `5 ≤ p < 8`, prime ⟹ `p = 5 ∨ p = 7`, and each is impossible.
  interval_cases p
  · -- `p = 5`: `u·x = 31` (prime), `7u ≤ 31 ⟹ u ≤ 4`, `u ∣ 31` ⟹ `u = 1`, contra `hu_ne_one`.
    norm_num at hux hu_le7
    have hu4 : u ≤ 4 := by omega
    interval_cases u <;> omega
  · exact absurd hp (by norm_num)
  · -- `p = 7`: `u·x = 57 = 3·19`, `7u ≤ 57 ⟹ u ≤ 8`; `u ∈ {1, 3}` excluded (`hu_ne_one`, `q ∤ u`).
    norm_num at hux hu_le7
    have hu8 : u ≤ 8 := by omega
    interval_cases u <;> omega

/-- **Peterfalvi (13.15), the non-`1 mod q` branch** (side-agnostic): in case (9.7.b), if
`p ≢ 1 (mod q)` then the complement has the *full* Singer cyclotomic order `u = (p^q − 1)/(p − 1)`.

The cofactor `x` (with `u·x = (p^q − 1)/(p − 1)`) satisfies `x ≡ 1 (mod q)` by the (13.14)
divisor-congruence `cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one` and is odd (it divides the
odd cyclotomic quotient, `cyclotomic_quotient_odd`); with `q` odd these force `x = 1` or
`x ≥ 2q + 1`,
and the latter is ruled out by `caseB_order_x_absurd_of_ge`. Hence `x = 1` and
`u = (p^q − 1)/(p − 1)`.

The `T`-side `v`-value `v = (q^p − 1)/(q − 1)` of Peterfalvi (14.4) is the instance with the roles
of
`p, q` swapped and `q ≢ 1 (mod p)` (04.16 p. 87).  The char/`σ`-theory inputs `hanalytic`, `hm5`,
`hm7`, `h11c` are supplied by the caller (they bottom out in the analytic inequality (13.10) with
`c = 1`/`d = 1`, i.e. `typeP_Galois`, issue 9000). -/
theorem caseB_order_u_full_of_not_modEq {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (hnotmod : ¬ p ≡ 1 [MOD q])
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u) (hx0 : x ≠ 0)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    u = (p ^ q - 1) / (p - 1) := by
  have hx1 : x = 1 := by
    by_contra hxne1
    -- `x ∣ (p^q-1)/(p-1)` is odd and `≡ 1 (mod q)`; with `q` odd, `x ≠ 1 ⟹ x ≥ 2q+1`.
    have hvalodd : Odd ((p ^ q - 1) / (p - 1)) := cyclotomic_quotient_odd hp hpodd hqodd
    have hxdvd : x ∣ (p ^ q - 1) / (p - 1) := ⟨u, by rw [← hux]; ring⟩
    have hxmod : x ≡ 1 [MOD q] :=
      cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one hp hq hnotmod x hx0 hxdvd
    have hxodd : Odd x := by
      rcases Nat.even_or_odd x with he | ho
      · exact absurd (even_iff_two_dvd.mpr (he.two_dvd.trans hxdvd))
          (Nat.not_even_iff_odd.mpr hvalodd)
      · exact ho
    have hx1le : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hx1le).mp hxmod.symm  -- `x - 1 = q * k`
    have hxk : x = q * k + 1 := by omega
    have hk_ne : k ≠ 0 := by
      intro h0; rw [h0, Nat.mul_zero] at hk; omega
    have hk_even : Even k := by
      rcases Nat.even_or_odd k with he | ho
      · exact he
      · exact absurd (show Even x by rw [hxk]; exact (hqodd.mul ho).add_one)
          (Nat.not_even_iff_odd.mpr hxodd)
    obtain ⟨j, hj⟩ := hk_even
    have hk2 : 2 ≤ k := by omega
    have hx_ge : 2 * q + 1 ≤ x := by
      have hqk : 2 * q ≤ q * k := by
        calc 2 * q = q * 2 := by ring
          _ ≤ q * k := by gcongr
      rw [hxk]; omega
    exact caseB_order_x_absurd_of_ge hp hq hp3 hq2 hpq hx_ge hux hu_ne_one hu_cop_q
      hm5 hm7 h11c hanalytic
  rw [hx1, mul_one] at hux
  exact hux

/-- **Peterfalvi (13.15), the `p ≡ 1 (mod q)` branch** (side-agnostic): in case (9.7.b), if
`p ≡ 1 (mod q)` then the complement order is `u = (p^q − 1)/(q(p − 1))`.

The cofactor `x` (with `u·x = (p^q − 1)/(p − 1)`) is divisible by `q`: by (13.14)
`cyclotomic_quotient_dvd_of_modEq_one`, `q ∣ (p^q − 1)/(p − 1) = u·x`, and `q ∤ u` (coprimality)
forces `q ∣ x`.  Writing `x = q·t`, oddness of `x` (it divides the odd cyclotomic quotient) forces
`t` odd; with `t ≠ 1` this gives `t ≥ 3`, i.e. `x ≥ 3q ≥ 2q + 1`, ruled out by
`caseB_order_x_absurd_of_ge`.  Hence `x = q` and `u = (p^q − 1)/(q(p − 1))`. -/
theorem caseB_order_u_div_q_of_modEq {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (hmod : p ≡ 1 [MOD q])
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u) (_hx0 : x ≠ 0)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    u = (p ^ q - 1) / (q * (p - 1)) := by
  have hqpos : 0 < q := hq.pos
  have hxq : x = q := by
    by_contra hxne
    have hqdvd_val : q ∣ (p ^ q - 1) / (p - 1) := cyclotomic_quotient_dvd_of_modEq_one hp hmod
    have hvalodd : Odd ((p ^ q - 1) / (p - 1)) := cyclotomic_quotient_odd hp hpodd hqodd
    have hxdvd : x ∣ (p ^ q - 1) / (p - 1) := ⟨u, by rw [← hux]; ring⟩
    have hcop : Nat.Coprime q u := hq.coprime_iff_not_dvd.mpr hu_cop_q
    have hqx : q ∣ x := hcop.dvd_of_dvd_mul_left (by rw [hux]; exact hqdvd_val)
    obtain ⟨t, ht⟩ := hqx  -- `x = q * t`
    have hxodd : Odd x := by
      rcases Nat.even_or_odd x with he | ho
      · exact absurd (even_iff_two_dvd.mpr (he.two_dvd.trans hxdvd))
          (Nat.not_even_iff_odd.mpr hvalodd)
      · exact ho
    have htodd : Odd t := by
      rcases Nat.even_or_odd t with he | ho
      · exact absurd (show Even x by rw [ht]; exact Nat.even_mul.mpr (Or.inr he))
          (Nat.not_even_iff_odd.mpr hxodd)
      · exact ho
    have ht_ne : t ≠ 1 := fun h1 => hxne (by rw [ht, h1, Nat.mul_one])
    have ht3 : 3 ≤ t := by obtain ⟨s, hs⟩ := htodd; omega
    have hx_ge : 2 * q + 1 ≤ x := by
      have h3q : 3 * q ≤ q * t := by
        calc 3 * q = q * 3 := by ring
          _ ≤ q * t := by gcongr
      rw [ht]; omega
    exact caseB_order_x_absurd_of_ge hp hq hp3 hq2 hpq hx_ge hux hu_ne_one hu_cop_q
      hm5 hm7 h11c hanalytic
  rw [hxq] at hux  -- `hux : u * q = (p^q - 1)/(p - 1)`
  have hval : u = (p ^ q - 1) / (p - 1) / q := by
    rw [← hux, Nat.mul_comm u q, Nat.mul_div_cancel_left u hqpos]
  rw [hval, Nat.div_div_eq_div_mul, Nat.mul_comm (p - 1) q]

/-- **Peterfalvi (13.15)** (side-agnostic numeric engine, assembled dichotomy): in case (9.7.b),
the complement order `u` is the Singer cyclotomic value
`u = (p^q − 1)/(p − 1)` when `p ≢ 1 (mod q)`, or `u = (p^q − 1)/(q(p − 1))` when `p ≡ 1 (mod q)`.

This packages the two branches `caseB_order_u_div_q_of_modEq` (the `p ≡ 1 (mod q)` case) and
`caseB_order_u_full_of_not_modEq` (the `p ≢ 1 (mod q)` case) into the exact conjunction shape of the
`S`-side statement `S15.caseB_order_u`: once the char/`σ`-theory inputs (`hanalytic`, the (13.11)
`m`-lower bounds, `h11c`) are supplied for the concrete `Hypothesis` data — which bottom out in the
analytic inequality (13.10) with `c = 1`/`d = 1`, i.e. `typeP_Galois`, issue 9000 — this engine
discharges `caseB_order_u` by instantiation, and the `T`-side `v`-value `v = (q^p − 1)/(q − 1)` of
(14.4) is the `p ↔ q` instance.  The engine itself is *ungated* (all char content is hypotheses). -/
theorem caseB_order_u_value {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q)
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u) (hx0 : x ≠ 0)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    (p ≡ 1 [MOD q] → u = (p ^ q - 1) / (q * (p - 1))) ∧
      (¬ p ≡ 1 [MOD q] → u = (p ^ q - 1) / (p - 1)) :=
  ⟨fun hmod => caseB_order_u_div_q_of_modEq hp hq hp3 hq2 hpq hpodd hqodd hmod hux
      hu_ne_one hu_cop_q hx0 hm5 hm7 h11c hanalytic,
    fun hnotmod => caseB_order_u_full_of_not_modEq hp hq hp3 hq2 hpq hpodd hqodd hnotmod hux
      hu_ne_one hu_cop_q hx0 hm5 hm7 h11c hanalytic⟩

/-- **Peterfalvi (13.15)**: if the genuine Clifford case (9.7.b) holds for `S`, then `u` has
the final Singer cyclotomic order, with the extra factor `q` precisely in the `p ≡ 1 (mod q)`
branch.

The case-(b) certificate supplies `u ∣ (p^q - 1)/(p - 1)`, hence a cofactor `x`.  The remaining
inputs of `caseB_order_u_value` are the already-proved (13.10)--(13.14) facts: `c = 1`, the lower
bounds for `m`, `u ≡ 1 (mod q)`, and the oddness of the cyclotomic quotient. -/
theorem caseB_order_u_of_analytic_inequality [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief)) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  have hc1 := c_eq_one_of_analytic_inequality hG hyp h1310
  have hdiv := caseB.u_dvd_norm_quotient
  rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
    hyp.chiefFactorS_p_eq hG chief, hyp.toTypesIIIIIIVSetupS_q_eq hG] at hdiv
  obtain ⟨x, hx⟩ := hdiv
  have hux : hyp.u * x = (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := hx.symm
  have hu_ne_one : hyp.u ≠ 1 := by
    intro hu1
    have hUcard : Nat.card ↥hyp.U = 1 := by
      rw [hyp.card_U_eq_uc, hu1, hc1]
    have hUne : hyp.U ≠ ⊥ := by
      rw [← hyp.Sdata_U_eq]
      exact (hyp.toTypesIIIIIIVSetupS hG).nontrivial.1
    exact hUne (Subgroup.card_eq_one.mp hUcard)
  have hu_cop_q : ¬ hyp.q ∣ hyp.u := by
    intro hqu
    have hmod : hyp.u % hyp.q = 1 % hyp.q := hyp.u_modEq_one hG
    obtain ⟨k, hk⟩ := hqu
    have hq2 : 2 ≤ hyp.q := hyp.q_prime.two_le
    have h1q : 1 % hyp.q = 1 := Nat.one_mod_eq_one.mpr (by omega)
    rw [hk, Nat.mul_mod_right, h1q] at hmod
    omega
  have hvalodd : Odd ((hyp.p ^ hyp.q - 1) / (hyp.p - 1)) :=
    cyclotomic_quotient_odd hyp.p_prime hyp.p_odd hyp.q_odd
  have hx0 : x ≠ 0 := by
    intro hx0
    have hzero : (hyp.p ^ hyp.q - 1) / (hyp.p - 1) = 0 := by
      rw [← hux, hx0, mul_zero]
    rw [hzero] at hvalodd
    obtain ⟨k, hk⟩ := hvalodd
    omega
  have h11c : hyp.q = 3 →
      ((hyp.p : ℚ) ^ 2 - 1) / 6 < (hyp.u : ℚ) := by
    intro hq3
    have h := ((numeric_bounds_of_analytic_inequality hyp h1310).2.2 hq3).2
    rw [hc1] at h
    norm_num at h
    have hp2one : 1 ≤ hyp.p ^ 2 := Nat.one_le_pow _ _ hyp.p_prime.pos
    push_cast [Nat.cast_sub hp2one] at h
    exact h
  rw [hc1] at h1310
  norm_num at h1310
  have hp1 : 1 ≤ hyp.p := hyp.p_prime.one_le
  have hpq1 : 1 ≤ hyp.p ^ hyp.q := Nat.one_le_pow _ _ hyp.p_prime.pos
  have hpred_dvd : hyp.p - 1 ∣ hyp.p ^ hyp.q - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.p 1 hyp.q
  have hquotient_mul :
      (hyp.p ^ hyp.q - 1) / (hyp.p - 1) * (hyp.p - 1) = hyp.p ^ hyp.q - 1 :=
    Nat.div_mul_cancel hpred_dvd
  have hquotient_mulQ :
      (((hyp.p ^ hyp.q - 1) / (hyp.p - 1) : ℕ) : ℚ) * ((hyp.p : ℚ) - 1) =
        (hyp.p : ℚ) ^ hyp.q - 1 := by
    have h := congrArg (Nat.cast (R := ℚ)) hquotient_mul
    push_cast [Nat.cast_sub hp1, Nat.cast_sub hpq1] at h
    convert h using 1
  have huxQ : (hyp.u : ℚ) * (x : ℚ) =
      (((hyp.p ^ hyp.q - 1) / (hyp.p - 1) : ℕ) : ℚ) := by
    exact_mod_cast hux
  have hproduct :
      (hyp.u : ℚ) * (x : ℚ) * ((hyp.p : ℚ) - 1) =
        (hyp.p : ℚ) ^ hyp.q - 1 := by
    rw [huxQ]
    exact hquotient_mulQ
  have hqR : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hp1R : (0 : ℚ) < (hyp.p : ℚ) - 1 := by
    have hp2R : (2 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hyp.p_prime.two_le
    linarith
  have hxR : (0 : ℚ) < (x : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hx0
  rw [div_lt_iff₀ hqR] at h1310
  have hanalytic : hyp.m < (hyp.q : ℚ) * ((hyp.p : ℚ) ^ hyp.q - 1) /
      ((hyp.p : ℚ) ^ (hyp.q - 1) * (x : ℚ) * ((hyp.p : ℚ) - 1)) := by
    have hden : (0 : ℚ) <
        (hyp.p : ℚ) ^ (hyp.q - 1) * (x : ℚ) * ((hyp.p : ℚ) - 1) := by positivity
    rw [lt_div_iff₀ hden]
    have hscale := mul_lt_mul_of_pos_right h1310 (mul_pos hxR hp1R)
    nlinarith [hproduct]
  exact caseB_order_u_value hyp.p_prime hyp.q_prime hyp.three_le_p hyp.q_ne_two hyp.p_ne_q
    hyp.p_odd hyp.q_odd hux hu_ne_one hu_cop_q hx0
    hyp.m_gt_seven_tenths_of_five_le_q hyp.m_gt_four_fifths_of_seven_le_q h11c hanalytic

end OddOrder.Peterfalvi.S15
