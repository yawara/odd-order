import OddOrder.Peterfalvi.S15_SAndT_Setup.Canonicalization

/-!
# Peterfalvi §13 — reusable norm and arithmetic estimates

The carrier-independent pieces of the (13.5)–(13.10) norm cascade: the elementary `T`-side
order bound, Galois/AM–GM lower bounds on cyclic-closed sets, and the rational arithmetic
endpoint of (13.10).  The former monolithic `CharacterDegreeData` cascade has been retired;
its honest replacement supplies these lemmas with explicit Core data.
-/
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`2v ≤ |Q| − 1`** — the `T`-side mirror of `two_mul_u_le`: from the (13.4) value
`v = (q^p − 1)/(q − 1)` and `q ≥ 3`, so `v ≤ (q^p−1)/2`. -/
theorem Hypothesis.two_mul_v_le (hyp : Hypothesis (G := G))
    (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    2 * hyp.v ≤ hyp.q ^ hyp.p - 1 := by
  have hq3 := hyp.three_le_q
  have h1 : (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ≤ (hyp.q ^ hyp.p - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : (hyp.q ^ hyp.p - 1) / 2 * 2 ≤ hyp.q ^ hyp.p - 1 := Nat.div_mul_le_self _ _
  omega

/-- **AM–GM via `log`** (analytic core of [Is] Lemma 3.14): for positive reals whose product is
`≥ 1`, the sum is at least the count.  This powers Peterfalvi (13.9.b): for a cyclic-equivalence
class `[a] = {a^k : gcd(k, |⟨a⟩|) = 1}`, the values `χ(a^k)` are the Galois conjugates of `χ(a)`,
so `∏_k |χ(a^k)|² = |N(χ(a))|² ≥ 1` whenever `χ(a) ≠ 0` (the field norm of a nonzero algebraic
integer is a nonzero rational integer), whence `∑_k |χ(a^k)|² ≥ φ(|⟨a⟩|) = |[a]|`; summing over the
cyclic classes gives `∑_{x∈A}|χ(x)|² ≥ |A|` for any cyclic-closed `A` with `χ ≠ 0` on `A`.
Proof: `log x ≤ x − 1` summed gives `0 ≤ log (∏ f) ≤ ∑ (f − 1) = ∑ f − |s|`. -/
theorem sum_ge_card_of_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < f i) (hprod : 1 ≤ ∏ i ∈ s, f i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, f i := by
  have hlog : ∑ i ∈ s, Real.log (f i) ≤ ∑ i ∈ s, (f i - 1) :=
    Finset.sum_le_sum (fun i hi => Real.log_le_sub_one_of_pos (hpos i hi))
  have hprodlog : (0 : ℝ) ≤ ∑ i ∈ s, Real.log (f i) := by
    rw [← Real.log_prod (fun i hi => (hpos i hi).ne')]
    exact Real.log_nonneg hprod
  have hsum : (0 : ℝ) ≤ ∑ i ∈ s, (f i - 1) := le_trans hprodlog hlog
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  linarith

/-- **[Isaacs] Lemma 3.14 (sum form, virtual characters)**: a virtual character nowhere zero on
a cyclic-closed `Finset A` has `∑_{x∈A}‖φ(x)‖² ≥ |A|` — the `ℤ[Irr]` extension of
`sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed`, combining the Galois product bound
`one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed` with the AM–GM
`sum_ge_card_of_one_le_prod`. -/
theorem sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed {H : Type*} [Group H] [Finite H]
    {φ : ClassFunction H ℂ} (hφ : φ ∈ ZIrr H) {A : Finset H}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card H) → x ^ k ∈ A)
    (hne : ∀ x ∈ A, φ x ≠ 0) :
    (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
  sum_ge_card_of_one_le_prod A (fun x => ‖φ x‖ ^ 2)
    (fun x hx => pow_pos (norm_pos_iff.mpr (hne x hx)) 2)
    (OddOrder.Algebra.one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed hφ hclosed hne)

/-- **The nonvanishing locus of a virtual character inside a cyclic-closed set is cyclic-closed**
(Peterfalvi (1.9.b)): for `k` coprime to `|G|` there is `σ : ℂ ≃+* ℂ` with
`σ(φ(x)) = φ(x^k)` (`exists_complexRingEquiv_mapRingEquiv_eq_pow` with `a = |G|`, `b = 1`),
and ring automorphisms preserve nonvanishing. -/
theorem filter_ne_zero_cyclicClosed [Finite G] {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {A : Finset G} (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A) :
    ∀ x ∈ A.filter (fun y => φ y ≠ 0), ∀ k : ℕ, k.Coprime (Nat.card G) →
      x ^ k ∈ A.filter (fun y => φ y ≠ 0) := by
  classical
  intro x hx k hk
  obtain ⟨hxA, hxne⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hclosed x hxA k hk, ?_⟩
  obtain ⟨σ, hσ⟩ := OddOrder.RepresentationTheory.exists_complexRingEquiv_mapRingEquiv_eq_pow G
    (a := Nat.card G) (b := 1) (mul_one _).symm (Nat.coprime_one_right _) hk
  have hval : ClassFunction.mapRingEquiv σ φ x = φ (x ^ k) :=
    (hσ hφ x).1 (orderOf_dvd_natCard x)
  rw [ClassFunction.mapRingEquiv_apply] at hval
  rw [← hval]
  simpa using hxne

/-- **Peterfalvi (13.9.b) core** ([Is] Lemma 3.14, sum form): for a character `φ` that is nowhere
zero on a cyclic-closed `Finset A`, the squared-norm sum over `A` is at least `|A|`. -/
theorem sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed
    {H : Type*} [Group H] [Finite H]
    {φ : ClassFunction H ℂ} (hφ : OddOrder.RepresentationTheory.IsCharacter φ) {A : Finset H}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card H) → x ^ k ∈ A)
    (hne : ∀ x ∈ A, φ x ≠ 0) :
    (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
  sum_ge_card_of_one_le_prod A (fun x => ‖φ x‖ ^ 2)
    (fun x hx => pow_pos (norm_pos_iff.mpr (hne x hx)) 2)
    (OddOrder.Algebra.one_le_prod_normSq_character_of_cyclicClosed hφ hclosed hne)

/-- **Peterfalvi (13.10), arithmetic core** (04.15 pp.85–86): the (13.6)–(13.9) norm estimates,
the disjoint-union counting identity, and the (13.4) counting values force
`u / c > m p^(q-1) / q`.  All character-theoretic inputs are explicit hypotheses. -/
theorem analytic_inequality_arith {p q u c : ℕ} {m gi slam seta g0 LS HS TT QT : ℚ}
    (hp2 : 2 ≤ p) (hq2 : 2 ≤ q) (hc0 : 0 < c)
    (h1 : 1 ≥ gi + slam + 1 - LS)
    (h2 : 1 ≥ gi + seta + HS + TT)
    (h3 : 1 = gi + g0 + HS + QT)
    (h139b : g0 ≤ slam + seta)
    (hgi : 0 < gi)
    (hLS : LS = ((u : ℚ) * (q : ℚ)) / ((c : ℚ) * (p : ℚ) ^ q))
    (hTT : TT = 1 / (p : ℚ) - 1 / ((p : ℚ) * ((q : ℚ) - 1))
      + 1 / ((p : ℚ) * ((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hQT : QT = ((q : ℚ) - 1) / ((p : ℚ) * (q : ℚ) ^ p))
    (hm : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)) :
    (u : ℚ) / (c : ℚ) > m * ((p : ℚ) ^ (q - 1)) / (q : ℚ) := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show 0 < q by omega)
  have hcQ : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc0
  have hq1 : (0 : ℚ) < (q : ℚ) - 1 := by
    have h2q : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq2
    linarith
  have hqpowp : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hppow1 : (0 : ℚ) < (p : ℚ) ^ (q - 1) := by positivity
  have hppowq : (0 : ℚ) < (p : ℚ) ^ q := by positivity
  have hStageA : LS > TT - QT := by linarith
  have hTTQT : TT - QT = m / (p : ℚ) := by
    rw [hTT, hQT, hm]
    field_simp
    ring
  rw [hTTQT, hLS] at hStageA
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (0 : ℚ) < (q : ℚ) / (p : ℚ) ^ q := by positivity
  have e1 : ((u : ℚ) * (q : ℚ)) / ((c : ℚ) * (p : ℚ) ^ q)
      = ((u : ℚ) / (c : ℚ)) * ((q : ℚ) / (p : ℚ) ^ q) := by
    field_simp
  have e2 : m / (p : ℚ)
      = (m * ((p : ℚ) ^ (q - 1)) / (q : ℚ)) * ((q : ℚ) / (p : ℚ) ^ q) := by
    rw [hpexp]
    field_simp
  rw [e1, e2] at hStageA
  exact lt_of_mul_lt_mul_right hStageA (le_of_lt hfac)

end OddOrder.Peterfalvi.S15
