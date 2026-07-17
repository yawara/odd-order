/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm

/-!
# Peterfalvi Part II, Ch. I §1: the distinguished involution (Prop 4(b))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §1, p. 101.

Proposition 4(b): there is a *unique* pair `(s, r)` with `tst = r⁻¹tr`,
`s ∈ H ∩ I` and `r ∈ Q`.  Following the book, `s` is the *distinguished
involution* of `Q` and `tst = r⁻¹tr` the *structure equation* of `G`.

The proof parametrizes the involutions of `H ∩ I` by `K` (Prop 3, `s = uᵏ`
for a fixed base involution `u`), reduces the structure equation to the
condition `k⁻² = a` for an element `a = yx ∈ K` coming from the canonical
form of `tut`, and uses that `k ↦ k²` is a bijection of `K` (elements of
`K ⊆ D` have odd order).
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## Closure properties of `K` (p. 98) -/

lemma mem_D_of_mem_KSet {a : G} (ha : a ∈ hyp.KSet) : a ∈ hyp.D := ha.1

lemma t_conj_eq_inv_of_mem_KSet {a : G} (ha : a ∈ hyp.KSet) :
    hyp.t * a * hyp.t = a⁻¹ := ha.2

/-- `K` is closed under inversion. -/
lemma inv_mem_KSet {a : G} (ha : a ∈ hyp.KSet) : a⁻¹ ∈ hyp.KSet := by
  obtain ⟨haD, hainv⟩ := ha
  refine ⟨hyp.D.inv_mem haD, ?_⟩
  rw [inv_inv]
  have h2 := congrArg Inv.inv hainv
  rw [inv_inv, mul_inv_rev, mul_inv_rev, hyp.t_inv_eq, ← mul_assoc] at h2
  exact h2

/-- `K` is closed under natural-number powers. -/
lemma pow_mem_KSet {a : G} (ha : a ∈ hyp.KSet) (n : ℕ) : a ^ n ∈ hyp.KSet := by
  obtain ⟨haD, hainv⟩ := ha
  refine ⟨hyp.D.pow_mem haD n, ?_⟩
  have hstep : hyp.t * a * hyp.t⁻¹ = a⁻¹ := by rw [hyp.t_inv_eq]; exact hainv
  calc hyp.t * a ^ n * hyp.t
      = hyp.t * a ^ n * hyp.t⁻¹ := by rw [hyp.t_inv_eq]
    _ = (hyp.t * a * hyp.t⁻¹) ^ n := by rw [conj_pow]
    _ = (a⁻¹) ^ n := by rw [hstep]
    _ = (a ^ n)⁻¹ := inv_pow a n

lemma one_mem_KSet : (1 : G) ∈ hyp.KSet :=
  ⟨hyp.D.one_mem, by rw [mul_one, inv_one, ← sq]; exact hyp.t_sq⟩

/-- `K` is closed under integer powers. -/
lemma zpow_mem_KSet {a : G} (ha : a ∈ hyp.KSet) (k : ℤ) :
    a ^ k ∈ hyp.KSet := by
  rcases k with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact hyp.pow_mem_KSet ha n
  · rw [zpow_negSucc]
    exact hyp.inv_mem_KSet (hyp.pow_mem_KSet ha (n + 1))

/-! ## Odd order of elements of `D` -/

/-- Every element of `D` has odd order (`|D|` is odd). -/
lemma odd_orderOf_of_mem_D {a : G} (ha : a ∈ hyp.D) : Odd (orderOf a) := by
  have key : orderOf a = orderOf (⟨a, ha⟩ : hyp.D) :=
    orderOf_injective hyp.D.subtype hyp.D.subtype_injective ⟨a, ha⟩
  have hdvd : orderOf a ∣ Nat.card hyp.D := by
    rw [key]; exact orderOf_dvd_natCard _
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ orderOf a := Nat.dvd_of_mod_eq_zero (by omega)
  have hd2 : (2 : ℕ) ∣ Nat.card hyp.D := h2.trans hdvd
  have hodd := Nat.odd_iff.mp hyp.D_odd
  omega

/-! ## Odd square roots

`k ↦ k²` is a bijection on any set of odd-order elements: for such an
element `a`, the unique square root within `⟨a⟩` is `a^{(|a|+1)/2}`. -/

/-- An odd-order element is the square of `a^{(|a|+1)/2}`. -/
theorem sq_pow_half_orderOf {a : G} (ha : Odd (orderOf a)) :
    (a ^ ((orderOf a + 1) / 2)) ^ 2 = a := by
  rw [← pow_mul]
  obtain ⟨j, hj⟩ := ha
  rw [show (orderOf a + 1) / 2 * 2 = orderOf a + 1 from by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

/-- Odd-order square roots are unique: if `k₁, k₂` have odd order and
`k₁² = k₂²`, then `k₁ = k₂`. -/
theorem eq_of_sq_eq_of_odd_orderOf {k₁ k₂ a : G} (h1 : Odd (orderOf k₁))
    (h2 : Odd (orderOf k₂)) (e1 : k₁ ^ 2 = a) (e2 : k₂ ^ 2 = a) : k₁ = k₂ := by
  have hoa1 : orderOf a = orderOf k₁ := by
    rw [← e1]; exact (Nat.coprime_two_right.mpr h1).orderOf_pow
  have hoa2 : orderOf a = orderOf k₂ := by
    rw [← e2]; exact (Nat.coprime_two_right.mpr h2).orderOf_pow
  have hk1 : k₁ = a ^ ((orderOf k₁ + 1) / 2) := by
    rw [← e1, ← pow_mul]
    obtain ⟨j, hj⟩ := h1
    rw [show 2 * ((orderOf k₁ + 1) / 2) = orderOf k₁ + 1 from by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hk2 : k₂ = a ^ ((orderOf k₂ + 1) / 2) := by
    rw [← e2, ← pow_mul]
    obtain ⟨j, hj⟩ := h2
    rw [show 2 * ((orderOf k₂ + 1) / 2) = orderOf k₂ + 1 from by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [hk1, hk2, ← hoa1, ← hoa2]

/-! ## Conjugation relations for elements of `K` -/

/-- For `k ∈ K`, `kt = tk⁻¹` (`t` inverts `k`). -/
lemma mul_t_eq_of_mem_KSet {k : G} (hk : k ∈ hyp.KSet) :
    k * hyp.t = hyp.t * k⁻¹ := by
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  calc k * hyp.t = (hyp.t * hyp.t) * (k * hyp.t) := by rw [htt, one_mul]
    _ = hyp.t * (hyp.t * k * hyp.t) := by group
    _ = hyp.t * k⁻¹ := by rw [hk.2]

/-- For `k ∈ K`, `tk = k⁻¹t`. -/
lemma t_mul_eq_of_mem_KSet {k : G} (hk : k ∈ hyp.KSet) :
    hyp.t * k = k⁻¹ * hyp.t := by
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  calc hyp.t * k = (hyp.t * k) * (hyp.t * hyp.t) := by rw [htt, mul_one]
    _ = (hyp.t * k * hyp.t) * hyp.t := by group
    _ = k⁻¹ * hyp.t := by rw [hk.2]

/-- For `k ∈ K`, `ktk = t`. -/
lemma mul_t_mul_self_of_mem_KSet {k : G} (hk : k ∈ hyp.KSet) :
    k * hyp.t * k = hyp.t := by
  rw [hyp.mul_t_eq_of_mem_KSet hk, mul_assoc, inv_mul_cancel, mul_one]

/-- Conjugation by `t` of `uᵏ = k⁻¹uk` (for `k ∈ K`) equals the `k`-conjugate
of `t u t`: `t (k⁻¹uk) t = k (tut) k⁻¹`. -/
lemma t_conj_conj_of_mem_KSet {k u : G} (hk : k ∈ hyp.KSet) :
    hyp.t * (k⁻¹ * u * k) * hyp.t = k * (hyp.t * u * hyp.t) * k⁻¹ := by
  have e : hyp.t * k⁻¹ = k * hyp.t := (hyp.mul_t_eq_of_mem_KSet hk).symm
  have hL : hyp.t * (k⁻¹ * u * k) * hyp.t
      = (hyp.t * k⁻¹) * u * (hyp.t * k⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv, hyp.t_inv_eq]; group
  have hR : k * (hyp.t * u * hyp.t) * k⁻¹ = (k * hyp.t) * u * (k * hyp.t)⁻¹ := by
    rw [mul_inv_rev, hyp.t_inv_eq]; group
  rw [hL, hR, e]

/-- The `k`-conjugate of a canonical form `xty` (for `k ∈ K`) is again in
canonical form, with distinguished middle factor `k(yx)k`:
`k(xty)k⁻¹ = (kyk⁻¹)⁻¹ · k(yx)k · t · (kyk⁻¹)`. -/
lemma canonicalForm_conj_eq {k x y : G} (hk : k ∈ hyp.KSet) :
    k * (x * hyp.t * y) * k⁻¹ =
      (k * y * k⁻¹)⁻¹ * (k * (y * x) * k) * hyp.t * (k * y * k⁻¹) := by
  have hktk := hyp.mul_t_mul_self_of_mem_KSet hk
  have hc1 : (k * y * k⁻¹)⁻¹ * (k * (y * x) * k) = k * x * k := by
    rw [mul_inv_rev, mul_inv_rev]; group
  calc k * (x * hyp.t * y) * k⁻¹
      = k * x * (k * hyp.t * k) * y * k⁻¹ := by rw [hktk]; group
    _ = (k * x * k) * hyp.t * (k * y * k⁻¹) := by group
    _ = ((k * y * k⁻¹)⁻¹ * (k * (y * x) * k)) * hyp.t * (k * y * k⁻¹) := by
        rw [hc1]
    _ = (k * y * k⁻¹)⁻¹ * (k * (y * x) * k) * hyp.t * (k * y * k⁻¹) := by group

/-! ## `tut ∉ H` and the `Q`-centralizer of `t` -/

/-- For an involution `u ∈ H ∩ I`, the conjugate `tut` lies outside `H`
(as `u ∈ Q` and `Q ∩ D = 1`, while `tut ∈ H` would force `u ∈ H^t`). -/
lemma t_mul_mul_t_notMem_H {u : G} (huH : u ∈ hyp.H) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) : hyp.t * u * hyp.t ∉ hyp.H := by
  intro hmem
  have huQ := hyp.mem_Q_of_sq_eq_one_of_mem_H huH hu2
  have huD : u ∈ hyp.D := by
    rw [hyp.mem_D_iff]
    exact ⟨huH, by rw [hyp.t_inv_eq]; exact hmem⟩
  have hbot : u ∈ hyp.Q ⊓ hyp.D := ⟨huQ, huD⟩
  rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
  exact hu1 hbot

/-- An element of `Q` commuting with `t` is trivial (`Q ∩ C_G(t) = 1`,
used for the uniqueness of `r`). -/
lemma eq_one_of_mem_Q_commute_t {q : G} (hq : q ∈ hyp.Q)
    (hc : Commute q hyp.t) : q = 1 := by
  have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
  have hqtq : hyp.t * q * hyp.t = q := by
    calc hyp.t * q * hyp.t = hyp.t * (q * hyp.t) := by rw [mul_assoc]
      _ = hyp.t * (hyp.t * q) := by rw [hc.eq]
      _ = (hyp.t * hyp.t) * q := by rw [mul_assoc]
      _ = q := by rw [htt, one_mul]
  have hqD : q ∈ hyp.D := by
    rw [hyp.mem_D_iff]
    exact ⟨hyp.Q_le_H hq, by rw [hyp.t_inv_eq, hqtq]; exact hyp.Q_le_H hq⟩
  have hbot : q ∈ hyp.Q ⊓ hyp.D := ⟨hq, hqD⟩
  rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
  exact hbot

/-! ## Chapter I §1, Proposition 4 (b) (p. 101) -/

/-- **Peterfalvi Part II, Ch. I Prop 4 (b)** (p. 101) — there is a *unique*
pair `(s, r)` with `tst = r⁻¹tr`, `s ∈ H ∩ I` and `r ∈ Q`.  The element `s`
is the *distinguished involution* of `Q` and `tst = r⁻¹tr` the *structure
equation* of `G`.

Proof (following the book).  Fix a base involution `u ∈ Q ∩ I`; by Prop 3
every `s ∈ H ∩ I` is `uᵏ` for a unique `k ∈ K`.  The canonical form
`tut = xty` (Prop 4(a)) yields `a = yx ∈ K`, and for `s = uᵏ` the conjugate
`tst` is again in canonical form with `Q`-part `kyk⁻¹` and distinguished
factor `k(yx)k`; so `(s, r)` is a valid pair iff `k(yx)k = 1`, i.e. `k⁻² = a`.
Since `k ↦ k²` is a bijection of `K`, there is exactly one such `k`. -/
theorem existsUnique_distinguishedInvolution :
    ∃! p : G × G, (p.1 ∈ hyp.H ∧ p.1 ^ 2 = 1 ∧ p.1 ≠ 1) ∧ p.2 ∈ hyp.Q ∧
      hyp.t * p.1 * hyp.t = p.2⁻¹ * hyp.t * p.2 := by
  classical
  -- base involution `u ∈ Q` and the canonical form of `tut`
  obtain ⟨u, huQ, hu2, hu1⟩ := hyp.exists_involution_mem_Q
  have huH := hyp.Q_le_H huQ
  have huu : u * u = 1 := by rw [← sq]; exact hu2
  have htutH : hyp.t * u * hyp.t ∉ hyp.H := hyp.t_mul_mul_t_notMem_H huH hu2 hu1
  obtain ⟨x, hxH, y, hyQ, hxy⟩ := hyp.exists_canonicalForm htutH
  -- `a = y*x ∈ K`
  have hinvol : (x * hyp.t * y) * (x * hyp.t * y) = 1 := by
    rw [← hxy]
    have htt : hyp.t * hyp.t = 1 := by rw [← sq]; exact hyp.t_sq
    calc (hyp.t * u * hyp.t) * (hyp.t * u * hyp.t)
        = hyp.t * u * ((hyp.t * hyp.t) * u * hyp.t) := by group
      _ = hyp.t * u * (u * hyp.t) := by rw [htt, one_mul]
      _ = hyp.t * (u * u) * hyp.t := by group
      _ = hyp.t * hyp.t := by rw [huu, mul_one]
      _ = 1 := htt
  have hatat : hyp.t * (y * x) * hyp.t = (y * x)⁻¹ := by
    have h3 : x * (hyp.t * (y * x) * hyp.t) * y = 1 := by rw [← hinvol]; group
    have hM : hyp.t * (y * x) * hyp.t
        = x⁻¹ * (x * (hyp.t * (y * x) * hyp.t) * y) * y⁻¹ := by group
    rw [mul_inv_rev, hM, h3]; group
  have haH : y * x ∈ hyp.H := mul_mem (hyp.Q_le_H hyQ) hxH
  have haK : y * x ∈ hyp.KSet := by
    refine ⟨?_, hatat⟩
    rw [hyp.mem_D_iff]
    exact ⟨haH, by rw [hyp.t_inv_eq, hatat]; exact inv_mem haH⟩
  -- unique square root `k₀ ∈ K` with `k₀² = (y*x)⁻¹`
  have haiK : (y * x)⁻¹ ∈ hyp.KSet := hyp.inv_mem_KSet haK
  have haiodd : Odd (orderOf (y * x)⁻¹) := hyp.odd_orderOf_of_mem_D haiK.1
  have hsqrt : ∃! k, k ∈ hyp.KSet ∧ k ^ 2 = (y * x)⁻¹ := by
    refine ⟨((y * x)⁻¹) ^ ((orderOf (y * x)⁻¹ + 1) / 2),
      ⟨hyp.pow_mem_KSet haiK _, sq_pow_half_orderOf haiodd⟩, ?_⟩
    rintro k ⟨hkK, hksq⟩
    exact eq_of_sq_eq_of_odd_orderOf (hyp.odd_orderOf_of_mem_D hkK.1)
      (hyp.odd_orderOf_of_mem_D (hyp.pow_mem_KSet haiK _).1) hksq
      (sq_pow_half_orderOf haiodd)
  obtain ⟨k₀, ⟨hk0K, hk0sq⟩, hk0uniq⟩ := hsqrt
  have hk0H : k₀ ∈ hyp.H := hyp.D_le_H hk0K.1
  have hk0a : k₀ * (y * x) * k₀ = 1 := by
    have ha_eq : y * x = k₀⁻¹ * k₀⁻¹ := by
      rw [show y * x = (k₀ ^ 2)⁻¹ from by rw [hk0sq, inv_inv], sq, mul_inv_rev]
    rw [ha_eq]; group
  -- the distinguished pair `(s₀, r₀)`
  refine ⟨(k₀⁻¹ * u * k₀, k₀ * y * k₀⁻¹), ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact mul_mem (mul_mem (inv_mem hk0H) huH) hk0H
  · rw [sq]
    calc (k₀⁻¹ * u * k₀) * (k₀⁻¹ * u * k₀) = k₀⁻¹ * (u * u) * k₀ := by group
      _ = 1 := by rw [huu]; group
  · intro h1
    apply hu1
    have h1' : k₀⁻¹ * u * k₀ = 1 := h1
    have h2 : k₀ * (k₀⁻¹ * u * k₀) * k₀⁻¹ = k₀ * 1 * k₀⁻¹ := by rw [h1']
    rw [show k₀ * (k₀⁻¹ * u * k₀) * k₀⁻¹ = u from by group,
      show k₀ * 1 * k₀⁻¹ = 1 from by group] at h2
    exact h2
  · exact hyp.Q_normal_in_H k₀ hk0H y hyQ
  · rw [hyp.t_conj_conj_of_mem_KSet hk0K, hxy, hyp.canonicalForm_conj_eq hk0K, hk0a]
    group
  -- uniqueness
  · rintro ⟨s, r⟩ ⟨⟨hsH, hs2, hs1⟩, hrQ, hstr⟩
    replace hsH : s ∈ hyp.H := hsH
    replace hs2 : s ^ 2 = 1 := hs2
    replace hs1 : s ≠ 1 := hs1
    replace hrQ : r ∈ hyp.Q := hrQ
    replace hstr : hyp.t * s * hyp.t = r⁻¹ * hyp.t * r := hstr
    have himg := hyp.image_conj_KSet_eq_involutions_H huH hu2 hu1
    have hs_mem : s ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := ⟨hs2, hs1, hsH⟩
    rw [← himg] at hs_mem
    obtain ⟨k, hkK, hks₀⟩ := hs_mem
    have hks : k⁻¹ * u * k = s := hks₀
    have hkH : k ∈ hyp.H := hyp.D_le_H hkK.1
    have hkyk : k * y * k⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H k hkH y hyQ
    -- `tst` in canonical form via `k`
    have hcan : hyp.t * s * hyp.t
        = (k * y * k⁻¹)⁻¹ * (k * (y * x) * k) * hyp.t * (k * y * k⁻¹) := by
      rw [← hks, hyp.t_conj_conj_of_mem_KSet hkK, hxy, hyp.canonicalForm_conj_eq hkK]
    have heq : (k * y * k⁻¹)⁻¹ * (k * (y * x) * k) * hyp.t * (k * y * k⁻¹)
        = r⁻¹ * hyp.t * r := hcan ▸ hstr
    have hx1H : (k * y * k⁻¹)⁻¹ * (k * (y * x) * k) ∈ hyp.H :=
      mul_mem (hyp.Q_le_H (inv_mem hkyk)) (mul_mem (mul_mem hkH haH) hkH)
    obtain ⟨hX, hY⟩ := hyp.canonicalForm_unique hx1H hkyk
      (inv_mem (hyp.Q_le_H hrQ)) hrQ heq
    -- `k(yx)k = 1`, hence `k² = (yx)⁻¹` and `k = k₀`
    have hkak : k * (y * x) * k = 1 := by
      have hX2 : (k * y * k⁻¹)⁻¹ * (k * (y * x) * k) = (k * y * k⁻¹)⁻¹ := by
        rw [hX, ← hY]
      calc k * (y * x) * k
          = (k * y * k⁻¹) * ((k * y * k⁻¹)⁻¹ * (k * (y * x) * k)) := by group
        _ = (k * y * k⁻¹) * (k * y * k⁻¹)⁻¹ := by rw [hX2]
        _ = 1 := by group
    have hksq : k ^ 2 = (y * x)⁻¹ := by
      have hyx : y * x = k⁻¹ * k⁻¹ := by
        rw [show y * x = k⁻¹ * (k * (y * x) * k) * k⁻¹ from by group, hkak]; group
      rw [hyx, mul_inv_rev, inv_inv, sq]
    have hk_eq : k = k₀ := hk0uniq k ⟨hkK, hksq⟩
    have hs_eq : s = k₀⁻¹ * u * k₀ := by rw [← hks, hk_eq]
    have hr_eq : r = k₀ * y * k₀⁻¹ := by rw [← hY, hk_eq]
    simp only [Prod.mk.injEq]
    exact ⟨hs_eq, hr_eq⟩

/-! ## Chapter I §1, Proposition 4 (c) (p. 101)

`N = ⋂_{x ∈ G} H^x` is the *normal core* `𝒩(G)` of `H`.  Because `G` acts
faithfully on `Ω` (hypothesis (A2)), `N = 1`, so the book's `N = C_D(Q) ⊆
C_D(t)` holds with all three subgroups equal to `1`, and the quotient
`Ḡ = G/N` coincides with `G` (hence trivially satisfies (A1), `Q̄ ≅ Q`, and
`|s̄t̄| = |st|`).  The mathematically substantial part in this setting is the
identity `C_D(Q) = 1`.  (The general quotient construction of Prop 4(c), used
in the Chapters II–IV induction where the ambient action need not be
faithful, is recovered there by instantiating the hypotheses on `G/N`.) -/

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)** (p. 101), the kernel — `𝒩(G) =
⋂_x H^x = 1` (the action is faithful, (A2)). -/
theorem normalCore_H_eq_bot : hyp.H.normalCore = ⊥ := by
  haveI := hyp.faithful
  haveI := hyp.doubly_transitive
  haveI : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
  intro ω
  rw [one_smul]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G hyp.basept ω
  have hmem : g⁻¹ * n * g ∈ hyp.H := by
    have := hn g⁻¹
    rwa [inv_inv] at this
  have hfix : (g⁻¹ * n * g) • hyp.basept = hyp.basept :=
    hyp.smul_basept_eq_of_mem_H hmem
  rw [← hg, ← mul_smul, show n * g = g * (g⁻¹ * n * g) from by group, mul_smul, hfix]

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)** (p. 101), the substantial clause
— `C_D(Q) = 1` (elements of `D` centralizing `Q` fix every point of `Ω`, hence
are trivial by faithfulness). -/
theorem centralizer_Q_inf_D_eq_bot :
    hyp.D ⊓ Subgroup.centralizer (hyp.Q : Set G) = ⊥ := by
  haveI := hyp.faithful
  rw [eq_bot_iff]
  intro d hd
  obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
  rw [Subgroup.mem_bot]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
  intro ω
  rw [one_smul]
  by_cases hω : ω = hyp.basept
  · rw [hω]; exact hyp.smul_basept_eq_of_mem_H (hyp.D_le_H hdD)
  · obtain ⟨q, hq⟩ := hyp.qRegularEquiv.surjective ⟨ω, hω⟩
    have hq' : (↑q : G) • (hyp.t • hyp.basept) = ω := congrArg Subtype.val hq
    have hcomm : Commute d (↑q : G) :=
      (Subgroup.mem_centralizer_iff.mp hdC (↑q) q.2).symm
    rw [← hq', ← mul_smul, hcomm.eq, mul_smul, hyp.smul_t_basept_eq_of_mem_D hdD]

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)** (p. 101), packaged — the book's
`𝒩(G) = C_D(Q)` (both `= 1` under (A2)). -/
theorem normalCore_eq_centralizer_Q :
    hyp.H.normalCore = hyp.D ⊓ Subgroup.centralizer (hyp.Q : Set G) := by
  rw [hyp.normalCore_H_eq_bot, hyp.centralizer_Q_inf_D_eq_bot]

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)** (p. 101) — `𝒩(G) ⊆ C_D(t) = V`. -/
theorem normalCore_le_V : hyp.H.normalCore ≤ hyp.V := by
  rw [hyp.normalCore_H_eq_bot]; exact bot_le

/-! ## The distinguished involution `s` and structure conjugator `r` (p. 101)

Named witnesses of Proposition 4(b): the *distinguished involution* `s` of
`Q` and the element `r ∈ Q` of the *structure equation* `tst = r⁻¹tr`. -/

/-- The distinguished pair `(s, r)` of Prop 4(b). -/
noncomputable def distinguishedPair : G × G :=
  hyp.existsUnique_distinguishedInvolution.exists.choose

/-- The **distinguished involution** `s` of `Q` (Prop 4(b)). -/
noncomputable def distinguishedInvolution : G := hyp.distinguishedPair.1

/-- The element `r ∈ Q` of the structure equation `tst = r⁻¹tr` (Prop 4(b)). -/
noncomputable def structureConjugator : G := hyp.distinguishedPair.2

lemma distinguishedPair_spec :
    (hyp.distinguishedInvolution ∈ hyp.H ∧ hyp.distinguishedInvolution ^ 2 = 1 ∧
      hyp.distinguishedInvolution ≠ 1) ∧ hyp.structureConjugator ∈ hyp.Q ∧
      hyp.t * hyp.distinguishedInvolution * hyp.t =
        hyp.structureConjugator⁻¹ * hyp.t * hyp.structureConjugator :=
  hyp.existsUnique_distinguishedInvolution.exists.choose_spec

lemma distinguishedInvolution_mem_H : hyp.distinguishedInvolution ∈ hyp.H :=
  hyp.distinguishedPair_spec.1.1

lemma distinguishedInvolution_sq : hyp.distinguishedInvolution ^ 2 = 1 :=
  hyp.distinguishedPair_spec.1.2.1

lemma distinguishedInvolution_ne_one : hyp.distinguishedInvolution ≠ 1 :=
  hyp.distinguishedPair_spec.1.2.2

lemma structureConjugator_mem_Q : hyp.structureConjugator ∈ hyp.Q :=
  hyp.distinguishedPair_spec.2.1

/-- **Structure equation** `tst = r⁻¹tr` (Prop 4(b)). -/
lemma structure_equation :
    hyp.t * hyp.distinguishedInvolution * hyp.t =
      hyp.structureConjugator⁻¹ * hyp.t * hyp.structureConjugator :=
  hyp.distinguishedPair_spec.2.2

/-- Uniqueness of the distinguished pair: any `(s', r')` satisfying the
defining conditions equals `(s, r)`. -/
lemma eq_distinguishedPair_of_structure {s' r' : G} (hsH : s' ∈ hyp.H)
    (hs2 : s' ^ 2 = 1) (hs1 : s' ≠ 1) (hrQ : r' ∈ hyp.Q)
    (heq : hyp.t * s' * hyp.t = r'⁻¹ * hyp.t * r') :
    s' = hyp.distinguishedInvolution ∧ r' = hyp.structureConjugator := by
  have h : (s', r') = hyp.distinguishedPair :=
    hyp.existsUnique_distinguishedInvolution.unique
      ⟨⟨hsH, hs2, hs1⟩, hrQ, heq⟩ hyp.distinguishedPair_spec
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
