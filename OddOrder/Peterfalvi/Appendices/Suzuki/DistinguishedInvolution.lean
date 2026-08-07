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

namespace HypothesisA1

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : HypothesisA1 G Ω)

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

omit [Finite G] in
/-- An odd-order element is the square of `a^{(|a|+1)/2}`. -/
theorem sq_pow_half_orderOf {a : G} (ha : Odd (orderOf a)) :
    (a ^ ((orderOf a + 1) / 2)) ^ 2 = a := by
  rw [← pow_mul]
  obtain ⟨j, hj⟩ := ha
  rw [show (orderOf a + 1) / 2 * 2 = orderOf a + 1 from by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

omit [Finite G] in
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

The book puts `N = ⋂_{x ∈ G} H^x` (the *normal core* `𝒩(G)` of `H`) and proves

> `N = C_D(Q) ⊂ C_D(t)`.  The group `Ḡ = G/N` acting on `Ω` satisfies (A1),
> `Q̄ ≅ Q` and, if `s` is as in (b), then the order of the image `s̄t̄` of `st`
> in `Ḡ` is equal to the order of `st`.

Under (A1) alone `N` need not be trivial, and that is exactly how §3 uses the
statement: Proposition 1(a) there says "the statement concerning `𝒩(L)` has
been seen in §1, Proposition 4(c)", and Proposition 1(c) says "by §1,
Proposition 4(c), the order of `st` is equal to the order of `s̄t̄` in `L̄`".
So the two subgroup clauses are proved here on `HypothesisA1`; the quotient
clauses live with the quotient construction (`CentralizerQuotient`). -/

/-- `𝒩(G) = ⋂_x H^x` is exactly the set of elements acting trivially on `Ω`
(the kernel of the permutation representation).  Only double transitivity is
used, through the transitivity it implies. -/
theorem mem_normalCore_H_iff {n : G} :
    n ∈ hyp.H.normalCore ↔ ∀ ω : Ω, n • ω = ω := by
  haveI := hyp.doubly_transitive
  haveI : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  constructor
  · intro hn ω
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G hyp.basept ω
    have hmem : g⁻¹ * n * g ∈ hyp.H := by
      have := hn g⁻¹
      rwa [inv_inv] at this
    have hfix : (g⁻¹ * n * g) • hyp.basept = hyp.basept :=
      hyp.smul_basept_eq_of_mem_H hmem
    rw [← hg, ← mul_smul, show n * g = g * (g⁻¹ * n * g) from by group,
      mul_smul, hfix]
  · intro hfix g
    show g * n * g⁻¹ ∈ hyp.H
    rw [hyp.H_def, MulAction.mem_stabilizer_iff, mul_smul, mul_smul,
      hfix (g⁻¹ • hyp.basept), smul_inv_smul]

/-- `𝒩(G) ≤ D`: an element acting trivially on `Ω` fixes both `basept` and
`t • basept`. -/
theorem normalCore_H_le_D : hyp.H.normalCore ≤ hyp.D := by
  intro n hn
  have hfix := hyp.mem_normalCore_H_iff.mp hn
  rw [hyp.D_def]
  refine Subgroup.mem_inf.mpr ⟨hyp.H.normalCore_le hn, ?_⟩
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hyp.H_def,
    MulAction.mem_stabilizer_iff]
  simp [mul_smul, hfix]

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)** (p. 101), first clause —
`𝒩(G) = C_D(Q)`.

`⊆`: `n ∈ 𝒩(G)` fixes every point, so it lies in `D` and, for `q ∈ Q`, the
conjugate `n q n⁻¹ ∈ Q` moves `t • basept` exactly as `q` does; regularity of
`Q` on `Ω - {basept}` forces `n q n⁻¹ = q`.
`⊇`: `d ∈ C_D(Q)` fixes `basept` and `t • basept`, hence fixes
`q • (t • basept)` for every `q ∈ Q`, i.e. all of `Ω`. -/
theorem normalCore_H_eq_centralizer_Q :
    hyp.H.normalCore = hyp.D ⊓ Subgroup.centralizer (hyp.Q : Set G) := by
  refine le_antisymm (fun n hn => ?_) (fun d hd => ?_)
  · have hfix := hyp.mem_normalCore_H_iff.mp hn
    refine Subgroup.mem_inf.mpr ⟨hyp.normalCore_H_le_D hn, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hnH : n ∈ hyp.H := hyp.H.normalCore_le hn
    have hconjQ : n * q * n⁻¹ ∈ hyp.Q := hyp.Q_normal_in_H n hnH q hq
    have hfixinv : ∀ ω : Ω, n⁻¹ • ω = ω := fun ω => by
      have h := hfix (n⁻¹ • ω)
      rw [smul_inv_smul] at h
      exact h.symm
    -- both `n q n⁻¹` and `q` send `t • basept` to the same point
    have hsame : (n * q * n⁻¹) • (hyp.t • hyp.basept) =
        q • (hyp.t • hyp.basept) := by
      rw [mul_smul, mul_smul, hfixinv (hyp.t • hyp.basept),
        hfix (q • hyp.t • hyp.basept)]
    have hne : q • (hyp.t • hyp.basept) ≠ hyp.basept :=
      hyp.Q_smul_t_basept_ne hq
    have := hyp.qRegularEquiv.injective (a₁ := ⟨n * q * n⁻¹, hconjQ⟩)
      (a₂ := ⟨q, hq⟩) (Subtype.ext hsame)
    have hq' : n * q * n⁻¹ = q := congrArg Subtype.val this
    calc q * n = (n * q * n⁻¹) * n := by rw [hq']
      _ = n * q := by group
  · obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
    refine hyp.mem_normalCore_H_iff.mpr fun ω => ?_
    by_cases hω : ω = hyp.basept
    · rw [hω]; exact hyp.smul_basept_eq_of_mem_H (hyp.D_le_H hdD)
    · obtain ⟨q, hq⟩ := hyp.qRegularEquiv.surjective ⟨ω, hω⟩
      have hq' : (↑q : G) • (hyp.t • hyp.basept) = ω := congrArg Subtype.val hq
      have hcomm : Commute d (↑q : G) :=
        (Subgroup.mem_centralizer_iff.mp hdC (↑q) q.2).symm
      rw [← hq', ← mul_smul, hcomm.eq, mul_smul,
        hyp.smul_t_basept_eq_of_mem_D hdD]

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)** (p. 101), second clause —
`𝒩(G) ⊆ C_D(t) = V`.

The book's argument: "as `t` is conjugate to an element of `Q`, `t`
centralizes `N`".  `Q` has even order, so it contains an involution `u`; by
Prop 2(b) the involutions form one class, so `t = g⁻¹ u g` for some `g`.
`N` centralizes `Q` by the first clause and is normal, so `g⁻¹ N g = N` is
centralized by `g⁻¹ u g = t`. -/
theorem normalCore_H_le_V : hyp.H.normalCore ≤ hyp.V := by
  obtain ⟨u, huQ, hu2, hu1⟩ := hyp.exists_involution_mem_Q
  obtain ⟨g, hg⟩ := isConj_iff.mp (hyp.isConj_of_involutions hu2 hu1 hyp.t_sq
    hyp.t_ne_one)
  intro n hn
  have hnD : n ∈ hyp.D := hyp.normalCore_H_le_D hn
  refine Subgroup.mem_inf.mpr ⟨hnD, ?_⟩
  -- `g⁻¹ n g ∈ 𝒩(G)` centralizes `Q ∋ u`
  have hconj : g⁻¹ * n * g ∈ hyp.H.normalCore := by
    have := (Subgroup.normalCore_normal hyp.H).conj_mem n hn g⁻¹
    simpa using this
  have hcQ : g⁻¹ * n * g ∈ Subgroup.centralizer (hyp.Q : Set G) :=
    (Subgroup.mem_inf.mp
      (hyp.normalCore_H_eq_centralizer_Q ▸ hconj)).2
  have hcu : u * (g⁻¹ * n * g) = (g⁻¹ * n * g) * u :=
    Subgroup.mem_centralizer_iff.mp hcQ u huQ
  rw [Subgroup.mem_centralizer_iff]
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [← hg]
  calc g * u * g⁻¹ * n = g * (u * (g⁻¹ * n * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * n * g) * u) * g⁻¹ := by rw [hcu]
    _ = n * (g * u * g⁻¹) := by group

end HypothesisA1

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ### Proposition 4(c) under (A2)

Adding faithfulness collapses `𝒩(G)` to `1`, so under the standing hypothesis
of §2 onwards all three subgroups of the first clause are trivial. -/

/-- `𝒩(G) = ⋂_x H^x = 1` under (A2). -/
theorem normalCore_H_eq_bot : hyp.H.normalCore = ⊥ := by
  haveI := hyp.faithful
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  exact FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
    fun ω => by rw [one_smul]; exact hyp.toHypothesisA1.mem_normalCore_H_iff.mp hn ω

/-- `C_D(Q) = 1` under (A2) — Prop 4(c)'s first clause with `𝒩(G) = 1`. -/
theorem centralizer_Q_inf_D_eq_bot :
    hyp.D ⊓ Subgroup.centralizer (hyp.Q : Set G) = ⊥ := by
  rw [← hyp.toHypothesisA1.normalCore_H_eq_centralizer_Q, hyp.normalCore_H_eq_bot]

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)**, first clause under (A2). -/
theorem normalCore_eq_centralizer_Q :
    hyp.H.normalCore = hyp.D ⊓ Subgroup.centralizer (hyp.Q : Set G) :=
  hyp.toHypothesisA1.normalCore_H_eq_centralizer_Q

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)**, second clause under (A2). -/
theorem normalCore_le_V : hyp.H.normalCore ≤ hyp.V :=
  hyp.toHypothesisA1.normalCore_H_le_V

end Hypothesis

namespace HypothesisA1

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : HypothesisA1 G Ω)

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

/-- **The braid relation `t s t = s t s`**, which is the form `|s t| = 3` is used in from
Peterfalvi Part II, Ch. IV §3 onwards (`corollaryTwo_of_standardModel`'s `hC2`).

`s` and `t` are involutions, so `(s t s)(t s t) = (s t)³ = 1` and `s t s = (t s t)⁻¹`,
which is `t s t` again. -/
lemma braid_of_orderOf_mul_eq_three
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3) :
    hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution := by
  set s : G := hyp.distinguishedInvolution with hsdef
  set t : G := hyp.t with htdef
  have h3 : (s * t) ^ 3 = 1 := by rw [← hst]; exact pow_orderOf_eq_one _
  have hsinv : s⁻¹ = s :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hyp.distinguishedInvolution_sq)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hyp.t_sq)
  have h : s * t * s * (t * s * t) = 1 := by
    have hexp : (s * t) ^ 3 = s * t * s * (t * s * t) := by
      rw [pow_succ, pow_succ, pow_one]; group
    rw [← hexp]; exact h3
  have h2 : s * t * s = (t * s * t)⁻¹ := mul_eq_one_iff_eq_inv.mp h
  rw [h2, mul_inv_rev, mul_inv_rev, hsinv, htinv, mul_assoc]

/-! ### Proposition 4(c), third clause: `|s̄t̄| = |st|`

The book's argument (p. 102): "The elements of `⟨st⟩ ∩ N` are inverted by `t`,
centralized by `t` and of odd order; it follows that `⟨st⟩ ∩ N = 1` and the
order of `s̄t̄` is the same as that of `st`."  This is used verbatim in §3
Proposition 1(c) to transport the value of `|st|` through the induction. -/

/-- `t` inverts every power of `st` (both `s` and `t` are involutions, so
`t (st) t⁻¹ = (st)⁻¹`, and conjugation is an automorphism). -/
lemma conj_t_pow_distinguished_mul_t (n : ℕ) :
    hyp.t * (hyp.distinguishedInvolution * hyp.t) ^ n * hyp.t =
      ((hyp.distinguishedInvolution * hyp.t) ^ n)⁻¹ := by
  set s : G := hyp.distinguishedInvolution with hsdef
  set t : G := hyp.t with htdef
  have hsinv : s⁻¹ = s :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hyp.distinguishedInvolution_sq)
  have htinv : t⁻¹ = t :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hyp.t_sq)
  have htt : t * t = 1 := by rw [← sq]; exact hyp.t_sq
  have hbase : (MulAut.conj t) (s * t) = (s * t)⁻¹ := by
    rw [MulAut.conj_apply, mul_inv_rev, hsinv, htinv]
    calc t * (s * t) * t = t * s * (t * t) := by group
      _ = t * s := by rw [htt, mul_one]
  calc t * (s * t) ^ n * t
      = (MulAut.conj t) ((s * t) ^ n) := by
        rw [MulAut.conj_apply, htinv]
    _ = ((MulAut.conj t) (s * t)) ^ n := map_pow _ _ _
    _ = ((s * t)⁻¹) ^ n := by rw [hbase]
    _ = ((s * t) ^ n)⁻¹ := inv_pow _ _

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)** (p. 101), third clause, key step —
`⟨st⟩ ∩ 𝒩(G) = 1`. -/
theorem pow_eq_one_of_mem_normalCore {n : ℕ}
    (hn : (hyp.distinguishedInvolution * hyp.t) ^ n ∈ hyp.H.normalCore) :
    (hyp.distinguishedInvolution * hyp.t) ^ n = 1 := by
  set x : G := (hyp.distinguishedInvolution * hyp.t) ^ n with hxdef
  -- inverted by `t`
  have hinv : hyp.t * x * hyp.t = x⁻¹ := hyp.conj_t_pow_distinguished_mul_t n
  -- centralized by `t`, since `𝒩(G) ≤ V = C_D(t)`
  have hV : x ∈ hyp.V := hyp.normalCore_H_le_V hn
  have hcent : hyp.t * x = x * hyp.t :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hV).2 hyp.t rfl
  have hfix : hyp.t * x * hyp.t = x := by
    rw [hcent, mul_assoc, show hyp.t * hyp.t = 1 by rw [← sq]; exact hyp.t_sq,
      mul_one]
  have hxx : x = x⁻¹ := by rw [← hinv, hfix]
  have hsq : x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [hxx]
    exact inv_mul_cancel x
  exact OddOrder.GroupTheory.eq_one_of_sq_eq_one_of_odd_card hyp.D_odd
    (hyp.normalCore_H_le_D hn) hsq

/-- **Peterfalvi Part II, Ch. I Prop 4 (c)** (p. 101), third clause — the order
of the image `s̄t̄` in `Ḡ = G/𝒩(G)` equals the order of `st`. -/
theorem orderOf_mk_distinguished_mul_t :
    orderOf (QuotientGroup.mk' hyp.H.normalCore
        (hyp.distinguishedInvolution * hyp.t)) =
      orderOf (hyp.distinguishedInvolution * hyp.t) := by
  refine Nat.dvd_antisymm ?_ (orderOf_dvd_of_pow_eq_one ?_)
  · refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  · refine hyp.pow_eq_one_of_mem_normalCore ?_
    have := pow_orderOf_eq_one (QuotientGroup.mk' hyp.H.normalCore
      (hyp.distinguishedInvolution * hyp.t))
    rw [← map_pow] at this
    exact (QuotientGroup.eq_one_iff _).mp this

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

end HypothesisA1

end OddOrder.Peterfalvi.Appendices.Suzuki
