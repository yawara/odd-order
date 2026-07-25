/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.RingTheory.Int.Basic

/-!
# Degree-`p` faithful transitive actions of order `p(p-1)` are two-transitive

A finite group of order `p·(p-1)` acting faithfully and transitively on a set of
prime cardinality `p` is (sharply) two-transitive.

The cyclic Sylow `p`-subgroup `⟨σ⟩` is normal (its number divides `p - 1` and is
`≡ 1 (mod p)`), acts regularly (a fixed point of `σ` would propagate to all of `Ω`
by normality and transitivity, contradicting faithfulness), and any two-point
stabilizer element is forced to commute with `⟨σ⟩`, hence fixes every point, hence
is trivial; counting orbits of pairs finishes.

This is used to reconstruct the rank-one (two-transitive) hypothesis for
`N_G(R)/R` acting on the set `𝒜` of order-`p` subgroups in step (12) of
Peterfalvi, Part II, Ch. II (the first case of the theorem of Suzuki).
-/

namespace OddOrder.GroupTheory

open MulAction

variable {G : Type*} {Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]

section PrimeDegree

variable [FaithfulSMul G Ω] [IsPretransitive G Ω] {p : ℕ}

omit [Finite Ω] in
/-- A nonidentity element of the normal cyclic Sylow subgroup `⟨σ⟩` fixes no point:
its fixed point would propagate to every point of `Ω` (conjugates of `σ`-powers stay
in `⟨σ⟩`), contradicting faithfulness. -/
private theorem not_smul_eq_of_orderOf_eq_prime (hp : p.Prime) {σ : G}
    (hσ : orderOf σ = p) (hnorm : (Subgroup.zpowers σ).Normal) {τ : G}
    (hτN : τ ∈ Subgroup.zpowers σ) (hτ1 : τ ≠ 1) (y : Ω) : τ • y ≠ y := by
  intro hfix
  -- `σ ∈ ⟨τ⟩` since `⟨τ⟩` is a nontrivial subgroup of the order-`p` cyclic `⟨σ⟩`.
  have hστ : σ ∈ Subgroup.zpowers τ := by
    have hle : Subgroup.zpowers τ ≤ Subgroup.zpowers σ := by
      rw [Subgroup.zpowers_le]
      exact hτN
    have hcardσ : Nat.card (Subgroup.zpowers σ) = p := by rw [Nat.card_zpowers, hσ]
    have hdvd : Nat.card (Subgroup.zpowers τ) ∣ p := by
      rw [← hcardσ]
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd).symm with heq | heq
    · have : Subgroup.zpowers τ = Subgroup.zpowers σ :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [heq, hcardσ])
      rw [this]
      exact Subgroup.mem_zpowers σ
    · exfalso
      have h2 : Subgroup.zpowers τ = ⊥ := Subgroup.eq_bot_of_card_eq _ heq
      exact hτ1 (by simpa [h2, Subgroup.mem_bot] using Subgroup.mem_zpowers τ)
  -- if some `z` were moved by `σ`, transitivity + normality would move `y` too.
  have hall : ∀ z : Ω, σ • z = z := by
    intro z
    obtain ⟨g, rfl⟩ := exists_smul_eq G y z
    -- `g⁻¹ σ g ∈ ⟨σ⟩`; it suffices that it fixes `y`.
    by_contra hne
    have hmem : g⁻¹ * σ * g ∈ Subgroup.zpowers σ := by
      have := hnorm.conj_mem σ (Subgroup.mem_zpowers σ) g⁻¹
      simpa using this
    -- `τ` fixes `y`, hence so does all of `⟨τ⟩ ∋ σ`... transported by `g`:
    -- `σ • (g • y) ≠ g • y` gives `(g⁻¹ σ g) • y ≠ y`, i.e. an element of `⟨σ⟩`
    -- moving `y`; but every element of `⟨σ⟩` is a power of `τ`... contradiction
    -- with `τ • y = y` requires `⟨σ⟩ ≤ stabilizer`.  Assemble via stabilizers:
    have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer G y := by
      have hτs : τ ∈ MulAction.stabilizer G y := hfix
      have h1 : Subgroup.zpowers τ ≤ MulAction.stabilizer G y := by
        rw [Subgroup.zpowers_le]
        exact hτs
      have h2 : σ ∈ MulAction.stabilizer G y := h1 hστ
      rw [Subgroup.zpowers_le]
      exact h2
    have h3 : (g⁻¹ * σ * g) • y = y := hstab hmem
    have h4 : σ • g • y = g • y := by
      have h5 : (g * (g⁻¹ * σ * g)) • y = g • y := by rw [mul_smul, h3]
      have h6 : g * (g⁻¹ * σ * g) = σ * g := by group
      rw [h6, mul_smul] at h5
      exact h5
    exact hne h4
  -- `σ` acts trivially: faithfulness collapses it to `1`, contradicting its order.
  have hσ1 : σ = 1 := by
    apply eq_of_smul_eq_smul (α := Ω)
    intro z
    rw [hall z, one_smul]
  rw [hσ1, orderOf_one] at hσ
  exact hp.one_lt.ne' hσ.symm

omit [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω] [IsPretransitive G Ω] in
/-- **A group of order `p(p-1)` has a normal subgroup of order `p`** — action-free
core: Cauchy provides `σ` of order `p`, and the Sylow count (`≡ 1 (mod p)`,
dividing `p - 1`) forces `⟨σ⟩` to be the unique, hence normal, Sylow
`p`-subgroup.  (In step (12) of the first case of the theorem of Suzuki this is
Appendix II, Prop. 1's regular normal subgroup `R₁/R` of `N_G(R)/R`.) -/
theorem exists_orderOf_eq_prime_zpowers_normal (hp : p.Prime)
    (hG : Nat.card G = p * (p - 1)) :
    ∃ σ : G, orderOf σ = p ∧ (Subgroup.zpowers σ).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Cauchy: an element of order `p`.
  haveI := Fintype.ofFinite G
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (G := G) p
    (by rw [← Nat.card_eq_fintype_card, hG]; exact ⟨p - 1, rfl⟩)
  set N : Subgroup G := Subgroup.zpowers σ with hNdef
  have hcardN : Nat.card N = p := by rw [hNdef, Nat.card_zpowers, hσ]
  -- `N` is the unique (hence normal) Sylow `p`-subgroup.
  have hfact : (Nat.card G).factorization p = 1 := by
    rw [hG]
    have h1 : p - 1 ≠ 0 := by have := hp.one_lt; omega
    rw [Nat.factorization_mul hp.pos.ne' h1, Finsupp.add_apply,
      hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd
        (fun hdvd => by have := Nat.le_of_dvd (by omega) hdvd; omega)]
  have hnorm : N.Normal := by
    set S : Sylow p G := Sylow.ofCard N (by rw [hcardN, hfact, pow_one])
    have hidx : (S : Subgroup G).index = p - 1 := by
      have h1 := (S : Subgroup G).card_mul_index
      have h2 : Nat.card (S : Subgroup G) = p := hcardN
      rw [h2, hG] at h1
      exact Nat.eq_of_mul_eq_mul_left hp.pos h1
    have hdvd : Nat.card (Sylow p G) ∣ p - 1 := hidx ▸ S.card_dvd_index
    have hone : Nat.card (Sylow p G) = 1 := by
      have h1 := card_sylow_modEq_one p G
      have h2 : Nat.card (Sylow p G) ≤ p - 1 :=
        Nat.le_of_dvd (by have := hp.one_lt; omega) hdvd
      have h3 : Nat.card (Sylow p G) % p = 1 % p := h1
      have h4 : 1 % p = 1 := Nat.one_mod_eq_one.mpr hp.one_lt.ne'
      have h5 : Nat.card (Sylow p G) % p = Nat.card (Sylow p G) :=
        Nat.mod_eq_of_lt (by have := hp.one_lt; omega)
      omega
    haveI : Subsingleton (Sylow p G) :=
      (Nat.card_eq_one_iff_unique.mp hone).1
    exact Sylow.normal_of_subsingleton S
  exact ⟨σ, hσ, hnorm⟩

/-- The engine behind this file: a generator `σ` of the unique (normal) Sylow
`p`-subgroup, which acts freely, and regularly from every base point. -/
private theorem exists_normal_regular (hp : p.Prime) (hΩ : Nat.card Ω = p)
    (hG : Nat.card G = p * (p - 1)) :
    ∃ σ : G, orderOf σ = p ∧ (Subgroup.zpowers σ).Normal ∧
      (∀ τ ∈ Subgroup.zpowers σ, τ ≠ 1 → ∀ y : Ω, τ • y ≠ y) ∧
      ∀ a : Ω, Function.Surjective (fun i : ZMod p => σ ^ (i.val) • a) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ, hnorm⟩ := exists_orderOf_eq_prime_zpowers_normal hp hG
  -- `σ` has no fixed point, so `i ↦ σ^i • a` is injective `ZMod p → Ω`, so surjective.
  have hfree : ∀ (τ : G), τ ∈ Subgroup.zpowers σ → τ ≠ 1 → ∀ y : Ω, τ • y ≠ y :=
    fun τ hτ hτ1 y => not_smul_eq_of_orderOf_eq_prime hp hσ hnorm hτ hτ1 y
  refine ⟨σ, hσ, hnorm, hfree, fun a => ?_⟩
  have hinj : Function.Injective (fun i : ZMod p => σ ^ (i.val) • a) := by
    have key : ∀ i' j' : ZMod p, j'.val < i'.val →
        σ ^ (i'.val) • a = σ ^ (j'.val) • a → False := by
      intro i' j' hlt heq
      have h2 : σ ^ (i'.val - j'.val) • (σ ^ (j'.val) • a) = σ ^ (j'.val) • a := by
        rw [smul_smul, ← pow_add]
        have h3 : i'.val - j'.val + j'.val = i'.val := by omega
        rw [h3, heq]
      have h4 : σ ^ (i'.val - j'.val) ≠ 1 := by
        intro h5
        have h6 : orderOf σ ∣ i'.val - j'.val := orderOf_dvd_of_pow_eq_one h5
        rw [hσ] at h6
        have h7 : i'.val < p := ZMod.val_lt i'
        have h8 := Nat.le_of_dvd (by omega) h6
        omega
      exact hfree _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _) h4 _ h2
    intro i j hij
    simp only at hij
    by_contra hne
    have hvne : i.val ≠ j.val := fun hv => hne (ZMod.val_injective p hv)
    rcases Nat.lt_or_ge j.val i.val with h | h
    · exact key i j h hij
    · exact key j i (lt_of_le_of_ne h hvne) hij.symm
  have h1 : Nat.card (ZMod p) = Nat.card Ω := by
    rw [Nat.card_zmod, hΩ]
  exact ((Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, h1⟩).2

/-- **Two-point stabilizers are trivial** for a faithful transitive action of a group
of order `p(p-1)` on `p` points: any `g` fixing two distinct points is forced to
commute with the normal Sylow `p`-generator `σ` (conjugation preserves the unique
power sending the first point to the second), hence fixes all of `Ω`. -/
theorem eq_one_of_smul_eq_of_smul_eq (hp : p.Prime) (hΩ : Nat.card Ω = p)
    (hG : Nat.card G = p * (p - 1)) {g : G} {a b : Ω} (hab : a ≠ b)
    (hga : g • a = a) (hgb : g • b = b) : g = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ, hnorm, hfree, hsurjAll⟩ := exists_normal_regular hp hΩ hG
  set N : Subgroup G := Subgroup.zpowers σ with hNdef
  have hcardN : Nat.card N = p := by rw [hNdef, Nat.card_zpowers, hσ]
  have hsurj := hsurjAll a
  -- write `b = σ^i • a`, `i ≠ 0`.
  obtain ⟨i, hi⟩ := hsurj b
  simp only at hi
  have hi0 : σ ^ (i.val) ≠ 1 := by
    intro h0
    rw [h0, one_smul] at hi
    exact hab hi
  have hga' : g⁻¹ • a = a := by
    rw [inv_smul_eq_iff]
    exact hga.symm
  -- conjugation-power helper (`MulAut.conj` as a hom).
  have hconjpow : ∀ (x : G) (s : ℤ), (g * x * g⁻¹) ^ s = g * x ^ s * g⁻¹ := by
    intro x s
    simp
  -- `g` conjugates `σ^i` to an `N`-element sending `a ↦ b`: uniqueness pins it.
  have hconj : g * σ ^ (i.val) * g⁻¹ = σ ^ (i.val) := by
    have hmem : g * σ ^ (i.val) * g⁻¹ ∈ N :=
      hnorm.conj_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _) g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    -- both sides send `a` to `b`, so their difference fixes `b`.
    have h2 : (σ ^ k * (σ ^ (i.val))⁻¹) • b = b := by
      have hb : (σ ^ (i.val))⁻¹ • b = a := by
        rw [← hi, inv_smul_smul]
      rw [mul_smul, hb, hk, mul_smul, hga', mul_smul, hi]
      exact hgb
    have h3 : σ ^ k * (σ ^ (i.val))⁻¹ = 1 := by
      by_contra hne
      exact hfree _ (mul_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers σ) _)
        (inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _))) hne b h2
    rw [← hk]
    exact mul_inv_eq_one.mp h3
  -- hence `g` commutes with all of `N`, hence fixes every `σ^j • a`, hence `g = 1`.
  have hcomm : ∀ τ ∈ N, g * τ * g⁻¹ = τ := by
    intro τ hτ
    have hστ : σ ∈ Subgroup.zpowers (σ ^ (i.val)) := by
      have hle : Subgroup.zpowers (σ ^ (i.val)) ≤ N :=
        (Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _)
      have hcard : Nat.card (Subgroup.zpowers (σ ^ (i.val))) ∣ p := by
        have hc := Subgroup.card_dvd_of_le hle
        rwa [hcardN] at hc
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hcard).symm with heq | heq
      · have : Subgroup.zpowers (σ ^ (i.val)) = N :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [heq, hcardN])
        rw [this]
        exact Subgroup.mem_zpowers σ
      · exact absurd (Subgroup.eq_bot_of_card_eq _ heq) (fun h0 =>
          hi0 (by simpa [h0, Subgroup.mem_bot] using
            Subgroup.mem_zpowers (σ ^ (i.val))))
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hστ
    obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.mp hτ
    have hgs : g * σ * g⁻¹ = σ := by
      calc g * σ * g⁻¹ = g * (σ ^ (i.val)) ^ s * g⁻¹ := by rw [hs]
        _ = (g * σ ^ (i.val) * g⁻¹) ^ s := (hconjpow _ s).symm
        _ = (σ ^ (i.val)) ^ s := by rw [hconj]
        _ = σ := hs
    calc g * τ * g⁻¹ = g * σ ^ u * g⁻¹ := by rw [hu]
      _ = (g * σ * g⁻¹) ^ u := (hconjpow σ u).symm
      _ = σ ^ u := by rw [hgs]
      _ = τ := hu
  apply eq_of_smul_eq_smul (α := Ω)
  intro z
  obtain ⟨j, hj⟩ := hsurj z
  simp only at hj
  have hcj : g * σ ^ (j.val) * g⁻¹ = σ ^ (j.val) :=
    hcomm _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _)
  rw [one_smul, ← hj]
  calc g • σ ^ (j.val) • a
      = (g * σ ^ (j.val)) • a := by rw [mul_smul]
    _ = (g * σ ^ (j.val) * g⁻¹) • a := by
        rw [mul_smul (g * σ ^ (j.val)) g⁻¹, hga']
    _ = σ ^ (j.val) • a := by rw [hcj]

omit [Finite G] in
/-- Conjugation spreads from a generator to all its integer powers. -/
private theorem conj_zpow_eq (u x : G) (s : ℤ) :
    (u * x * u⁻¹) ^ s = u * x ^ s * u⁻¹ := by simp

omit [Finite G] [Finite Ω] [IsPretransitive G Ω] in
/-- An element centralizing the regular normal subgroup `⟨σ⟩` acts as one of its
elements, hence (by faithfulness) lies in it. -/
private theorem mem_zpowers_of_centralizes {σ : G}
    (hsurjAll : ∀ a : Ω, Function.Surjective (fun i : ZMod p => σ ^ (i.val) • a))
    (a : Ω) {u : G} (hcen : ∀ n ∈ Subgroup.zpowers σ, u * n * u⁻¹ = n) :
    u ∈ Subgroup.zpowers σ := by
  obtain ⟨s, hs⟩ := hsurjAll a (u • a)
  simp only at hs
  have hall : ∀ z : Ω, u • z = σ ^ (s.val) • z := by
    intro z
    obtain ⟨j, hj⟩ := hsurjAll a z
    simp only at hj
    have hc := hcen (σ ^ (j.val)) (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _)
    have hc' : u * σ ^ (j.val) = σ ^ (j.val) * u := by
      have h1 := congrArg (fun w => w * u) hc
      simpa [mul_assoc] using h1
    calc u • z = u • σ ^ (j.val) • a := by rw [hj]
      _ = (u * σ ^ (j.val)) • a := by rw [mul_smul]
      _ = (σ ^ (j.val) * u) • a := by rw [hc']
      _ = σ ^ (j.val) • u • a := by rw [mul_smul]
      _ = σ ^ (j.val) • σ ^ (s.val) • a := by rw [← hs]
      _ = σ ^ (s.val) • σ ^ (j.val) • a := by
          rw [smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm]
      _ = σ ^ (s.val) • z := by rw [hj]
  have hu : u = σ ^ (s.val) := eq_of_smul_eq_smul hall
  rw [hu]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _

/-- **No elementary abelian subgroup of order `4`** (2-rank one) for a faithful
transitive action of a group of order `p(p-1)` on `p` points, `p` an odd prime:
every involution inverts the regular normal `⟨σ⟩` (its conjugation exponent `k`
satisfies `k² ≡ 1`, and `k ≡ 1` would put the involution inside the odd-order
`⟨σ⟩`), so the product of two distinct commuting involutions centralizes `⟨σ⟩`
and dies the same way. -/
theorem not_exists_elementaryAbelian_four (hp : p.Prime) (hp2 : p ≠ 2)
    (hΩ : Nat.card Ω = p) (hG : Nat.card G = p * (p - 1)) :
    ¬ ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨E, hEcard, hEsq⟩
  obtain ⟨σ, hσ, hnorm, hfree, hsurjAll⟩ := exists_normal_regular hp hΩ hG
  obtain ⟨a⟩ : Nonempty Ω :=
    (Nat.card_ne_zero.mp (by rw [hΩ]; exact hp.pos.ne')).1
  -- `⟨σ⟩` has odd order, hence no involutions.
  have hNinv : ∀ n ∈ Subgroup.zpowers σ, n ^ 2 = 1 → n = 1 := by
    intro n hn h2
    have ho2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hop : orderOf n ∣ p := hσ ▸ orderOf_dvd_of_mem_zpowers hn
    have hg : Nat.gcd 2 p = 1 :=
      (Nat.coprime_primes Nat.prime_two hp).mpr (fun h => hp2 h.symm)
    have h3 := Nat.dvd_gcd ho2 hop
    rw [hg, Nat.dvd_one] at h3
    exact orderOf_eq_one_iff.mp h3
  -- every nonidentity element of `E` inverts `σ`.
  have hinv : ∀ u ∈ E, u ≠ 1 → u * σ * u⁻¹ = σ⁻¹ := by
    intro u hu hu1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (hnorm.conj_mem σ (Subgroup.mem_zpowers σ) u)
    have huu : u * u = 1 := by
      have := hEsq u hu
      rwa [pow_two] at this
    -- `u² = 1` forces `σ = σ^{k²}`.
    have hσk2 : (σ ^ k) ^ k = σ := by
      calc (σ ^ k) ^ k = (u * σ * u⁻¹) ^ k := by rw [hk]
        _ = u * σ ^ k * u⁻¹ := conj_zpow_eq u σ k
        _ = u * (u * σ * u⁻¹) * u⁻¹ := by rw [hk]
        _ = (u * u) * σ * ((u * u))⁻¹ := by group
        _ = σ := by rw [huu]; group
    have hdvd : (p : ℤ) ∣ k * k - 1 := by
      have h2 : σ ^ (k * k - 1) = 1 := by
        have h2a : σ ^ (k * k) = σ := by
          rw [zpow_mul]
          exact hσk2
        rw [zpow_sub, h2a, zpow_one, mul_inv_cancel]
      have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
      rwa [hσ] at h3
    have hfac : (p : ℤ) ∣ (k - 1) * (k + 1) := by
      have h4 : (k - 1) * (k + 1) = k * k - 1 := by ring
      rw [h4]
      exact hdvd
    rcases ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hfac) with hd | hd
    · -- `k ≡ 1`: `u` would centralize `⟨σ⟩` and be an involution inside it.
      exfalso
      have hσk : σ ^ k = σ := by
        have h4 : σ ^ (k - 1) = 1 :=
          orderOf_dvd_iff_zpow_eq_one.mp (by rw [hσ]; exact hd)
        calc σ ^ k = σ ^ (k - 1 + 1) := by congr 1; ring
          _ = σ ^ (k - 1) * σ := zpow_add_one σ (k - 1)
          _ = σ := by rw [h4, one_mul]
      have hcu : u * σ * u⁻¹ = σ := by rw [← hk, hσk]
      have hcen : ∀ n ∈ Subgroup.zpowers σ, u * n * u⁻¹ = n := by
        intro n hn
        obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hn
        calc u * n * u⁻¹ = u * σ ^ s * u⁻¹ := by rw [hs]
          _ = (u * σ * u⁻¹) ^ s := (conj_zpow_eq u σ s).symm
          _ = σ ^ s := by rw [hcu]
          _ = n := hs
      exact hu1 (hNinv u (mem_zpowers_of_centralizes hsurjAll a hcen)
        (hEsq u hu))
    · -- `k ≡ -1`: inversion.
      have h4 : σ ^ (k + 1) = 1 :=
        orderOf_dvd_iff_zpow_eq_one.mp (by rw [hσ]; exact hd)
      have h5 : σ ^ k = σ⁻¹ := by
        have h6 : σ ^ k * σ = 1 := by
          rw [← zpow_add_one]
          exact h4
        exact eq_inv_of_mul_eq_one_left h6
      rw [hk] at h5
      exact h5
  -- two distinct nonidentity elements of `E`.
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  haveI : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [hEcard]; norm_num)
  obtain ⟨u', hu'⟩ := exists_ne (1 : ↥E)
  obtain ⟨v', hv'1, hv'u⟩ : ∃ v' : ↥E, v' ≠ 1 ∧ v' ≠ u' := by
    by_contra hall
    push Not at hall
    have hle : Nat.card ↥E ≤ 2 := by
      have hsub : (Set.univ : Set ↥E) ⊆ {1, u'} := by
        intro x _
        by_cases hx : x = 1
        · exact Or.inl hx
        · exact Or.inr (hall x hx)
      calc Nat.card ↥E = (Set.univ : Set ↥E).ncard := (Set.ncard_univ _).symm
        _ ≤ ({1, u'} : Set ↥E).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
            have h1 := Set.ncard_insert_le (1 : ↥E) {u'}
            simpa [Set.ncard_singleton] using h1
    omega
  -- the product centralizes `σ`, is an involution, hence dies in `⟨σ⟩`.
  have huv1 : ((u' : G)) * ((v' : G)) ≠ 1 := by
    intro h0
    have h1 : (u' : G)⁻¹ = (v' : G) := inv_eq_of_mul_eq_one_right h0
    have huu : (u' : G) * (u' : G) = 1 := by
      have := hEsq _ u'.2
      rwa [pow_two] at this
    have h2 : (u' : G)⁻¹ = (u' : G) := inv_eq_of_mul_eq_one_right huu
    exact hv'u (Subtype.ext (h1.symm.trans h2))
  have hcuv : (u' : G) * (v' : G) * σ * ((u' : G) * (v' : G))⁻¹ = σ := by
    have h1 := hinv _ u'.2 (fun h0 => hu' (Subtype.ext h0))
    have h2 := hinv _ v'.2 (fun h0 => hv'1 (Subtype.ext h0))
    calc (u' : G) * (v' : G) * σ * ((u' : G) * (v' : G))⁻¹
        = (u' : G) * ((v' : G) * σ * (v' : G)⁻¹) * (u' : G)⁻¹ := by group
      _ = (u' : G) * σ⁻¹ * (u' : G)⁻¹ := by rw [h2]
      _ = ((u' : G) * σ * (u' : G)⁻¹)⁻¹ := by group
      _ = σ⁻¹⁻¹ := by rw [h1]
      _ = σ := inv_inv σ
  have hcen : ∀ n ∈ Subgroup.zpowers σ,
      (u' : G) * (v' : G) * n * ((u' : G) * (v' : G))⁻¹ = n := by
    intro n hn
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hn
    calc (u' : G) * (v' : G) * n * ((u' : G) * (v' : G))⁻¹
        = (u' : G) * (v' : G) * σ ^ s * ((u' : G) * (v' : G))⁻¹ := by rw [hs]
      _ = ((u' : G) * (v' : G) * σ * ((u' : G) * (v' : G))⁻¹) ^ s :=
          (conj_zpow_eq _ σ s).symm
      _ = σ ^ s := by rw [hcuv]
      _ = n := hs
  exact huv1 (hNinv _ (mem_zpowers_of_centralizes hsurjAll a hcen)
    (hEsq _ (mul_mem u'.2 v'.2)))

/-- **A faithful transitive action of a group of order `p(p-1)` on `p` points is
two-transitive** (indeed sharply so): two-point stabilizers are trivial, so the
`G`-orbit of a distinct pair exhausts all `p(p-1)` distinct pairs. -/
theorem isMultiplyPretransitive_of_card_eq_mul_pred (hp : p.Prime)
    (hΩ : Nat.card Ω = p) (hG : Nat.card G = p * (p - 1)) :
    IsMultiplyPretransitive G Ω 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [is_two_pretransitive_iff]
  intro a b c d hab hcd
  classical
  -- the orbit of `(a, b)` in the diagonal action covers all distinct pairs.
  have horb : MulAction.orbit G (a, b) = {q : Ω × Ω | q.1 ≠ q.2} := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro q ⟨g, rfl⟩
      simp only [Set.mem_setOf_eq]
      intro h
      exact hab (smul_left_cancel g h)
    · -- `|orbit| = |G| / |stab| = p(p-1) = |distinct pairs|`.
      have hstab : MulAction.stabilizer G (a, b) = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        rw [MulAction.mem_stabilizer_iff] at hg
        rw [Subgroup.mem_bot]
        exact eq_one_of_smul_eq_of_smul_eq hp hΩ hG hab
          (congrArg Prod.fst hg) (congrArg Prod.snd hg)
      have horbcard : (MulAction.orbit G (a, b)).ncard = p * (p - 1) := by
        rw [← Nat.card_coe_set_eq,
          Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G (a, b)), hstab, ← hG]
        exact Nat.card_congr (QuotientGroup.quotientBot.toEquiv)
      have hpairs : ({q : Ω × Ω | q.1 ≠ q.2}).ncard = p * (p - 1) := by
        have h1 : {q : Ω × Ω | q.1 ≠ q.2} = (Set.diagonal Ω)ᶜ := by
          ext q
          simp [Set.mem_diagonal_iff]
        have h2 : (Set.diagonal Ω).ncard = p := by
          rw [← hΩ]
          rw [← Nat.card_coe_set_eq]
          exact Nat.card_congr (Equiv.ofBijective (fun x : Ω => ⟨(x, x), rfl⟩)
            ⟨fun x y hxy => congrArg Prod.fst (Subtype.ext_iff.mp hxy),
              fun ⟨⟨x, y⟩, hq⟩ => ⟨x, Subtype.ext (Prod.ext_iff.mpr
                ⟨rfl, hq⟩)⟩⟩).symm
        have h3 : Nat.card (Ω × Ω) = p * p := by
          rw [Nat.card_prod, hΩ]
        have h4 := Set.ncard_add_ncard_compl (Set.diagonal Ω)
        rw [h2, h3] at h4
        rw [h1]
        have h5 : p * (p - 1) = p * p - p := by
          have := hp.one_lt
          rw [Nat.mul_sub, Nat.mul_one]
        omega
      rw [horbcard, hpairs]
    · exact Set.toFinite _
  have hmem : (c, d) ∈ MulAction.orbit G (a, b) := by
    rw [horb]
    exact hcd
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

end PrimeDegree

end OddOrder.GroupTheory
