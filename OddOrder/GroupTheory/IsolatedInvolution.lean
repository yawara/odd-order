/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow

/-!
# Isolated involutions: Navarro (7.8)

**Navarro, *Characters and Blocks of Finite Groups*, Lemma (7.8)** (p. 146): let `P` be a Sylow
`2`-subgroup of the finite group `G` and `u ∈ P` an involution.  The following are equivalent.

* `u` is the only `G`-conjugate of itself inside `P`;
* `⁅u, g⁆` has odd order for every `g ∈ G`.

This is the hypothesis of Glauberman's `Z*`-theorem (Navarro (7.9), issue 0186), in the two forms
its proof needs: the first is how the theorem is stated, the second is what passes to quotients
(the order of `⁅u, g⁆ N` divides the order of `⁅u, g⁆`).

## Note on the proof

Navarro proves the substantial direction through the dihedral group `D = ⟨u, v⟩` (`v = u^g`),
identifying `⟨uv⟩ = D'` and ruling out `2 ∣ |D'|`.  The proof below avoids dihedral structure
theory: if `w = u·u^g` had even order, write `|w| = 2^a·m` with `m` odd, put `c = w^m` (a
`2`-element) and conjugate `v` by `w^k` with `k = (m+1)/2`.  Because `v` inverts `w`, that
conjugate is exactly `c·u`, so `u` and the `G`-conjugate `c·u` of `u` both lie in the `2`-group
`⟨c⟩ ⊔ ⟨u⟩`; the hypothesis forces `c·u = u`, i.e. `c = 1`, contradicting `|c| = 2^a > 1`.

## Main results

* `OddOrder.GroupTheory.conj_eq_of_mem_pGroup` — the hypothesis upgraded from `P` to an arbitrary
  `2`-subgroup (Navarro's Step 5 of (7.9) as well)
* `OddOrder.GroupTheory.odd_orderOf_commutator_of_forall_conj_eq` — the substantial direction
* `OddOrder.GroupTheory.forall_conj_eq_iff_forall_odd_orderOf_commutator` — Navarro (7.8)
-/

open scoped Pointwise commutatorElement

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

section Isolated

variable (P : Sylow 2 G) {u : G}

/-- **Navarro's Step 5**: the isolation hypothesis, stated for the fixed Sylow `2`-subgroup `P`,
holds inside *every* `2`-subgroup.  Conjugating a `2`-subgroup `Q` into `P` by `y` sends both `u`
and `x u x⁻¹` into `P`, and the hypothesis applied twice identifies them. -/
theorem conj_eq_of_mem_pGroup
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hxQ : x * u * x⁻¹ ∈ Q) (huQ : u ∈ Q) :
    x * u * x⁻¹ = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSQ⟩ := hQ.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G S P
  have hmem : ∀ {z : G}, z ∈ Q → y * z * y⁻¹ ∈ (P : Subgroup G) := by
    intro z hz
    have hzS : z ∈ (S : Subgroup G) := hSQ hz
    have hsm : y * z * y⁻¹ ∈ (y • S : Sylow 2 G) := by
      refine Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr ?_
      simpa [smul_eq_mul, mul_assoc] using hzS
    rwa [hy] at hsm
  have h1 : y * u * y⁻¹ = u := hiso y (hmem huQ)
  have h2 : (y * x) * u * (y * x)⁻¹ = u := by
    refine hiso (y * x) ?_
    have hm := hmem hxQ
    rwa [show y * (x * u * x⁻¹) * y⁻¹ = (y * x) * u * (y * x)⁻¹ by group] at hm
  have h3 : y * (x * u * x⁻¹) * y⁻¹ = y * u * y⁻¹ := by
    rw [h1, show y * (x * u * x⁻¹) * y⁻¹ = (y * x) * u * (y * x)⁻¹ by group, h2]
  exact mul_left_cancel (mul_right_cancel h3)

include P in
/-- **Navarro (7.8), the substantial direction**: if `u` is the only `G`-conjugate of itself in
`P`, then `⁅u, g⁆` has odd order for every `g`. -/
theorem odd_orderOf_commutator_of_forall_conj_eq (hu2 : orderOf u = 2)
    (hiso : ∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u) (g : G) :
    Odd (orderOf ⁅u, g⁆) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2' : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, sq] at this
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2'
  set v : G := g * u * g⁻¹ with hvdef
  have hv2 : v * v = 1 := by
    rw [hvdef]
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2', mul_one, mul_inv_cancel]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  set w : G := u * v with hwdef
  have hcomm : ⁅u, g⁆ = w := by
    rw [commutatorElement_def, hwdef, hvdef, huinv]; group
  rw [hcomm]
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  -- both `u` and `v` invert `w`
  have hu_inv_w : u * w * u⁻¹ = w⁻¹ := by
    rw [hwdef, mul_inv_rev, hvinv, huinv]
    calc u * (u * v) * u = (u * u) * v * u := by group
      _ = v * u := by rw [hu2', one_mul]
  have hv_inv_w : v * w * v⁻¹ = w⁻¹ := by
    -- ⚠ `hvinv` must fire before `mul_inv_rev`: `v` is a `set` definition unfolding to a
    -- product, so `mul_inv_rev` would match `v⁻¹` first and expand it
    rw [hwdef, hvinv, mul_inv_rev, hvinv, huinv]
    calc v * (u * v) * v = v * u * (v * v) := by group
      _ = v * u := by rw [hv2, mul_one]
  set n : ℕ := orderOf w with hndef
  have hn0 : n ≠ 0 := (orderOf_pos w).ne'
  set m : ℕ := ordCompl[2] n with hmdef
  have hmodd : Odd m := by
    rw [Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd]
    exact Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hmdvd : m ∣ n := Nat.ordCompl_dvd n 2
  set c : G := w ^ m with hcdef
  have hcord : orderOf c = ordProj[2] n := by
    rw [hcdef, orderOf_pow, ← hndef, Nat.gcd_eq_right hmdvd, hmdef]
    exact (Nat.div_eq_of_eq_mul_left (Nat.ordCompl_pos 2 hn0)
      (Nat.ordProj_mul_ordCompl_eq_self n 2).symm)
  have hcne : c ≠ 1 := by
    intro h
    have h1 : ordProj[2] n = 1 := by rw [← hcord, h, orderOf_one]
    have h2 : 0 < n.factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 hodd
    have := Nat.one_lt_two_pow_iff.mpr h2.ne'
    omega
  -- `u` inverts `c` as well, hence normalises `⟨c⟩`
  have hu_inv_c : u * c * u⁻¹ = c⁻¹ := by
    have : (MulAut.conj u) (w ^ m) = ((MulAut.conj u) w) ^ m := map_pow _ _ _
    rw [hcdef]
    simpa [MulAut.conj_apply, hu_inv_w, inv_pow] using this
  have hun : u ∈ Subgroup.normalizer (Subgroup.zpowers c) := by
    have hconjzpow : ∀ j : ℤ, u * c ^ j * u⁻¹ = c ^ (-j) := by
      intro j
      have h := map_zpow (MulAut.conj u) c j
      simpa [MulAut.conj_apply, hu_inv_c, zpow_neg, inv_zpow] using h
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨-j, (hconjzpow j).symm⟩
    · rintro ⟨j, hj⟩
      refine ⟨-j, ?_⟩
      have hh := hconjzpow (-j)
      rw [neg_neg] at hh
      exact mul_left_cancel (mul_right_cancel (hh.trans hj))
  -- the `2`-group `⟨c⟩ ⊔ ⟨u⟩` contains `u` and the `G`-conjugate `c * u` of `u`
  have hupg : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hu2, pow_one]
  have hcpg : IsPGroup 2 (Subgroup.zpowers c) := by
    refine IsPGroup.of_card (n := n.factorization 2) ?_
    rw [Nat.card_zpowers, hcord]
  have hQ : IsPGroup 2 (Subgroup.zpowers c ⊔ Subgroup.zpowers u : Subgroup G) :=
    hcpg.to_sup_of_normal_left' hupg (Subgroup.zpowers_le.mpr hun)
  have huQ : u ∈ (Subgroup.zpowers c ⊔ Subgroup.zpowers u : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hcuQ : c * u ∈ (Subgroup.zpowers c ⊔ Subgroup.zpowers u : Subgroup G) :=
    mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) huQ
  -- conjugating `v` by `w ^ k` with `2 k = m + 1` lands on `c * u`
  set k : ℕ := (m + 1) / 2 with hkdef
  have h2k : 2 * k = m + 1 := by
    obtain ⟨j, hj⟩ := hmodd
    rw [hkdef, hj]; omega
  have hvwk : v * (w ^ k)⁻¹ = w ^ k * v := by
    have hpow : v * w ^ k * v⁻¹ = (w ^ k)⁻¹ := by
      have h := map_pow (MulAut.conj v) w k
      simpa [MulAut.conj_apply, hv_inv_w, inv_pow] using h
    have h2 := congrArg (fun z : G => z⁻¹) hpow
    simp only [mul_inv_rev, inv_inv] at h2
    have hinv : v * (w ^ k)⁻¹ * v⁻¹ = w ^ k := by
      calc v * (w ^ k)⁻¹ * v⁻¹ = v * ((w ^ k)⁻¹ * v⁻¹) := by group
        _ = w ^ k := h2
    calc v * (w ^ k)⁻¹ = (v * (w ^ k)⁻¹ * v⁻¹) * v := by group
      _ = w ^ k * v := by rw [hinv]
  have hconjv : w ^ k * v * (w ^ k)⁻¹ = c * u := by
    calc w ^ k * v * (w ^ k)⁻¹ = w ^ k * (v * (w ^ k)⁻¹) := by group
      _ = w ^ k * (w ^ k * v) := by rw [hvwk]
      _ = w ^ (2 * k) * v := by rw [two_mul, pow_add]; group
      _ = w ^ m * (w * v) := by rw [h2k, pow_succ]; group
      _ = c * u := by
          rw [hcdef, hwdef]
          calc w ^ m * (u * v * v) = w ^ m * (u * (v * v)) := by group
            _ = w ^ m * u := by rw [hv2, mul_one]
  have hconj : (w ^ k * g) * u * (w ^ k * g)⁻¹ = c * u := by
    rw [← hconjv, hvdef]; group
  have hfix := conj_eq_of_mem_pGroup P hiso hQ (x := w ^ k * g)
    (by rw [hconj]; exact hcuQ) huQ
  rw [hconj] at hfix
  exact hcne (mul_right_cancel (b := u) (by rw [one_mul]; exact hfix))

omit [Finite G] in
include P in
/-- **Navarro (7.8), the easy direction**: if `⁅u, g⁆` always has odd order then `u` is the only
`G`-conjugate of itself in `P`.  Indeed `⁅u, g⁆ = u · u^g` lies in `P` as soon as `u^g` does, and
an element of odd order in a `2`-group is trivial. -/
theorem forall_conj_eq_of_odd_orderOf_commutator (hu : u ∈ (P : Subgroup G))
    (hu2 : orderOf u = 2) (hodd : ∀ g : G, Odd (orderOf ⁅u, g⁆)) (g : G)
    (hg : g * u * g⁻¹ ∈ (P : Subgroup G)) : g * u * g⁻¹ = u := by
  have hu2' : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, sq] at this
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2'
  have hcomm : ⁅u, g⁆ = u * (g * u * g⁻¹) := by
    rw [commutatorElement_def, huinv]; group
  -- `⁅u, g⁆` lies in `P` and has odd order, so it is trivial
  have hmem : ⁅u, g⁆ ∈ (P : Subgroup G) := by rw [hcomm]; exact mul_mem hu hg
  have hone : ⁅u, g⁆ = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' (⟨⁅u, g⁆, hmem⟩ : (P : Subgroup G))
    have hdvd : orderOf ⁅u, g⁆ ∣ 2 ^ k := by
      have h := orderOf_dvd_of_pow_eq_one hk
      rwa [Subgroup.orderOf_mk] at h
    have hcop : Nat.Coprime (orderOf ⁅u, g⁆) (2 ^ k) :=
      (Nat.coprime_two_right.mpr (hodd g)).pow_right k
    have h1 : orderOf ⁅u, g⁆ = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    exact orderOf_eq_one_iff.mp h1
  rw [hcomm] at hone
  calc g * u * g⁻¹ = u * (u * (g * u * g⁻¹)) := by rw [← mul_assoc, hu2', one_mul]
    _ = u := by rw [hone, mul_one]

include P in
/-- **Navarro (7.8)**: for an involution `u` of a Sylow `2`-subgroup `P` of `G`, being the only
`G`-conjugate of itself inside `P` is the same as having `⁅u, g⁆` of odd order for every `g`. -/
theorem forall_conj_eq_iff_forall_odd_orderOf_commutator (hu : u ∈ (P : Subgroup G))
    (hu2 : orderOf u = 2) :
    (∀ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) → g * u * g⁻¹ = u)
      ↔ ∀ g : G, Odd (orderOf ⁅u, g⁆) :=
  ⟨fun hiso => odd_orderOf_commutator_of_forall_conj_eq P hu2 hiso,
   fun hodd => forall_conj_eq_of_odd_orderOf_commutator P hu hu2 hodd⟩

end Isolated

section ConjOfOddProduct

omit [Finite G] in
/-- **Two involutions whose product has odd order are conjugate**, by an explicit power of that
product: with `c = b·a` of odd order `m` and `k = (m+1)/2`, one has `c^k a c^{-k} = b`.

`a` inverts `c` (`a c a⁻¹ = a b a a⁻¹ = a b = c⁻¹`), so `c^k a c^{-k} = c^{2k} a = c^{m+1} a = c a
= b`.  Keeping the conjugator inside `⟨c⟩` matters: Navarro's (7.9) needs it to lie in a
prescribed subgroup, and `⟨c⟩ ≤ ⟨a, b⟩`.

This is the positive counterpart of `odd_orderOf_commutator_of_forall_conj_eq`, which rules out
*even* order by the same computation. -/
theorem conj_zpow_eq_of_odd_orderOf_mul {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (b * a))) :
    ((b * a) ^ ((orderOf (b * a) + 1) / 2)) * a * ((b * a) ^ ((orderOf (b * a) + 1) / 2))⁻¹
      = b := by
  set c : G := b * a with hc
  set m : ℕ := orderOf c with hm
  set k : ℕ := (m + 1) / 2 with hk
  have h2k : 2 * k = m + 1 := by
    obtain ⟨j, hj⟩ := hodd
    rw [hk, hj]; omega
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hcinv : a * c * a⁻¹ = c⁻¹ := by
    rw [hc, mul_inv_rev, hainv, hbinv]
    calc a * (b * a) * a = a * b * (a * a) := by group
      _ = a * b := by rw [ha, mul_one]
  -- `a` inverts every power of `c`
  have hpow : a * c ^ k * a⁻¹ = (c ^ k)⁻¹ := by
    have h := map_pow (MulAut.conj a) c k
    simpa [MulAut.conj_apply, hcinv, inv_pow] using h
  have hstep : a * (c ^ k)⁻¹ = c ^ k * a := by
    have h2 := congrArg (fun w : G => w⁻¹) hpow
    simp only [mul_inv_rev, inv_inv] at h2
    have hinv : a * (c ^ k)⁻¹ * a⁻¹ = c ^ k := by
      calc a * (c ^ k)⁻¹ * a⁻¹ = a * ((c ^ k)⁻¹ * a⁻¹) := by group
        _ = c ^ k := h2
    calc a * (c ^ k)⁻¹ = (a * (c ^ k)⁻¹ * a⁻¹) * a := by group
      _ = c ^ k * a := by rw [hinv]
  calc c ^ k * a * (c ^ k)⁻¹ = c ^ k * (a * (c ^ k)⁻¹) := by group
    _ = c ^ k * (c ^ k * a) := by rw [hstep]
    _ = c ^ (2 * k) * a := by rw [two_mul, pow_add]; group
    _ = c ^ m * (c * a) := by rw [h2k, pow_succ]; group
    _ = c * a := by rw [pow_orderOf_eq_one, one_mul]
    _ = b := by rw [hc]; calc b * a * a = b * (a * a) := by group
                  _ = b := by rw [ha, mul_one]

omit [Finite G] in
/-- The conjugator of `conj_zpow_eq_of_odd_orderOf_mul` lies in `⟨b·a⟩`. -/
theorem conj_zpow_mem_zpowers {a b : G} :
    ((b * a) ^ ((orderOf (b * a) + 1) / 2)) ∈ Subgroup.zpowers (b * a) :=
  pow_mem (Subgroup.mem_zpowers _) _

end ConjOfOddProduct

end OddOrder.GroupTheory
