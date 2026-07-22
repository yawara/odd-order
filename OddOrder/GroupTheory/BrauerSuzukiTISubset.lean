/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiNormalizer
import OddOrder.GroupTheory.TISubset

/-!
# Brauer–Suzuki: the TI-subset `A = C − RH` (Gorenstein Ch. 12, Lemma 1.3)

**Gorenstein, *Finite Groups*, Ch. 12, Lemma 1.3** (p. 374): in the
`QuaternionSylowSetup` (issue 9318), with `C = C_G(T)`, `N = N_G(T)`,
`H` the normal `2`-complement of `C` (`BrauerSuzukiNormalizer`), `R = ⟨x⁴⟩`,
and `RH = R ⊔ H`, the set

`A = C − RH`

is a **TI-subset** with normalizer-bound `N`: distinct `G`-conjugates of `A` are
disjoint and `N = N_G(A)`.

The mathematical heart is: **for every `a ∈ A`, `T ≤ ⟨a⟩`**.  Indeed the `2`-part
`a₂` of `a` is a `2`-element of `C`, so `⟨a₂⟩` lies in a Sylow `2`-subgroup of `C`,
i.e. a `C`-conjugate `cXc⁻¹` of the cyclic `X = ⟨x⟩`; the condition `a ∉ RH` forces
`|a₂| ≥ 2ⁿ⁻¹`, and `T` (central in `C`, hence `cTc⁻¹ = T`) is the unique subgroup of
order `2ⁿ⁻¹` of that cyclic group, so `T ≤ ⟨a₂⟩ ≤ ⟨a⟩`.  Since `⟨a⟩` is cyclic, `T`
is *the* unique subgroup of order `2ⁿ⁻¹` of `⟨a⟩` — a `G`-intrinsic invariant of `a`,
whence any `g` with `a, gag⁻¹ ∈ A` satisfies `T = g⁻¹Tg`, i.e. `g ∈ N`.

This feeds Lemma 1.4 (`inner_induce_eq_of_isTISubset`, the TI induction isometry).
-/

namespace OddOrder.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Generic cyclic-group helpers: the unique subgroup of each order -/

/-- In a finite group, a subgroup `H ≤ zpowers a` of cardinality `d` is exactly
`zpowers (a ^ (orderOf a / d))` — the unique subgroup of that order in the cyclic
group `⟨a⟩`. -/
theorem eq_zpowers_of_le_zpowers_of_card [Finite G] {a : G} {H : Subgroup G}
    (hH : H ≤ zpowers a) (d : ℕ) (hd : Nat.card H = d) :
    H = zpowers (a ^ (orderOf a / d)) := by
  have haord : 0 < orderOf a := orderOf_pos a
  have hdvdM : d ∣ orderOf a := by
    rw [← hd, ← Nat.card_zpowers a]; exact Subgroup.card_dvd_of_le hH
  obtain ⟨c, hc⟩ := hdvdM
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · rw [h0, Nat.zero_mul] at hc; omega
    · exact h
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h
    · rw [h0, Nat.mul_zero] at hc; omega
    · exact h
  have hMd : orderOf a / d = c := by rw [hc, Nat.mul_div_cancel_left _ hdpos]
  rw [hMd]
  have hcdvd : c ∣ orderOf a := ⟨d, by rw [hc]; ring⟩
  have hordc : orderOf (a ^ c) = d := by
    rw [orderOf_pow, Nat.gcd_eq_right hcdvd, hc, Nat.mul_div_assoc d (dvd_refl c),
      Nat.div_self hcpos, Nat.mul_one]
  have hcardc : Nat.card (zpowers (a ^ c)) = d := by rw [Nat.card_zpowers, hordc]
  have hle : H ≤ zpowers (a ^ c) := by
    intro h hh
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hH hh)
    subst hi
    have h2 : orderOf (a ^ i) = orderOf (⟨a ^ i, hh⟩ : H) :=
      orderOf_injective H.subtype H.subtype_injective ⟨a ^ i, hh⟩
    have hord_dvd : orderOf (a ^ i) ∣ d := by
      rw [← hd, h2]; exact orderOf_dvd_natCard _
    have hpow1 : (a ^ i) ^ (d : ℤ) = 1 := by
      have h3 : (a ^ i) ^ d = 1 := orderOf_dvd_iff_pow_eq_one.mp hord_dvd
      rwa [← zpow_natCast (a ^ i) d] at h3
    rw [← zpow_mul] at hpow1
    have hMdvd : (orderOf a : ℤ) ∣ i * d := orderOf_dvd_iff_zpow_eq_one.mpr hpow1
    have hcdvd_i : (c : ℤ) ∣ i := by
      have hc' : (orderOf a : ℤ) = d * c := by rw [hc]; push_cast; ring
      rw [hc'] at hMdvd
      have h4 : (d : ℤ) * c ∣ d * i := by rwa [mul_comm i (d : ℤ)] at hMdvd
      exact (mul_dvd_mul_iff_left (by exact_mod_cast (by omega : d ≠ 0) : (d : ℤ) ≠ 0)).mp h4
    obtain ⟨j, rfl⟩ := hcdvd_i
    refine ⟨j, ?_⟩
    change (a ^ c) ^ j = a ^ ((c : ℤ) * j)
    rw [← zpow_natCast a c, ← zpow_mul]
  exact eq_of_le_of_card_ge hle (by rw [hcardc, hd])

/-- Two subgroups of the cyclic group `⟨a⟩` with the same cardinality are equal. -/
theorem eq_of_le_zpowers_of_card_eq [Finite G] {a : G} {H K : Subgroup G}
    (hH : H ≤ zpowers a) (hK : K ≤ zpowers a) (hcard : Nat.card H = Nat.card K) : H = K := by
  rw [eq_zpowers_of_le_zpowers_of_card hH (Nat.card H) rfl,
    eq_zpowers_of_le_zpowers_of_card hK (Nat.card K) rfl, hcard]

/-- Two elements of `zpowers a` with the same order generate the same cyclic subgroup
(unique subgroup of each order in a cyclic group). -/
theorem zpowers_eq_of_mem_of_orderOf_eq [Finite G] {a u v : G}
    (hu : u ∈ zpowers a) (hv : v ∈ zpowers a) (h : orderOf u = orderOf v) :
    zpowers u = zpowers v :=
  eq_of_le_zpowers_of_card_eq (zpowers_le.mpr hu) (zpowers_le.mpr hv)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, h])

/-- Nested subgroups of a cyclic group: if `A, B ≤ ⟨g⟩` and `|A| ∣ |B|`, then `A ≤ B`
(subgroups of a finite cyclic group are totally ordered by their orders). -/
theorem le_of_le_zpowers_of_card_dvd [Finite G] {g : G} {A B : Subgroup G}
    (hA : A ≤ zpowers g) (hB : B ≤ zpowers g) (hdvd : Nat.card A ∣ Nat.card B) : A ≤ B := by
  have hcardA_pos : 0 < Nat.card A := Nat.card_pos
  have hcardB_pos : 0 < Nat.card B := Nat.card_pos
  have hBM : Nat.card B ∣ orderOf g := by
    rw [← Nat.card_zpowers g]; exact Subgroup.card_dvd_of_le hB
  rw [eq_zpowers_of_le_zpowers_of_card hA (Nat.card A) rfl,
    eq_zpowers_of_le_zpowers_of_card hB (Nat.card B) rfl, zpowers_le]
  set M := orderOf g with hMdef
  obtain ⟨r, hr⟩ := hdvd   -- Nat.card B = Nat.card A * r
  obtain ⟨s, hs⟩ := hBM    -- M = Nat.card B * s
  have hMdivB : M / Nat.card B = s := by rw [hs, Nat.mul_div_cancel_left _ hcardB_pos]
  have hBdivA : Nat.card B / Nat.card A = r := by rw [hr, Nat.mul_div_cancel_left _ hcardA_pos]
  have hMdivA : M / Nat.card A = r * s := by
    rw [hs, hr, mul_assoc, Nat.mul_div_cancel_left _ hcardA_pos]
  refine ⟨(Nat.card B / Nat.card A : ℕ), ?_⟩
  change (g ^ (M / Nat.card B)) ^ ((Nat.card B / Nat.card A : ℕ) : ℤ) = g ^ (M / Nat.card A)
  rw [hMdivB, hBdivA, hMdivA]
  rw [← zpow_natCast g s, ← zpow_mul, ← Nat.cast_mul, ← zpow_natCast g (r * s)]
  congr 1
  push_cast
  ring

namespace QuaternionSylowSetup

variable {G : Type*} [Group G] [Finite G] (Q : QuaternionSylowSetup G)

/-! ### `R`, `T` central in `C`; the subgroup `RH` and the set `A` -/

/-- `R ≤ T`: `x⁴ = (x²)² ∈ ⟨x²⟩ = T`. -/
theorem R_le_T : Q.R ≤ Q.T := by
  intro g hg
  obtain ⟨m, rfl⟩ := Q.mem_R_iff.mp hg
  exact Q.mem_T_iff.mpr ⟨2 * m, by congr 1; ring⟩

/-- `T ≤ X`. -/
theorem T_le_X : Q.T ≤ Q.X := by
  intro g hg
  obtain ⟨m, rfl⟩ := Q.mem_T_iff.mp hg
  exact Q.mem_X_iff.mpr ⟨2 * m, rfl⟩

/-- `T ≤ C`. -/
theorem T_le_C : Q.T ≤ Q.C := Q.T_le_X.trans Q.X_le_C

/-- `R ≤ C`. -/
theorem R_le_C : Q.R ≤ Q.C := Q.R_le_T.trans Q.T_le_C

/-- `R ≤ X`: `x⁴ = (x)⁴ ∈ ⟨x⟩ = X`. -/
theorem R_le_X : Q.R ≤ Q.X := by
  intro g hg
  obtain ⟨m, rfl⟩ := Q.mem_R_iff.mp hg
  exact Q.mem_X_iff.mpr ⟨4 * m, rfl⟩

/-- Every element of `C` centralizes every element of `T` (`T ≤ Z(C)`). -/
theorem C_centralizes_T {c t : G} (hc : c ∈ Q.C) (ht : t ∈ Q.T) : c * t * c⁻¹ = t := by
  rw [C, mem_centralizer_iff] at hc
  have := hc t ht
  rw [← this, mul_inv_cancel_right]

/-- `c ∈ C` fixes `x²` under conjugation. -/
theorem conj_x_sq (c : G) (hc : c ∈ Q.C) : c * Q.x ^ (2 : ℕ) * c⁻¹ = Q.x ^ (2 : ℕ) :=
  Q.C_centralizes_T hc (mem_zpowers _)

/-- `c ∈ C` fixes `x⁴` under conjugation. -/
theorem conj_x_pow4 (c : G) (hc : c ∈ Q.C) : c * Q.x ^ (4 : ℕ) * c⁻¹ = Q.x ^ (4 : ℕ) :=
  Q.C_centralizes_T hc (Q.R_le_T (mem_zpowers _))

/-- `RH = R ⊔ H`. -/
noncomputable def RH : Subgroup G := Q.R ⊔ Q.H

/-- `A = C − RH`, the TI-subset of Lemma 1.3. -/
def A : Set G := (Q.C : Set G) \ (Q.RH : Set G)

theorem R_le_RH : Q.R ≤ Q.RH := le_sup_left
theorem H_le_RH : Q.H ≤ Q.RH := le_sup_right
theorem RH_le_C : Q.RH ≤ Q.C := sup_le Q.R_le_C Q.H_le_C

/-- `|R| = 2ⁿ⁻²`. -/
theorem card_R : Nat.card Q.R = 2 ^ (Q.n - 2) := by
  have hle : 2 ≤ Q.n := by have := Q.hn; omega
  rw [R, Nat.card_zpowers, orderOf_pow, Q.hx_order, show (4 : ℕ) = 2 ^ 2 from by norm_num,
    Nat.gcd_eq_right (pow_dvd_pow 2 hle), Nat.pow_div hle (by norm_num)]

/-- `orderOf (x²) = 2ⁿ⁻¹`. -/
theorem orderOf_x_sq : orderOf (Q.x ^ (2 : ℕ)) = 2 ^ (Q.n - 1) := by
  rw [← Nat.card_zpowers]; exact Q.card_T

/-! ### The Sylow lemma: a `2`-element of `C` lies in a `C`-conjugate of `X` -/

/-- **A `2`-element `w` of `C` lies in a `C`-conjugate of the cyclic group `X`**
(Sylow): there is `c ∈ C` with `⟨w⟩ ≤ ⟨c·x·c⁻¹⟩`.  Proof: `X` is a Sylow
`2`-subgroup of `C` (`exists_sylow_C_eq`); the `2`-group `⟨w⟩` lies in some Sylow
`2`-subgroup, which is `C`-conjugate to `X`. -/
theorem exists_conj_X_ge {w : G} (hwC : w ∈ Q.C) {k : ℕ} (hk : orderOf w = 2 ^ k) :
    ∃ c ∈ Q.C, Subgroup.zpowers w ≤ Subgroup.zpowers (c * Q.x * c⁻¹) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Q.exists_sylow_C_eq
  set w' : ↥Q.C := ⟨w, hwC⟩ with hw'def
  have hordw' : orderOf w' = 2 ^ k := by
    rw [← orderOf_injective Q.C.subtype Q.C.subtype_injective w']; exact hk
  have hpg : IsPGroup 2 (Subgroup.zpowers w') := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers, hordw']
  obtain ⟨Q', hQ'⟩ := hpg.exists_le_sylow
  obtain ⟨c', hc'⟩ := MulAction.exists_smul_eq (↥Q.C) P Q'
  refine ⟨(c' : G), c'.2, ?_⟩
  intro g hg
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hgC : g ∈ Q.C := by rw [← hj]; exact zpow_mem hwC j
  set g' : ↥Q.C := ⟨g, hgC⟩ with hg'def
  have hg'zp : g' ∈ Subgroup.zpowers w' :=
    ⟨j, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hj)⟩
  have hg'Q' : g' ∈ (Q' : Subgroup ↥Q.C) := hQ' hg'zp
  rw [← hc', Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP,
    mem_subgroupOf] at hg'Q'
  -- `hg'Q' : ↑((MulAut.conj c')⁻¹ • g') ∈ X`, i.e. `c'⁻¹ * g * c' ∈ X`
  have hcoe : (((MulAut.conj c')⁻¹ • g' : ↥Q.C) : G) = (c' : G)⁻¹ * g * (c' : G) := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
    simp [hg'def]
  rw [hcoe] at hg'Q'
  obtain ⟨t, ht⟩ := Q.mem_X_iff.mp hg'Q'  -- ht : (c')⁻¹ g c' = x ^ t
  refine ⟨t, ?_⟩
  change ((c' : G) * Q.x * (c' : G)⁻¹) ^ t = g
  rw [conj_zpow, ← ht]; group

/-! ### The `2`-element dichotomy inside `C` -/

/-- A `2`-element `w ∈ C` of order `≥ 2ⁿ⁻¹` contains `T` in its cyclic span. -/
theorem T_le_zpowers_of_two_element {w : G} (hwC : w ∈ Q.C) {k : ℕ}
    (hk : orderOf w = 2 ^ k) (hge : Q.n - 1 ≤ k) : Q.T ≤ Subgroup.zpowers w := by
  obtain ⟨c, hcC, hle⟩ := Q.exists_conj_X_ge hwC hk
  set cx := c * Q.x * c⁻¹ with hcx
  -- `T ≤ ⟨cx⟩` (since `cx² = c x² c⁻¹ = x²` and `T = ⟨x²⟩`)
  have hTcx : Q.T ≤ Subgroup.zpowers cx := by
    rw [T]
    refine zpowers_le.mpr ?_
    have hcx2 : cx ^ (2 : ℕ) = Q.x ^ (2 : ℕ) := by
      have hc : cx = MulAut.conj c Q.x := by rw [hcx, MulAut.conj_apply]
      rw [hc, ← map_pow, MulAut.conj_apply, Q.conj_x_sq c hcC]
    rw [← hcx2]
    exact pow_mem (mem_zpowers cx) 2
  refine le_of_le_zpowers_of_card_dvd hTcx hle ?_
  rw [Q.card_T, Nat.card_zpowers, hk]
  exact pow_dvd_pow 2 hge

/-- A `2`-element `w ∈ C` of order `≤ 2ⁿ⁻²` lies in `R`. -/
theorem mem_R_of_two_element {w : G} (hwC : w ∈ Q.C) {k : ℕ}
    (hk : orderOf w = 2 ^ k) (hle : k ≤ Q.n - 2) : w ∈ Q.R := by
  obtain ⟨c, hcC, hlecx⟩ := Q.exists_conj_X_ge hwC hk
  set cx := c * Q.x * c⁻¹ with hcx
  have hRcx : Q.R ≤ Subgroup.zpowers cx := by
    rw [R]
    refine zpowers_le.mpr ?_
    have hcx4 : cx ^ (4 : ℕ) = Q.x ^ (4 : ℕ) := by
      have hc : cx = MulAut.conj c Q.x := by rw [hcx, MulAut.conj_apply]
      rw [hc, ← map_pow, MulAut.conj_apply, Q.conj_x_pow4 c hcC]
    rw [← hcx4]
    exact pow_mem (mem_zpowers cx) 4
  have : Subgroup.zpowers w ≤ Q.R :=
    le_of_le_zpowers_of_card_dvd hlecx hRcx (by
      rw [Nat.card_zpowers, hk, Q.card_R]; exact pow_dvd_pow 2 hle)
  exact this (mem_zpowers w)

/-! ### The key lemma: `a ∈ A ⟹ T ≤ ⟨a⟩` -/

/-- **The heart of Lemma 1.3**: for `a ∈ A = C − RH`, `T ≤ ⟨a⟩`. -/
theorem T_le_zpowers_of_mem_A {a : G} (ha : a ∈ Q.A) : Q.T ≤ Subgroup.zpowers a := by
  obtain ⟨haC, haRH⟩ := ha
  -- the `2`-part `a₂ = a ^ mm` and `2'`-part `a₂' = a ^ (2^v)`
  set M := orderOf a with hM
  have hMpos : 0 < M := orderOf_pos a
  set v := M.factorization 2 with hv
  set mm := M / 2 ^ v with hmm
  have hmm_dvd : mm ∣ M := Nat.ordCompl_dvd M 2
  have h2v_dvd : 2 ^ v ∣ M := Nat.ordProj_dvd M 2
  have hmm_odd : ¬ 2 ∣ mm := Nat.not_dvd_ordCompl Nat.prime_two hMpos.ne'
  have hsplit : 2 ^ v * mm = M := Nat.ordProj_mul_ordCompl_eq_self M 2
  set a2 : G := a ^ mm with ha2
  set a2' : G := a ^ (2 ^ v) with ha2'
  have ha2C : a2 ∈ Q.C := pow_mem haC mm
  have ha2'C : a2' ∈ Q.C := pow_mem haC (2 ^ v)
  -- orders
  have horda2 : orderOf a2 = 2 ^ v := by
    rw [ha2, orderOf_pow, ← hM, Nat.gcd_eq_right hmm_dvd]
    conv_lhs => rw [← hsplit]
    rw [Nat.mul_div_assoc _ (dvd_refl mm), Nat.div_self (by
      rcases Nat.eq_zero_or_pos mm with h0 | h; · rw [h0] at hmm_odd; simp at hmm_odd
      · exact h), Nat.mul_one]
  have horda2' : orderOf a2' = mm := by
    rw [ha2', orderOf_pow, ← hM, Nat.gcd_eq_right h2v_dvd]
  -- a₂' ∈ H (odd order element of C)
  have ha2'H : a2' ∈ Q.H := by
    refine Q.mem_H_iff.mpr ⟨ha2'C, ?_⟩
    rw [horda2', Nat.odd_iff]
    omega
  -- claim: v ≥ n - 1 (else a ∈ RH)
  have hvge : Q.n - 1 ≤ v := by
    by_contra hlt
    -- v ≤ n - 2, so a₂ ∈ R
    have hvle : v ≤ Q.n - 2 := by have := Q.hn; omega
    have ha2R : a2 ∈ Q.R := Q.mem_R_of_two_element ha2C horda2 hvle
    -- a = a₂^α * a₂'^β ∈ R ⊔ H = RH  (Bézout, since gcd(mm, 2^v) = 1)
    have hcop : Nat.Coprime mm (2 ^ v) := by
      rw [Nat.coprime_comm]
      exact (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.not_even_iff.mp
        (fun h => hmm_odd h.two_dvd)))).pow_left v
    have hbez : (mm : ℤ) * Nat.gcdA mm (2 ^ v) + ((2 ^ v : ℕ) : ℤ) * Nat.gcdB mm (2 ^ v) = 1 := by
      have h := Nat.gcd_eq_gcd_ab mm (2 ^ v)
      rw [hcop, Nat.cast_one] at h
      linarith [h]
    have ha_eq : a = a2 ^ (Nat.gcdA mm (2 ^ v)) * a2' ^ (Nat.gcdB mm (2 ^ v)) := by
      rw [ha2, ha2', ← zpow_natCast a mm, ← zpow_natCast a (2 ^ v), ← zpow_mul, ← zpow_mul,
        ← zpow_add, hbez, zpow_one]
    have haRH' : a ∈ Q.RH := by
      rw [ha_eq]
      exact Subgroup.mul_mem _
        (Q.R_le_RH (zpow_mem ha2R _))
        (Q.H_le_RH (zpow_mem ha2'H _))
    exact haRH haRH'
  -- T ≤ ⟨a₂⟩ ≤ ⟨a⟩
  have hTa2 : Q.T ≤ Subgroup.zpowers a2 := Q.T_le_zpowers_of_two_element ha2C horda2 hvge
  refine hTa2.trans ?_
  rw [zpowers_le]
  exact ha2 ▸ pow_mem (mem_zpowers a) mm

/-- **Every element of `A = C − RH` has order divisible by `4`.**  From `a ∈ A` we get
`T ≤ ⟨a⟩` (`T_le_zpowers_of_mem_A`), hence `|T| = 2ⁿ⁻¹ ∣ orderOf a`, and `4 = 2² ∣ 2ⁿ⁻¹`
because `n ≥ 3`.  In particular no element of `A` is an involution or has odd order — the
key group-theoretic input to Gorenstein Lemma 1.6 (`θ*` vanishes on involutions and
odd-order elements, since these cannot be conjugate into `A`). -/
theorem four_dvd_orderOf_of_mem_A {a : G} (ha : a ∈ Q.A) : 4 ∣ orderOf a := by
  have hTa : Q.T ≤ Subgroup.zpowers a := Q.T_le_zpowers_of_mem_A ha
  have hdvd : Nat.card ↥Q.T ∣ orderOf a := by
    rw [← Nat.card_zpowers (a := a)]
    exact Subgroup.card_dvd_of_le hTa
  rw [Q.card_T] at hdvd
  refine dvd_trans ?_ hdvd
  rw [show (4 : ℕ) = 2 ^ 2 from rfl]
  exact pow_dvd_pow 2 (by have := Q.hn; omega)

/-! ### Lemma 1.3: `A` is a TI-subset with normalizer-bound `N` -/

/-- **Gorenstein Lemma 1.3 (TI part)**: `A = C − RH` is a TI-subset with
normalizer-bound `N`.  If `a, g·a·g⁻¹ ∈ A`, then `T ≤ ⟨a⟩` and `T ≤ ⟨gag⁻¹⟩`, so
`x²` and `g⁻¹x²g` are two elements of order `2ⁿ⁻¹` of the cyclic group `⟨a⟩`; hence
they generate the same subgroup `T`, forcing `g⁻¹Tg = T`, i.e. `g ∈ N`. -/
theorem A_isTISubset : IsTISubset Q.A Q.N := by
  intro g ⟨a, ha, hga⟩
  have hTa : Q.T ≤ Subgroup.zpowers a := Q.T_le_zpowers_of_mem_A ha
  have hTb : Q.T ≤ Subgroup.zpowers (g * a * g⁻¹) := Q.T_le_zpowers_of_mem_A hga
  -- `x² ∈ ⟨a⟩` and `g⁻¹x²g ∈ ⟨a⟩`
  have hx2a : Q.x ^ (2 : ℕ) ∈ Subgroup.zpowers a := hTa (mem_zpowers _)
  have hx2b : Q.x ^ (2 : ℕ) ∈ Subgroup.zpowers (g * a * g⁻¹) := hTb (mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx2b  -- (gag⁻¹)^k = x²
  have hconj_mem : g⁻¹ * Q.x ^ (2 : ℕ) * g ∈ Subgroup.zpowers a := by
    refine ⟨k, ?_⟩
    rw [← hk, conj_zpow]; group
  -- both `x²` and `g⁻¹x²g` have order `2ⁿ⁻¹` and lie in `⟨a⟩`
  have hordeq : orderOf (Q.x ^ (2 : ℕ)) = orderOf (g⁻¹ * Q.x ^ (2 : ℕ) * g) := by
    rw [show g⁻¹ * Q.x ^ (2 : ℕ) * g = (MulAut.conj g⁻¹) (Q.x ^ (2 : ℕ)) from by
      rw [MulAut.conj_apply, inv_inv]]
    exact (orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective _).symm
  have heq : Subgroup.zpowers (Q.x ^ (2 : ℕ)) = Subgroup.zpowers (g⁻¹ * Q.x ^ (2 : ℕ) * g) :=
    zpowers_eq_of_mem_of_orderOf_eq hx2a hconj_mem hordeq
  -- conclude `g ∈ N = normalizer T` via the conjugate-equality criterion for the normalizer
  have hmapeq : Q.T.map (MulAut.conj g) = Q.T := by
    change (Subgroup.zpowers (Q.x ^ (2 : ℕ))).map (MulAut.conj g) = Subgroup.zpowers (Q.x ^ (2 : ℕ))
    conv_lhs => rw [heq]
    rw [MonoidHom.map_zpowers]
    congr 1
    change (MulAut.conj g) (g⁻¹ * Q.x ^ (2 : ℕ) * g) = Q.x ^ (2 : ℕ)
    rw [MulAut.conj_apply]; group
  rw [N, mem_normalizer_iff_map_conj_eq]
  exact hmapeq

/-! ### `N` normalizes `A` (Lemma 1.3, the `N ≤ N_G(A)` direction) -/

/-- Conjugation by `N` preserves `T` (`N = N_G(T)`). -/
theorem conj_mem_T_of_mem_N {n t : G} (hn : n ∈ Q.N) (ht : t ∈ Q.T) : n * t * n⁻¹ ∈ Q.T := by
  rw [N, Subgroup.mem_normalizer_iff] at hn
  exact (hn t).mp ht

/-- **`N` normalizes `R`** (Gorenstein p. 374): `R` is the unique subgroup of order `2ⁿ⁻²`
of the cyclic group `T = ⟨x²⟩`, and `N` normalizes `T`, so `n·R·n⁻¹ = R`. -/
theorem map_R_conj_of_mem_N {n : G} (hn : n ∈ Q.N) : Q.R.map (MulAut.conj n) = Q.R := by
  refine eq_of_le_zpowers_of_card_eq (a := Q.x ^ (2 : ℕ)) ?_ Q.R_le_T ?_
  · rintro _ ⟨r, hr, rfl⟩
    change n * r * n⁻¹ ∈ Q.T
    exact Q.conj_mem_T_of_mem_N hn (Q.R_le_T hr)
  · exact Nat.card_congr
      (Subgroup.equivMapOfInjective Q.R _ (MulAut.conj n).injective).symm.toEquiv

/-- **`N` normalizes `H`** (`H ⊴ N`, group-of-conjugates form). -/
theorem map_H_conj_of_mem_N {n : G} (hn : n ∈ Q.N) : Q.H.map (MulAut.conj n) = Q.H := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    change n * h * n⁻¹ ∈ Q.H
    exact Q.conj_mem_H_of_mem_N hn hh
  · intro h hh
    refine ⟨n⁻¹ * h * n⁻¹⁻¹, Q.conj_mem_H_of_mem_N (inv_mem hn) hh, ?_⟩
    change n * (n⁻¹ * h * n⁻¹⁻¹) * n⁻¹ = h
    group

/-- **`N` normalizes `RH`** (Gorenstein p. 374): `RH = R ⊔ H` with `R, H` both `N`-invariant. -/
theorem map_RH_conj_of_mem_N {n : G} (hn : n ∈ Q.N) : Q.RH.map (MulAut.conj n) = Q.RH := by
  rw [RH, Subgroup.map_sup, Q.map_R_conj_of_mem_N hn, Q.map_H_conj_of_mem_N hn]

theorem conj_mem_RH_of_mem_N {n w : G} (hn : n ∈ Q.N) (hw : w ∈ Q.RH) : n * w * n⁻¹ ∈ Q.RH := by
  have h : n * w * n⁻¹ ∈ Q.RH.map (MulAut.conj n) := ⟨w, hw, rfl⟩
  rwa [Q.map_RH_conj_of_mem_N hn] at h

/-- **Gorenstein Lemma 1.3 (`N ≤ N_G(A)`)**: `N` normalizes `A = C − RH`, since it
normalizes both `C` and `RH`. -/
theorem conj_mem_A_of_mem_N {n a : G} (hn : n ∈ Q.N) (ha : a ∈ Q.A) : n * a * n⁻¹ ∈ Q.A := by
  obtain ⟨haC, haRH⟩ := ha
  refine ⟨Q.conj_mem_C_of_mem_N hn haC, ?_⟩
  intro hmem
  refine haRH ?_
  have h := Q.conj_mem_RH_of_mem_N (inv_mem hn) hmem
  rwa [show n⁻¹ * (n * a * n⁻¹) * (n⁻¹)⁻¹ = a from by group] at h

/-! ### The product structure of `RH`, `A ≠ ∅`, and `N_G(A) ≤ N` (completing `N = N_G(A)`) -/

/-- `R` centralizes `H`: `R ≤ T ≤ Z(C)` and `H ≤ C`. -/
theorem R_centralizes_H {r h : G} (hr : r ∈ Q.R) (hh : h ∈ Q.H) : r * h = h * r := by
  have h1 : h * r * h⁻¹ = r := Q.C_centralizes_T (Q.H_le_C hh) (Q.R_le_T hr)
  calc r * h = (h * r * h⁻¹) * h := by rw [h1]
    _ = h * r := by group

/-- **The product structure of `RH`** (Gorenstein p. 374): since `R` is central in `C`
(so commutes with `H`), `RH = R ⊔ H` is the pointwise product `R · H`. -/
theorem mem_RH_iff {g : G} : g ∈ Q.RH ↔ ∃ r ∈ Q.R, ∃ h ∈ Q.H, g = r * h := by
  constructor
  · intro hg
    let S₀ : Subgroup G :=
      { carrier := {g | ∃ r ∈ Q.R, ∃ h ∈ Q.H, g = r * h}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, (one_mul 1).symm⟩
        mul_mem' := by
          rintro a b ⟨r₁, hr₁, h₁, hh₁, rfl⟩ ⟨r₂, hr₂, h₂, hh₂, rfl⟩
          refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, h₁ * h₂, mul_mem hh₁ hh₂, ?_⟩
          have hcomm : h₁ * r₂ = r₂ * h₁ := (Q.R_centralizes_H hr₂ hh₁).symm
          calc r₁ * h₁ * (r₂ * h₂) = r₁ * (h₁ * r₂) * h₂ := by group
            _ = r₁ * (r₂ * h₁) * h₂ := by rw [hcomm]
            _ = r₁ * r₂ * (h₁ * h₂) := by group
        inv_mem' := by
          rintro a ⟨r, hr, h, hh, rfl⟩
          refine ⟨r⁻¹, inv_mem hr, h⁻¹, inv_mem hh, ?_⟩
          rw [mul_inv_rev, Q.R_centralizes_H (inv_mem hr) (inv_mem hh)] }
    have hle : Q.RH ≤ S₀ := by
      rw [RH, sup_le_iff]
      exact ⟨fun r hr => ⟨r, hr, 1, one_mem _, (mul_one r).symm⟩,
        fun h hh => ⟨1, one_mem _, h, hh, (one_mul h).symm⟩⟩
    exact hle hg
  · rintro ⟨r, hr, h, hh, rfl⟩
    exact mul_mem (Q.R_le_RH hr) (Q.H_le_RH hh)

/-- `X ⊓ H = ⊥`: `X` is a `2`-group, `H` has odd order. -/
theorem X_inf_H_eq_bot : Q.X ⊓ Q.H = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgX, hgH⟩
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
  have hodd : Odd (orderOf g) := (Q.mem_H_iff.mp hgH).2
  have hdvd : orderOf g ∣ 2 ^ Q.n := Q.hx_order ▸ orderOf_dvd_of_mem_zpowers hgX
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hj] at hodd ⊢
  rcases Nat.eq_zero_or_pos j with hj0 | hpos
  · rw [hj0, pow_zero]
  · exfalso
    have hdvd2 : (2 : ℕ) ∣ 2 ^ j := dvd_pow_self 2 hpos.ne'
    rw [Nat.odd_iff] at hodd
    omega

/-- `x^k ∈ RH ⟹ x^k ∈ R` (elements of `X ∩ RH` lie in `R`, since `RH = R·H`, `X ⊓ H = ⊥`). -/
theorem mem_R_of_mem_X_of_mem_RH {k : ℤ} (hmem : Q.x ^ k ∈ Q.RH) : Q.x ^ k ∈ Q.R := by
  obtain ⟨r, hr, h, hh, heq⟩ := Q.mem_RH_iff.mp hmem
  have hhX : h ∈ Q.X := by
    have he : h = r⁻¹ * Q.x ^ k := by rw [heq]; group
    rw [he]
    exact mul_mem (inv_mem (Q.R_le_X hr)) (Q.mem_X_iff.mpr ⟨k, rfl⟩)
  have hh1 : h = 1 := by
    have hmemInf : h ∈ Q.X ⊓ Q.H := ⟨hhX, hh⟩
    rw [Q.X_inf_H_eq_bot, Subgroup.mem_bot] at hmemInf
    exact hmemInf
  rw [heq, hh1, mul_one]
  exact hr

/-- **`x ∉ RH`** (`orderOf x = 2ⁿ` but `R = ⟨x⁴⟩` has order `2ⁿ⁻²`). -/
theorem x_notMem_RH : Q.x ∉ Q.RH := by
  intro hx
  have hxR : Q.x ∈ Q.R := by
    have h := Q.mem_R_of_mem_X_of_mem_RH (k := 1) (by rwa [zpow_one])
    rwa [zpow_one] at h
  have hdvd : orderOf Q.x ∣ Nat.card Q.R := by
    have h1 := orderOf_dvd_natCard (⟨Q.x, hxR⟩ : Q.R)
    rwa [← orderOf_injective Q.R.subtype Q.R.subtype_injective ⟨Q.x, hxR⟩] at h1
  rw [Q.hx_order, Q.card_R] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h2 : (2 : ℕ) ^ (Q.n - 2) < 2 ^ Q.n :=
    Nat.pow_lt_pow_right one_lt_two (by have := Q.hn; omega)
  omega

/-- **`A = C − RH` is nonempty** (`x ∈ A`). -/
theorem A_nonempty : Q.A.Nonempty :=
  ⟨Q.x, Q.x_mem_C, Q.x_notMem_RH⟩

/-- **Gorenstein Lemma 1.3 (`N_G(A) ≤ N`)**: any `g` normalizing the set `A` lies in `N`.
Since `A ≠ ∅`, the assumption produces an overlap, and `A` is a TI-subset with bound `N`. -/
theorem mem_N_of_forall_conj_mem_A {g : G} (hg : ∀ a ∈ Q.A, g * a * g⁻¹ ∈ Q.A) : g ∈ Q.N := by
  obtain ⟨a, ha⟩ := Q.A_nonempty
  exact Q.A_isTISubset g ⟨a, ha, hg a ha⟩

/-- **Gorenstein Lemma 1.3, full form `N = N_G(A)`**: `g` normalizes the set `A` iff `g ∈ N`. -/
theorem mem_N_iff_forall_conj_mem_A {g : G} : g ∈ Q.N ↔ ∀ a ∈ Q.A, g * a * g⁻¹ ∈ Q.A := by
  constructor
  · intro hg a ha
    exact Q.conj_mem_A_of_mem_N hg ha
  · exact Q.mem_N_of_forall_conj_mem_A

end QuaternionSylowSetup

end OddOrder.GroupTheory
