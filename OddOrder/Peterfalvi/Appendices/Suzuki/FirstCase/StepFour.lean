/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepThree
import OddOrder.GroupTheory.WielandtFixedPoint

/-!
# Peterfalvi Part II, Ch. II, step (4): `|Q| = |C_Q(P)|^p`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (4), p. 109.

The book applies Wielandt's fixed point theorem ([HB] Ch. XI, Theorem 12.4)
to the action of the Frobenius group `KP` on `Q` and obtains
`|Q| = |C_Q(P)|^p`.  Here this is Peterfalvi (9.1), formalized sorry-free as
`wielandt_fixedPoint_frobenius` with corollary
`wielandt_fixedPoint_trivial_U_fixed` (`C_H(U) = 1 ⟹ |H| = |C_H(E)|^{|E|}`);
step (4) assembles the `CoprimeFrobeniusAction` carrier for `L = KP` acting
on `Q` by conjugation:

* `KP` is Frobenius with kernel `K`: `C_K(P) = 1` (step (1)) and `|P| = p`
  prime (`isFrobeniusGroup_of_prime_complement_fixedFree`);
* `C_Q(K) = 1`: `K` is fixed-point-free on `Q` (§2 Proposition 1(a));
* coprimality `(|Q|, |KP|) = 1`: `(|Q|, |K|) = 1` is `coprime_card_Q_K`,
  and `p ∤ |Q|` follows from step (3) — a prime divisor `r` of `|Q₁|`
  satisfies `r ≡ 2^i (mod 2^p − 1)`, which for `r = p` odd is impossible
  (`p` and `2^{i mod p}` are both `< 2^p − 1`, so they would be equal).
  The book notes this `r ≠ p` consequence after step (3).

Steps (3)–(4) inherit the step (2)(b) `sorry` (issue 9318) through
`|C_M(P)| = r`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory (fixedSubgroup CoprimeFrobeniusAction)
open Pointwise

/-- For an odd prime `p` there is no `i` with `p ≡ 2^i (mod 2^p − 1)`:
reducing the exponent mod `p` (as `2^p ≡ 1`), both `p` and `2^{i mod p}`
are `< 2^p − 1`, so the congruence would force `p = 2^{i mod p}`, making
`p` even or `p = 1`. -/
private theorem not_odd_prime_modEq_two_pow {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (i : ℕ) : ¬ p ≡ 2 ^ i [MOD 2 ^ p - 1] := by
  intro hmod
  have hp2 : 2 ≤ p := hp.two_le
  have h4 : 4 ≤ 2 ^ p := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
  -- `2^p ≡ 1 (mod 2^p − 1)`
  have hcycle : (2 : ℕ) ^ p ≡ 1 [MOD 2 ^ p - 1] := by
    have h1 : (2 : ℕ) ^ p = (2 ^ p - 1) + 1 := by omega
    calc (2 : ℕ) ^ p = (2 ^ p - 1) + 1 := h1
      _ ≡ 0 + 1 [MOD 2 ^ p - 1] :=
        Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
      _ = 1 := by norm_num
  -- reduce the exponent mod `p`
  have hred : (2 : ℕ) ^ i ≡ 2 ^ (i % p) [MOD 2 ^ p - 1] := by
    conv_lhs => rw [← Nat.div_add_mod i p]
    rw [pow_add, pow_mul]
    calc ((2 : ℕ) ^ p) ^ (i / p) * 2 ^ (i % p)
        ≡ 1 ^ (i / p) * 2 ^ (i % p) [MOD 2 ^ p - 1] :=
          Nat.ModEq.mul_right _ (hcycle.pow _)
      _ = 2 ^ (i % p) := by rw [one_pow, one_mul]
  have hmod' : p ≡ 2 ^ (i % p) [MOD 2 ^ p - 1] := hmod.trans hred
  -- both sides are `< 2^p − 1`
  have hjlt : i % p < p := Nat.mod_lt _ (by omega)
  have hpow2 : 2 * 2 ^ (p - 1) = 2 ^ p := by
    rw [← pow_succ']
    congr 1
    omega
  have h2j : 2 ^ (i % p) < 2 ^ p - 1 := by
    have h1 : (2 : ℕ) ^ (i % p) ≤ 2 ^ (p - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ≤ 2 ^ (p - 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hplt : p < 2 ^ p - 1 := by
    have h1 : p - 1 < 2 ^ (p - 1) := Nat.lt_two_pow_self
    omega
  -- hence equality, contradicting `p` odd (or `p = 1`)
  have heq : p = 2 ^ (i % p) := by
    have h1 : p % (2 ^ p - 1) = 2 ^ (i % p) % (2 ^ p - 1) := hmod'
    rwa [Nat.mod_eq_of_lt hplt, Nat.mod_eq_of_lt h2j] at h1
  rcases Nat.eq_zero_or_pos (i % p) with h0 | hpos
  · rw [h0, pow_zero] at heq
    exact hp.one_lt.ne' heq
  · have h2 : 2 ∣ p := heq ▸ dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpos)
    obtain ⟨t, ht⟩ := hodd
    omega

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- Step (3) ⟹ `p ∤ |Q₁|` (the book records `r ≠ p` as a consequence of
the congruence `r ≡ 2^i (mod 2^p − 1)`): `p` odd cannot be congruent to a
power of two modulo `2^p − 1`.

Inherits the step (2)(b) `sorry` (issue 9318) through step (3). -/
theorem not_p_dvd_card_Q1 : ¬ fc.p ∣ Nat.card ↥fc.toHypothesis.Q1 := by
  intro hdvd
  obtain ⟨i, hi⟩ :=
    fc.exists_pow_two_modEq_of_prime_dvd_card_Q1 fc.p_prime hdvd
  exact not_odd_prime_modEq_two_pow fc.p_prime fc.p_odd i hi

/-- `p ∤ |Q|`: the Sylow `2`-part is out for parity, and `p ∤ |Q₁|` by
`not_p_dvd_card_Q1`.

Inherits the step (2)(b) `sorry` (issue 9318) through step (3). -/
theorem not_p_dvd_card_Q : ¬ fc.p ∣ Nat.card ↥fc.toHypothesis.Q := by
  intro hdvd
  classical
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥fc.toHypothesis.Q) := inferInstance
  have hcard : Nat.card ↥(S : Subgroup ↥fc.toHypothesis.Q) *
      Nat.card ↥fc.toHypothesis.Q1Subgroup = Nat.card ↥fc.toHypothesis.Q :=
    (fc.toHypothesis.sylowTwo_isComplement'_Q1Subgroup S).card_mul
  rw [← hcard] at hdvd
  rcases (Nat.Prime.dvd_mul fc.p_prime).mp hdvd with hS | hQ1
  · -- `p` odd cannot divide the `2`-group `S`
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn] at hS
    have h2 : fc.p ∣ 2 := fc.p_prime.dvd_of_dvd_pow hS
    have hp2 : fc.p = 2 :=
      (Nat.prime_dvd_prime_iff_eq fc.p_prime Nat.prime_two).mp h2
    exact fc.p_ne_two hp2
  · exact fc.not_p_dvd_card_Q1 (fc.toHypothesis.card_Q1 ▸ hQ1)

/-- **Peterfalvi Part II, Ch. II, step (4)** (p. 109):
`|Q| = |C_Q(P)|^p`.

Wielandt's fixed point theorem — here Peterfalvi (9.1), the sorry-free
`wielandt_fixedPoint_trivial_U_fixed` — applied to the coprime action of the
Frobenius group `L = KP` (kernel `K`, complement `P` of prime order `p`,
`C_K(P) = 1` by step (1)) on `Q` by conjugation, with `C_Q(K) = 1`
(§2 Proposition 1(a)) and `(|Q|, |KP|) = 1` (`coprime_card_Q_K` +
`not_p_dvd_card_Q`).

Inherits the step (2)(b) `sorry` (issue 9318) through `not_p_dvd_card_Q`. -/
theorem card_Q_eq_card_inf_centralizer_pow :
    Nat.card ↥fc.toHypothesis.Q =
      Nat.card ↥(fc.toHypothesis.Q ⊓
        Subgroup.centralizer (fc.P : Set G)) ^ fc.p := by
  classical
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  -- `L = KP` acts on `Q` by conjugation (`L ≤ H ≤ N_G(Q)`).
  set L : Subgroup G := fc.toHypothesis.K ⊔ fc.P with hLdef
  have hLH : L ≤ fc.toHypothesis.H :=
    sup_le (fc.toHypothesis.K_le_D.trans fc.toHypothesis.D_le_H)
      ((fc.P_le_V.trans fc.toHypothesis.V_le_D).trans
        fc.toHypothesis.D_le_H)
  set φ : ↥L →* MulAut ↥fc.toHypothesis.Q :=
    fc.toHypothesis.Q.normalizerMonoidHom.comp
      (Subgroup.inclusion (hLH.trans fc.toHypothesis.H_le_normalizer_Q))
    with hφdef
  have hφval : ∀ (a : ↥L) (x : ↥fc.toHypothesis.Q),
      ((φ a x : ↥fc.toHypothesis.Q) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hKL : fc.toHypothesis.K ≤ L := le_sup_left
  have hPL : fc.P ≤ L := le_sup_right
  set U : Subgroup ↥L := fc.toHypothesis.K.subgroupOf L with hUdef
  set E : Subgroup ↥L := fc.P.subgroupOf L with hEdef
  have hcardU : Nat.card ↥U = Nat.card ↥fc.toHypothesis.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  have hcardE : Nat.card ↥E = fc.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, fc.card_P]
  -- `U ◁ L`: `K` is normal in `D ⊇ L`.
  have hLD : L ≤ fc.toHypothesis.D :=
    sup_le fc.toHypothesis.K_le_D
      (fc.P_le_V.trans fc.toHypothesis.V_le_D)
  haveI hUnormal : U.Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ fc.toHypothesis.K := hn
    have h := (inferInstance :
        (fc.toHypothesis.K.subgroupOf fc.toHypothesis.D).Normal).conj_mem
      (⟨(n : G), hLD n.2⟩ : ↥fc.toHypothesis.D)
      (Subgroup.mem_subgroupOf.mpr hn') ⟨(g : G), hLD g.2⟩
    exact Subgroup.mem_subgroupOf.mp h
  -- `U ⊔ E = ⊤` in `L = K ⊔ P`.
  have hsup : U ⊔ E = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, hUdef, hEdef,
      Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_subgroupOf_eq_of_le hPL,
      ← MonoidHom.range_eq_map, L.range_subtype]
  -- `(|E|, |U|) = 1` (Fermat: `p ∤ 2^p − 1`).
  have hcardK : Nat.card ↥fc.toHypothesis.K = 2 ^ fc.p - 1 := by
    rw [fc.toHypothesis.card_K_eq_card_Q0_sub_one, fc.card_Q0_eq_two_pow]
  have hfermat : ¬ fc.p ∣ 2 ^ fc.p - 1 := by
    intro hdvd
    have hcast : ((2 ^ fc.p - 1 : ℕ) : ZMod fc.p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod fc.p) fc.p _).mpr hdvd
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      ZMod.pow_card, Nat.cast_one, sub_eq_zero] at hcast
    exact one_ne_zero (α := ZMod fc.p) (by linear_combination hcast)
  have hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U) := by
    rw [hcardE, hcardU, hcardK]
    exact (Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr hfermat
  -- `U` and `E` are complements in `L`.
  have hcompl : Subgroup.IsComplement' U E := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (Subgroup.disjoint_of_coprime_natCard hcopUE.symm)
    have h1 : ((U ⊔ E : Subgroup ↥L) : Set ↥L) =
        (U : Set ↥L) * (E : Set ↥L) :=
      Subgroup.normal_mul U E
    rw [← h1, hsup, Subgroup.coe_top]
  have h4 : 4 ≤ 2 ^ fc.p := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ fc.p := Nat.pow_le_pow_right (by norm_num) fc.p_prime.two_le
  have hUne : U ≠ ⊥ := by
    intro hbot
    have h1 := hcardU
    rw [hbot, Subgroup.card_bot, hcardK] at h1
    omega
  -- `C_U(E) = 1`: step (1)'s `C_K(P) = 1`.
  have hfpf : ∀ u ∈ U, (∀ e ∈ E, e * u * e⁻¹ = u) → u = 1 := by
    intro u hu hall
    have huK : ((u : ↥L) : G) ∈ fc.toHypothesis.K := hu
    have huC : ((u : ↥L) : G) ∈
        Subgroup.centralizer (fc.P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgE : (⟨g, hPL hg⟩ : ↥L) ∈ E := Subgroup.mem_subgroupOf.mpr hg
      have h := congrArg Subtype.val (hall ⟨g, hPL hg⟩ hgE)
      have h' : g * ((u : ↥L) : G) * g⁻¹ = ((u : ↥L) : G) := h
      calc g * ((u : ↥L) : G)
          = (g * ((u : ↥L) : G) * g⁻¹) * g := by group
        _ = ((u : ↥L) : G) * g := by rw [h']
    have hmem : ((u : ↥L) : G) ∈
        fc.toHypothesis.K ⊓ Subgroup.centralizer (fc.P : Set G) :=
      ⟨huK, huC⟩
    rw [fc.K_inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L U E :=
    OddOrder.Isaacs.Ch06.isFrobeniusGroup_of_prime_complement_fixedFree
      hcompl (by rw [hcardE]; exact fc.p_prime) hUne hfpf
  -- `Q` is solvable (nilpotent) and `(|Q|, |L|) = 1`.
  haveI hQsolv : IsSolvable ↥fc.toHypothesis.Q := by
    letI := fc.toHypothesis.isNilpotent_Q
    infer_instance
  have hcoprime :
      Nat.Coprime (Nat.card ↥fc.toHypothesis.Q) (Nat.card ↥L) := by
    have hcardL : Nat.card ↥L = Nat.card ↥U * Nat.card ↥E :=
      hcompl.card_mul.symm
    rw [hcardL, hcardU]
    refine Nat.Coprime.mul_right fc.toHypothesis.coprime_card_Q_K ?_
    rw [hcardE]
    exact ((Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr
      fc.not_p_dvd_card_Q).symm
  -- the Wielandt carrier
  let act : CoprimeFrobeniusAction ↥L ↥fc.toHypothesis.Q :=
    ⟨U, E, hfrob, hQsolv, φ, hcoprime⟩
  -- `C_Q(K) = 1`: `K` is fixed-point-free on `Q` (§2 Prop 1(a)).
  have hfixU : act.fixedByU = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k₀, hk₀K, hk₀1⟩ := fc.toHypothesis.exists_ne_one_mem_KSet
    have hk₀mem : k₀ ∈ fc.toHypothesis.K := by
      change k₀ ∈ (fc.toHypothesis.K : Set G)
      rw [fc.toHypothesis.coe_K]
      exact hk₀K
    have hφfix := hx (⟨k₀, hKL hk₀mem⟩ : ↥L)
      (Subgroup.mem_subgroupOf.mpr hk₀mem)
    have hQfix : fc.toHypothesis.conjQByK ⟨k₀, hk₀mem⟩ x = x := by
      apply Subtype.ext
      rw [fc.toHypothesis.conjQByK_apply_val]
      exact congrArg (fun z : ↥fc.toHypothesis.Q => (z : G)) hφfix
    have hk₀ne : (⟨k₀, hk₀mem⟩ : ↥fc.toHypothesis.K) ≠ 1 :=
      fun h => hk₀1 (congrArg Subtype.val h)
    exact fc.toHypothesis.conjQByK_fixed_eq_one hk₀ne hQfix
  -- Wielandt: `|Q| = |C_Q(P)|^{|E|}`.
  have hkey := OddOrder.GroupTheory.wielandt_fixedPoint_trivial_U_fixed
    act hfixU
  -- `C_Q(P)` as an ambient subgroup: `fixedSubgroup φ E ≃ Q ⊓ C_G(P)`.
  have hfixinf : Nat.card ↥act.fixedByE =
      Nat.card ↥(fc.toHypothesis.Q ⊓
        Subgroup.centralizer (fc.P : Set G)) := by
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun x => ⟨((x : ↥fc.toHypothesis.Q) : G),
        (x : ↥fc.toHypothesis.Q).2, ?_⟩) ⟨?_, ?_⟩
    · change ((x : ↥fc.toHypothesis.Q) : G) ∈
        Subgroup.centralizer (fc.P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgL : g ∈ L := hPL hg
      have hfix := x.2 (⟨g, hgL⟩ : ↥L) (Subgroup.mem_subgroupOf.mpr hg)
      have hval : g * ((x : ↥fc.toHypothesis.Q) : G) * g⁻¹ =
          ((x : ↥fc.toHypothesis.Q) : G) :=
        congrArg (fun z : ↥fc.toHypothesis.Q => (z : G)) hfix
      calc g * ((x : ↥fc.toHypothesis.Q) : G)
          = (g * ((x : ↥fc.toHypothesis.Q) : G) * g⁻¹) * g := by group
        _ = ((x : ↥fc.toHypothesis.Q) : G) * g := by rw [hval]
    · intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : ↥(fc.toHypothesis.Q ⊓
          Subgroup.centralizer (fc.P : Set G)) => (z : G)) hab
    · rintro ⟨g, hgQ, hgC⟩
      refine ⟨⟨⟨g, hgQ⟩, ?_⟩, rfl⟩
      intro l hl
      apply Subtype.ext
      have hlP : ((l : ↥L) : G) ∈ fc.P := hl
      have hcomm := Subgroup.mem_centralizer_iff.mp hgC _ hlP
      change ((l : ↥L) : G) * g * ((l : ↥L) : G)⁻¹ = g
      rw [hcomm]
      group
  have hEcard : Nat.card ↥act.E = fc.p := hcardE
  rw [hkey, hfixinf, hEcard]

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
