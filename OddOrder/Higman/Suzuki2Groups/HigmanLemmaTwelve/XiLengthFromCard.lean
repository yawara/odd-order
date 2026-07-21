/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthThreeReduction
import OddOrder.Higman.Suzuki2Groups.CenterInvolutions
import OddOrder.GroupTheory.FreeActionOrbitCount
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# ξ-length from the group order: the counting half

G. Higman, *Suzuki 2-groups*, §6 ("the order of `G` is `q²` or `q³`");
T. Peterfalvi, Appendix III, Theorem (b).

A regular actor on the involutions of a finite 2-group acts fixed-point-freely
on the whole group: a nontrivial fixed subgroup would contain an involution
with a nontrivial stabilizer.  Free orbit counting then pins every invariant
subgroup to order `≡ 1 (mod |K|)`; with `|K| = 2^n - 1`, the two-power
subgroup orders must be powers of `q = 2^n`.  In particular a group of order
`q³` admits no chain of four strict inclusions of normal invariant
subgroups — the counting half of "`|P| = q³` iff ξ-length `3`".
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

variable {P : Type uP} [Group P] [Finite P]

/-! ## Fixed-point-freeness of a regular involution actor -/

/-- **A regular actor on the involutions of a 2-group is fixed-point-free.**
The fixed points of `k ≠ 1` form a subgroup; if nontrivial, it contains an
element of order two, i.e. an involution fixed by both `k` and `1`,
contradicting the uniqueness in regularity. -/
theorem fixedPointFree_of_actsRegularlyOnInvolutions
    (hP2 : IsPGroup 2 P)
    {K : Subgroup (MulAut P)} (hreg : ActsRegularlyOnInvolutions K) :
    ∀ k : ↥K, k ≠ 1 → ∀ x : P, (k : MulAut P) x = x → x = 1 := by
  intro k hk x hx
  by_contra hxne
  -- the fixed subgroup of `k`
  set C : Subgroup P := MonoidHom.eqLocus
    (k : MulAut P).toMonoidHom (MonoidHom.id P) with hC
  have hxC : x ∈ C := hx
  have hCne : C ≠ ⊥ := by
    intro hbot
    rw [hbot] at hxC
    exact hxne (Subgroup.mem_bot.mp hxC)
  -- an element of order two in the fixed subgroup
  have hCp : IsPGroup 2 ↥C := hP2.to_subgroup C
  have hClt : 1 < Nat.card ↥C :=
    (Subgroup.one_lt_card_iff_ne_bot C).mpr hCne
  obtain ⟨m, hm⟩ := hCp.exists_card_eq
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hm
    omega
  letI : Fintype ↥C := Fintype.ofFinite ↥C
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card (G := ↥C) 2 (by
    rw [← Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self 2 hm0)
  have htinv : (t : P) ∈ involutions P := by
    constructor
    · have := pow_orderOf_eq_one t
      rw [ht] at this
      exact congrArg Subtype.val this
    · intro h1
      have : t = 1 := Subtype.ext h1
      rw [this, orderOf_one] at ht
      norm_num at ht
  -- `k` and `1` both fix the involution `t`
  obtain ⟨a, -, hunique⟩ := hreg (t : P) htinv (t : P) htinv
  have hka : k = a := hunique k t.2
  have h1a : (1 : ↥K) = a := hunique 1 (by
    show ((1 : ↥K) : MulAut P) (t : P) = (t : P)
    rw [OneMemClass.coe_one, MulAut.one_apply])
  exact hk (hka.trans h1a.symm)

/-! ## Orbit counting on invariant subgroups -/

/-- **Free orbit counting**: the order of a fixed-point-free actor divides
`|T| - 1` for every invariant subgroup `T`. -/
theorem card_dvd_card_sub_one_of_fixedPointFree
    {K : Subgroup (MulAut P)}
    (hfree : ∀ k : ↥K, k ≠ 1 → ∀ x : P, (k : MulAut P) x = x → x = 1)
    {T : Subgroup P} (hT : IsAInvariant K.subtype T) :
    Nat.card ↥K ∣ Nat.card ↥T - 1 := by
  classical
  letI : Fintype ↥T := Fintype.ofFinite ↥T
  letI : MulAction ↥K {t : ↥T // t ≠ 1} :=
    { smul := fun k t => ⟨hT.restrict k t.1, fun h => t.2 (by
        have := congrArg (hT.restrict k).symm h
        rwa [MulEquiv.symm_apply_apply, map_one] at this)⟩
      one_smul := fun t => Subtype.ext (by
        change hT.restrict 1 t.1 = t.1
        rw [map_one, MulAut.one_apply])
      mul_smul := fun k l t => Subtype.ext (by
        change hT.restrict (k * l) t.1 = hT.restrict k (hT.restrict l t.1)
        rw [map_mul, MulAut.mul_apply]) }
  have hsub : Nat.card {t : ↥T // t ≠ 1} = Nat.card ↥T - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [← hsub]
  apply OddOrder.RepresentationTheory.card_dvd_of_no_nontrivial_fixed
  intro k hk t ht
  apply t.2
  have hfix : hT.restrict k t.1 = t.1 := congrArg Subtype.val ht
  have hfixP : (k : MulAut P) (t.1 : P) = (t.1 : P) := by
    have := congrArg Subtype.val hfix
    rwa [IsAInvariant.restrict_apply_val] at this
  exact Subtype.ext (hfree k hk (t.1 : P) hfixP)

/-- `2^n - 1 ∣ 2^k - 1` forces `n ∣ k`. -/
theorem dvd_of_two_pow_sub_one_dvd {n k : ℕ} (hn : n ≠ 0)
    (h : 2 ^ n - 1 ∣ 2 ^ k - 1) : n ∣ k := by
  have hone : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  have h1n : (1 : ℕ) ≡ 2 ^ n [MOD 2 ^ n - 1] :=
    (Nat.modEq_iff_dvd' hone).mpr dvd_rfl
  have hpow : (1 : ℕ) ≡ 2 ^ (n * (k / n)) [MOD 2 ^ n - 1] := by
    have := h1n.pow (k / n)
    rwa [one_pow, ← pow_mul] at this
  have hsplit : 2 ^ (k % n) ≡ 2 ^ k [MOD 2 ^ n - 1] := by
    calc 2 ^ (k % n) = 1 * 2 ^ (k % n) := (one_mul _).symm
      _ ≡ 2 ^ (n * (k / n)) * 2 ^ (k % n) [MOD 2 ^ n - 1] :=
        hpow.mul_right _
      _ = 2 ^ (n * (k / n) + k % n) := by rw [← pow_add]
      _ = 2 ^ k := by rw [Nat.div_add_mod]
  have hk1 : (1 : ℕ) ≡ 2 ^ k [MOD 2 ^ n - 1] :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr h
  have hmod : (2 : ℕ) ^ (k % n) ≡ 1 [MOD 2 ^ n - 1] :=
    hsplit.trans hk1.symm
  have hdvd : 2 ^ n - 1 ∣ 2 ^ (k % n) - 1 :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
  have hlt : 2 ^ (k % n) - 1 < 2 ^ n - 1 := by
    have hpowlt : (2 : ℕ) ^ (k % n) < 2 ^ n :=
      (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mpr
        (Nat.mod_lt k (Nat.pos_of_ne_zero hn))
    have hge1 : (1 : ℕ) ≤ 2 ^ (k % n) := Nat.one_le_two_pow
    omega
  have hzero : 2 ^ (k % n) - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  have hge : (1 : ℕ) ≤ 2 ^ (k % n) := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ (k % n) = 1 :=
    le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hge
  have hkn : k % n = 0 := by
    rcases Nat.pow_eq_one.mp h2 with h | h
    · norm_num at h
    · exact h
  exact Nat.dvd_of_mod_eq_zero hkn

/-- **Every invariant subgroup has order a power of `q = 2^n`** when the
actor has order `2^n - 1` and acts fixed-point-freely. -/
theorem card_invariant_eq_pow_of_fixedPointFree
    (hP2 : IsPGroup 2 P) {K : Subgroup (MulAut P)} {n : ℕ} (hn : n ≠ 0)
    (hfree : ∀ k : ↥K, k ≠ 1 → ∀ x : P, (k : MulAut P) x = x → x = 1)
    (hKcard : Nat.card ↥K = 2 ^ n - 1)
    {T : Subgroup P} (hT : IsAInvariant K.subtype T) :
    ∃ j : ℕ, Nat.card ↥T = (2 ^ n) ^ j := by
  obtain ⟨m, hm⟩ := (hP2.to_subgroup T).exists_card_eq
  have hdvd : 2 ^ n - 1 ∣ 2 ^ m - 1 := by
    rw [← hKcard, ← hm]
    exact card_dvd_card_sub_one_of_fixedPointFree hfree hT
  obtain ⟨j, hj⟩ := dvd_of_two_pow_sub_one_dvd hn hdvd
  exact ⟨j, by rw [hm, hj, pow_mul]⟩

/-! ## The counting half of "order `q³` iff ξ-length `3`" -/

/-- **No four-step chain of normal invariant subgroups in order `q³`.**
Five strictly increasing invariant subgroups would have five strictly
increasing powers of `q` as orders, exceeding `q³`. -/
theorem no_four_chain_of_card_eq_cube
    (hP2 : IsPGroup 2 P) {K : Subgroup (MulAut P)} {n : ℕ} (hn : n ≠ 0)
    (hfree : ∀ k : ↥K, k ≠ 1 → ∀ x : P, (k : MulAut P) x = x → x = 1)
    (hKcard : Nat.card ↥K = 2 ^ n - 1)
    (hcard : Nat.card P = (2 ^ n) ^ 3) :
    ∀ A B C D E : NormalInvariantSubgroup K.subtype,
      A < B → B < C → C < D → D < E → False := by
  intro A B C D E hAB hBC hCD hDE
  have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow_iff.mpr hn
  -- orders are powers of `q`
  have hpow : ∀ F : NormalInvariantSubgroup K.subtype,
      ∃ j : ℕ, Nat.card ↥F.1 = (2 ^ n) ^ j := fun F =>
    card_invariant_eq_pow_of_fixedPointFree hP2 hn hfree hKcard F.2.2
  obtain ⟨a, ha⟩ := hpow A
  obtain ⟨b, hb⟩ := hpow B
  obtain ⟨c, hc⟩ := hpow C
  obtain ⟨d, hd⟩ := hpow D
  obtain ⟨e, he⟩ := hpow E
  -- strict inclusions give strict cardinality increases
  have hmono : ∀ {F G : NormalInvariantSubgroup K.subtype}, F < G →
      Nat.card ↥F.1 < Nat.card ↥G.1 := by
    intro F G hFG
    have hle : F.1 ≤ G.1 := le_of_lt hFG
    have hne : F.1.subgroupOf G.1 ≠ ⊤ := by
      intro htop
      have hGle : G.1 ≤ F.1 := by
        intro g hg
        have hx : (⟨g, hg⟩ : ↥G.1) ∈ F.1.subgroupOf G.1 := by
          rw [htop]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hx
      exact absurd (Subtype.ext (le_antisymm hle hGle)) (ne_of_lt hFG)
    have hlt : Nat.card ↥(F.1.subgroupOf G.1) < Nat.card ↥G.1 :=
      Subgroup.card_lt_card_of_ne_top hne
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hlt
  -- exponents strictly increase
  have hexp : ∀ {x y : ℕ}, (2 ^ n) ^ x < (2 ^ n) ^ y → x < y := fun h =>
    (Nat.pow_lt_pow_iff_right hq1).mp h
  have hab : a < b := hexp (ha ▸ hb ▸ hmono hAB)
  have hbc : b < c := hexp (hb ▸ hc ▸ hmono hBC)
  have hcd : c < d := hexp (hc ▸ hd ▸ hmono hCD)
  have hde : d < e := hexp (hd ▸ he ▸ hmono hDE)
  -- but the top order is `q³`
  have hEle : Nat.card ↥E.1 ≤ (2 ^ n) ^ 3 := by
    rw [← hcard]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card E.1)
  rw [he] at hEle
  have : e ≤ 3 := (Nat.pow_le_pow_iff_right hq1).mp hEle
  omega

/-! ## The field-theoretic exclusion for the middle quotient -/

/-- **A Singer generator fixed by the `n`-th Frobenius power bounds the
degree**: if `x` generates `GaloisField 2 m` over `𝔽₂` and `x^(2^n) = x`,
then `m ≤ n`.  All of `𝔽₂(x)` is then fixed by the `n`-th Frobenius power,
i.e. consists of roots of `X^(2^n) - X`, of which there are at most `2^n`.
This excludes an irreducible middle quotient of order `q²` in the ξ-length
bridge: its Singer generator has order `2^n - 1`. -/
theorem le_of_adjoin_frobeniusFixed_eq_top
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (x : GaloisField 2 m) (hfix : x ^ 2 ^ n = x)
    (htop : Algebra.adjoin (ZMod 2) ({x} : Set (GaloisField 2 m)) = ⊤) :
    m ≤ n := by
  classical
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm
  haveI : Finite (GaloisField 2 m) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have h2n : (2 : ℕ) ^ n ≠ 0 := by positivity
  -- the Frobenius-fixed subalgebra
  let T : Subalgebra (ZMod 2) (GaloisField 2 m) :=
    { carrier := {y | y ^ 2 ^ n = y}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_pow, ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [add_pow_char_pow, ha, hb]
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, ← map_pow]
        congr 1
        fin_cases c
        · exact zero_pow h2n
        · exact one_pow _ }
  have hT : ∀ y : GaloisField 2 m, y ^ 2 ^ n = y := by
    intro y
    have htople : (⊤ : Subalgebra (ZMod 2) (GaloisField 2 m)) ≤ T := by
      rw [← htop]
      apply Algebra.adjoin_le
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hfix
    exact htople (Algebra.mem_top)
  -- every element is a root of `X^(2^n) - X`
  let f : Polynomial (GaloisField 2 m) :=
    Polynomial.X ^ 2 ^ n - Polynomial.X
  have hdeg : f.natDegree = 2 ^ n := by
    have h1 : (Polynomial.X : Polynomial (GaloisField 2 m)).natDegree <
        (Polynomial.X ^ 2 ^ n :
          Polynomial (GaloisField 2 m)).natDegree := by
      rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
      exact Nat.one_lt_two_pow_iff.mpr hn
    rw [show f = Polynomial.X ^ 2 ^ n - Polynomial.X from rfl,
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1,
      Polynomial.natDegree_X_pow]
  have hfne : f ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact h2n hdeg.symm
  have hroot : ∀ y : GaloisField 2 m, y ∈ f.roots.toFinset := by
    intro y
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨hfne, ?_⟩
    show f.IsRoot y
    simp [f, Polynomial.IsRoot, hT y]
  have hcardle : Fintype.card (GaloisField 2 m) ≤ 2 ^ n := by
    calc Fintype.card (GaloisField 2 m)
        = Finset.univ.card := rfl
      _ ≤ f.roots.toFinset.card :=
          Finset.card_le_card fun y _ => hroot y
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := f.card_roots'
      _ = 2 ^ n := hdeg
  rw [← Nat.card_eq_fintype_card, hcard] at hcardle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcardle

end OddOrder.Higman.Suzuki2Groups
