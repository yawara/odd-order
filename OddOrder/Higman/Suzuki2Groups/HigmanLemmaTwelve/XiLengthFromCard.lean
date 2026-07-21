/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthThreeReduction
import OddOrder.Higman.Suzuki2Groups.CenterInvolutions
import OddOrder.GroupTheory.FreeActionOrbitCount
import Mathlib.FieldTheory.Finite.GaloisField
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabBridge
import OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.InvariantSummands

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

/-! ## The irreducible middle quotient is impossible -/

open OddOrder.RepresentationTheory in
/-- **An elementary abelian group of order `q²` with a fixed-point-free
cyclic actor of order `q - 1` has a proper nontrivial invariant subgroup.**
Otherwise the group is a faithful irreducible `𝔽₂[K]`-module; its Singer
model has a generator of multiplicative order `2^n - 1`, which is fixed by
the `n`-th Frobenius power yet generates a field of degree `2n` — forcing
`2n ≤ n`. -/
theorem exists_proper_invariant_subgroup_of_card_sq
    {Q : Type uP} [Group Q] [Finite Q]
    (hcomm : ∀ x y : Q, x * y = y * x)
    (hsq : ∀ x : Q, x ^ 2 = 1)
    {K : Type uP} [Group K] [Finite K] [IsCyclic K]
    (rho : K →* MulAut Q)
    (hfree : ∀ k : K, k ≠ 1 → ∀ x : Q, rho k x = x → x = 1)
    {n : ℕ} (hn : n ≠ 0)
    (hKcard : Nat.card K = 2 ^ n - 1)
    (hQcard : Nat.card Q = 2 ^ (2 * n)) :
    ∃ V : Subgroup Q, V ≠ ⊥ ∧ V ≠ ⊤ ∧ IsAInvariant rho V := by
  classical
  by_contra hnone
  push_neg at hnone
  letI : CommGroup Q :=
    { (inferInstance : Group Q) with mul_comm := hcomm }
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule (by
    intro q
    apply Additive.toMul.injective
    change Additive.toMul q ^ 2 = 1
    exact hsq _)
  have hQnontriv : Nontrivial Q := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hQcard]
    exact Nat.one_lt_two_pow_iff.mpr (by omega)
  haveI : Nontrivial (Additive Q) := hQnontriv
  set rho' : Representation (ZMod 2) K (Additive Q) :=
    OddOrder.GroupTheory.elabRepresentation 2 rho with hrho'
  have hrho'apply : ∀ (k : K) (x : Q),
      rho' k (Additive.ofMul x) = Additive.ofMul (rho k x) := fun k x =>
    OddOrder.GroupTheory.elabRepresentation_apply 2 rho k x
  -- the subgroup ↔ submodule dictionary
  let Φ : Submodule (ZMod 2) (Additive Q) ≃o Subgroup Q :=
    (AddSubgroup.toZModSubmodule (n := 2)).symm.trans AddSubgroup.toSubgroup'
  have hmemΦ : ∀ (M : Submodule (ZMod 2) (Additive Q)) (x : Q),
      x ∈ Φ M ↔ Additive.ofMul x ∈ M := by
    intro M x
    simp only [Φ, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
      AddSubgroup.mem_toZModSubmodule]
    rfl
  -- irreducibility of the linearized action
  have hirr : Representation.IsIrreducible rho' := by
    have hbot_ne_top : (⊥ : Subrepresentation rho') ≠ ⊤ := fun h =>
      bot_ne_top (congrArg Subrepresentation.toSubmodule h)
    letI : Nontrivial (Subrepresentation rho') := ⟨⊥, ⊤, hbot_ne_top⟩
    apply IsSimpleOrder.of_forall_eq_top
    intro W hWbot
    set V : Subgroup Q := Φ W.toSubmodule with hV
    have hVmem : ∀ x : Q, x ∈ V ↔ Additive.ofMul x ∈ W.toSubmodule :=
      hmemΦ W.toSubmodule
    have hVinv : IsAInvariant rho V := by
      intro k
      ext y
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      change (rho k)⁻¹ y ∈ V ↔ y ∈ V
      rw [hVmem, hVmem]
      constructor
      · intro h
        have hstep := W.apply_mem_toSubmodule k h
        rw [hrho'apply] at hstep
        have hcancel : rho k ((rho k)⁻¹ y) = y := by
          rw [← map_inv]
          change rho k (rho k⁻¹ y) = y
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            MulAut.one_apply]
        rwa [hcancel] at hstep
      · intro h
        have hstep := W.apply_mem_toSubmodule k⁻¹ h
        rw [hrho'apply] at hstep
        rwa [map_inv] at hstep
    have hVne_bot : V ≠ ⊥ := by
      intro hVbot
      apply hWbot
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊥
      apply Φ.injective
      rw [Φ.map_bot, ← hV]
      exact hVbot
    have hVtop : V = ⊤ := by
      by_contra hVne_top
      exact hnone V hVne_bot hVne_top hVinv
    apply Subrepresentation.toSubmodule_injective
    change W.toSubmodule = ⊤
    apply Φ.injective
    rw [Φ.map_top, ← hV]
    exact hVtop
  -- faithfulness of the linearized action
  have hker : ∀ k : K, rho' k = 1 → k = 1 := by
    intro k hk
    by_contra hkne
    obtain ⟨x, hxne⟩ := exists_ne (1 : Q)
    apply hxne
    apply hfree k hkne
    have happ : rho' k (Additive.ofMul x) = Additive.ofMul x := by
      rw [hk]
      rfl
    rw [hrho'apply] at happ
    exact Additive.ofMul.injective happ
  have hfaith : Function.Injective rho' := by
    intro k l hkl
    have hmul : rho' (k⁻¹ * l) = 1 := by
      rw [map_mul]
      calc rho' k⁻¹ * rho' l = rho' k⁻¹ * rho' k := by rw [hkl]
        _ = rho' (k⁻¹ * k) := (map_mul rho' k⁻¹ k).symm
        _ = 1 := by rw [inv_mul_cancel, map_one]
    exact inv_mul_eq_one.mp (hker _ hmul)
  -- the dimension is `2n`
  have hfin : Module.finrank (ZMod 2) (Additive Q) = 2 * n := by
    have hcardQ' : Nat.card (Additive Q) = 2 ^ (2 * n) := by
      rw [Nat.card_congr (Additive.ofMul (α := Q)).symm]
      exact hQcard
    have h2 : (2 : ℕ) ^ (2 * n) = 2 ^ Module.finrank (ZMod 2) (Additive Q) := by
      rw [← hcardQ', Module.natCard_eq_pow_finrank (K := ZMod 2),
        Nat.card_eq_fintype_card, ZMod.card]
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  -- the Singer model and the degree contradiction
  letI : CommGroup K := IsCyclic.commGroup
  obtain ⟨e, mu, hmuinj, hcompat⟩ :=
    exists_galoisFieldLinearModel_of_faithful_irreducible rho' (2 * n)
      (by omega) hfin hirr hfaith
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := K)
  have htop := adjoin_generator_eq_top_of_irreducible_linearModel rho' hirr
    e mu hcompat c hcgen
  have hordc : orderOf c = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hcgen, hKcard]
  have hordmu : orderOf (mu c) = 2 ^ n - 1 := by
    rw [orderOf_injective mu hmuinj, hordc]
  have hufix : (mu c) ^ 2 ^ n = mu c := by
    have hu : (mu c) ^ (2 ^ n - 1) = 1 := by
      rw [← hordmu]
      exact pow_orderOf_eq_one _
    have h1 : (2 : ℕ) ^ n = (2 ^ n - 1) + 1 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [h1, pow_succ, hu, one_mul]
  have hfix : (mu c : GaloisField 2 (2 * n)) ^ 2 ^ n =
      (mu c : GaloisField 2 (2 * n)) := by
    have hval := congrArg Units.val hufix
    push_cast at hval
    exact hval
  have hle := le_of_adjoin_frobeniusFixed_eq_top (m := 2 * n)
    (by omega) hn _ hfix htop
  omega

/-! ## The bridge: order `q³` gives ξ-length three -/

/-- **Higman / Peterfalvi Appendix III, Theorem (b) for order `q³`**: a
Suzuki 2-group of order `q³` has ξ-length three for its regular actor.
The involution subgroup `Ω` and the preimage of a proper nontrivial
invariant normal subgroup of `P ⧸ Ω` give the three-step chain; the
four-step chain is excluded by counting. -/
theorem hasXiLengthThree_of_card_eq_cube
    (hP : IsSuzuki2Group P)
    {K : Subgroup (MulAut P)} (hKcyc : IsCyclic ↥K)
    (hreg : ActsRegularlyOnInvolutions K)
    {n : ℕ} (hn : n ≠ 0)
    (hKcard : Nat.card ↥K = 2 ^ n - 1)
    (hcard : Nat.card P = (2 ^ n) ^ 3) :
    HasXiLengthThree K.subtype := by
  classical
  obtain ⟨hP2, -, hmulti, -, -, -⟩ := id hP
  obtain ⟨u₀, v₀, hu₀, hv₀, huv₀⟩ := hmulti
  letI : Nontrivial P := ⟨⟨u₀, v₀, huv₀⟩⟩
  have hfree := fixedPointFree_of_actsRegularlyOnInvolutions hP2 hreg
  -- `#involutions = |K|` via the regular bijection
  have hmemK : ∀ k : ↥K, (k : MulAut P) u₀ ∈ involutions P := by
    intro k
    constructor
    · rw [← map_pow, hu₀.1, map_one]
    · intro h
      apply hu₀.2
      apply (k : MulAut P).injective
      rw [h, map_one]
  have hbij : Function.Bijective (fun k : ↥K =>
      (⟨(k : MulAut P) u₀, hmemK k⟩ : ↥(involutions P))) := by
    constructor
    · intro k l hkl
      have hval : (k : MulAut P) u₀ = (l : MulAut P) u₀ :=
        congrArg Subtype.val hkl
      obtain ⟨a, -, huniq⟩ := hreg u₀ hu₀ ((k : MulAut P) u₀) (hmemK k)
      rw [huniq k rfl, huniq l hval.symm]
    · rintro ⟨y, hy⟩
      obtain ⟨a, ha, -⟩ := hreg u₀ hu₀ y hy
      exact ⟨a, Subtype.ext ha⟩
  have hinvcard : (involutions P).ncard = 2 ^ n - 1 := by
    rw [← hKcard, Nat.card_eq_of_bijective _ hbij, Nat.card_coe_set_eq]
  -- the involution subgroup and its order `q`
  have hΩmem : ∀ x : P, x ∈ involutionSubgroup P ↔ x ^ 2 = 1 := fun x =>
    mem_involutionSubgroup_iff_sq_eq_one hP
  have hΩcard : Nat.card ↥(involutionSubgroup P) = 2 ^ n := by
    have h1 : (1 : P) ∈ (involutionSubgroup P : Set P) :=
      (involutionSubgroup P).one_mem
    have hstep : (((involutionSubgroup P : Set P)) \ {1}).ncard + 1 =
        (involutionSubgroup P : Set P).ncard :=
      Set.ncard_diff_singleton_add_one h1 (Set.toFinite _)
    rw [← involutions_eq_involutionSubgroup_diff_identity hP, hinvcard] at hstep
    have h2 : (involutionSubgroup P : Set P).ncard =
        Nat.card ↥(involutionSubgroup P) :=
      (Nat.card_coe_set_eq _).symm
    rw [h2] at hstep
    have hge := Nat.one_le_two_pow (n := n)
    omega
  -- `Ω` is central, normal, invariant
  have hΩle_center : involutionSubgroup P ≤ Subgroup.center P := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact involutions_subset_center_of_transitive hP2 K hreg.transitive
        ⟨(hΩmem x).mp hx, hx1⟩
  haveI hΩnormal : (involutionSubgroup P).Normal := by
    constructor
    intro x hx g
    have hxc := Subgroup.mem_center_iff.mp (hΩle_center hx) g
    have heq : g * x * g⁻¹ = x := by
      rw [hxc]
      group
    rw [heq]
    exact hx
  have hΩinv : IsAInvariant K.subtype (involutionSubgroup P) := by
    intro a
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (K.subtype a)⁻¹ x ∈ involutionSubgroup P ↔
      x ∈ involutionSubgroup P
    rw [hΩmem, hΩmem]
    constructor
    · intro h
      have hx : (K.subtype a) ((K.subtype a)⁻¹ x) = x := by
        simp
      rw [← hx, ← map_pow, h, map_one]
    · intro h
      rw [← map_pow, h, map_one]
  have hΩbot : involutionSubgroup P ≠ ⊥ := by
    intro h
    have hu : u₀ ∈ involutionSubgroup P := (hΩmem u₀).mpr hu₀.1
    rw [h] at hu
    exact hu₀.2 (Subgroup.mem_bot.mp hu)
  -- the quotient has order `q²`
  have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow_iff.mpr hn
  have hQcard : Nat.card (P ⧸ involutionSubgroup P) = 2 ^ (2 * n) := by
    have hsplit : Nat.card P =
        Nat.card (P ⧸ involutionSubgroup P) *
          Nat.card ↥(involutionSubgroup P) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hcard, hΩcard] at hsplit
    have hq0 : 0 < 2 ^ n := by positivity
    have : (2 ^ n) ^ 3 = ((2 : ℕ) ^ (2 * n)) * 2 ^ n := by
      rw [← pow_add, ← pow_mul]
      ring_nf
    rw [this] at hsplit
    exact Nat.eq_of_mul_eq_mul_right hq0 hsplit.symm
  haveI hQP2 : IsPGroup 2 (P ⧸ involutionSubgroup P) := hP2.to_quotient _
  haveI hQnontriv : Nontrivial (P ⧸ involutionSubgroup P) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hQcard]
    exact Nat.one_lt_two_pow_iff.mpr (by omega)
  -- a proper nontrivial invariant normal subgroup of the quotient
  have hVexists : ∃ V : Subgroup (P ⧸ involutionSubgroup P), V ≠ ⊥ ∧
      V ≠ ⊤ ∧ V.Normal ∧
      IsAInvariant (IsAInvariant.quotientMulAutHom hΩinv) V := by
    by_cases hZ : Subgroup.center (P ⧸ involutionSubgroup P) = ⊤
    · -- abelian quotient
      have hcommQ : ∀ a b : P ⧸ involutionSubgroup P, a * b = b * a := by
        intro a b
        have hb : b ∈ Subgroup.center (P ⧸ involutionSubgroup P) := by
          rw [hZ]
          exact Subgroup.mem_top b
        exact Subgroup.mem_center_iff.mp hb a
      by_cases hA : Agemo (P ⧸ involutionSubgroup P) 2 1 = ⊥
      · -- elementary abelian quotient: the module exclusion produces `V`
        have hsqQ : ∀ x : P ⧸ involutionSubgroup P, x ^ 2 = 1 := by
          intro x
          have hx : x ^ 2 ^ 1 ∈ Agemo (P ⧸ involutionSubgroup P) 2 1 :=
            Agemo.mem_of_eq_pow x
          rw [hA] at hx
          simpa using Subgroup.mem_bot.mp hx
        haveI := hKcyc
        have hfree' : ∀ k : ↥K, k ≠ 1 →
            ∀ x : P ⧸ involutionSubgroup P,
              IsAInvariant.quotientMulAutHom hΩinv k x = x → x = 1 := by
          apply OddOrder.Peterfalvi.Appendices.Suzuki2Groups.quotient_fixedPointFree_of_fixedPoints_le
            K.subtype (involutionSubgroup P) hΩinv
          · exact OddOrder.Peterfalvi.Appendices.Suzuki2Groups.card_coprime_of_card_eq_sub_one
              (involutionSubgroup P) (by rw [hKcard, hΩcard])
          · intro k hk x hx
            rw [hfree k hk x hx]
            exact Subgroup.one_mem _
        obtain ⟨V, hVb, hVt, hVi⟩ :=
          exists_proper_invariant_subgroup_of_card_sq hcommQ hsqQ
            (IsAInvariant.quotientMulAutHom hΩinv) hfree' hn hKcard hQcard
        refine ⟨V, hVb, hVt, ?_, hVi⟩
        constructor
        intro x hx g
        have heq : g * x * g⁻¹ = x := by
          rw [hcommQ g x]
          group
        rw [heq]
        exact hx
      · -- `℧₁` is a proper nontrivial characteristic subgroup
        refine ⟨Agemo (P ⧸ involutionSubgroup P) 2 1, hA, ?_, ?_,
          IsAInvariant.of_characteristic _⟩
        · -- not the whole group: squaring would be a bijective endomorphism
          intro htop
          letI : CommGroup (P ⧸ involutionSubgroup P) :=
            { (inferInstance : Group _) with mul_comm := hcommQ }
          have hrange : (powMonoidHom 2 :
              P ⧸ involutionSubgroup P →* P ⧸ involutionSubgroup P).range =
              ⊤ := by
            rw [eq_top_iff, ← htop, Agemo]
            apply (Subgroup.closure_le _).mpr
            rintro g ⟨x, rfl⟩
            exact ⟨x, by simp [powMonoidHom]⟩
          have hinj : Function.Injective (powMonoidHom 2 :
              P ⧸ involutionSubgroup P →* P ⧸ involutionSubgroup P) :=
            Finite.injective_iff_surjective.mpr
              (MonoidHom.range_eq_top.mp hrange)
          -- an element of order two
          obtain ⟨m, hm⟩ := hQP2.exists_card_eq
          have hm0 : m ≠ 0 := by
            intro h0
            rw [h0, pow_zero] at hm
            exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hm
          letI : Fintype (P ⧸ involutionSubgroup P) := Fintype.ofFinite _
          obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card
            (G := P ⧸ involutionSubgroup P) 2 (by
              rw [← Nat.card_eq_fintype_card, hm]
              exact dvd_pow_self 2 hm0)
          have ht1 : t = 1 := by
            apply hinj
            show t ^ 2 = (1 : P ⧸ involutionSubgroup P) ^ 2
            rw [one_pow, ← ht]
            exact pow_orderOf_eq_one t
          rw [ht1, orderOf_one] at ht
          norm_num at ht
        · exact Subgroup.normal_of_characteristic _
    · -- the center of the quotient is proper and nontrivial
      refine ⟨Subgroup.center (P ⧸ involutionSubgroup P), ?_, hZ,
        inferInstance, IsAInvariant.of_characteristic _⟩
      have := hQP2.center_nontrivial
      intro h
      rw [h] at this
      exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
  obtain ⟨V, hVbot, hVtop, hVnormal, hVinv⟩ := hVexists
  -- the preimage gives the middle chain member
  haveI hBnormal : (V.comap
      (QuotientGroup.mk' (involutionSubgroup P))).Normal :=
    Subgroup.Normal.comap hVnormal _
  have hBinv : IsAInvariant K.subtype
      (V.comap (QuotientGroup.mk' (involutionSubgroup P))) :=
    hΩinv.comap_quotient hVinv
  have hΩB : involutionSubgroup P ≤
      V.comap (QuotientGroup.mk' (involutionSubgroup P)) := by
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' (involutionSubgroup P) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact V.one_mem
  have hΩB_ne : involutionSubgroup P ≠
      V.comap (QuotientGroup.mk' (involutionSubgroup P)) := by
    intro heq
    apply hVbot
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (involutionSubgroup P) v
    have hgB : g ∈ V.comap (QuotientGroup.mk' (involutionSubgroup P)) := by
      rw [Subgroup.mem_comap]
      exact hv
    rw [← heq] at hgB
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff g).mpr hgB)
  have hBtop : V.comap (QuotientGroup.mk' (involutionSubgroup P)) ≠ ⊤ := by
    intro h
    apply hVtop
    rw [eq_top_iff]
    intro v _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (involutionSubgroup P) v
    have hg : g ∈ V.comap (QuotientGroup.mk' (involutionSubgroup P)) := by
      rw [h]
      exact Subgroup.mem_top g
    rw [Subgroup.mem_comap] at hg
    exact hg
  -- assemble
  refine ⟨⟨involutionSubgroup P, hΩnormal, hΩinv⟩,
    ⟨V.comap (QuotientGroup.mk' (involutionSubgroup P)), hBnormal, hBinv⟩,
    ?_, ?_, ?_,
    fun A B C D E hAB hBC hCD hDE =>
      no_four_chain_of_card_eq_cube hP2 hn hfree hKcard hcard
        A B C D E hAB hBC hCD hDE⟩
  · rw [← Subtype.coe_lt_coe]
    show (⊥ : Subgroup P) < involutionSubgroup P
    exact bot_lt_iff_ne_bot.mpr hΩbot
  · rw [← Subtype.coe_lt_coe]
    show involutionSubgroup P <
      V.comap (QuotientGroup.mk' (involutionSubgroup P))
    exact lt_of_le_of_ne hΩB hΩB_ne
  · rw [← Subtype.coe_lt_coe]
    show V.comap (QuotientGroup.mk' (involutionSubgroup P)) < ⊤
    exact lt_top_iff_ne_top.mpr hBtop

end OddOrder.Higman.Suzuki2Groups
