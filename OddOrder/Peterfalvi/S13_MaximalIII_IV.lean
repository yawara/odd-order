/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_SixTwoGeneral
import OddOrder.Peterfalvi.S13_SixTwoBridge
import OddOrder.Peterfalvi.S12_MaximalIII_IV_V
import OddOrder.GroupTheory.ElementaryAbelian

/-!
# Peterfalvi Section 13: Maximal Subgroups of Types III and IV

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 13, pp. 64--68.

This section specializes the type-III/IV/V setup of §12 to types III and IV.  It
establishes the commutator-layer identities `M'' = H C`, `H_0 = H'`, `C = U'`,
then proves that `H` is elementary abelian of order `p^q`.  The final character
calculation (11.8)--(11.9) rules out the reducible Clifford case and identifies
the subgroup as type III.

The scaffold keeps the structural and orthogonality calculations as named
propositions on the §13 hypothesis.  This gives later sections stable endpoints
without pretending that the quotient-module and `omega_ij^sigma` API is already
available.
-/

namespace OddOrder.Peterfalvi.S13
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-! ## (11.1): the auxiliary prime inequality -/

/-- For `n >= 5`, the elementary estimate used in **Peterfalvi (11.1)**. -/
private theorem four_mul_sq_add_one_lt_three_pow {n : ℕ} (hn : 5 ≤ n) :
    4 * n ^ 2 + 1 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
  | succ n hn ih =>
      have hstep : 4 * (n + 1) ^ 2 + 1 < 3 * (4 * n ^ 2 + 1) := by
        nlinarith [hn]
      calc
        4 * (n + 1) ^ 2 + 1 < 3 * (4 * n ^ 2 + 1) := hstep
        _ ≤ 3 * 3 ^ n := Nat.mul_le_mul_left 3 ih.le
        _ = 3 ^ (n + 1) := by rw [pow_succ]; omega

/-- **Peterfalvi (11.1)**: if `p` and `q` are distinct odd primes, then
`p^q > 4 q^2 + 1`. -/
theorem prime_pow_gt_four_mul_sq_add_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hpq : p ≠ q) :
    4 * q ^ 2 + 1 < p ^ q := by
  have hp_three : 3 ≤ p := by
    have hp_two : 2 ≤ p := hp.two_le
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      subst p
      rcases hpodd with ⟨k, hk⟩
      omega
    omega
  have hq_three : 3 ≤ q := by
    have hq_two : 2 ≤ q := hq.two_le
    have hq_ne_two : q ≠ 2 := by
      intro hq2
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    omega
  rcases lt_trichotomy p q with hp_lt_q | hp_eq_q | hq_lt_p
  · have hq_five : 5 ≤ q := by
      have hpq_succ : p + 1 ≤ q := Nat.succ_le_of_lt hp_lt_q
      have hq_ne_four : q ≠ 4 := by
        intro hq4
        subst q
        rcases hqodd with ⟨k, hk⟩
        omega
      omega
    calc
      4 * q ^ 2 + 1 < 3 ^ q := four_mul_sq_add_one_lt_three_pow hq_five
      _ ≤ p ^ q := Nat.pow_le_pow_left hp_three q
  · exact (hpq hp_eq_q).elim
  · have hbase : q + 1 ≤ p := Nat.succ_le_of_lt hq_lt_p
    have hqpow_le : (q + 1) ^ q ≤ p ^ q := Nat.pow_le_pow_left hbase q
    have hqpow_large : 4 * q ^ 2 + 1 < (q + 1) ^ q := by
      have hqpow_three : (q + 1) ^ 3 ≤ (q + 1) ^ q :=
        pow_le_pow_right' (by omega) hq_three
      have hpoly : 4 * q ^ 2 + 1 < (q + 1) ^ 3 := by
        nlinarith [hq_three]
      exact hpoly.trans_le hqpow_three
    exact hqpow_large.trans_le hqpow_le

/-! ## (11.2): Type III/IV setup -/

/-- **Peterfalvi (11.2)**: the Type III/IV specialization of §12.

`SOf X` is Peterfalvi's `S(X) = {chi in S | X <= Ker chi}`.  The fields ending
in `Formula` are the named algebraic or character-theoretic calculations proved
throughout §13. -/
structure Hypothesis (M : Subgroup G) where
  [finiteG : Finite G]
  base : OddOrder.Peterfalvi.S12.Hypothesis M
  params : OddOrder.Peterfalvi.S12.CharacterParameters base
  type_alt : IsTypeIII M ∨ IsTypeIV M
  s11Setup : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M
  chief : OddOrder.Peterfalvi.S11.ChiefFactorData s11Setup
  /-- **(11.2)**: the §11 chief-factor setup and the §12 base hypothesis share the *same* type-`P`
  structure `(H, U, W₁, W₂)`.  Peterfalvi (11.2) fixes a single such structure for `M`; this field
  records that the chief factor `H̄ = H/H₀` (built on `s11Setup`) sits over the very same
  `H = M_F`, `W₁`, `W₂` as the `base` (§12) hypothesis.  A faithful producer builds `s11Setup` from
  `base.typeP`, so this holds by `rfl` there. -/
  setup_typeP_eq : s11Setup.typeP = base.typeP
  C : Subgroup G
  C_le_U : C ≤ base.typeP.U
  /-- **(11.2)**: `C = C_U(H)`, the centralizer of `H` in `U`. -/
  C_eq_centralizer :
    C = base.typeP.U ⊓ Subgroup.centralizer (base.typeP.H : Set G)
  /-- **(8.5.a) normality of `C`**: `M` normalizes `C`.  Discharge route for the producer:
  `C` is the `π(H)`-complement `O_{π(H)'}(F(M))` of the Hall part `H = M_F` in the Fitting
  subgroup `F(M) = H·C` (`TypePData.fitting_eq` + `C_eq_centralizer`), hence characteristic
  in `F(M)` and normal in `M`. -/
  C_normalized_by_M : M ≤ Subgroup.normalizer (C : Set G)
  Hprime : Subgroup G
  Hprime_eq : Hprime = derivedInG base.typeP.H
  Uprime : Subgroup G
  Uprime_eq : Uprime = derivedInG base.typeP.U
  SOf : Subgroup G → Set (ClassFunction ↥M ℂ)
  /-- **(11.2) family pin**: `S(X)` is the source-kernel filtration of the §10 induced family
  (Coq `seqIndD M' M M' X`) — the general kernel-filter family of `S08_SixTwoGeneral`, through
  which the whole general-(6.2) layer (orthogonality/norms/real-freeness/B2/h56 producer,
  issue 2022) applies to `S(X)`.  At `X = ⊥` this is `base.Sset`
  (`S12.inducedFamily_eq_inducedKernelFamily_bot`). -/
  SOf_eq : ∀ X : Subgroup G, SOf X = OddOrder.Peterfalvi.S08.inducedKernelFamily
    ((derivedInG M).subgroupOf M) (X.subgroupOf M)
  notOrthogonalFormula : ClassFunction ↥M ℂ → Prop
  finalOrthogonalityFormula : ClassFunction ↥M ℂ → Prop
  caseB_of_97 : Prop

namespace Hypothesis

/-- Peterfalvi's `H`. -/
def H {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.base.typeP.H

/-- Peterfalvi's `U`. -/
def U {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.base.typeP.U

/-- Peterfalvi's `p = |W_2|`. -/
noncomputable def p {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  hyp.base.w2

/-- Peterfalvi's `q = |W_1|`. -/
noncomputable def q {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  hyp.base.w1

/-- Peterfalvi's `H_0 C`. -/
def H0C {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.chief.H0 ⊔ hyp.C

/-- Peterfalvi's `H C`. -/
def HC {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.H ⊔ hyp.C

/-- **Peterfalvi (11.5), inclusion `M'' ⊆ HC` (= (8.4.c)/(8.5.a))**: the second derived
subgroup is contained in `HC`.  This is the unconditional half of (11.5); it follows from
the type-`P` Fitting bound `TypePData.secondDerived_le_fitting` (`M'' ≤ H ⊔ (U ∩ C_G(H))`,
Peterfalvi (8.5.a)) together with `C = C_U(H) = U ∩ C_G(H)` (the `C_eq_centralizer` field).
The reverse inclusion is the coherence content carried by `S13.secondDerived_eq_HC`. -/
theorem secondDerived_le_HC {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M ≤ hyp.HC := by
  change secondDerivedInAmbient M ≤ hyp.base.typeP.H ⊔ hyp.C
  rw [hyp.C_eq_centralizer]
  exact hyp.base.typeP.secondDerived_le_fitting

/-- **Peterfalvi (11.6), inclusion `U' ⊆ C`**: the derived subgroup `U' = [U,U]` is contained
in `C = C_U(H)`.  This is the unconditional half of the `C = U'` clause of (11.6): `[U,U]`
centralizes `H` (Peterfalvi (8.5.b), `S11.typeP_commutator_U_centralizes_H`) and lies in `U`,
so `U' = [U,U] ⊆ U ∩ C_G(H) = C`.  The reverse inclusion `C ⊆ U'` is the coherence content
carried by `S13.core_structure`. -/
theorem derivedU_le_C {M : Subgroup G} (hyp : Hypothesis M) :
    derivedInG hyp.U ≤ hyp.C := by
  change derivedInG hyp.base.typeP.U ≤ hyp.C
  rw [hyp.C_eq_centralizer]
  refine le_inf (Subgroup.map_subtype_le _) ?_
  rw [show derivedInG hyp.base.typeP.U = ⁅hyp.base.typeP.U, hyp.base.typeP.U⁆
        from Subgroup.map_subtype_commutator hyp.base.typeP.U]
  exact OddOrder.Peterfalvi.S11.typeP_commutator_U_centralizes_H hyp.base.typeP

/-- `H₀C ≤ M'`: both joinands lie in the derived subgroup (`H₀ ≤ H ≤ M'`, `C ≤ U ≤ M'`). -/
theorem H0C_le_derived {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.H0C ≤ derivedInG M := by
  refine sup_le ?_ (hyp.C_le_U.trans hyp.base.typeP.U_le)
  have h1 : hyp.chief.H0 ≤ hyp.s11Setup.typeP.H := hyp.chief.H0_lt_H.le
  rw [hyp.setup_typeP_eq] at h1
  exact h1.trans hyp.base.typeP.H_le

/-- `HC ≤ M'`. -/
theorem HC_le_derived {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.HC ≤ derivedInG M :=
  sup_le hyp.base.typeP.H_le (hyp.C_le_U.trans hyp.base.typeP.U_le)

/-- **`M` normalizes `H₀C`** (`H₀ ⊴ M` from the chief data, `C ⊴ M` from (8.5.a)). -/
theorem H0C_normalized_by_M {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer ((hyp.H0C : Subgroup G) : Set G) :=
  le_trans (le_inf hyp.chief.H0_normalized_by_M hyp.C_normalized_by_M)
    (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- **`M` normalizes `H = M_F`** (the maximal nilpotent normal Hall subgroup). -/
theorem H_normalized_by_M [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer ((hyp.H : Subgroup G) : Set G) := by
  have h := (Subgroup.normal_subgroupOf_iff_le_normalizer
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le M)).mp
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M)
  change M ≤ Subgroup.normalizer ((hyp.base.typeP.H : Subgroup G) : Set G)
  rw [hyp.base.typeP.H_eq]
  exact h

/-- **`M` normalizes `HC`**. -/
theorem HC_normalized_by_M [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer ((hyp.HC : Subgroup G) : Set G) :=
  le_trans (le_inf hyp.H_normalized_by_M hyp.C_normalized_by_M)
    (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- `(H₀C).subgroupOf M` is normal in `↥M`. -/
theorem H0C_subgroupOf_normal {M : Subgroup G} (hyp : Hypothesis M) :
    ((hyp.H0C.subgroupOf M)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (hyp.H0C_le_derived.trans (Subgroup.map_subtype_le _))).mpr hyp.H0C_normalized_by_M

/-- `(HC).subgroupOf M` is normal in `↥M`. -/
theorem HC_subgroupOf_normal [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    ((hyp.HC.subgroupOf M)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (hyp.HC_le_derived.trans (Subgroup.map_subtype_le _))).mpr hyp.HC_normalized_by_M

/-- `H ⊓ U = ⊥` (the `derived_complement` disjointness, ambient form). -/
theorem H_inf_U_eq_bot {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.base.typeP.H ⊓ hyp.base.typeP.U = ⊥ := by
  have hdisj := hyp.base.typeP.derived_complement.disjoint
  rw [eq_bot_iff]
  intro x hx
  have hxM' : x ∈ derivedInG M := hyp.base.typeP.H_le hx.1
  have h1 := hdisj.le_bot (⟨hx.1, hx.2⟩ :
    (⟨x, hxM'⟩ : ↥(derivedInG M)) ∈ hyp.base.typeP.H.subgroupOf (derivedInG M) ⊓
      hyp.base.typeP.U.subgroupOf (derivedInG M))
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

/-- The chief inequality `H₀ < H`, transported to the `base` type-`P` structure. -/
theorem H0_lt_H {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.chief.H0 < hyp.base.typeP.H := by
  have h : hyp.chief.H0 < hyp.s11Setup.typeP.H := hyp.chief.H0_lt_H
  rwa [hyp.setup_typeP_eq] at h

/-- **`H ⊄ H₀C`** — the (11.4)/(11.3) properness input: if `H ≤ H₀C` then, decomposing along
the normal factor `H₀.subgroupOf M` inside `↥M` (`Subgroup.normal_mul`), any `h ∈ H ∖ H₀`
splits as `h = a·b` with `a ∈ H₀`, `b ∈ C ⊓ H ≤ U ⊓ H = ⊥`, so `h = a ∈ H₀` — contradiction
with the chief nontriviality `H₀ < H`. -/
theorem H_not_le_H0C {M : Subgroup G} (hyp : Hypothesis M) :
    ¬ hyp.base.typeP.H ≤ hyp.H0C := by
  intro hle
  haveI hH0n : ((hyp.chief.H0).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hyp.H0_lt_H.le.trans (hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)))).mpr
      hyp.chief.H0_normalized_by_M
  obtain ⟨h, hhH, hhH0⟩ := SetLike.exists_of_lt hyp.H0_lt_H
  have hhM : h ∈ M :=
    hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _) hhH
  have hH0le : hyp.chief.H0 ≤ M :=
    hyp.H0_lt_H.le.trans (hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hCle : hyp.C ≤ M :=
    (hyp.C_le_U.trans hyp.base.typeP.U_le).trans (Subgroup.map_subtype_le _)
  -- the trace of `h` lies in `H₀-trace ⊔ C-trace = H₀-trace · C-trace`
  have hmem : (⟨h, hhM⟩ : ↥M) ∈
      (hyp.chief.H0).subgroupOf M ⊔ hyp.C.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hH0le hCle]
    exact Subgroup.mem_subgroupOf.mpr (hle hhH)
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  -- `b = a⁻¹·h ∈ C ⊓ H = ⊥`
  have hbC : ((b : ↥M) : G) ∈ hyp.C := Subgroup.mem_subgroupOf.mp hb
  have haH0 : ((a : ↥M) : G) ∈ hyp.chief.H0 := Subgroup.mem_subgroupOf.mp ha
  have hbH : ((b : ↥M) : G) ∈ hyp.base.typeP.H := by
    have hbeq : (b : ↥M) = (a : ↥M)⁻¹ * ⟨h, hhM⟩ := by
      rw [← hab]; group
    have : ((b : ↥M) : G) = ((a : ↥M) : G)⁻¹ * h := by rw [hbeq]; rfl
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hyp.H0_lt_H.le haH0)) hhH
  have hbU : ((b : ↥M) : G) ∈ hyp.base.typeP.U := hyp.C_le_U hbC
  have hb1 : ((b : ↥M) : G) = 1 := by
    have := hyp.H_inf_U_eq_bot.le ⟨hbH, hbU⟩
    rwa [Subgroup.mem_bot] at this
  -- hence `h = a ∈ H₀`, contradiction
  refine hhH0 ?_
  have hha : h = ((a : ↥M) : G) := by
    have h1 : (⟨h, hhM⟩ : ↥M) = a * b := hab.symm
    have h2 : h = ((a * b : ↥M) : G) := congrArg Subtype.val h1
    rw [h2]
    change ((a : ↥M) : G) * ((b : ↥M) : G) = ((a : ↥M) : G)
    rw [hb1, mul_one]
  rw [hha]
  exact haH0

/-- **`H₀C`-trace is proper in `M'`-trace** — the `hBne` input of the h56 producer at
`B = H₀C`: a full trace would force `M' ≤ H₀C`, hence `H ≤ H₀C` (`H_not_le_H0C`). -/
theorem H0C_trace_ne_top {M : Subgroup G} (hyp : Hypothesis M) :
    (hyp.H0C.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
  intro htop
  refine hyp.H_not_le_H0C ?_
  intro x hx
  have hxM' : x ∈ derivedInG M := hyp.base.typeP.H_le hx
  have hxM : x ∈ M := Subgroup.map_subtype_le _ hxM'
  have hmem : (⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hxM'⟩ :
      ↥((derivedInG M).subgroupOf M)) ∈
      (hyp.H0C.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M) := by
    rw [htop]; trivial
  exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hmem)

/-- **Ambient commutators of `H` lie in `H₀`** (`H/H₀` elementary abelian ⟹ abelian):
`H' ≤ H₀`, elementwise. -/
theorem commutator_mem_H0 {M : Subgroup G} (hyp : Hypothesis M)
    {x y : G} (hx : x ∈ hyp.base.typeP.H) (hy : y ∈ hyp.base.typeP.H) :
    x * y * x⁻¹ * y⁻¹ ∈ hyp.chief.H0 := by
  have hx' : x ∈ hyp.s11Setup.H := by
    change x ∈ hyp.s11Setup.typeP.H
    rw [hyp.setup_typeP_eq]; exact hx
  have hy' : y ∈ hyp.s11Setup.H := by
    change y ∈ hyp.s11Setup.typeP.H
    rw [hyp.setup_typeP_eq]; exact hy
  set xh : ↥hyp.s11Setup.H := ⟨x, hx'⟩ with hxh
  set yh : ↥hyp.s11Setup.H := ⟨y, hy'⟩ with hyh
  have hmk : QuotientGroup.mk' hyp.chief.N (xh * yh * xh⁻¹ * yh⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    have h := hyp.chief.quotient_elementaryAbelian.comm
      (QuotientGroup.mk' hyp.chief.N xh) (QuotientGroup.mk' hyp.chief.N yh)
    rw [h]; group
  have hmem : xh * yh * xh⁻¹ * yh⁻¹ ∈ hyp.chief.N := by
    have := hmk
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at this
  have hmap : ((xh * yh * xh⁻¹ * yh⁻¹ : ↥hyp.s11Setup.H) : G) ∈ hyp.chief.H0 := by
    rw [hyp.chief.H0_eq]
    exact Subgroup.mem_map_of_mem _ hmem
  simpa using hmap

/-- Every element of `C` commutes with every element of `H` (`C = C_U(H)`). -/
theorem commute_of_mem_C_of_mem_H {M : Subgroup G} (hyp : Hypothesis M)
    {c h : G} (hc : c ∈ hyp.C) (hh : h ∈ hyp.base.typeP.H) : Commute c h := by
  have hc' := hyp.C_eq_centralizer ▸ hc
  exact (Subgroup.mem_centralizer_iff.mp hc'.2 h hh).symm

/-- **Ambient commutators of `HC` lie in `H₀C`** — the (11.4) centrality core: writing
`x = h₁c₁`, `y = h₂c₂` (`HC = H·C` along the normal factor `H`, with `C` centralizing `H`),
the commutator splits as `⁅x,y⁆ = ⁅h₁,h₂⁆·⁅c₁,c₂⁆ ∈ H₀·C ⊆ H₀C`
(`commutator_mem_H0` for the `H`-part). -/
theorem commutator_HC_mem_H0C [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {x y : G} (hx : x ∈ hyp.HC) (hy : y ∈ hyp.HC) :
    x * y * x⁻¹ * y⁻¹ ∈ hyp.H0C := by
  -- decompose along the normal factor `H.subgroupOf M` inside `↥M`
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hCle : hyp.C ≤ M := (hyp.C_le_U.trans hyp.base.typeP.U_le).trans
    (Subgroup.map_subtype_le _)
  haveI hHn : ((hyp.base.typeP.H).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr hyp.H_normalized_by_M
  have hdecomp : ∀ z : G, z ∈ hyp.HC → ∃ h ∈ hyp.base.typeP.H, ∃ c ∈ hyp.C, z = h * c := by
    intro z hz
    have hzM : z ∈ M := (hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)) hz
    have hmem : (⟨z, hzM⟩ : ↥M) ∈
        (hyp.base.typeP.H).subgroupOf M ⊔ hyp.C.subgroupOf M := by
      rw [← Subgroup.subgroupOf_sup hHle hCle]
      exact Subgroup.mem_subgroupOf.mpr hz
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    refine ⟨((a : ↥M) : G), Subgroup.mem_subgroupOf.mp ha,
      ((b : ↥M) : G), Subgroup.mem_subgroupOf.mp hb, ?_⟩
    have := congrArg (fun m : ↥M => (m : G)) hab
    simpa using this.symm
  obtain ⟨h₁, hh₁, c₁, hc₁, rfl⟩ := hdecomp x hx
  obtain ⟨h₂, hh₂, c₂, hc₂, rfl⟩ := hdecomp y hy
  -- the swap identity `⁅h₁c₁, h₂c₂⁆ = ⁅h₁,h₂⁆·⁅c₁,c₂⁆`
  have hsw12 : Commute c₁ h₂ := hyp.commute_of_mem_C_of_mem_H hc₁ hh₂
  have hsw11 : Commute c₁ h₁ := hyp.commute_of_mem_C_of_mem_H hc₁ hh₁
  have hsw21 : Commute c₂ h₁ := hyp.commute_of_mem_C_of_mem_H hc₂ hh₁
  have hsw22 : Commute c₂ h₂ := hyp.commute_of_mem_C_of_mem_H hc₂ hh₂
  have hkey : h₁ * c₁ * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹
      = (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
    have e12 : c₁ * h₂ = h₂ * c₁ := hsw12
    have e11 : c₁ * h₁⁻¹ = h₁⁻¹ * c₁ := hsw11.inv_right
    have e21 : c₂ * h₁⁻¹ = h₁⁻¹ * c₂ := hsw21.inv_right
    have e22 : c₂ * h₂⁻¹ = h₂⁻¹ * c₂ := hsw22.inv_right
    have e12i : c₁⁻¹ * h₂⁻¹ = h₂⁻¹ * c₁⁻¹ := (hsw12.inv_inv)
    have e22i : c₂ * h₂ = h₂ * c₂ := hsw22
    -- normalize both sides via the four swaps
    calc h₁ * c₁ * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹
        = h₁ * (c₁ * h₂) * c₂ * (c₁⁻¹ * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by group
      _ = h₁ * (h₂ * c₁) * c₂ * (c₁⁻¹ * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by rw [e12]
      _ = h₁ * h₂ * (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ * (c₂⁻¹ * h₂⁻¹) := by group
      _ = h₁ * h₂ * h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by
          have hcomm3 : (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ = h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) := by
            have a1 : Commute (c₁ * c₂ * c₁⁻¹) h₁⁻¹ :=
              ((hsw11.mul_left hsw21).mul_left hsw11.inv_left).inv_right
            exact a1
          rw [show h₁ * h₂ * (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ * (c₂⁻¹ * h₂⁻¹)
              = h₁ * h₂ * ((c₁ * c₂ * c₁⁻¹) * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) from by group,
            hcomm3]
          group
      _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
          have hcomm4 : (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * h₂⁻¹ = h₂⁻¹ * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
            have a1 : Commute (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) h₂⁻¹ :=
              (((hsw12.mul_left hsw22).mul_left hsw12.inv_left).mul_left
                hsw22.inv_left).inv_right
            exact a1
          rw [show h₁ * h₂ * h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) * (c₂⁻¹ * h₂⁻¹)
              = h₁ * h₂ * h₁⁻¹ * ((c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * h₂⁻¹) from by group,
            hcomm4]
          group
  rw [hkey]
  have hHpart : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ ∈ hyp.chief.H0 := hyp.commutator_mem_H0 hh₁ hh₂
  have hCpart : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ hyp.C :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc₁ hc₂)
      (Subgroup.inv_mem _ hc₁)) (Subgroup.inv_mem _ hc₂)
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hHpart) (Subgroup.mem_sup_right hCpart)

end Hypothesis

/-! ## (11.3)--(11.5): commutator-chain consequences -/

/-- **Peterfalvi (11.3), the Theorem (6.3) coherence-extension input** (§13 instance): if the
sub-family `S(H₀C)` is coherent, then so is the full family `S`.

This is Peterfalvi's Theorem (6.3) applied with `(L, K, M, H, H₁) = (M, M', 1, HC, H₀C)`; its
hypotheses hold in the §13 setup ((6.3.a) `HC` nilpotent — `H = M_F` nilpotent and `C = C_U(H)`
centralizes `H`; (6.3.b) from the coherence of `S(H₀C)`; (6.3.c) from (9.6)/(11.1)).  Left as a
named obligation: the repo's §6 coherence is packaged through the `SibleyDadeHypothesis`
filtration machinery (`S08_Theorem63`), not as a standalone "subfamily-coherent ⟹ coherent"
statement, so discharging this is §6 character theory (lane-b). -/
theorem coherent_S_of_coherent_SH0C [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M)
    (_hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau hyp.base.Sset hyp.base.A0) := by
  sorry

/-- **Peterfalvi (11.3)**: `S(H_0 C)` is not coherent.

If it were, Theorem (6.3) (`coherent_S_of_coherent_SH0C`) would make the full family `S` coherent,
contradicting Theorem (10.8) (`S12.S_not_coherent`).  The theorem is thereby reduced, with no
`sorry` of its own, to those two cited results. -/
theorem S_H0C_not_coherent [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) :=
  fun hcoh => OddOrder.Peterfalvi.S12.S_not_coherent _hG hyp.base
    (coherent_S_of_coherent_SH0C _hG hyp hcoh)

/-- **Peterfalvi (11.4)**: if `S(H_1)` is coherent for a normal subgroup `H_1 < M'`,
then `|M'/H_1| - 1 ≤ 2 q |U/C|` (the quotient bound from Theorem (6.2)), stated here in
the subtraction-free form `|M' : H_1| ≤ 2 q |U : C| + 1`. -/
theorem coherent_quotient_bound [Finite G] [Fintype G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H1 : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) (hH1_norm : M ≤ Subgroup.normalizer (H1 : Set G))
    (hH1_lt : H1 < derivedInG M)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf H1) hyp.base.A0)) :
    H1.relIndex (derivedInG M) ≤ 2 * hyp.q * hyp.C.relIndex hyp.U + 1 := by
  sorry

/-- **Peterfalvi (11.5), reverse inclusion `HC ⊆ M''`** (named obligation): the coherence content
of (11.5).  Since `M'/M''` is abelian, `S(M'')` is coherent by (5.7); the quotient bound (11.4)
together with (11.1)/(9.6) then forces `M'' = HC`.  Char-gated — it bottoms out in Theorem (10.8)
via (11.3)/(11.4) — so it is left as a clean named subgroup-inclusion obligation. -/
theorem HC_le_secondDerived [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.HC ≤ secondDerivedInAmbient M := by
  sorry

/-- **Peterfalvi (11.5)**: the second derived subgroup is `H C`, i.e. `M'' = HC`.

`M'' ⊆ HC` is unconditional ((8.5.a), `secondDerived_le_HC`); the reverse `HC ⊆ M''` is the
coherence content carried by `HC_le_secondDerived`.  The theorem composes the two with no `sorry`
of its own. -/
theorem secondDerived_eq_HC [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M = hyp.HC :=
  le_antisymm hyp.secondDerived_le_HC (HC_le_secondDerived _hG hyp)

/-! ## (11.6)--(11.7): the core structure of `H` and `U` -/

/-- **Peterfalvi (11.6), the `U`-centralizes-`H_0` clause via Wielandt (9.1)**: if the cyclic
factor `W_1` acts fixed-point-freely on the chief subgroup `H_0` (`C_{H_0}(W_1) = 1`), then the
Frobenius kernel `U` centralizes `H_0`.

This is the ambient-form Wielandt corollary `frobenius_kernel_centralizes_of_complement_fpf`
(lane-h's (9.1)) applied to the Frobenius group `U W_1` (`typeP_uW1_frobenius`) acting coprimely
on `H_0 ≤ H = M_F`.  The fixed-point-free hypothesis `hfpf` and `U ≠ 1` (`hU`) are the §8/carrier
inputs (in Peterfalvi, `C_{H_0}(W_1) = 1` comes from (9.6) and `|W_2| = p`); the Wielandt content
itself is unconditional and axiom-clean. -/
theorem U_centralizes_H0_of_W1_fpf [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (hU : hyp.base.typeP.U ≠ ⊥)
    (hfpf : ∀ n ∈ hyp.chief.H0,
      (∀ w ∈ hyp.base.typeP.W1, w * n * w⁻¹ = n) → n = 1) :
    hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) := by
  -- `H_0 ≤ H = M_F` (the two type-`P` witnesses share `M_F = maxNilpotentNormalHall M`).
  have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
    rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
  have hH0le : hyp.chief.H0 ≤ hyp.base.typeP.H := hHH ▸ hyp.chief.H0_lt_H.le
  -- `U ⊔ W_1 ≤ M ≤ N_G(H_0)`.
  have hUM : hyp.base.typeP.U ≤ M := hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _)
  have hUEnorm : hyp.base.typeP.U ⊔ hyp.base.typeP.W1 ≤
      Subgroup.normalizer (hyp.chief.H0 : Set G) :=
    sup_le (hUM.trans hyp.chief.H0_normalized_by_M)
      (hyp.base.typeP.W1_le.trans hyp.chief.H0_normalized_by_M)
  -- `H_0` is solvable (subgroup of the nilpotent Fitting-type Hall `M_F`).
  haveI : Group.IsNilpotent ↥hyp.base.typeP.H := by
    rw [hyp.base.typeP.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
  haveI : IsSolvable ↥hyp.base.typeP.H := IsNilpotent.to_isSolvable
  haveI : IsSolvable ↥(hyp.chief.H0.subgroupOf hyp.base.typeP.H) := inferInstance
  haveI hsolv : IsSolvable ↥hyp.chief.H0 :=
    solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hH0le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hH0le).symm.injective
  -- coprimality of `|H_0|` (dividing `|M_F|`) to `|U W_1|`.
  have hcop : Nat.Coprime (Nat.card ↥hyp.chief.H0)
      (Nat.card ↥(hyp.base.typeP.U ⊔ hyp.base.typeP.W1)) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hH0le)
      (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 hyp.base.typeP hU)
  exact OddOrder.GroupTheory.frobenius_kernel_centralizes_of_complement_fpf hUEnorm
    (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.base.typeP hU) hsolv hcop hfpf

/-- **Peterfalvi (11.6), the `U`-centralizes-`H_0` clause, gated on `W_2 ⊓ H_0 = ⊥`**: a cleaner
restatement of `U_centralizes_H0_of_W1_fpf` whose hypothesis is the subgroup equation
`W_2 ⊓ H_0 = ⊥` rather than the raw fixed-point-free condition.

The fixed-point-free input `C_{H_0}(W_1) = 1` reduces to `W_2 ⊓ H_0 = ⊥`: any `n ∈ H_0` centralized
by `W_1` lies in `H ⊓ C_G(W_1) = W_2` (`typeP_H_inf_centralizer_W1`), hence in `W_2 ⊓ H_0`.  This
isolates the genuine §8/chief content (`W_2 ⊓ H_0 = ⊥`, which holds because `|W_2| = p` is prime —
`typeIIIorIV_W2_prime` — and `W_2 ⊄ H_0` from the chief factor) as a single clean obligation. -/
theorem U_centralizes_H0_of_W2_inf_H0_bot [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (hU : hyp.base.typeP.U ≠ ⊥)
    (hbot : hyp.base.typeP.W2 ⊓ hyp.chief.H0 = ⊥) :
    hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) := by
  have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
    rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
  have hH0le : hyp.chief.H0 ≤ hyp.base.typeP.H := hHH ▸ hyp.chief.H0_lt_H.le
  refine U_centralizes_H0_of_W1_fpf hyp hU (fun n hn hcent => ?_)
  have hnW2 : n ∈ hyp.base.typeP.W2 := by
    rw [← OddOrder.Peterfalvi.S11.typeP_H_inf_centralizer_W1 hyp.base.typeP]
    refine Subgroup.mem_inf.mpr ⟨hH0le hn, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    exact fun w hw => mul_inv_eq_iff_eq_mul.mp (hcent w hw)
  have hmem : n ∈ hyp.base.typeP.W2 ⊓ hyp.chief.H0 := ⟨hnW2, hn⟩
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- **Peterfalvi (9.6) for §13, the `W₂ ⊓ H₀ = ⊥` core**: the cyclic factor `W₂ = C_H(W₁)` meets the
chief subgroup `H₀` trivially.

Since `|W₂| = p` is prime (`ChiefFactorData.typeIII_IV_p_eq_W2`), `W₂ ⊓ H₀` is `⊥` or `W₂`.  The
chief-factor computation `|C_{H̄}(W₁)| = p` (`coprimeFrobeniusChiefFactor_card`, the second component)
shows the image `W̄₂` of `W₂` in `H̄ = H/H₀` is nontrivial, so `W₂ ⊄ H₀`, ruling out `W₂ ⊓ H₀ = W₂`.
This is the genuine §8/chief input behind the fixed-point-free hypothesis `C_{H₀}(W₁) = 1` of
`U_centralizes_H0_of_W2_inf_H0_bot`; it is unconditional (no character input). -/
theorem chief_W2_inf_H0_eq_bot [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.s11Setup.typeP.W2 ⊓ hyp.chief.H0 = ⊥ := by
  set data := hyp.s11Setup.typeP with hdata
  have hU : data.U ≠ ⊥ := hyp.s11Setup.nontrivial.1
  -- `F` = the `W₁`-fixed points of the conjugation action on `H`; `F` maps onto `W₂`, and `H₀` is the
  -- image of the chief-factor kernel `N`.
  set F : Subgroup ↥data.H :=
    fixedSubgroup (OddOrder.Peterfalvi.S11.typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1)) with hF
  have hFW2 : F.map data.H.subtype = data.W2 := by
    rw [hF, OddOrder.Peterfalvi.S11.typeP_fixedSubgroup_map data le_sup_right,
      OddOrder.Peterfalvi.S11.typeP_H_inf_centralizer_W1]
  have hH0 : hyp.chief.H0 = hyp.chief.N.map data.H.subtype := hyp.chief.H0_eq
  -- the quotient chief-factor action and the order `|C_{H̄}(W₁)| = p`.
  set act := OddOrder.Peterfalvi.S11.typeP_quotientCoprimeAction data hU hyp.chief.N_aInvariant
    with hact
  have hcopHW1 : Nat.Coprime
      (Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1))) (Nat.card ↥data.H) :=
    (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left
      (Subgroup.card_subgroup_dvd_card _)
  haveI : IsSolvable ↥data.H := (OddOrder.Peterfalvi.S11.typeP_coprimeAction data hU).H_solvable
  have hmap : F.map (QuotientGroup.mk' hyp.chief.N) = act.fixedByE :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient hyp.chief.N_aInvariant hcopHW1 (Or.inr inferInstance)
  have hUnorm : act.U.Normal :=
    (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius data hU).isNormal
  have hEcyc : IsCyclic ↥act.fixedByE :=
    OddOrder.Peterfalvi.S11.typeP_quotient_fixedByE_cyclic data hU hyp.chief.N_aInvariant
  have hK1 : Nat.card (↥data.H ⧸ hyp.chief.N) ≠ 1 := by
    have hNtop : hyp.chief.N ≠ ⊤ := by
      intro htop
      have hH0H : hyp.chief.H0 = data.H := by
        rw [hH0, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact absurd (hH0H ▸ hyp.chief.H0_lt_H) (lt_irrefl _)
    exact fun h => hNtop (Subgroup.index_eq_one.mp h)
  have hcardE : Nat.card ↥act.fixedByE = hyp.chief.p :=
    (OddOrder.Peterfalvi.S11.coprimeFrobeniusChiefFactor_card act hUnorm hyp.chief.p_prime
      hyp.chief.quotient_elementaryAbelian hyp.chief.quotient_chiefFactor
      hyp.chief.U_noncentral_on_quotient hEcyc hK1).2
  -- `|W₂| = p` prime, so `|W₂ ⊓ H₀|` divides `p`.
  have hW2p : Nat.card ↥data.W2 = hyp.chief.p := hyp.chief.typeIII_IV_p_eq_W2 hyp.type_alt
  have hp := hyp.chief.p_prime
  have hdvd : Nat.card ↥(data.W2 ⊓ hyp.chief.H0 : Subgroup G) ∣ hyp.chief.p := by
    rw [← hW2p]; exact Subgroup.card_dvd_of_le inf_le_left
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpp
  · exact Subgroup.card_eq_one.mp h1
  · -- `|W₂ ⊓ H₀| = p = |W₂|` ⟹ `W₂ ⊆ H₀` ⟹ `F ≤ N` ⟹ `W̄₂ = ⊥`, contradicting `|C_{H̄}(W₁)| = p`.
    exfalso
    have hle : data.W2 ⊓ hyp.chief.H0 = data.W2 :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (hW2p.trans hpp.symm))
    have hW2H0 : data.W2 ≤ hyp.chief.H0 := hle ▸ inf_le_right
    have hFN : F ≤ hyp.chief.N := by
      have hmm : F.map data.H.subtype ≤ hyp.chief.N.map data.H.subtype := by
        rw [hFW2, ← hH0]; exact hW2H0
      exact (Subgroup.map_le_map_iff_of_injective data.H.subtype_injective).mp hmm
    have hmapbot : F.map (QuotientGroup.mk' hyp.chief.N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']; exact hFN
    rw [← hmap, hmapbot, Subgroup.card_bot] at hcardE
    have := hp.one_lt
    omega

/-- **Peterfalvi (11.6), the `U` centralizes `H₀` clause, unconditional**: the Frobenius kernel `U`
centralizes the chief subgroup `H₀`.

This discharges the second conjunct of (11.6) with *no character input*.  Peterfalvi's chain is:
`C_{H₀}(W₁) = 1` (here `chief_W2_inf_H0_eq_bot`, the `W₂ ⊓ H₀ = ⊥` form of (9.6)), so `U` centralizes
`H₀` by Wielandt (9.1) (`U_centralizes_H0_of_W2_inf_H0_bot`).  The remaining (11.6) conjuncts
(`H` a `p`-group, `H₀ = H'`, `C = U'`) stay gated on (11.5)/(9.3); see `core_structure`. -/
theorem U_centralizes_H0 [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) := by
  have hU : hyp.base.typeP.U ≠ ⊥ := by
    rw [← hyp.setup_typeP_eq]; exact hyp.s11Setup.nontrivial.1
  refine U_centralizes_H0_of_W2_inf_H0_bot hyp hU ?_
  rw [← hyp.setup_typeP_eq]
  exact chief_W2_inf_H0_eq_bot hyp

/-- **Peterfalvi (11.6)**: `H` is a `p`-group, `U` centralizes `H_0`, `H_0 = H'`, and `C = U'`.

The second clause `U` centralizes `H_0` is now **unconditional** (`U_centralizes_H0`, via (9.6)/(9.1)),
and the inclusion `U' ⊆ C` of the last clause is unconditional (`Hypothesis.derivedU_le_C`, from
(8.5.b)).  The remaining three obligations are character-gated: `H` a `p`-group needs (9.3) [`U`
centralizes `O_{p'}(H)`] + (11.5); `H_0 = H'` needs `[BG] 1.6(d)` + (11.5); and the reverse `C ⊆ U'`
needs (11.5) `secondDerived_eq_HC` (itself coherence-gated). -/
theorem core_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    IsPGroup hyp.p ↥hyp.H ∧
      hyp.U ≤ Subgroup.centralizer (hyp.chief.H0 : Set G) ∧
      hyp.chief.H0 = hyp.Hprime ∧ hyp.C = hyp.Uprime := by
  -- Conjunct 2 (`U` centralizes `H_0`) is discharged; the other three stay character-gated.
  refine ⟨?_, U_centralizes_H0 hyp, ?_, ?_⟩
  · -- `H` is a `p`-group: (9.3) [`U` centralizes `O_{p'}(H)`] + (11.5).
    sorry
  · -- `H_0 = H'`: `[BG]` Proposition 1.6(d) + (11.5).
    sorry
  · -- `C = U'`: `U' ⊆ C` is `derivedU_le_C`; reverse `C ⊆ U'` is (11.5)-gated.
    sorry

/-- **Peterfalvi (11.7)**: `H` is elementary abelian of order `p^q`, and
`H_0 = 1`. -/
theorem H_elementaryAbelian [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    IsElementaryAbelian hyp.p ↥hyp.H ∧ Nat.card ↥hyp.H = hyp.p ^ hyp.q ∧
      hyp.chief.H0 = ⊥ := by
  sorry

/-! ## (11.8): the main orthogonality calculation -/

/-- Carrier for the five substeps of Peterfalvi (11.8). -/
structure OrthogonalityData {M : Subgroup G} (hyp : Hypothesis M) where
  zeta : ClassFunction ↥M ℂ
  zeta_mem_SHC : zeta ∈ hyp.SOf hyp.HC
  S1 : Set (ClassFunction ↥M ℂ)
  S2 : Set (ClassFunction ↥M ℂ)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau2 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  beta : ClassFunction G ℂ
  coefficientA : ℤ
  frobenius_setup : Prop
  omega_support_reduction : Prop
  average_formula : Prop
  coefficient_formula : Prop
  coefficient_zero : coefficientA = 0
  conclusion_formula : Prop

/-- **Peterfalvi (11.8.1)--(11.8.4)**: the setup for the coefficient calculation
in the proof of (11.8). -/
theorem orthogonality_setup [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ data : OrthogonalityData hyp,
      data.frobenius_setup ∧ data.omega_support_reduction ∧
        data.average_formula ∧ data.coefficient_formula := by
  sorry

/-- **Peterfalvi (11.8.5)**: the coefficient `a` in the orthogonality
calculation is zero. -/
theorem orthogonality_coefficient_zero [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    data.coefficientA = 0 :=
  -- (11.8.5) is carried as the `coefficient_zero` field of `OrthogonalityData`; the
  -- real `a = 0` content lives in `orthogonality_setup` (11.8.1)-(11.8.4), which
  -- constructs the data.  This is the intended public-name wiring for that field.
  data.coefficient_zero

/-- **Peterfalvi (11.8)**: for `zeta in S(HC)`, the residual character is not
orthogonal to `(Irr W)^sigma`. -/
theorem not_orthogonal_mu0_sub_zeta [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    hyp.notOrthogonalFormula data.zeta := by
  sorry

/-! ## (11.9): final Type III conclusion -/

/-- **Peterfalvi (11.9)**: the final three conclusions of §13: the symmetric
orthogonality statement, `q > p`, and the fact that case (b) of (9.7) holds,
so `M` is of type III. -/
theorem final_typeIII_conclusions [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} (data : OrthogonalityData hyp) :
    hyp.finalOrthogonalityFormula data.zeta ∧ hyp.q > hyp.p ∧
      hyp.caseB_of_97 ∧ IsTypeIII M := by
  sorry

end OddOrder.Peterfalvi.S13
