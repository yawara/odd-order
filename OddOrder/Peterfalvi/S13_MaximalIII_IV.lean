/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_SixTwoGeneral
import OddOrder.Peterfalvi.S13_SixTwoBridge
import OddOrder.GroupTheory.MaximalSubgroupTypeConj
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

/-! ## Character-kernel subgroup (general helper)

The character kernel `ker φ = {g | φ(g) = φ(1)}` of a **genuine** character `φ` is a subgroup:
if `φ = χ_ρ` for a representation `ρ`, the keystone `rep_eq_id_of_character_eq_one` makes
`ρ g = id` exactly on `ker φ`, and `{g | ρ g = id}` is closed under the group operations.  This
is the general fact used by the (11.8.6) world-bridge decomposition below (to push a join
`H ⊔ C` into a single kernel condition).  It is stated for a general finite group and is a
candidate for hoisting to `S03_PreliminaryCharacter` once a second consumer appears. -/
section CharacterKernelSubgroup

open OddOrder.Peterfalvi.S03

variable {Γ : Type*} [Group Γ] [Finite Γ]

/-- **`ker φ` is closed under multiplication for a genuine character `φ`.**  Writing `φ = χ_ρ`,
`rep_eq_id_of_character_eq_one` turns `x, y ∈ ker φ` into `ρ x = ρ y = id`, so `ρ (xy) = id` and
`φ(xy) = tr(id) = φ(1)`. -/
theorem characterKernel_mul_mem {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ)
    {x y : Γ} (hx : x ∈ characterKernel φ) (hy : y ∈ characterKernel φ) :
    x * y ∈ characterKernel φ := by
  classical
  obtain ⟨V, _, _, _, ρ, hchar⟩ := hφ
  have hval : ∀ g : Γ, φ g = ρ.character g := fun g => congrFun hchar g
  rw [mem_characterKernel, characterDegree_def] at hx hy
  have hidx : ρ x = LinearMap.id :=
    rep_eq_id_of_character_eq_one ρ (by simp only [← hval]; exact hx)
  have hidy : ρ y = LinearMap.id :=
    rep_eq_id_of_character_eq_one ρ (by simp only [← hval]; exact hy)
  have hidxy : ρ (x * y) = LinearMap.id := by
    rw [map_mul, hidx, hidy]; ext v; simp
  rw [mem_characterKernel, characterDegree_def, hval (x * y), hval 1,
    show ρ.character (x * y) = LinearMap.trace ℂ V (ρ (x * y)) from rfl, hidxy,
    Representation.char_one, LinearMap.trace_id]

/-- **`ker φ` is closed under inversion for a genuine character `φ`.**  From `ρ x = id`,
`ρ x⁻¹ = (ρ x)⁻¹ = id` (via `ρ x⁻¹ · ρ x = ρ 1 = 1`). -/
theorem characterKernel_inv_mem {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ)
    {x : Γ} (hx : x ∈ characterKernel φ) : x⁻¹ ∈ characterKernel φ := by
  classical
  obtain ⟨V, _, _, _, ρ, hchar⟩ := hφ
  have hval : ∀ g : Γ, φ g = ρ.character g := fun g => congrFun hchar g
  rw [mem_characterKernel, characterDegree_def] at hx
  have hidx : ρ x = LinearMap.id :=
    rep_eq_id_of_character_eq_one ρ (by simp only [← hval]; exact hx)
  have hidinv : ρ x⁻¹ = LinearMap.id := by
    have h1 : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [hidx, show (LinearMap.id : V →ₗ[ℂ] V) = 1 from rfl, mul_one] at h1
    rw [h1]; rfl
  rw [mem_characterKernel, characterDegree_def, hval x⁻¹, hval 1,
    show ρ.character x⁻¹ = LinearMap.trace ℂ V (ρ x⁻¹) from rfl, hidinv,
    Representation.char_one, LinearMap.trace_id]

/-- **The character kernel of a genuine character, packaged as a subgroup.** -/
def characterKernelSubgroup {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ) : Subgroup Γ where
  carrier := characterKernel φ
  one_mem' := one_mem_characterKernel φ
  mul_mem' hx hy := characterKernel_mul_mem hφ hx hy
  inv_mem' hx := characterKernel_inv_mem hφ hx

@[simp] theorem mem_characterKernelSubgroup {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ)
    {g : Γ} : g ∈ characterKernelSubgroup hφ ↔ g ∈ characterKernel φ := Iff.rfl

theorem coe_characterKernelSubgroup {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ) :
    (characterKernelSubgroup hφ : Set Γ) = characterKernel φ := rfl

end CharacterKernelSubgroup

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
  /-- **(10.2)/(10.3) grid pins** (issue 2022 threading): the abstract `CharacterParameters`
  are pinned to the canonical `μ`-grid, its column sign, and the degree-`w₁` member `ζ`.
  `IsMinimalSimpleOdd`/`Odd` are `Prop`s, so the `∀`-quantification is proof-irrelevant. -/
  params_mu_eq : ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hodd : Odd (Nat.card G)),
    params.mu = base.muGrid hG hodd
  params_delta_sign : ∀ (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hodd : Odd (Nat.card G)),
    ∀ j : Fin base.w2, j ≠ 0 → base.muColumnSign hG hodd j = params.delta
  params_delta_pm : params.delta = 1 ∨ params.delta = -1
  params_zeta_mem : params.zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M
  params_zeta_degree : params.zeta 1 = (base.w1 : ℂ)
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

/-- **The §13 hypothesis holds for a type-III/IV maximal subgroup** — the producer connecting the
whole §13 (11.1)–(11.7) theory (and hence (11.5) `secondDerived_eq_HC`, (11.7) `core_structure`) to
the FT spine.  Every field is derived from the §12 hypothesis `hyp`: the (10.2)–(10.3) character
parameters (`exists_charParameters_full`; proof-irrelevance of the `Prop`s `IsMinimalSimpleOdd` and
`Odd` discharges the `∀ hG hodd` fields), the §11 chief-factor setup
(`toTypesIIIIIIVSetup`/`exists_chiefFactorData`), and `C = C_U(H) = U ⊓ C_G(H)` with its `M`-normality
(`S12.typePData_C_normalized_by_M`) and centralizer form.  The formula `Prop`s are unconstrained
placeholder fields. -/
theorem exists_hypothesis_of_isTypeIIIorIV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    ∃ s13 : Hypothesis M, s13.base = hyp := by
  haveI := hyp.finiteG
  classical
  have hnt : OddOrder.GroupTheory.TypePNontrivialCore M hyp.typeP :=
    OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  obtain ⟨params, hmu, _homega, hzmem, hzdeg, _hzconj, hδpm, hδsign⟩ :=
    hyp.exists_charParameters_full hG
  exact ⟨{
    base := hyp
    params := params
    params_mu_eq := fun _ _ => hmu
    params_delta_sign := fun _ _ j hj => hδsign j hj
    params_delta_pm := hδpm
    params_zeta_mem := hzmem
    params_zeta_degree := hzdeg
    type_alt := htype
    s11Setup := hyp.toTypesIIIIIIVSetup htype hnt
    chief := (OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
      (hyp.toTypesIIIIIIVSetup htype hnt)).choose
    setup_typeP_eq := rfl
    C := hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)
    C_le_U := inf_le_left
    C_eq_centralizer := rfl
    C_normalized_by_M := OddOrder.Peterfalvi.S12.typePData_C_normalized_by_M hyp.typeP hnt.1
    Hprime := derivedInG hyp.typeP.H
    Hprime_eq := rfl
    Uprime := derivedInG hyp.typeP.U
    Uprime_eq := rfl
    SOf := fun X => OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (X.subgroupOf M)
    SOf_eq := fun _ => rfl
    notOrthogonalFormula := fun _ => True
    finalOrthogonalityFormula := fun _ => True
    caseB_of_97 := True }, rfl⟩

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

/-- Peterfalvi's `H₀C' = H₀ ⊔ C'` with `C' = [C, C]` (`derivedInG C`) — the (9.11)
`Ptype_core_coherence` trigger set (`Coq S_ H0C'`). -/
noncomputable def H0Cprime {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.chief.H0 ⊔ derivedInG hyp.C

/-- `H₀C' ≤ H₀C` since `C' = [C, C] ≤ C`. -/
theorem H0Cprime_le_H0C {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.H0Cprime ≤ hyp.H0C := by
  show hyp.chief.H0 ⊔ derivedInG hyp.C ≤ hyp.chief.H0 ⊔ hyp.C
  exact sup_le_sup_left (Subgroup.map_subtype_le _) hyp.chief.H0

/-- **World-bridge subset `𝒮(H₀C) ⊆ 𝒮(H₀C')`** (kernel antitone, `C' = [C,C] ≤ C`, so
`H₀C' ≤ H₀C`).  Composed with `isCoherent_of_subset` this restricts the (9.11) coherence of the
`H₀C'` family to the capstone's `hY = coherent(𝒮(H₀C))` input (once a nonzero `𝒮(H₀C)` witness is
supplied).  The `hY`-route subset step (`coherent(𝒮(H₀C')) → coherent(𝒮(H₀C))`). -/
theorem sOf_H0C_subset_sOf_H0Cprime [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C
      ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime :=
  OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hyp.H0Cprime_le_H0C

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

/-- **World-bridge (subset direction, S12:4055)**: the §9 induced family `𝒮(Y) = sOf` (induced from
`HU`-sources nontrivial on `H` and killing `Y`) is contained in the §10/§13 kernel-filtered family
`S(Y) = SOf Y = inducedKernelFamily M' Y` (induced from *all* nontrivial `M'`-sources killing `Y`).
Both induce from `M' = HU` (`huSub_eq_derivedInG_subgroupOf`); the `H ⊄ Ker` condition of `xiSet`
gives the `θ ≠ 1` of `inducedKernelFamily`.  This is one half of the world-bridge; the reverse
decomposition `SOf(H₀C) = SHCSet ⊔ sOf(H₀C)` is the remaining direction. -/
theorem sOf_subset_SOf [Finite G] {M : Subgroup G} (hyp : Hypothesis M) (Y : Subgroup G) :
    OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ⊆ hyp.SOf Y := by
  classical
  have hHU : OddOrder.Peterfalvi.S11.huSub hyp.s11Setup = (derivedInG M).subgroupOf M :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf hyp.s11Setup
  rintro _ ⟨χ, hχ, rfl⟩
  rw [hyp.SOf_eq, ← hHU, OddOrder.Peterfalvi.S08.mem_inducedKernelFamily]
  refine ⟨χ, ?_, hχ.2, OddOrder.Peterfalvi.S11.induceHU_eq_induce hyp.s11Setup χ⟩
  intro htriv
  exact hχ.1 (by rw [htriv]; simp [OddOrder.Peterfalvi.S03.characterKernel])

/-- **`𝒮(Y) = sOf data Y` is closed under complex conjugation** (parallel to
`inducedKernelFamily_closedUnderConjugate`): conjugating the source `χ` preserves membership in
`𝒳(Y)` — the kernel is conjugation-invariant (`characterKernel_conj`), so both `H ⊄ Ker χ`
(`xiSet`) and `Y ⊆ Ker χ` are preserved — and `induceHU` commutes with conjugation
(`induceHU_eq_induce` + `ClassFunction.induce_conj`).  The conjugate-closure input of the (11.8.6)
`𝒮(H₀C)` witness (`hwit`). -/
theorem sOf_closedUnderConjugate [Finite G] {M : Subgroup G}
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M) (Y : Subgroup G) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (OddOrder.Peterfalvi.S11.sOf data Y) := by
  classical
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro φ hφ
  obtain ⟨χ, hχ, rfl⟩ := hφ
  set χc : IrreducibleCharacter ↥(OddOrder.Peterfalvi.S11.huSub data) :=
    ⟨(χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ).conj, χ.isIrreducible.conj⟩
    with hχcdef
  have hk : OddOrder.Peterfalvi.S03.characterKernel
      (χc : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)
      = OddOrder.Peterfalvi.S03.characterKernel
        (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ) :=
    OddOrder.Peterfalvi.S03.characterKernel_conj _
  refine ⟨χc, ⟨?_, ?_⟩, ?_⟩
  · -- `χc ∈ xiSet`: `H ⊄ Ker χc = Ker χ`
    have h1 := hχ.1
    simp only [OddOrder.Peterfalvi.S11.xiSet, Set.mem_setOf_eq] at h1 ⊢
    rwa [hk]
  · -- `Y ⊆ Ker χc = Ker χ`
    rw [hk]; exact hχ.2
  · -- `(induceHU χ).conj = induceHU χc`
    rw [OddOrder.Peterfalvi.S11.induceHU_eq_induce data
        (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ),
      OddOrder.Peterfalvi.S11.induceHU_eq_induce data
        (χc : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)]
    exact ClassFunction.induce_conj (OddOrder.Peterfalvi.S11.huSub data)
      (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)

/-- **World-bridge decomposition (reverse of `sOf_subset_SOf`, S12:4055)**: the §10/§13
kernel-filtered family `S(H₀C) = SOf(H₀C)` decomposes as the degree-`q` family `S(HC) = SOf(HC)`
together with the §9 family `𝒮(H₀C) = sOf(H₀C)`.  This is Peterfalvi's `S(H₀C) = S₁ ⊔ S₂` (11.8,
`S₁ = S(HC)`, `S₂ = 𝒮(H₀C)`), split by whether the source contains `H` in its kernel.

*Covering.* A source `θ` of `SOf(H₀C)` (irreducible, `θ ≠ 1`, `H₀C ≤ Ker θ`): if `H ≤ Ker θ` then,
since `C ≤ H₀C ≤ Ker θ` and `Ker θ` is a subgroup for the genuine `θ` (`characterKernelSubgroup`),
`HC = H ⊔ C ≤ Ker θ`, so `Ind θ ∈ SOf(HC)`; if `H ⊄ Ker θ` then `θ ∈ 𝒳` and `Ind θ ∈ sOf(H₀C)`.
*Reverse.* `SOf(HC) ⊆ SOf(H₀C)` (kernel antitone, `H₀C ≤ HC`) and `sOf(H₀C) ⊆ SOf(H₀C)`
(`sOf_subset_SOf`).  This is the second half of the world-bridge; the (11.8.6) capstone glues the
`S(HC)`-coherence (`SHC_isCoherent`) and the `𝒮(H₀C)`-coherence (9.11) along this decomposition. -/
theorem SOf_H0C_eq_SOf_HC_union_sOf [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.SOf hyp.H0C
      = hyp.SOf hyp.HC ∪ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C := by
  classical
  have hHU : OddOrder.Peterfalvi.S11.huSub hyp.s11Setup = (derivedInG M).subgroupOf M :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf hyp.s11Setup
  have hHM : hyp.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hCM : hyp.C ≤ M :=
    (hyp.C_le_U.trans hyp.base.typeP.U_le).trans (Subgroup.map_subtype_le _)
  have hH0C_le_HC : hyp.H0C ≤ hyp.HC := by
    have hH0H : hyp.chief.H0 ≤ hyp.H := by
      have h : hyp.chief.H0 < hyp.s11Setup.typeP.H := hyp.chief.H0_lt_H
      rw [hyp.setup_typeP_eq] at h
      exact h.le
    exact sup_le_sup_right hH0H hyp.C
  have hH_huSub : hyp.H.subgroupOf M ≤ OddOrder.Peterfalvi.S11.huSub hyp.s11Setup := by
    rw [hHU]; exact Subgroup.subgroupOf_mono M hyp.base.typeP.H_le
  have hC_huSub : hyp.C.subgroupOf M ≤ OddOrder.Peterfalvi.S11.huSub hyp.s11Setup := by
    rw [hHU]; exact Subgroup.subgroupOf_mono M (hyp.C_le_U.trans hyp.base.typeP.U_le)
  apply Set.Subset.antisymm
  · -- covering: `SOf(H₀C) ⊆ SOf(HC) ∪ sOf(H₀C)`
    intro φ hφ
    rw [hyp.SOf_eq, ← hHU, OddOrder.Peterfalvi.S08.mem_inducedKernelFamily] at hφ
    obtain ⟨θ, hθne, hθker, rfl⟩ := hφ
    by_cases hH :
        (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup :
            Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup))
          ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)
    · -- `H ≤ Ker θ`: `Ind θ ∈ SOf(HC)`
      left
      rw [hyp.SOf_eq, ← hHU, OddOrder.Peterfalvi.S08.mem_inducedKernelFamily]
      refine ⟨θ, hθne, ?_, rfl⟩
      rw [← coe_characterKernelSubgroup θ.isIrreducible.isCharacter, SetLike.coe_subset_coe]
      have hHCeq :
          (hyp.HC.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)
            = (hyp.H.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)
              ⊔ (hyp.C.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) := by
        rw [show hyp.HC = hyp.H ⊔ hyp.C from rfl, Subgroup.subgroupOf_sup hHM hCM,
          Subgroup.subgroupOf_sup hH_huSub hC_huSub]
      rw [hHCeq]
      refine sup_le ?_ ?_
      · -- `H`-trace ≤ Ker θ : this is `hInHu` (using `s11Setup.H = H`), which is `hH`
        have hhin : OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup
            = (hyp.H.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) := by
          show (hyp.s11Setup.typeP.H.subgroupOf M).subgroupOf
                (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)
              = (hyp.base.typeP.H.subgroupOf M).subgroupOf
                (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)
          rw [hyp.setup_typeP_eq]
        rw [← hhin]
        intro x hx
        exact hH hx
      · -- `C`-trace ≤ Ker θ : `C ≤ H₀C` and `hθker`
        intro x hx
        have hCH0C : hyp.C ≤ hyp.H0C := le_sup_right
        exact hθker (Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono M hCH0C) hx)
    · -- `H ⊄ Ker θ`: `Ind θ ∈ sOf(H₀C)`
      right
      rw [OddOrder.Peterfalvi.S11.mem_sOf]
      exact ⟨θ, ⟨hH, hθker⟩,
        (OddOrder.Peterfalvi.S11.induceHU_eq_induce hyp.s11Setup
          (θ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)).symm⟩
  · -- reverse: both families sit inside `SOf(H₀C)`
    apply Set.union_subset
    · simp only [hyp.SOf_eq]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
        (Subgroup.subgroupOf_mono M hH0C_le_HC)
    · exact hyp.sOf_subset_SOf hyp.H0C

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

/-- A proper subgroup of `M'` has proper double trace — the `hA'ne` input at `A' = H₁`. -/
theorem trace_ne_top_of_lt_derived {M : Subgroup G} {H1 : Subgroup G}
    (h : H1 < derivedInG M) :
    ((H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)) ≠ ⊤ := by
  intro htop
  obtain ⟨x, hxM', hxH1⟩ := SetLike.exists_of_lt h
  have hxM : x ∈ M := Subgroup.map_subtype_le _ hxM'
  have hmem : (⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hxM'⟩ :
      ↥((derivedInG M).subgroupOf M)) ∈
      (H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M) := by
    rw [htop]; trivial
  exact hxH1 (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hmem))

/-- **`HC/H₀C` is abelian**, in quotient form (`commutator_HC_mem_H0C` descended). -/
theorem HC_quotient_H0C_comm [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    [((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).Normal]
    (a b : ↥(hyp.HC.subgroupOf M) ⧸
      (hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)) :
    a * b = b * a := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  induction b using QuotientGroup.induction_on with | _ y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  -- `(x·y)⁻¹·(y·x) = ⁅y⁻¹, x⁻¹⁆` lies in `H₀C` by the ambient commutator bound.
  have hxHC : ((x : ↥M) : G) ∈ hyp.HC := Subgroup.mem_subgroupOf.mp x.2
  have hyHC : ((y : ↥M) : G) ∈ hyp.HC := Subgroup.mem_subgroupOf.mp y.2
  have hkey := hyp.commutator_HC_mem_H0C
    (Subgroup.inv_mem _ hyHC) (Subgroup.inv_mem _ hxHC)
  simp only [inv_inv] at hkey
  refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
  have hcoe : ((((x * y)⁻¹ * (y * x) : ↥(hyp.HC.subgroupOf M)) : ↥M) : G)
      = ((y : ↥M) : G)⁻¹ * ((x : ↥M) : G)⁻¹ * ((y : ↥M) : G) * ((x : ↥M) : G) := by
    push_cast
    group
  rw [hcoe]
  exact hkey

/-- **(11.4)/(6.2) centrality input at `(C, D) = (HC, HC)`**: the trivial section
`D/B = HC/H₀C` is central in `C/B = HC/H₀C` — i.e. the quotient is abelian
(`HC_quotient_H0C_comm`). -/
theorem HC_central_condition [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    [((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).Normal] :
    ((hyp.HC.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).map
      (QuotientGroup.mk' ((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M))) ≤
    Subgroup.center (↥(hyp.HC.subgroupOf M) ⧸
      (hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)) := by
  intro q _
  rw [Subgroup.mem_center_iff]
  intro r
  exact hyp.HC_quotient_H0C_comm r q

/-- **`|HC| = |H|·|C|`**: `H` and `C` are complementary inside `HC` (`H` normal there,
`H ⊓ C ≤ H ⊓ U = ⊥`). -/
theorem card_HC [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Nat.card ↥hyp.HC = Nat.card ↥hyp.base.typeP.H * Nat.card ↥hyp.C := by
  have hHle : hyp.base.typeP.H ≤ hyp.HC := le_sup_left
  have hCle : hyp.C ≤ hyp.HC := le_sup_right
  have hHCleM : hyp.HC ≤ M := hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)
  haveI hHn : (hyp.base.typeP.H.subgroupOf hyp.HC).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr
      (hHCleM.trans hyp.H_normalized_by_M)
  have hdisj : Disjoint (hyp.base.typeP.H.subgroupOf hyp.HC) (hyp.C.subgroupOf hyp.HC) := by
    rw [disjoint_iff]
    have hsplit : hyp.base.typeP.H.subgroupOf hyp.HC ⊓ hyp.C.subgroupOf hyp.HC
        = (hyp.base.typeP.H ⊓ hyp.C).subgroupOf hyp.HC :=
      (Subgroup.comap_inf _ _ _).symm
    have hbot : hyp.base.typeP.H ⊓ hyp.C = ⊥ := by
      rw [eq_bot_iff, ← hyp.H_inf_U_eq_bot]
      exact inf_le_inf_left _ hyp.C_le_U
    rw [hsplit, hbot, Subgroup.bot_subgroupOf]
  have hsup : (hyp.base.typeP.H.subgroupOf hyp.HC) ⊔ (hyp.C.subgroupOf hyp.HC) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHle hCle]
    exact Subgroup.subgroupOf_self _
  have hcomp : Subgroup.IsComplement' (hyp.base.typeP.H.subgroupOf hyp.HC)
      (hyp.C.subgroupOf hyp.HC) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
  have hmul := hcomp.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv] at hmul
  exact hmul.symm

/-- Bridge: the §9 setup's `H` is the §13 `H` (via `setup_typeP_eq`). -/
theorem s11Setup_H_eq {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.s11Setup.H = hyp.H := by
  show hyp.s11Setup.typeP.H = hyp.base.typeP.H
  rw [hyp.setup_typeP_eq]

/-- Bridge: the §9 setup's `U` is the §13 `U`. -/
theorem s11Setup_U_eq {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.s11Setup.U = hyp.U := by
  show hyp.s11Setup.typeP.U = hyp.base.typeP.U
  rw [hyp.setup_typeP_eq]

/-- Bridge: the §9 setup's `q` is the §13 `q`. -/
theorem s11Setup_q_eq {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.s11Setup.q = hyp.q := by
  show Nat.card ↥hyp.s11Setup.typeP.W1 = Nat.card ↥hyp.base.typeP.W1
  rw [hyp.setup_typeP_eq]

/-- Bridge: the §9 setup's `W₂` is the §13 `W₂`-carrier of `p`. -/
theorem s11Setup_card_W2_eq {M : Subgroup G} (hyp : Hypothesis M) :
    Nat.card ↥hyp.s11Setup.W2 = hyp.p := by
  show Nat.card ↥hyp.s11Setup.typeP.W2 = Nat.card ↥hyp.base.typeP.W2
  rw [hyp.setup_typeP_eq]

/-- `|H₀C| = |H₀| · |C|` (mirror of `card_HC`: `H₀ ⊓ C ≤ H ⊓ U = ⊥`). -/
theorem card_H0C [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Nat.card ↥hyp.H0C = Nat.card ↥hyp.chief.H0 * Nat.card ↥hyp.C := by
  have hH0H : hyp.chief.H0 ≤ hyp.base.typeP.H := by
    have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
      rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
    exact hHH ▸ hyp.chief.H0_lt_H.le
  have hHle : hyp.chief.H0 ≤ hyp.H0C := le_sup_left
  have hCle : hyp.C ≤ hyp.H0C := le_sup_right
  have hH0CleM : hyp.H0C ≤ M := hyp.H0C_le_derived.trans (Subgroup.map_subtype_le _)
  haveI hHn : (hyp.chief.H0.subgroupOf hyp.H0C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr
      (hH0CleM.trans hyp.chief.H0_normalized_by_M)
  have hdisj : Disjoint (hyp.chief.H0.subgroupOf hyp.H0C) (hyp.C.subgroupOf hyp.H0C) := by
    rw [disjoint_iff]
    have hsplit : hyp.chief.H0.subgroupOf hyp.H0C ⊓ hyp.C.subgroupOf hyp.H0C
        = (hyp.chief.H0 ⊓ hyp.C).subgroupOf hyp.H0C :=
      (Subgroup.comap_inf _ _ _).symm
    have hbot : hyp.chief.H0 ⊓ hyp.C = ⊥ := by
      rw [eq_bot_iff, ← hyp.H_inf_U_eq_bot]
      exact inf_le_inf hH0H hyp.C_le_U
    rw [hsplit, hbot, Subgroup.bot_subgroupOf]
  have hsup : (hyp.chief.H0.subgroupOf hyp.H0C) ⊔ (hyp.C.subgroupOf hyp.H0C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHle hCle]
    exact Subgroup.subgroupOf_self _
  have hcomp : Subgroup.IsComplement' (hyp.chief.H0.subgroupOf hyp.H0C)
      (hyp.C.subgroupOf hyp.H0C) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
  have hmul := hcomp.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv] at hmul
  exact hmul.symm

/-- **`|HC : H₀C| = p^q`** — the `C`-factor cancels and `|H : H₀| = p^q` is the chief-factor
order ((9.6), `quotient_order` + `typeIII_IV_p_eq_W2`). -/
theorem H0C_relIndex_HC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.H0C.relIndex hyp.HC = hyp.p ^ hyp.q := by
  have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
    rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
  have hH0H : hyp.chief.H0 ≤ hyp.base.typeP.H := hHH ▸ hyp.chief.H0_lt_H.le
  have hle : hyp.H0C ≤ hyp.HC := sup_le (hH0H.trans le_sup_left) le_sup_right
  have h1 : Nat.card ↥hyp.H0C * hyp.H0C.relIndex hyp.HC = Nat.card ↥hyp.HC := by
    have := Subgroup.card_mul_index (hyp.H0C.subgroupOf hyp.HC)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at this
  -- `|H| = p^q · |H₀|` (chief factor)
  have hp_eq : hyp.chief.p = hyp.p := by
    have h2 := hyp.chief.typeIII_IV_p_eq_W2 (hyp.base.isTypeIIIorIV hG)
    rw [hyp.s11Setup_card_W2_eq] at h2
    exact h2.symm
  have horder : Nat.card ↥hyp.base.typeP.H = hyp.p ^ hyp.q * Nat.card ↥hyp.chief.H0 := by
    have h := hyp.chief.quotient_order
    have hcardHH : Nat.card ↥hyp.s11Setup.H = Nat.card ↥hyp.base.typeP.H := by
      exact congrArg (fun (X : Subgroup G) => Nat.card ↥X) hHH
    rw [hcardHH, hp_eq] at h
    rw [h]
    congr 1
    rw [hyp.s11Setup_q_eq]
  -- combine through `card_HC` / `card_H0C`
  have hkey : (Nat.card ↥hyp.chief.H0 * Nat.card ↥hyp.C) * hyp.H0C.relIndex hyp.HC
      = (Nat.card ↥hyp.chief.H0 * Nat.card ↥hyp.C) * hyp.p ^ hyp.q := by
    rw [← hyp.card_H0C, h1, hyp.card_HC, horder, hyp.card_H0C]
    ring
  have hpos : 0 < Nat.card ↥hyp.chief.H0 * Nat.card ↥hyp.C :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hkey

/-- The (11.1) inputs: `p` and `q` are distinct odd primes.  `q = |W₁|` is prime (type-`P`
core), `p = |W₂|` is the chief-factor prime; both are odd (dividing `|G|`); and `p ≠ q`
since `p ∣ |H|` while `q ∣ |U ⊔ W₁|`, which are coprime. -/
theorem p_q_distinct_odd_primes [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.p.Prime ∧ hyp.q.Prime ∧ Odd hyp.p ∧ Odd hyp.q ∧ hyp.p ≠ hyp.q := by
  have hHH : hyp.s11Setup.typeP.H = hyp.base.typeP.H := by
    rw [hyp.s11Setup.typeP.H_eq, hyp.base.typeP.H_eq]
  -- `p` prime via the chief factor
  have hp_eq : hyp.chief.p = hyp.p := by
    have h2 := hyp.chief.typeIII_IV_p_eq_W2 (hyp.base.isTypeIIIorIV hG)
    rw [hyp.s11Setup_card_W2_eq] at h2
    exact h2.symm
  have hp_prime : hyp.p.Prime := hp_eq ▸ hyp.chief.p_prime
  -- `q` prime from the type-`P` core
  have hq_prime : hyp.q.Prime := by
    have h := hyp.s11Setup.nontrivial.2.1
    rwa [show Nat.card ↥hyp.s11Setup.typeP.W1 = hyp.q from hyp.s11Setup_q_eq] at h
  -- odd: both are cards of subgroups of the odd-order `G`
  have hodd : Odd (Nat.card G) := hG.odd
  have hp_odd : Odd hyp.p :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.typeP.W2)
  have hq_odd : Odd hyp.q :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.typeP.W1)
  -- `p ≠ q`: `p ∣ |H|`, `q ∣ |U ⊔ W₁|`, and those cards are coprime
  refine ⟨hp_prime, hq_prime, hp_odd, hq_odd, ?_⟩
  intro hpq
  have hUne : hyp.base.typeP.U ≠ ⊥ := by
    rw [← hyp.setup_typeP_eq]; exact hyp.s11Setup.nontrivial.1
  have hcop := OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 hyp.base.typeP hUne
  have hpH : hyp.p ∣ Nat.card ↥hyp.base.typeP.H := by
    have horder : Nat.card ↥hyp.base.typeP.H = hyp.p ^ hyp.q * Nat.card ↥hyp.chief.H0 := by
      have h := hyp.chief.quotient_order
      have hcardHH : Nat.card ↥hyp.s11Setup.H = Nat.card ↥hyp.base.typeP.H :=
        congrArg (fun (X : Subgroup G) => Nat.card ↥X) hHH
      rw [hcardHH, hp_eq] at h
      rw [h]
      congr 1
      rw [hyp.s11Setup_q_eq]
    rw [horder]
    exact Dvd.dvd.mul_right (dvd_pow_self _ hq_prime.pos.ne') _
  have hqUW : hyp.q ∣ Nat.card ↥(hyp.base.typeP.U ⊔ hyp.base.typeP.W1) := by
    have : hyp.base.typeP.W1 ≤ hyp.base.typeP.U ⊔ hyp.base.typeP.W1 := le_sup_right
    exact Subgroup.card_dvd_of_le this
  have h1 : hyp.p ∣ 1 := by
    rw [← hcop]
    exact Nat.dvd_gcd hpH (hpq ▸ hqUW)
  exact hp_prime.one_lt.ne' (Nat.eq_one_of_dvd_one h1 ▸ rfl)

/-- **`HC` is nilpotent** (Peterfalvi (6.3.a) for the §11 instance; Coq `PFsection11`
`nilHC` via `F(M') = HC`).  `H` and `C` are normal in `HC`, both nilpotent (`H = M_F`;
`C ≤ U` with `U` nilpotent), so `HC = H ⊔ C ≤ F(HC)` by Fitting's theorem. -/
theorem HC_isNilpotent [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Group.IsNilpotent ↥hyp.HC := by
  classical
  have hHle : hyp.base.typeP.H ≤ hyp.HC := le_sup_left
  have hCle : hyp.C ≤ hyp.HC := le_sup_right
  have hHCleM : hyp.HC ≤ M := hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)
  -- both traces are normal in `↥HC`
  haveI hHn : (hyp.base.typeP.H.subgroupOf hyp.HC).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr
      (hHCleM.trans hyp.H_normalized_by_M)
  haveI hCn : (hyp.C.subgroupOf hyp.HC).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCle).mpr ?_
    refine sup_le (le_trans ?_ (Subgroup.centralizer_le_normalizer (hyp.C : Set G)))
      Subgroup.le_normalizer
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact hyp.commute_of_mem_C_of_mem_H hc hh
  -- both traces are nilpotent
  haveI hHnil : Group.IsNilpotent ↥hyp.base.typeP.H := by
    rw [hyp.base.typeP.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
  haveI hUnil : Group.IsNilpotent ↥hyp.base.typeP.U := hyp.base.typeP.U_nilpotent
  haveI hCnil : Group.IsNilpotent ↥hyp.C := by
    haveI : Group.IsNilpotent ↥(hyp.C.subgroupOf hyp.base.typeP.U) := Subgroup.isNilpotent _
    exact nilpotent_of_surjective
      (Subgroup.subgroupOfEquivOfLe hyp.C_le_U).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hyp.C_le_U).surjective
  haveI hHtr : Group.IsNilpotent ↥(hyp.base.typeP.H.subgroupOf hyp.HC) :=
    nilpotent_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHle).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHle).symm.surjective
  haveI hCtr : Group.IsNilpotent ↥(hyp.C.subgroupOf hyp.HC) :=
    nilpotent_of_surjective
      (Subgroup.subgroupOfEquivOfLe hCle).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hCle).symm.surjective
  -- Fitting: both ≤ F(↥HC), and they join to ⊤
  have hHfit : hyp.base.typeP.H.subgroupOf hyp.HC ≤ OddOrder.Isaacs.Ch01.fitting ↥hyp.HC :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  have hCfit : hyp.C.subgroupOf hyp.HC ≤ OddOrder.Isaacs.Ch01.fitting ↥hyp.HC :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  have hsup : (hyp.base.typeP.H.subgroupOf hyp.HC) ⊔ (hyp.C.subgroupOf hyp.HC) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHle hCle]
    exact Subgroup.subgroupOf_self _
  have hfit_top : OddOrder.Isaacs.Ch01.fitting ↥hyp.HC = ⊤ :=
    le_antisymm le_top (hsup ▸ sup_le hHfit hCfit)
  haveI := OddOrder.Isaacs.Ch01.fitting.isNilpotent (G := ↥hyp.HC)
  have : Group.IsNilpotent ↥(⊤ : Subgroup ↥hyp.HC) := by
    rw [← hfit_top]
    infer_instance
  exact nilpotent_of_surjective
    (Subgroup.topEquiv (G := ↥hyp.HC)).toMonoidHom
    (Subgroup.topEquiv (G := ↥hyp.HC)).surjective

/-- **`|M' : HC| = |U : C|`** (cancel the common factor `|H|`). -/
theorem HC_relIndex_derived [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.HC.relIndex (derivedInG M) = hyp.C.relIndex hyp.U := by
  -- `relIndex · card = card` on both sides
  have h1 : Nat.card ↥hyp.HC * hyp.HC.relIndex (derivedInG M)
      = Nat.card ↥(derivedInG M) := by
    have := Subgroup.card_mul_index (hyp.HC.subgroupOf (derivedInG M))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.HC_le_derived).toEquiv] at this
  have hCleU' : hyp.C ≤ hyp.U := hyp.C_le_U
  have h2 : Nat.card ↥hyp.C * hyp.C.relIndex hyp.U = Nat.card ↥hyp.U := by
    have := Subgroup.card_mul_index (hyp.C.subgroupOf hyp.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleU').toEquiv] at this
  have hM' : Nat.card ↥(derivedInG M)
      = Nat.card ↥hyp.base.typeP.H * Nat.card ↥hyp.base.typeP.U := by
    have hmul := hyp.base.typeP.derived_complement.card_mul
    rw [← hmul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.base.typeP.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.base.typeP.U_le).toEquiv]
  -- combine: `(|H||C|)·rel_HC = |H||U| = (|H||C|)·rel_CU`, cancel the positive `|H||C|`
  have hkey : (Nat.card ↥hyp.base.typeP.H * Nat.card ↥hyp.C) * hyp.HC.relIndex (derivedInG M)
      = (Nat.card ↥hyp.base.typeP.H * Nat.card ↥hyp.C) * hyp.C.relIndex hyp.U := by
    rw [← hyp.card_HC, h1, hM', hyp.card_HC, mul_assoc, h2]
    rfl
  have hpos : 0 < Nat.card ↥hyp.base.typeP.H * Nat.card ↥hyp.C :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hkey

/-- **`|M : HC| = q · |U : C|`** (the (11.4) index: `|M:HC| = |M:M'|·|M':HC|`). -/
theorem HC_trace_index [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    (hyp.HC.subgroupOf M).index = hyp.base.w1 * hyp.C.relIndex hyp.U := by
  have htower : hyp.HC.relIndex (derivedInG M) * (derivedInG M).relIndex M
      = hyp.HC.relIndex M :=
    Subgroup.relIndex_mul_relIndex hyp.HC (derivedInG M) M hyp.HC_le_derived
      (Subgroup.map_subtype_le _)
  have hq : (derivedInG M).relIndex M = hyp.base.w1 := by
    have := hyp.base.typeP.card_W1_eq_derived_index
    exact this.symm
  change hyp.HC.relIndex M = hyp.base.w1 * hyp.C.relIndex hyp.U
  rw [← htower, hyp.HC_relIndex_derived, hq, Nat.mul_comm]

end Hypothesis

/-- **`M` normalizes `M''`** (`secondDerivedInAmbient` is conjugation-equivariant and `M`
normalizes itself). -/
theorem le_normalizer_secondDerived [Finite G] {M : Subgroup G} :
    M ≤ Subgroup.normalizer ((secondDerivedInAmbient M : Subgroup G) : Set G) := by
  intro m hm
  rw [← OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer]
  have h1 : (MulAut.conj m) • M = M := by
    have h2 : M.map (MulAut.conj m).toMonoidHom = M :=
      OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hm)
    rw [pointwise_mulAut_smul_eq_map]
    exact h2
  have hgoal : (MulAut.conj m) • secondDerivedInAmbient M = secondDerivedInAmbient M := by
    rw [secondDerivedInAmbient_pointwise_smul _ _, h1]
  have h3 := (pointwise_mulAut_smul_eq_map (MulAut.conj m) (secondDerivedInAmbient M)).symm
  exact h3.trans hgoal

namespace Hypothesis

/-- `M''`-trace inside `↥M` is the commutator of the `M'`-trace: `(M'').subgroupOf M = ⁅K, K⁆`
for `K = M'.subgroupOf M`. -/
theorem secondDerived_subgroupOf_eq_commutator [Finite G] {M : Subgroup G} :
    (secondDerivedInAmbient M).subgroupOf M
      = ⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆ := by
  have h1 : secondDerivedInAmbient M
      = Subgroup.map M.subtype ⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆ := by
    rw [Subgroup.map_commutator]
    have h2 : ((derivedInG M).subgroupOf M).map M.subtype = derivedInG M :=
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)
    rw [h2, secondDerivedInAmbient]
    exact Subgroup.map_subtype_commutator (derivedInG M)
  rw [h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

/-- **Irreducible characters trivial on the commutator are linear** (degree 1): such a
character factors through the abelianization, and irreducible characters of abelian groups
have degree 1.  Stated for any finite group. -/
theorem charValue_one_eq_one_of_commutator_le_ker {H : Type*} [Group H] [Finite H]
    (θ : OddOrder.RepresentationTheory.IrreducibleCharacter H)
    (hker : ((_root_.commutator H : Subgroup H) : Set H)
      ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction H ℂ)) :
    (θ : ClassFunction H ℂ) 1 = 1 := by
  haveI : IsMulCommutative (H ⧸ _root_.commutator H) :=
    inferInstanceAs (IsMulCommutative (Abelianization H))
  exact OddOrder.RepresentationTheory.apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
    (N := _root_.commutator H) θ hker

/-- Conversely, linear characters kill the commutator subgroup. -/
theorem commutator_le_ker_of_charValue_one {H : Type*} [Group H] [Finite H]
    (θ : OddOrder.RepresentationTheory.IrreducibleCharacter H)
    (hθ1 : (θ : ClassFunction H ℂ) 1 = 1) :
    ((_root_.commutator H : Subgroup H) : Set H)
      ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction H ℂ) := by
  intro n hn
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def, hθ1]
  have hn' : n ∈ Subgroup.closure (commutatorSet H) := by
    rwa [SetLike.mem_coe, _root_.commutator_eq_closure] at hn
  refine Subgroup.closure_induction
    (p := fun g _ => (θ : ClassFunction H ℂ) g = 1) ?_ ?_ ?_ ?_ hn'
  · rintro _ ⟨a, b, rfl⟩
    exact θ.isIrreducible.apply_commutatorElement_eq_one_of_apply_one_eq_one hθ1 a b
  · exact hθ1
  · intro a b _ _ ha hb
    rw [θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1, ha, hb, one_mul]
  · intro a _ ha
    have hai := θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1 a a⁻¹
    rw [mul_inv_cancel, hθ1, ha, one_mul] at hai
    exact hai.symm

/-- **`S(M\'\')` is the degree-`w₁` irreducible subfamily of `S`** ((11.8.1)-adjacent):
its members are the inductions of nontrivial *linear* characters of `M\'` (the kernel
condition `M\'\' ⊆ ker θ` is equivalent to linearity), which are irreducible by the
(8.4.d) inertia theorem and have degree `|M : M\'| = w₁`. -/
theorem SOf_secondDerived_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.SOf (secondDerivedInAmbient M)
      = {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧
          IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (hyp.base.w1 : ℂ))} := by
  classical
  haveI : Fintype G := Fintype.ofFinite _
  -- the trace `K = M\'.subgroupOf M` has index `w₁` (complement `M = M\' ⋊ W₁`)
  have hidx : ((derivedInG M).subgroupOf M).index = hyp.base.w1 := by
    rw [hyp.base.typeP.M_complement.symm.index_eq_card]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hyp.base.typeP.W1_le).toEquiv
  have hidx0 : (((derivedInG M).subgroupOf M).index : ℂ) ≠ 0 := by
    rw [hidx]
    exact_mod_cast Nat.card_pos.ne'
  -- the kernel condition of `S(M\'\')` is the commutator of the trace
  have hXcomm : ((secondDerivedInAmbient M).subgroupOf M).subgroupOf
      ((derivedInG M).subgroupOf M)
      = _root_.commutator ↥((derivedInG M).subgroupOf M) := by
    rw [secondDerived_subgroupOf_eq_commutator]
    exact OddOrder.Peterfalvi.S08.commutator_subgroupOf_self _
  ext φ
  rw [hyp.SOf_eq]
  constructor
  · rintro ⟨θ, hθne, hθker, rfl⟩
    have hkerC : ((_root_.commutator ↥((derivedInG M).subgroupOf M) : Subgroup _) : Set _)
        ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) := by
      intro x hx
      rw [← hXcomm] at hx
      exact hθker hx
    have hθdeg := charValue_one_eq_one_of_commutator_le_ker θ hkerC
    refine ⟨?_, ?_, ?_⟩
    · rw [OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le ⟨θ, hθne, hθker, rfl⟩
    · exact OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq θ
        (hyp.base.inertia_eq_derived_of_linear hG hθne hθdeg)
    · rw [ClassFunction.induce_apply_one, hθdeg, mul_one, hidx]
  · rintro ⟨hφS, hφirr, hφdeg⟩
    rw [OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot] at hφS
    obtain ⟨θ, hθne, -, rfl⟩ := hφS
    have hθdeg : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 := by
      have h1 := ClassFunction.induce_apply_one ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      rw [show ((ClassFunction.induce ((derivedInG M).subgroupOf M)
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) : ClassFunction ↥M ℂ) : ↥M → ℂ) 1
          = (hyp.base.w1 : ℂ) from hφdeg, ← hidx] at h1
      exact mul_left_cancel₀ hidx0 (by rw [← h1, mul_one])
    refine ⟨θ, hθne, ?_, rfl⟩
    intro x hx
    rw [hXcomm] at hx
    exact commutator_le_ker_of_charValue_one θ hθdeg hx

/-- **Peterfalvi (5.7) instance: `S(M'')` is coherent.**  `S(M'')` is the degree-`w₁`
irreducible subfamily of `S` (`SOf_secondDerived_eq`), whose coherence is
`S12.Hypothesis.SHC_isCoherent` (the (11.8)/(5.7) equal-degree producer). -/
theorem secondDerived_coherent [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf (secondDerivedInAmbient M)) hyp.base.A0) := by
  rw [hyp.SOf_secondDerived_eq _hG]
  exact ⟨hyp.base.SHC_isCoherent _hG⟩

/-- **`C ⊊ U`**: `U` does not centralize the chief factor `H̄` (`U_noncentral_on_quotient`),
but `C = C_U(H)` acts trivially on it. -/
theorem C_lt_U {M : Subgroup G} (hyp : Hypothesis M) : hyp.C < hyp.base.typeP.U := by
  refine lt_of_le_of_ne hyp.C_le_U ?_
  intro hCU
  refine hyp.chief.U_noncentral_on_quotient ?_
  rw [eq_top_iff]
  rintro hbar -
  rw [OddOrder.GroupTheory.mem_fixedSubgroup]
  intro l hl
  induction hbar using QuotientGroup.induction_on with | _ x => ?_
  have hmk : (QuotientGroup.mk x : ↥hyp.s11Setup.H ⧸ hyp.chief.N)
      = QuotientGroup.mk' hyp.chief.N x := rfl
  rw [hmk]
  refine congrArg (QuotientGroup.mk' hyp.chief.N) ?_
  -- `l ∈ U = C` centralizes `H`, so the conjugation action fixes `x`
  have hlU : (l : G) ∈ hyp.s11Setup.typeP.U := Subgroup.mem_subgroupOf.mp hl
  have hlU' : (l : G) ∈ hyp.base.typeP.U := by rwa [← hyp.setup_typeP_eq]
  have hlC : (l : G) ∈ hyp.C := by rw [hCU]; exact hlU'
  have hlcen : (l : G) ∈ Subgroup.centralizer (hyp.base.typeP.H : Set G) :=
    (hyp.C_eq_centralizer ▸ hlC).2
  have hxH : ((x : ↥hyp.s11Setup.H) : G) ∈ hyp.base.typeP.H := by
    have hx2 : ((x : ↥hyp.s11Setup.H) : G) ∈ hyp.s11Setup.typeP.H := x.2
    rwa [hyp.setup_typeP_eq] at hx2
  ext
  change (l : G) * ((x : ↥hyp.s11Setup.H) : G) * (l : G)⁻¹ = ((x : ↥hyp.s11Setup.H) : G)
  have hcomm := Subgroup.mem_centralizer_iff.mp hlcen _ hxH
  rw [← hcomm]
  group

/-- **The FPF divisibility `q ∣ |HC : M''| − 1`** — Peterfalvi (8.4.d) on `(HC)/M''`: the
`W₁`-conjugation on `HC` has its nonidentity fixed points inside `W₂ ≤ M''`
(`centralizer_W1` + `W2_le`), so the induced action on `(HC)/M''` is fixed-point-free and
Burnside gives the congruence (`W1_dvd_index_of_fixedPoints_le`). -/
theorem q_dvd_secondDerived_relIndex_HC_sub_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.base.w1 ∣ (secondDerivedInAmbient M).relIndex hyp.HC - 1 := by
  classical
  haveI hHCn : ((hyp.HC.subgroupOf M)).Normal := hyp.HC_subgroupOf_normal
  haveI hM''n : (((secondDerivedInAmbient M).subgroupOf M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((hyp.secondDerived_le_HC.trans hyp.HC_le_derived).trans
        (Subgroup.map_subtype_le _))).mpr le_normalizer_secondDerived
  letI act : MulDistribMulAction ↥(hyp.base.typeP.W1.subgroupOf M) ↥(hyp.HC.subgroupOf M) :=
    MulDistribMulAction.compHom _
      ((MulAut.conjNormal (H := hyp.HC.subgroupOf M)).comp
        (hyp.base.typeP.W1.subgroupOf M).subtype)
  have hsmul : ∀ (a : ↥(hyp.base.typeP.W1.subgroupOf M)) (x : ↥(hyp.HC.subgroupOf M)),
      ((a • x : ↥(hyp.HC.subgroupOf M)) : ↥M) = (a : ↥M) * (x : ↥M) * (a : ↥M)⁻¹ := by
    intro a x
    change ((MulAut.conjNormal (H := hyp.HC.subgroupOf M)
      ((hyp.base.typeP.W1.subgroupOf M).subtype a)) x : ↥M) = _
    rw [MulAut.conjNormal_apply]; rfl
  set Msub : Subgroup ↥(hyp.HC.subgroupOf M) :=
    ((secondDerivedInAmbient M).subgroupOf M).subgroupOf (hyp.HC.subgroupOf M) with hMsub
  haveI : Msub.Normal := hM''n.subgroupOf _
  have hCop : Nat.Coprime (Nat.card ↥(hyp.base.typeP.W1.subgroupOf M))
      (Nat.card ↥(hyp.HC.subgroupOf M)) := by
    have h1 : Nat.card ↥(hyp.base.typeP.W1.subgroupOf M) = Nat.card ↥hyp.base.typeP.W1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.base.typeP.W1_le).toEquiv
    have h2 : Nat.card ↥(hyp.HC.subgroupOf M) = Nat.card ↥hyp.HC :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (hyp.HC_le_derived.trans (Subgroup.map_subtype_le _))).toEquiv
    rw [h1, h2]
    exact (hyp.base.coprime_card_W1_derived hG).coprime_dvd_right
      (Subgroup.card_dvd_of_le hyp.HC_le_derived)
  have hMinv : ∀ a : ↥(hyp.base.typeP.W1.subgroupOf M), ∀ m ∈ Msub, a • m ∈ Msub := by
    intro a m hm
    have hmG : ((m : ↥M) : G) ∈ secondDerivedInAmbient M :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hm)
    have haM : ((a : ↥M) : G) ∈ M := (a : ↥M).2
    have hconj : ((a : ↥M) : G) * ((m : ↥M) : G) * ((a : ↥M) : G)⁻¹
        ∈ secondDerivedInAmbient M := by
      have hnorm := le_normalizer_secondDerived (M := M) haM
      rw [Subgroup.mem_normalizer_iff] at hnorm
      exact (hnorm _).mp hmG
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have hcoe : (((a • m : ↥(hyp.HC.subgroupOf M)) : ↥M) : G)
        = ((a : ↥M) : G) * ((m : ↥M) : G) * ((a : ↥M) : G)⁻¹ := by
      rw [hsmul]; rfl
    rw [hcoe]
    exact hconj
  have hfix : ∀ a : ↥(hyp.base.typeP.W1.subgroupOf M), a ≠ 1 →
      ∀ x : ↥(hyp.HC.subgroupOf M), a • x = x → x ∈ Msub := by
    intro a ha x hax
    have haG : ((a : ↥M) : G) ∈ hyp.base.typeP.W1 :=
      Subgroup.mem_subgroupOf.mp a.2
    have haGne : ((a : ↥M) : G) ≠ 1 := fun h1 => ha (Subtype.ext (Subtype.ext h1))
    have hxHC : ((x : ↥M) : G) ∈ hyp.HC := Subgroup.mem_subgroupOf.mp x.2
    have hxM' : ((x : ↥M) : G) ∈ derivedInG M := hyp.HC_le_derived hxHC
    have hcommG : ((a : ↥M) : G) * ((x : ↥M) : G) = ((x : ↥M) : G) * ((a : ↥M) : G) := by
      have h1 := hsmul a x
      rw [hax] at h1
      have h2 := congrArg (fun m : ↥M => (m : G)) h1
      simp only at h2
      have h3 : ((x : ↥M) : G) = ((a : ↥M) : G) * ((x : ↥M) : G) * ((a : ↥M) : G)⁻¹ := h2
      calc ((a : ↥M) : G) * ((x : ↥M) : G)
          = (((a : ↥M) : G) * ((x : ↥M) : G) * ((a : ↥M) : G)⁻¹) * ((a : ↥M) : G) := by group
        _ = ((x : ↥M) : G) * ((a : ↥M) : G) := by rw [← h3]
    have hxcen : ((x : ↥M) : G) ∈ Subgroup.centralizer ({((a : ↥M) : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcommG.symm
    have hxW2 : ((x : ↥M) : G) ∈ hyp.base.typeP.W2 := by
      rw [← hyp.base.typeP.centralizer_W1 _ haG haGne]
      exact ⟨hxM', hxcen⟩
    have hxM'' : ((x : ↥M) : G) ∈ secondDerivedInAmbient M := (hyp.base.typeP.W2_le hxW2).2
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hxM'')
  have hdvd := OddOrder.Peterfalvi.S08.W1_dvd_index_of_fixedPoints_le hCop Msub hMinv hfix
  -- translate `Msub.index` to the ambient relative index
  have hidx : Msub.index = (secondDerivedInAmbient M).relIndex hyp.HC := by
    have h1 : Msub.index
        = ((secondDerivedInAmbient M).subgroupOf M).relIndex (hyp.HC.subgroupOf M) := rfl
    rw [h1, Subgroup.relIndex_subgroupOf
      (show hyp.HC ≤ M from hyp.HC_le_derived.trans (Subgroup.map_subtype_le _))]
  have hq : Nat.card ↥(hyp.base.typeP.W1.subgroupOf M) = hyp.base.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.base.typeP.W1_le).toEquiv
  rw [← hq, ← hidx]
  exact hdvd

end Hypothesis

/-- Decomposition along an `M`-normalized factor: `x ∈ A ⊔ B` splits as `x = a·b`
(`A` normalized by `M ⊇ A ⊔ B`; the sup is computed inside `↥M` where `A`-trace is normal). -/
theorem exists_mul_of_mem_sup_of_normalized {M A B : Subgroup G}
    (hAM : A ≤ M) (hBM : B ≤ M)
    (hnorm : M ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  haveI hAn : (A.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mpr hnorm
  have hxM : x ∈ M := (sup_le hAM hBM) hx
  have hmem : (⟨x, hxM⟩ : ↥M) ∈ A.subgroupOf M ⊔ B.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hAM hBM]
    exact Subgroup.mem_subgroupOf.mpr hx
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  refine ⟨((a : ↥M) : G), Subgroup.mem_subgroupOf.mp ha,
    ((b : ↥M) : G), Subgroup.mem_subgroupOf.mp hb, ?_⟩
  have := congrArg (fun m : ↥M => (m : G)) hab
  simpa using this.symm

namespace Hypothesis

/-- **`M'' ≤ H ⊔ U'`** — the derived subgroup of `M' = H·U` collapses mod `H` to `U'`:
commutator generators `⁅a, b⁆` of `M''` reduce, through `M'/H`-projection along the
`H`-normal decomposition `a = h·u`, to `H`-multiples of `⁅u_a, u_b⁆ ∈ U'`. -/
theorem secondDerived_le_H_sup_derivedU [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M ≤ hyp.base.typeP.H ⊔ derivedInG hyp.base.typeP.U := by
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hUle : hyp.base.typeP.U ≤ M := hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _)
  have hM'eq : derivedInG M = hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
    rw [hyp.base.typeP.derivedInG_eq_fitting_sup_U, hyp.base.typeP.H_eq]
  haveI hHn : ((hyp.base.typeP.H).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr hyp.H_normalized_by_M
  -- the quotient projection `↥M → ↥M / H`-trace kills the `H`-parts
  set φ := QuotientGroup.mk' ((hyp.base.typeP.H).subgroupOf M) with hφ
  rintro x hx
  rw [secondDerivedInAmbient, derivedInG] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [commutator_eq_closure] at hc
  induction hc using Subgroup.closure_induction with
  | one =>
      simpa using Subgroup.one_mem (hyp.base.typeP.H ⊔ derivedInG hyp.base.typeP.U)
  | mul y z _ _ hy hz =>
      rw [map_mul]
      exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
      rw [map_inv]
      exact Subgroup.inv_mem _ hy
  | mem cel hcel =>
      obtain ⟨a, b, hab⟩ := hcel
      have hcel_eq : cel = a * b * a⁻¹ * b⁻¹ := hab.symm
      -- decompose both along the `H`-factor of `M' = H ⊔ U`
      have haM' : ((a : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact a.2
      have hbM' : ((b : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact b.2
      obtain ⟨ha', hha', ua, hua, haeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M haM'
      obtain ⟨hb', hhb', ub, hub, hbeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M hbM'
      -- mod `H`: `⁅a,b⁆ ≡ ⁅u_a, u_b⁆`, so the ratio lies in `H`
      have haMm : ((a : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) a.2
      have hbMm : ((b : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) b.2
      set A : ↥M := ⟨((a : ↥(derivedInG M)) : G), haMm⟩ with hA
      set B : ↥M := ⟨((b : ↥(derivedInG M)) : G), hbMm⟩ with hB
      set UA : ↥M := ⟨ua, hUle hua⟩ with hUA
      set UB : ↥M := ⟨ub, hUle hub⟩ with hUB
      have hφA : φ A = φ UA := by
        have h1 : A = ⟨ha', hHle hha'⟩ * UA := by
          ext; rw [haeq]; rfl
        rw [h1, map_mul]
        have h2 : φ ⟨ha', hHle hha'⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hha'
        rw [h2, one_mul]
      have hφB : φ B = φ UB := by
        have h1 : B = ⟨hb', hHle hhb'⟩ * UB := by
          ext; rw [hbeq]; rfl
        rw [h1, map_mul]
        have h2 : φ ⟨hb', hHle hhb'⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hhb'
        rw [h2, one_mul]
      have hratio : (A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹
          ∈ (hyp.base.typeP.H).subgroupOf M := by
        have hmapped : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹)
            = (φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹) * (φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹)⁻¹ := by
          simp only [map_mul, map_inv]
        have h1 : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹) = 1 := by
          rw [hmapped, hφA, hφB]; group
        exact (QuotientGroup.eq_one_iff
          (N := (hyp.base.typeP.H).subgroupOf M) _).mp h1
      -- conclude: the commutator is an `H`-multiple of `⁅u_a, u_b⁆ ∈ U'`
      have hcomm_coe : (((derivedInG M).subtype) cel : G)
          = ((A * B * A⁻¹ * B⁻¹ : ↥M) : G) := by
        rw [hcel_eq]; exact rfl
      have hsplit : ((A * B * A⁻¹ * B⁻¹ : ↥M) : G)
          = (((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹ : ↥M) : G)
            * ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) := by
        push_cast
        group
      rw [hcomm_coe, hsplit]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact Subgroup.mem_subgroupOf.mp hratio
      · have hUcomm : ua * ub * ua⁻¹ * ub⁻¹ ∈ derivedInG hyp.base.typeP.U := by
          rw [show derivedInG hyp.base.typeP.U
              = ⁅hyp.base.typeP.U, hyp.base.typeP.U⁆
            from Subgroup.map_subtype_commutator hyp.base.typeP.U]
          exact Subgroup.commutator_mem_commutator hua hub
        have hcoe : ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) = ua * ub * ua⁻¹ * ub⁻¹ := by
          push_cast
          rfl
        rw [hcoe]
        exact hUcomm

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
theorem coherent_S_of_coherent_SH0C [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M)
    (_hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau hyp.base.Sset hyp.base.A0) := by
  classical
  -- the (6.3) data: `(K, H, M, H₁) = (M', HC, ⊥, H₀C)`-traces inside `↥M`
  have hHCleM : hyp.HC ≤ M := hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)
  have hH0CleM : hyp.H0C ≤ M := hyp.H0C_le_derived.trans (Subgroup.map_subtype_le _)
  have hH0CleHC : hyp.H0C ≤ hyp.HC :=
    sup_le (hyp.H0_lt_H.le.trans le_sup_left) le_sup_right
  -- instances for the oracle
  haveI : IsSolvable ↥M := _hG.solvable_of_lt_top M (lt_top_iff_ne_top.mpr hyp.base.maximal.1)
  haveI : IsSolvable ↥((derivedInG M).subgroupOf M) := inferInstance
  haveI hHCnil : Group.IsNilpotent ↥(hyp.HC.subgroupOf M) := by
    haveI := hyp.HC_isNilpotent
    exact nilpotent_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHCleM).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHCleM).symm.surjective
  haveI hH₁n : (hyp.H0C.subgroupOf M).Normal := hyp.H0C_subgroupOf_normal
  have hHnorm : (hyp.HC.subgroupOf M).Normal := hyp.HC_subgroupOf_normal
  -- strictness `H₀C-trace < HC-trace`
  have hH₁H : hyp.H0C.subgroupOf M < hyp.HC.subgroupOf M := by
    refine lt_of_le_of_ne (Subgroup.subgroupOf_mono M hH0CleHC) ?_
    intro heq
    have hamb : hyp.H0C = hyp.HC := by
      have h1 := congrArg (Subgroup.map M.subtype) heq
      rwa [Subgroup.map_subgroupOf_eq_of_le hH0CleM,
        Subgroup.map_subgroupOf_eq_of_le hHCleM] at h1
    exact hyp.H_not_le_H0C (hamb ▸ (le_sup_left : hyp.base.typeP.H ≤ hyp.HC))
  have hHK : hyp.HC.subgroupOf M ≤ (derivedInG M).subgroupOf M :=
    Subgroup.subgroupOf_mono M hyp.HC_le_derived
  -- numerical bound (6.3.c): `4q² + 1 < p^q`
  have hbound : 4 * ((derivedInG M).subgroupOf M).index ^ 2 + 1
      < Nat.card (↥(hyp.HC.subgroupOf M)
          ⧸ (hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)) := by
    have hidx : ((derivedInG M).subgroupOf M).index = hyp.q :=
      hyp.base.typeP.card_W1_eq_derived_index.symm
    have hcardq : Nat.card (↥(hyp.HC.subgroupOf M)
        ⧸ (hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M))
        = hyp.p ^ hyp.q := by
      rw [← Subgroup.index_eq_card,
        show ((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).index
          = (hyp.H0C.subgroupOf M).relIndex (hyp.HC.subgroupOf M) from rfl,
        Subgroup.relIndex_subgroupOf hHCleM]
      exact hyp.H0C_relIndex_HC _hG
    rw [hidx, hcardq]
    obtain ⟨hp', hq', hpo, hqo, hne⟩ := hyp.p_q_distinct_odd_primes _hG
    exact prime_pow_gt_four_mul_sq_add_one hp' hq' hpo hqo hne
  -- assemble via the (6.3) oracle
  have hmain := OddOrder.Peterfalvi.S08.six_three_of_six_two_oracle
    (L := M) (K := (derivedInG M).subgroupOf M) (H := hyp.HC.subgroupOf M)
    (M := ⊥) (H₁ := hyp.H0C.subgroupOf M) hHnorm bot_le hH₁H hHK
    hyp.base.tau hyp.base.A0
    (fun X => OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) X)
    ?_ (by
      show Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
          (hyp.H0C.subgroupOf M)) hyp.base.A0)
      rw [← hyp.SOf_eq]
      exact _hcoh) hbound
  · have hSset : hyp.base.Sset
        = OddOrder.Peterfalvi.S08.inducedKernelFamily
            ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
      unfold OddOrder.Peterfalvi.S12.Hypothesis.Sset
      exact OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot
    rw [hSset]
    exact hmain
  · -- the (5.6) break-member oracle `h56` = the §11 dichotomy producer
    intro A B hAnorm hBnorm hBA hAH₁ _hcentral hAcoh hBncoh
    haveI := hAnorm
    haveI := hBnorm
    haveI : (A.subgroupOf ((derivedInG M).subgroupOf M)).Normal := hAnorm.subgroupOf _
    haveI : (B.subgroupOf ((derivedInG M).subgroupOf M)).Normal := hBnorm.subgroupOf _
    have hAne : A.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
      intro htop
      exact absurd (hHK.trans ((Subgroup.subgroupOf_eq_top.mp htop).trans hAH₁))
        (not_le_of_gt hH₁H)
    have hBne : B.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
      intro htop
      exact absurd (hHK.trans ((Subgroup.subgroupOf_eq_top.mp htop).trans (hBA.trans hAH₁)))
        (not_le_of_gt hH₁H)
    have hAcoh' : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
          (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj))
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A)
        hyp.base.A0) := hAcoh
    have hBncoh' : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
          (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj))
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B)
        hyp.base.A0) := fun h => hBncoh h
    exact hyp.base.exists_source_of_coherence_dichotomy _hG
      (hyp.params_mu_eq _hG _hG.odd) hyp.params_delta_pm
      (hyp.params_delta_sign _hG _hG.odd) hyp.params_zeta_mem hyp.params_zeta_degree
      (hyp.base.isTypeIIIorIV _hG)
      (OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV
        (hyp.base.isTypeIIIorIV _hG) hyp.base.typeP)
      (OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG _).choose
      hAne hBne hAcoh' hBncoh'

/-- **Peterfalvi (11.3)**: `S(H_0 C)` is not coherent.

If it were, Theorem (6.3) (`coherent_S_of_coherent_SH0C`) would make the full family `S` coherent,
contradicting Theorem (10.8) (`S12.S_not_coherent`).  The theorem is thereby reduced, with no
`sorry` of its own, to those two cited results. -/
theorem S_H0C_not_coherent [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) :=
  fun hcoh => OddOrder.Peterfalvi.S12.S_not_coherent _hG hyp.base
    (coherent_S_of_coherent_SH0C _hG hyp hcoh)

/-- **Peterfalvi (11.4)**: if `S(H_1)` is coherent for a normal subgroup `H_1 < M'`,
then `|M'/H_1| - 1 ≤ 2 q |U/C|` (the quotient bound from Theorem (6.2)), stated here in
the subtraction-free form `|M' : H_1| ≤ 2 q |U : C| + 1`. -/
theorem coherent_quotient_bound [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H1 : Subgroup G}
    (hyp : Hypothesis M) (hH1_norm : M ≤ Subgroup.normalizer (H1 : Set G))
    (hH1_lt : H1 < derivedInG M)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf H1) hyp.base.A0)) :
    H1.relIndex (derivedInG M) ≤ 2 * hyp.q * hyp.C.relIndex hyp.U + 1 := by
  classical
  -- normality instances for the section subgroups and their traces
  haveI hA'n : ((H1.subgroupOf M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hH1_lt.le.trans (Subgroup.map_subtype_le _))).mpr hH1_norm
  haveI hBn : ((hyp.H0C.subgroupOf M)).Normal := hyp.H0C_subgroupOf_normal
  haveI : ((H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hA'n.subgroupOf _
  haveI : ((hyp.H0C.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hBn.subgroupOf _
  haveI : ((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).Normal :=
    hBn.subgroupOf _
  -- coherence dichotomy at the pinned family (`SOf_eq`; `tau`/`A0` are definitional)
  have hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
        (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
        (H1.subgroupOf M)) hyp.base.A0) := by
    have h := hcoh
    rw [hyp.SOf_eq] at h
    exact h
  have hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
        (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
        (hyp.H0C.subgroupOf M)) hyp.base.A0) := by
    have h := S_H0C_not_coherent _hG hyp
    rw [hyp.SOf_eq] at h
    exact h
  -- the (6.2) bound at `(C, D) = (HC, HC)`-traces
  have hbound := hyp.base.six_two_dichotomy_bound _hG
    (hyp.params_mu_eq _hG _hG.odd) hyp.params_delta_pm
    (hyp.params_delta_sign _hG _hG.odd) hyp.params_zeta_mem hyp.params_zeta_degree
    (hyp.base.isTypeIIIorIV _hG)
    (OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV
      (hyp.base.isTypeIIIorIV _hG) hyp.base.typeP)
    (OddOrder.Peterfalvi.S11.exists_chiefFactorData _hG _).choose
    (A' := H1.subgroupOf M) (B := hyp.H0C.subgroupOf M)
    (C := hyp.HC.subgroupOf M) (D := hyp.HC.subgroupOf M)
    (Hypothesis.trace_ne_top_of_lt_derived hH1_lt) hyp.H0C_trace_ne_top
    (Subgroup.subgroupOf_mono M
      (sup_le (hyp.H0_lt_H.le.trans le_sup_left) le_sup_right))
    (Subgroup.subgroupOf_mono M hyp.HC_le_derived)
    hyp.HC_central_condition hAcoh hBncoh
  -- the square-root factor is `√1 = 1`
  have hsq : Nat.card (↥(hyp.HC.subgroupOf M) ⧸
      (hyp.HC.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)) = 1 := by
    rw [Subgroup.subgroupOf_self]
    haveI : Subsingleton (↥(hyp.HC.subgroupOf M) ⧸ (⊤ : Subgroup ↥(hyp.HC.subgroupOf M))) :=
      QuotientGroup.subsingleton_quotient_top
    exact Nat.card_unique
  rw [hsq] at hbound
  simp only [Nat.cast_one, Real.sqrt_one, mul_one] at hbound
  -- the left side is the relative index `|M' : H₁|`
  have hL : Nat.card (↥((derivedInG M).subgroupOf M) ⧸
      (H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M))
      = H1.relIndex (derivedInG M) := by
    have h1 : Nat.card (↥((derivedInG M).subgroupOf M) ⧸
        (H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M))
        = (H1.subgroupOf M).relIndex ((derivedInG M).subgroupOf M) := rfl
    rw [h1]
    exact Subgroup.relIndex_subgroupOf (show derivedInG M ≤ M from Subgroup.map_subtype_le _)
  rw [hL] at hbound
  -- the index factor is `q·|U:C|`
  have hidx : ((hyp.HC.subgroupOf M).index : ℝ)
      = (hyp.base.w1 * hyp.C.relIndex hyp.U : ℕ) := by
    rw [hyp.HC_trace_index]
  rw [hidx] at hbound
  -- conclude over `ℕ`
  have hfinal : (H1.relIndex (derivedInG M) : ℝ)
      ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U : ℕ) + 1 := by linarith
  have : H1.relIndex (derivedInG M) ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1 := by
    exact_mod_cast hfinal
  calc H1.relIndex (derivedInG M) ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1 := this
    _ = 2 * hyp.q * hyp.C.relIndex hyp.U + 1 := by
        change 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1
          = 2 * hyp.base.w1 * hyp.C.relIndex hyp.U + 1
        ring

/-- **`HC < M'`** (sorry-free): if `HC = M'` then `U ≤ HC = H·C`; decomposing `u = a·b`
(`a ∈ H`, `b ∈ C`) along the normal `H`-factor forces `a ∈ H ∩ U = ⊥`, so `u = b ∈ C`,
contradicting `C ⊊ U` (`C_lt_U`).  The strict inclusion feeds the (11.4)/(11.5) quotient bound
and the `𝒮(HC)`-nonemptiness (`coherent_SOf_HC`). -/
theorem HC_lt_derived [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.HC < derivedInG M := by
  refine lt_of_le_of_ne hyp.HC_le_derived ?_
  intro hEq
  refine (hyp.C_lt_U).not_ge ?_
  intro u hu
  have huHC : u ∈ hyp.HC := by rw [hEq]; exact hyp.base.typeP.U_le hu
  -- decompose `u = h·c` along the normal `H`-factor inside `↥M`
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hCle : hyp.C ≤ M := (hyp.C_le_U.trans hyp.base.typeP.U_le).trans
    (Subgroup.map_subtype_le _)
  haveI hHn : ((hyp.base.typeP.H).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr hyp.H_normalized_by_M
  have huM : u ∈ M := (hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)) huHC
  have hmem : (⟨u, huM⟩ : ↥M) ∈
      (hyp.base.typeP.H).subgroupOf M ⊔ hyp.C.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hHle hCle]
    exact Subgroup.mem_subgroupOf.mpr huHC
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have haH : ((a : ↥M) : G) ∈ hyp.base.typeP.H := Subgroup.mem_subgroupOf.mp ha
  have hbC : ((b : ↥M) : G) ∈ hyp.C := Subgroup.mem_subgroupOf.mp hb
  -- `a = u·b⁻¹ ∈ H ∩ U = ⊥`, so `u = b ∈ C`
  have haU : ((a : ↥M) : G) ∈ hyp.base.typeP.U := by
    have haeq : (a : ↥M) = ⟨u, huM⟩ * (b : ↥M)⁻¹ := by rw [← hab]; group
    have hcoe : ((a : ↥M) : G) = u * ((b : ↥M) : G)⁻¹ := by rw [haeq]; rfl
    rw [hcoe]
    exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (hyp.C_le_U hbC))
  have ha1 : ((a : ↥M) : G) = 1 := by
    have := hyp.H_inf_U_eq_bot.le ⟨haH, haU⟩
    rwa [Subgroup.mem_bot] at this
  have hueq : u = ((b : ↥M) : G) := by
    have h1 : (⟨u, huM⟩ : ↥M) = a * b := hab.symm
    have h2 : u = ((a * b : ↥M) : G) := congrArg Subtype.val h1
    rw [h2]
    change ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G)
    rw [ha1, one_mul]
  rw [hueq]
  exact hbC

/-- **Coherence restricts to a subfamily** (Peterfalvi (5.2) monotonicity).  If `S` is coherent and
`S' ⊆ S` carries a nonzero `A`-supported witness, then `S'` is coherent with the *same* coherent
extension: the isometry (`extension_inner_eq`), `τ`-agreement (`extends_on_supported`) and
`ZIrr`-codomain (`extension_mem_ZIrr`) laws all transport along the `zSpan` / `zSupportedSpan`
monotonicity (`Submodule.span_mono` / `zSupportedSpan_mono_left`); only the `nonzero` witness must be
re-supplied for `S'`.  This extracts the restriction pattern shared by `coherent_SOf_HC` (`S(HC) ⊆
S(M'')`) and the world-bridge `𝒮(H₀C)`-coherence subset step (`sOf(H₀C) ⊆ sOf(H₀C')`, the (9.11)
`hY` route). -/
noncomputable def isCoherent_of_subset {L : Type*} [Group L] [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S S' : Set (ClassFunction L ℂ)} {A : Set L}
    (h : OddOrder.Peterfalvi.S07.IsCoherent τ S A) (hsub : S' ⊆ S)
    (hwit : ∃ φ : ClassFunction L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S' A ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent τ S' A where
  nonzero := hwit
  extension := h.extension
  extension_inner_eq := fun a b ha hb =>
    h.extension_inner_eq a b (Submodule.span_mono hsub ha) (Submodule.span_mono hsub hb)
  extends_on_supported := fun a ha =>
    h.extends_on_supported a (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hsub ha)
  extension_mem_ZIrr := fun a ha =>
    h.extension_mem_ZIrr a (Submodule.span_mono hsub ha)

/-- **Coherence transports along a support change that shrinks the supported lattice**
(the support-side companion of `isCoherent_of_subset`: same family `S`, different support set).
If `S` is coherent on `A₁` and every `A₂`-supported lattice element is already `A₁`-supported
(`ℤ[S, A₂] ⊆ ℤ[S, A₁]`), then `S` is coherent on `A₂` with the *same* extension — only the
`nonzero` witness must be re-supplied on `A₂`.

The (9.11)/(6.8) use: the certain-type coherence (4.9)(b) lives on `A(M)`
(`supportInSubgroup (typePA M) M`) while the §10–§13 coherence interface uses
`A₀(M) ⊇ A(M)`; the column characters `μ_j` vanish off `A ∪ {1}` and `1 ∉ A₀`, so an
`A₀`-supported `ℤ[𝒯]`-combination is automatically `A`-supported and the lattices agree. -/
noncomputable def isCoherent_of_supportedSpan_le {L : Type*} [Group L] [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S : Set (ClassFunction L ℂ)} {A₁ A₂ : Set L}
    (h : OddOrder.Peterfalvi.S07.IsCoherent τ S A₁)
    (hle : OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₂ ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₁)
    (hwit : ∃ φ : ClassFunction L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₂ ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent τ S A₂ where
  nonzero := hwit
  extension := h.extension
  extension_inner_eq := h.extension_inner_eq
  extends_on_supported := fun a ha => h.extends_on_supported a (hle ha)
  extension_mem_ZIrr := h.extension_mem_ZIrr

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.9)(b) certain-type coherence, §10 interface form**: the certain-type column set
`𝒯 = certainTypeSet (hyp.toHypothesis46 …) k` is coherent for the §10 Dade map `hyp.tau` on the
§10 support `A₀(M)`.  This is the reducible-μ-side coherence input of the (9.11) `caseB`/
all-reducible assembly (issue 1019 update⁶⁰) — the §12-world analogue of the (6.8) case-(B)
`SibleyDadeHypothesis.certainTypeSet_isCoherent_tau`.

No `congrMap` seam is needed: under `toHypothesis46` the certain-type Dade map
`dadeIntegralCharacterMap h46.dade0 h46.tau` is *definitionally* `hyp.tau`
(`dade0 := hyp.dadeData.dade` and `tau := ….fullDadeIsometryData hyp.hconj` are the very
components of `S12.Hypothesis.tau`).  The support moves from `A(M)` to `A₀(M) = A(M) ∪ V^M` by
`isCoherent_of_supportedSpan_le`: every column `μ_j` vanishes off `A(M) ∪ {1}`
(`columnSum_support_subset`), so an `A₀`-supported `ℤ[𝒯]`-combination is automatically
`A(M)`-supported (`1 ∉ A₀`, `one_notMem_A0`); the `A₀`-witness is the `A(M)`-supported
`μ_{k⁻¹} − μ_k` of `certainType_nonzero`, enlarged along `A(M) ⊆ A₀(M)`. -/
noncomputable def certainTypeSet_isCoherent_A0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M) (hodd : Odd (Nat.card G))
    [NeZero (Nat.card (hyp.toHypothesis46 hG hodd).W1)]
    {k : ((hyp.toHypothesis46 hG hodd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hodd).W1 ⊔ (hyp.toHypothesis46 hG hodd).W2)) →* ℂˣ}
    (hk : k ≠ 1) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet (hyp.toHypothesis46 hG hodd) k) hyp.A0 := by
  haveI := hyp.finiteG
  classical
  -- (4.9)(b) on `A(M)`; the certain-type Dade map is definitionally `hyp.tau`
  have hbase : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S06.certainTypeSet (hyp.toHypothesis46 hG hodd) k)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.typeP) M) :=
    OddOrder.Peterfalvi.S06.certainType_isCoherent (hyp.toHypothesis46 hG hodd) hk
  refine isCoherent_of_supportedSpan_le hbase ?_ ?_
  · -- `ℤ[𝒯, A₀] ⊆ ℤ[𝒯, A(M)]`: members vanish off `A(M) ∪ {1}` and `1 ∉ A₀`
    rintro φ ⟨hφspan, hφsupp⟩
    refine ⟨hφspan, ?_⟩
    have hsupp1 : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.typeP) M ∪ {1} := by
      have hle : OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
          (OddOrder.Peterfalvi.S06.certainTypeSet (hyp.toHypothesis46 hG hodd) k) ≤
          (ClassFunction.supportedSubmodule (G := ↥M) (k := ℂ)
            (OddOrder.Peterfalvi.S04.supportInSubgroup
              (OddOrder.GroupTheory.typePA M hyp.typeP) M ∪ {1})).restrictScalars ℤ := by
        refine Submodule.span_le.mpr (fun s hs => ?_)
        obtain ⟨χ₂, hχ₂, -, rfl⟩ := hs
        simpa only [Submodule.restrictScalars_mem, ClassFunction.mem_supportedSubmodule]
          using OddOrder.Peterfalvi.S06.columnSum_support_subset
            (hyp.toHypothesis46 hG hodd) hχ₂
      exact (ClassFunction.mem_supportedSubmodule).mp (hle hφspan)
    intro x hx
    rcases hsupp1 hx with hA | h1
    · exact hA
    · exact absurd (h1 ▸ hφsupp hx) hyp.one_notMem_A0
  · -- the `A₀`-witness: `μ_{k⁻¹} − μ_k`, `A(M)`-supported ⊆ `A₀`-supported
    obtain ⟨φ, ⟨hφspan, hφsupp⟩, hφne⟩ :=
      OddOrder.Peterfalvi.S06.certainType_nonzero (hyp.toHypothesis46 hG hodd) hk
    exact ⟨φ, ⟨hφspan, hφsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      Set.subset_union_left)⟩, hφne⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), all-reducible corner ((9.9)(c))**: if every member of `𝒮(H₀C′)` is
reducible, the family is coherent on `A₀(M)`.  In this corner the family consists entirely of
μ-grid column sums (`reducible_mem_inducedKernelFamily_mem_certainTypeSet`, through `𝒮 ⊆ S =
inducedKernelFamily` by `sOf_subset_SOf`), i.e. it lies in the certain-type set `𝒯` at any
nonzero reference column — so the (4.9)(b) coherence `certainTypeSet_isCoherent_A0` restricts
along `isCoherent_of_subset`.  The nonzero supported witness is the conjugate difference
`ζ̄ − ζ` of any member (`hne`; conjugation preserves `𝒮(H₀C′)` by `sOf_closedUnderConjugate`,
the difference is `A₀`-supported by `inducedKernelFamily_conjDiff_support` and nonzero since odd
order admits no real characters).

This closes the base of the (9.11) `Ptype_core_coherence` induction in the corner where no
irreducible seed exists (`sOf_degreeSubfamily_isCoherent` is empty-cut there); the complementary
mixed corner proceeds by irreducible-cut base + `xAdjoinStepW_k` column-pair adjunction. -/
noncomputable def coherent_sOf_H0Cprime_of_allReducible [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {kref : Fin hyp.base.w2} (hkref : kref ≠ 0)
    (hallred : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      ¬ IsIrreducibleCharacter φ)
    (hne : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Nonempty) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- the certain-type coherence at the reference column
  have hcohT := certainTypeSet_isCoherent_A0 hG hyp.base hG.odd
    (hyp.base.muColumnChar_ne_one hG hG.odd hkref)
  -- `𝒮(H₀C′) ⊆ 𝒯` (every member is reducible, hence a μ-grid column sum)
  have hsub : OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ⊆
      OddOrder.Peterfalvi.S06.certainTypeSet (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd kref) := by
    intro φ hφ
    have hφSK : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
      have h := hyp.sOf_subset_SOf hyp.H0Cprime hφ
      rwa [hyp.SOf_eq] at h
    exact hyp.base.reducible_mem_inducedKernelFamily_mem_certainTypeSet hG hyp.type_alt
      (OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV hyp.type_alt hyp.base.typeP)
      (OddOrder.Peterfalvi.S11.exists_chiefFactorData hG _).choose
      hyp.params.w2_prime hkref hφSK (hallred φ hφ)
  -- the nonzero supported witness `ζ̄ − ζ` (`Prop`-confined)
  have hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0 ∧ φ ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hne
    have hζc : ζ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime :=
      Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime hζ
    have hζSK : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
      have h := hyp.sOf_subset_SOf hyp.H0Cprime hζ
      rwa [hyp.SOf_eq] at h
    refine ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _
        (Submodule.subset_span hζc) (Submodule.subset_span hζ)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 hζSK
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζSK (sub_eq_zero.mp h)
  exact isCoherent_of_subset hcohT hsub hwit

/-- **Peterfalvi (11.8): `S(HC)` is coherent** (sorry-free).  `S(HC) = SOf HC` is the subfamily of
the degree-`w₁` family `S(M'')` cut out by the *larger* kernel condition (`M'' ≤ HC`,
`secondDerived_le_HC`, so `S(HC) ⊆ S(M'')` by kernel-antitonicity), so it inherits the coherent
extension of `S(M'')` (`secondDerived_coherent`) verbatim — the isometry/`τ`-agreement/`ZIrr`-codomain
laws transport along `zSpan`/`zSupportedSpan` monotonicity.  The one genuinely new input is the
`nonzero` supported witness `ζ̄ − ζ` for a member `ζ ∈ S(HC)`: existence of `ζ` from
`inducedKernelFamily_nonempty_of_commutator_ne_top` at the proper trace `HC ⊊ M'` (`HC_lt_derived`),
its conjugate difference being `A₀`-supported (`mderivSharp_subset_A0`) and nonzero (odd order has no
real characters, `inducedKernelFamily_hasNoRealCharacters`).  This is the `S(HC)`-coherence input of
the (11.8.6) world-bridge capstone (glued with the `𝒮(H₀C)`-coherence along
`SOf_H0C_eq_SOf_HC_union_sOf`). -/
theorem coherent_SOf_HC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0) := by
  classical
  -- coherence of the larger degree-`w₁` family `S(M'')` (5.7)
  obtain ⟨hM''coh⟩ := hyp.secondDerived_coherent hG
  -- `S(HC) ⊆ S(M'')`  (`M'' ≤ HC`, kernel antitone)
  have hsub : hyp.SOf hyp.HC ⊆ hyp.SOf (secondDerivedInAmbient M) := by
    rw [hyp.SOf_eq, hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
      (Subgroup.subgroupOf_mono M hyp.secondDerived_le_HC)
  -- a genuine member `ζ ∈ S(HC)` from the proper trace `HC ⊊ M'`
  haveI hHCKnorm : ((hyp.HC.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hyp.HC_subgroupOf_normal.subgroupOf _
  have hne : (hyp.HC.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
    rw [Ne, Subgroup.subgroupOf_eq_top]
    intro hle
    have hdle : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hMle : derivedInG M ≤ hyp.HC := fun x hx =>
      Subgroup.mem_subgroupOf.mp
        (hle (show (⟨x, hdle hx⟩ : ↥M) ∈ (derivedInG M).subgroupOf M from hx))
    exact (HC_lt_derived hyp).ne (le_antisymm hyp.HC_le_derived hMle)
  obtain ⟨ζ, hζ⟩ : (hyp.SOf hyp.HC).Nonempty := by
    rw [hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_nonempty_of_commutator_ne_top
      (hyp.base.commutator_quotient_ne_top hG hne)
  rw [hyp.SOf_eq] at hζ
  have hζc := OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hζ
  -- assemble the restricted coherence, reusing `S(M'')`'s coherent extension (`isCoherent_of_subset`)
  refine ⟨isCoherent_of_subset hM''coh hsub ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩⟩
  · -- `ζ̄ − ζ ∈ ℤ[S(HC)]`
    rw [hyp.SOf_eq]
    exact Submodule.sub_mem _ (Submodule.subset_span hζc) (Submodule.subset_span hζ)
  · -- `ζ̄ − ζ` is `A₀`-supported
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hζ
  · -- `ζ̄ − ζ ≠ 0` (odd order ⇒ no real characters)
    intro h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζ (sub_eq_zero.mp h)

/-- **(9.11) constant-degree base case on the kernel filtration `S(Y)`**: the degree-`d`
irreducible subfamily of `S(Y) = SOf Y` is coherent, given one degree-`d` irreducible member.
This is the `SOf`-world form of `S12.inducedFamily_degreeSubfamily_isCoherent` — the base case
of the Peterfalvi (9.11) `Ptype_core_coherence` induction at the family `S(H₀C')` (Coq: the
degree-`qa` uniform subfamily `S1` on which `uniform_degree_coherence` fires before the
conjugate-pair extension, `PFsection9.v:1538-1546`; in the Galois case the whole family).

Every `S(Y)`-member lies in the full induced family `S = S(⊥)` (`inducedKernelFamily_antitone`,
`inducedFamily_eq_inducedKernelFamily_bot`), so the ambient degree-`d` irreducible subfamily of
`S` is coherent by the R-datum-free (5.7)/Dade engine, and the `S(Y)`-cut restricts along
`isCoherent_of_subset`; the nonzero supported witness is the conjugate difference `ζ̄ − ζ` of the
given member (conjugation preserves membership, irreducibility and degree; the difference is
`A₀`-supported by `inducedKernelFamily_conjDiff_support` and nonzero since odd order admits no
real characters). -/
noncomputable def SOf_degreeSubfamily_isCoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (Y : Subgroup G) (d : ℕ)
    (hex : ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter ζ ∧
      ((ζ : ↥M → ℂ) 1 = (d : ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- `S(Y) ⊆ S = S(⊥)` (the `⊥`-kernel condition is vacuous)
  have hsubfam : hyp.SOf Y ⊆ OddOrder.Peterfalvi.S12.inducedFamily M := by
    rw [hyp.SOf_eq, OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
  -- the ambient degree-`d` irreducible subfamily of `S` is coherent (S12 engine); the
  -- `∃`-witness eliminations stay inside `Prop`-valued `have`s (the goal is `Type`-valued)
  have hex' : ∃ ζ : ClassFunction ↥M ℂ,
      ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧ IsIrreducibleCharacter ζ ∧
      ((ζ : ↥M → ℂ) 1 = (d : ℂ)) := by
    obtain ⟨ζ, hζS, hζirr, hζ1⟩ := hex
    exact ⟨ζ, hsubfam hζS, hζirr, hζ1⟩
  have hcoh := hyp.base.inducedFamily_degreeSubfamily_isCoherent hG d hex'
  -- the `S(Y)`-cut is a subfamily of the ambient cut
  have hsub : {φ : ClassFunction ↥M ℂ | φ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter φ ∧
      ((φ : ↥M → ℂ) 1 = (d : ℂ))} ⊆
      {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} :=
    fun φ hφ => ⟨hsubfam hφ.1, hφ.2.1, hφ.2.2⟩
  -- the nonzero supported witness `ζ̄ − ζ` for the cut (again `Prop`-confined)
  have hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.base.A0 ∧ φ ≠ 0 := by
    obtain ⟨ζ, hζS, hζirr, hζ1⟩ := hex
    have hζSK : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (Y.subgroupOf M) := by
      rwa [hyp.SOf_eq] at hζS
    have hζcS : ζ.conj ∈ hyp.SOf Y := by
      rw [hyp.SOf_eq]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hζSK
    have hζc1 : ((ζ.conj : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ) := by
      rw [ClassFunction.conj_apply, hζ1, star_natCast]
    refine ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _
        (Submodule.subset_span ⟨hζcS, hζirr.conj, hζc1⟩)
        (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 hζSK
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζSK (sub_eq_zero.mp h)
  exact isCoherent_of_subset hcoh hsub hwit

/-- **(9.11) constant-degree base case on the §9 family `𝒮(Y) = sOf`** — the form the (9.11)
`Ptype_core_coherence` induction actually consumes.  ⚠ The Coq §9 family is `S_ Y = seqIndD M' M
M`_\F Y` (third argument `H = M`_\F`, PFsection9.v:209): sources are nontrivial **on `H`** (the
`𝒳`-condition of `xiSet`), *not* merely nontrivial — so the (9.11) target is the `𝒳`-side family
`sOf`, not the kernel-filter family `SOf` (`seqIndD HU M HU` is the *§11* notation,
PFsection11.v:90; issue 1019 update⁵⁸ corrects update⁵⁰ on this point).

The degree-`d` irreducible subfamily of `𝒮(Y)` is coherent, given one degree-`d` irreducible
member: `𝒮(Y) ⊆ S(Y)` (`sOf_subset_SOf`) cuts the subfamily out of the `SOf`-version
(`SOf_degreeSubfamily_isCoherent`), and the nonzero supported witness is again the conjugate
difference `ζ̄ − ζ` (conjugation preserves `𝒮(Y)`-membership by `sOf_closedUnderConjugate`). -/
noncomputable def sOf_degreeSubfamily_isCoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (Y : Subgroup G) (d : ℕ)
    (hex : ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
      IsIrreducibleCharacter ζ ∧ ((ζ : ↥M → ℂ) 1 = (d : ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.base.A0 := by
  haveI := hyp.base.finiteG
  classical
  -- transport the witness to the `SOf`-cut and fire the `SOf`-version
  have hexS : ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter ζ ∧
      ((ζ : ↥M → ℂ) 1 = (d : ℂ)) := by
    obtain ⟨ζ, hζ, hi, hd⟩ := hex
    exact ⟨ζ, hyp.sOf_subset_SOf Y hζ, hi, hd⟩
  have hcoh := SOf_degreeSubfamily_isCoherent hG hyp Y d hexS
  -- the `𝒮(Y)`-cut is a subfamily of the `S(Y)`-cut
  have hsub : {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} ⊆
      {φ : ClassFunction ↥M ℂ | φ ∈ hyp.SOf Y ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (d : ℂ))} :=
    fun φ hφ => ⟨hyp.sOf_subset_SOf Y hφ.1, hφ.2.1, hφ.2.2⟩
  -- the nonzero supported witness `ζ̄ − ζ` inside the `𝒮(Y)`-cut (`Prop`-confined)
  have hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        {φ : ClassFunction ↥M ℂ | φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y ∧
          IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} hyp.base.A0 ∧ φ ≠ 0 := by
    obtain ⟨ζ, hζ, hζirr, hζ1⟩ := hex
    have hζc : ζ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y :=
      Hypothesis.sOf_closedUnderConjugate hyp.s11Setup Y hζ
    have hζc1 : ((ζ.conj : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ) := by
      rw [ClassFunction.conj_apply, hζ1, star_natCast]
    have hζSK : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (Y.subgroupOf M) := by
      have h := hyp.sOf_subset_SOf Y hζ
      rwa [hyp.SOf_eq] at h
    refine ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _
        (Submodule.subset_span ⟨hζc, hζirr.conj, hζc1⟩)
        (Submodule.subset_span ⟨hζ, hζirr, hζ1⟩)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 hζSK
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζSK (sub_eq_zero.mp h)
  exact isCoherent_of_subset hcoh hsub hwit

/-- **(9.11) `hY`-route subset step**: the capstone's `𝒮(H₀C)`-coherence input (`hY`) follows from
the (9.11) coherence of the smaller-kernel family `𝒮(H₀C')` (`coherent_H0C_commutator`'s honest
target, the Coq `Ptype_core_coherence` induction) by `isCoherent_of_subset` along `𝒮(H₀C) ⊆
𝒮(H₀C')`, once a nonzero `A₀`-supported `𝒮(H₀C)` witness is supplied.  This wires the (9.11) result
to the world-bridge capstone `coherent_SOf_H0C_of_glued`'s `hY` parameter.

Two named obligations remain: `hcoh` = coherent(`𝒮(H₀C')`) (the (9.11) induction port over the
sorry-free S07/S08 engines — `coherent_subset_of_constant_degree` base + `coherentPairChain` /
`xAdjoinStepW` extension), and `hwit` = a nonzero `𝒮(H₀C)` witness (nonemptiness via
`S11.caseA_exists_irreducible_sOf_H0C` + a Clifford case split).  See issue 1019 update⁴⁵/⁴⁶. -/
noncomputable def coherent_sOf_H0C_of_coherent_sOf_H0Cprime [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0)
    (hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 :=
  isCoherent_of_subset hcoh hyp.sOf_H0C_subset_sOf_H0Cprime hwit

/-- **(9.11) `hY`-route bridge, `SOf`-target form** (the Coq/authoritative intermediate).  The
capstone's `𝒮(H₀C)`-coherence input (`hY`) follows from the (9.11) coherence of the §10
`inducedKernelFamily` family `SOf(H₀C') = S_ H0C'` (Coq's `Ptype_core_coherence` target — the
`HU`-induced family that carries the S08 subcoherent/witness machinery) by `isCoherent_of_subset`
along `𝒮(H₀C) ⊆ SOf(H₀C')` (`sOf ⊆ SOf` via `sOf_subset_SOf`, then `SOf`-antitone since `H₀C' ≤
H₀C`), once a nonzero `A₀`-supported `𝒮(H₀C)` witness is supplied.  This is preferred over
`coherent_sOf_H0C_of_coherent_sOf_H0Cprime` (which threads the smaller `𝒮(H₀C')` intermediate):
the (9.11) induction naturally lands `SOf(H₀C')`, so this bridge is the direct connector. -/
noncomputable def coherent_sOf_H0C_of_coherent_SOf_H0Cprime [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (hyp.SOf hyp.H0Cprime) hyp.base.A0)
    (hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 := by
  refine isCoherent_of_subset hcoh ?_ hwit
  have hSOf : hyp.SOf hyp.H0C ⊆ hyp.SOf hyp.H0Cprime := by
    rw [hyp.SOf_eq, hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
      (Subgroup.subgroupOf_mono M hyp.H0Cprime_le_H0C)
  exact (hyp.sOf_subset_SOf hyp.H0C).trans hSOf

/-- **`S(HC)` is a subfamily of `SHCSet = S(M'')` = the degree-`w₁` irreducibles** (world-bridge
`S₁`-identification): every member of `S(HC)` kills `HC ⊇ M''`, so it kills `M''` and lies in
`S(M'')`, which is exactly the degree-`w₁` irreducible family `SHCSet` (`SOf_secondDerived_eq`).
Concretely `S(HC) ⊆ S(M'')` (kernel-antitone, `M'' ≤ HC`) and `S(M'') = SHCSet`.  This exhibits the
world-bridge `S₁ = S(HC)` as the uniform-degree-`q` part and lets the (11.8.6) capstone reuse the
`SHCSet` orthogonality/generation infrastructure on `S(HC)`. -/
theorem SOf_HC_subset_SHCSet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.SOf hyp.HC ⊆ hyp.base.SHCSet := by
  have hsub : hyp.SOf hyp.HC ⊆ hyp.SOf (secondDerivedInAmbient M) := by
    rw [hyp.SOf_eq, hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
      (Subgroup.subgroupOf_mono M hyp.secondDerived_le_HC)
  rwa [hyp.SOf_secondDerived_eq hG] at hsub

/-- **World-bridge source orthogonality (pairwise)**: a member of `S(HC)` is orthogonal to a member
of `𝒮(H₀C) = sOf`.  Both are `Ind_{HU}`-members of the pairwise-orthogonal §10 family
`inducedKernelFamily HU` (`sOf ⊆ SOf` via `sOf_subset_SOf`), and they are **distinct**: an
`S(HC)`-source `θ` kills `H` (`H ≤ HC ≤ Ker θ`), while an `𝒮(H₀C)`-source `χ'` lies in `𝒳`
(`H ⊄ Ker χ'`).  If `Ind θ = Ind χ'` then `θ, χ'` are `M`-conjugate (`induce_eq_induce_iff_conj`),
and `H ⊴ M` conjugation-invariance (`subsetCharacterKernel_conjBy_of_invariant`, via
`hSubgroupOfM_normal`) transports `H ≤ Ker θ` to `H ≤ Ker χ'` — contradicting `χ' ∈ 𝒳`.  This is the
`hsrc_ortho` input of the (11.8.6) world-bridge union-glue engine. -/
theorem SOf_HC_inner_sOf_H0C_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {x y : ClassFunction ↥M ℂ} (hx : x ∈ hyp.SOf hyp.HC)
    (hy : y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) :
    ClassFunction.inner x y = 0 := by
  classical
  have hHU : OddOrder.Peterfalvi.S11.huSub hyp.s11Setup = (derivedInG M).subgroupOf M :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf hyp.s11Setup
  -- both sit in the pairwise-orthogonal `inducedKernelFamily HU`
  have hxIKF : x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) (hyp.HC.subgroupOf M) := by
    have h := hx; rw [hyp.SOf_eq, ← hHU] at h; exact h
  have hyIKF : y ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) (hyp.H0C.subgroupOf M) := by
    have h := hyp.sOf_subset_SOf hyp.H0C hy; rw [hyp.SOf_eq, ← hHU] at h; exact h
  refine OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hxIKF hyIKF ?_
  -- distinctness `x ≠ y`
  intro hxy
  -- `H` realized inside `HU`
  have hhin : OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup
      = (hyp.H.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) := by
    show (hyp.s11Setup.typeP.H.subgroupOf M).subgroupOf _
        = (hyp.base.typeP.H.subgroupOf M).subgroupOf _
    rw [hyp.setup_typeP_eq]
  -- `x`-source `θ` kills `hInHu` (`H ≤ HC`)
  obtain ⟨θ, hθne, hθker, hxeq⟩ := hxIKF
  have hHθ : (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) := by
    rw [hhin]
    refine subset_trans (SetLike.coe_subset_coe.mpr (Subgroup.subgroupOf_mono _
      (Subgroup.subgroupOf_mono M (le_sup_left : hyp.H ≤ hyp.HC)))) hθker
  -- `y`-source `χ'` lies in `𝒳`: `¬ hInHu ⊆ Ker χ'`
  obtain ⟨χ', hχ'xiOf, hyeq⟩ := hy
  have hχ'xi : ¬ ((OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ' : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)) := hχ'xiOf.1
  -- `Ind θ = Ind χ'`, so the sources are `M`-conjugate
  rw [OddOrder.Peterfalvi.S11.induceHU_eq_induce] at hyeq
  have heqInd := hxeq.symm.trans (hxy.trans hyeq)
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ χ').mp heqInd
  -- `hInHu` is `M`-conjugation-invariant (`H ⊴ M`)
  have hAinv : ∀ a ∈ (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)),
      ClassFunction.conjByMulEquiv g a ∈ (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) := by
    intro a ha
    simp only [SetLike.mem_coe] at ha ⊢
    rw [OddOrder.Peterfalvi.S11.hInHu, Subgroup.mem_subgroupOf] at ha ⊢
    rw [ClassFunction.conjByMulEquiv_apply]
    exact (OddOrder.Peterfalvi.S11.hSubgroupOfM_normal hyp.s11Setup).conj_mem _ ha g
  -- transport `hInHu ⊆ Ker θ` to `hInHu ⊆ Ker (conjBy g θ) = Ker χ'`
  have hHχ' : (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup : Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.conjBy g (θ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)) :=
    OddOrder.Peterfalvi.S11.subsetCharacterKernel_conjBy_of_invariant g _ _ hAinv hHθ
  rw [← IrreducibleCharacter.coe_conjBy, hg] at hHχ'
  exact hχ'xi hHχ'

/-- **World-bridge source orthogonality (span level)** — the `hsrc_ortho` input of the (11.8.6)
union-glue engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`:
`ℤ[S(HC)] ⊥ ℤ[𝒮(H₀C)]`.  Bilinear extension of the pairwise `SOf_HC_inner_sOf_H0C_eq_zero`
(double `span_induction`, additivity + `ℤ`-linearity of the inner product). -/
theorem span_inner_SOf_HC_sOf_H0C_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {u v : ClassFunction ↥M ℂ}
    (hu : u ∈ Submodule.span ℤ (hyp.SOf hyp.HC))
    (hv : v ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C)) :
    ClassFunction.inner u v = 0 := by
  classical
  have hright : ∀ x ∈ hyp.SOf hyp.HC,
      ∀ w ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C),
      ClassFunction.inner x w = 0 := by
    intro x hx w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact SOf_HC_inner_sOf_H0C_eq_zero hyp hx hy
    | zero => rw [ClassFunction.inner_zero_right]
    | add y z _ _ ihy ihz => rw [ClassFunction.inner_add_right, ihy, ihz, add_zero]
    | smul a y _ ih =>
        rw [← Int.cast_smul_eq_zsmul ℂ a y,
          OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]
  induction hu using Submodule.span_induction with
  | mem x hx => exact hright x hx v hv
  | zero => rw [ClassFunction.inner_zero_left]
  | add x z _ _ ihx ihz => rw [ClassFunction.inner_add_left, ihx, ihz, add_zero]
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih, mul_zero]

/-- **Peterfalvi (11.8.6) world-bridge capstone (glued form)**: `S(H₀C)` is coherent, assembled from
the two side-coherences along the world-bridge decomposition `S(H₀C) = S(HC) ∪ 𝒮(H₀C)`
(`SOf_H0C_eq_SOf_HC_union_sOf`).

This is the world-bridge analogue of `S12.Hypothesis.coherent_Sset_of_glued`.  The `S07` union-glue
engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` is fed:
- `coh` — the degree-`q` side `S(HC)`-coherence (**landed**, `coherent_SOf_HC`);
- `hY` — the `𝒮(H₀C)`-coherence (§14-gated, (9.11) `Ptype_core_coherence` route);
- `hsrc_ortho` — the source orthogonality `ℤ[S(HC)] ⊥ ℤ[𝒮(H₀C)]` (**landed, discharged here**,
  `span_inner_SOf_HC_sOf_H0C_eq_zero`);
- the `τ₃` glue map `ν` with its `hagreeX`/`hagreeY`/`hmixed`/`hDτ`/`hgen` inputs (§14/§9-gated —
  the (6.7) image-orthogonality, (5.8) column identity, and (6.8.1) generation).

The genuine world-bridge wiring (set-decomposition rewrite + engine instantiation + the
source-orthogonality discharge) is proven here; only the §14/§9 glue inputs remain as parameters,
to be supplied once the `𝒮(H₀C)`-side character theory lands.  Downstream, `coherent(S(H₀C))` feeds
`coherent_S_of_coherent_SH0C` (**already sorry-free**) to give `coherent(S)`, contradicting (11.3). -/
noncomputable def coherent_SOf_H0C_of_glued [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0)
    (hY : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0)
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G)
    (hagreeX : ∀ x ∈ hyp.SOf hyp.HC, ν x = coh.extension x)
    (hagreeY : ∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C, ν y = hY.extension y)
    (hmixed : ∀ x ∈ hyp.SOf hyp.HC, ∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (D : Set (ClassFunction ↥M ℂ)) (hDτ : ∀ d ∈ D, ν d = hyp.base.tau d)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan
        (hyp.SOf hyp.HC ∪ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.SOf hyp.HC) hyp.base.A0 ∪
        OddOrder.Peterfalvi.S07.zSupportedSpan
          (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ∪ D)) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0 := by
  haveI := hyp.base.finiteG
  rw [hyp.SOf_H0C_eq_SOf_HC_union_sOf]
  exact OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal
    coh hY ν hagreeX hagreeY
    (fun _ hu _ hv => span_inner_SOf_HC_sOf_H0C_eq_zero hyp hu hv) hmixed D hDτ hgen

/-- **Peterfalvi (11.5), reverse inclusion `HC ⊆ M''`** (named obligation): the coherence content
of (11.5).  Since `M'/M''` is abelian, `S(M'')` is coherent by (5.7); the quotient bound (11.4)
together with (11.1)/(9.6) then forces `M'' = HC`.  Char-gated — it bottoms out in Theorem (10.8)
via (11.3)/(11.4) — so it is left as a clean named subgroup-inclusion obligation. -/
theorem HC_le_secondDerived [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.HC ≤ secondDerivedInAmbient M := by
  classical
  rw [← Subgroup.relIndex_eq_one]
  -- `HC < M'` (else `U ≤ HC` forces `U ≤ C`, contradicting `C ⊊ U`)
  have hHCltM' : hyp.HC < derivedInG M := HC_lt_derived hyp
  -- `(11.4)` at `H₁ := M''` with `(5.7)`
  have hM''lt : secondDerivedInAmbient M < derivedInG M :=
    lt_of_le_of_lt hyp.secondDerived_le_HC hHCltM'
  have h114 := coherent_quotient_bound _hG hyp le_normalizer_secondDerived hM''lt
    (hyp.secondDerived_coherent _hG)
  -- tower `|M':M''| = X·|U:C|`
  set X := (secondDerivedInAmbient M).relIndex hyp.HC with hX
  set v := hyp.C.relIndex hyp.U with hv
  have htower : (secondDerivedInAmbient M).relIndex (derivedInG M) = X * v := by
    rw [hX, hv, ← hyp.HC_relIndex_derived]
    exact (Subgroup.relIndex_mul_relIndex (secondDerivedInAmbient M) hyp.HC (derivedInG M)
      hyp.secondDerived_le_HC hyp.HC_le_derived).symm
  rw [htower] at h114
  -- `v ≥ 2` from `C ⊊ U`
  have hvpos : v ≠ 0 := by
    intro h0
    have h2 : Nat.card ↥hyp.C * v = Nat.card ↥hyp.U := by
      have := Subgroup.card_mul_index (hyp.C.subgroupOf hyp.U)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show hyp.C ≤ hyp.U from hyp.C_le_U)).toEquiv] at this
    rw [h0, Nat.mul_zero] at h2
    exact (Nat.card_pos (α := ↥hyp.U)).ne' h2.symm
  have hvne1 : v ≠ 1 := by
    intro h1
    rw [hv, Subgroup.relIndex_eq_one] at h1
    exact hyp.C_lt_U.not_ge h1
  have hv2 : 2 ≤ v := by omega
  -- `X ≤ 2q`
  have hX2q : X ≤ 2 * hyp.q := by
    by_contra hgt
    push Not at hgt
    have hge : 2 * hyp.q + 1 ≤ X := hgt
    have h1 : (2 * hyp.q + 1) * v ≤ X * v := Nat.mul_le_mul_right v hge
    have h2 : 2 * hyp.q * v + v ≤ 2 * hyp.q * v + 1 := by
      calc 2 * hyp.q * v + v = (2 * hyp.q + 1) * v := by ring
        _ ≤ X * v := h1
        _ ≤ 2 * hyp.q * v + 1 := h114
    omega
  -- `q ∣ X − 1`, `X` and `q` odd ⟹ `X = 1`
  have hdvd : hyp.q ∣ X - 1 := hyp.q_dvd_secondDerived_relIndex_HC_sub_one _hG
  have hXodd : Odd X := by
    refine _hG.odd.of_dvd_nat ?_
    calc X ∣ Nat.card ↥hyp.HC := Subgroup.relIndex_dvd_card _ _
      _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.HC
  have hqodd : Odd hyp.q := by
    refine _hG.odd.of_dvd_nat ?_
    calc hyp.q = Nat.card ↥hyp.base.typeP.W1 := rfl
      _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.base.typeP.W1
  have hqpos : 0 < hyp.q := hqodd.pos
  obtain ⟨k, hk⟩ := hdvd
  have hXpos : 0 < X := hXodd.pos
  rw [Nat.odd_iff] at hXodd hqodd
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · omega
    · rw [Nat.mul_one] at hk
      omega
  · exfalso
    have h3 : hyp.q * 2 ≤ hyp.q * k := Nat.mul_le_mul_left hyp.q hk2
    have h4 : 2 * hyp.q ≤ X - 1 := by
      rw [hk]
      omega
    omega

/-- **Peterfalvi (11.5)**: the second derived subgroup is `H C`, i.e. `M'' = HC`.

`M'' ⊆ HC` is unconditional ((8.5.a), `secondDerived_le_HC`); the reverse `HC ⊆ M''` is the
coherence content carried by `HC_le_secondDerived`.  The theorem composes the two with no `sorry`
of its own. -/
theorem secondDerived_eq_HC [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M = hyp.HC :=
  le_antisymm hyp.secondDerived_le_HC (HC_le_secondDerived _hG hyp)

/-- **Peterfalvi (11.6), `C = U'`**: `U' ≤ C` is (8.5.b) (`derivedU_le_C`); conversely
`C ≤ HC = M'' ≤ H ⊔ U'` ((11.5) + `secondDerived_le_H_sup_derivedU`), and an
`H ⊔ U'`-element of `U` splits as `h·u'` with `h ∈ H ⊓ U = ⊥`, so `C ≤ U'`. -/
theorem C_eq_derivedU [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.C = derivedInG hyp.base.typeP.U := by
  refine le_antisymm ?_ hyp.derivedU_le_C
  intro c hc
  have hcM'' : c ∈ secondDerivedInAmbient M := by
    rw [secondDerived_eq_HC hG hyp]
    exact Subgroup.mem_sup_right hc
  have hcHU' : c ∈ hyp.base.typeP.H ⊔ derivedInG hyp.base.typeP.U :=
    hyp.secondDerived_le_H_sup_derivedU hcM''
  -- split `c = h·u'` and cancel the `H`-part inside `U`
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hU'le : derivedInG hyp.base.typeP.U ≤ M :=
    ((Subgroup.map_subtype_le _).trans hyp.base.typeP.U_le).trans (Subgroup.map_subtype_le _)
  obtain ⟨h, hh, u', hu', hceq⟩ :=
    exists_mul_of_mem_sup_of_normalized hHle hU'le hyp.H_normalized_by_M hcHU'
  have hhU : h ∈ hyp.base.typeP.U := by
    have h1 : h = c * u'⁻¹ := by rw [hceq]; group
    rw [h1]
    exact Subgroup.mul_mem _ (hyp.C_le_U hc)
      (Subgroup.inv_mem _ ((Subgroup.map_subtype_le _) hu'))
  have hh1 : h = 1 := by
    have := hyp.H_inf_U_eq_bot.le ⟨hh, hhU⟩
    rwa [Subgroup.mem_bot] at this
  rw [hceq, hh1, one_mul]
  exact hu'

end OddOrder.Peterfalvi.S13
