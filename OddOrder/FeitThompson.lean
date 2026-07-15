import OddOrder.FeitThompsonCharacterData

/-!
# Feit–Thompson Section 16 assembly and odd-order theorem

Peterfalvi §§13–16 (pp. 64–92) and BG Appendix C: construct the named
Section 16 inputs, derive the final contradiction, and perform the
minimal-counterexample reduction.
-/

namespace OddOrder
open OddOrder.BG
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.RepresentationTheory
open scoped Pointwise

universe u

section
open scoped OddOrder.Peterfalvi.S15.FiniteInduce


/-- **Peterfalvi §13 coherent Dade-grid producer** (`sorry`-free) — *lane-b*
(Peterfalvi §3–§13 coherent grids).  Given the maximal pair and the type-P
structure, constructs the character grids `ω, μ, ν`, the signs `δ, δ'`, the integral
maps, and the induction identities (13.1.d/e).

The mathematically substantive fields are the genuine §13 grid:
* `omega := omegaS` — the shared `ω`-grid, materialized from the certain-type machinery of
  `mp.S` (`certainTypeS`, indexed by `mp.K`, `mp.Kstar` and aligned to `tp.W₁, tp.W₂` via
  `tp.W1_eq_K`/`W2_eq_Kstar`).  `omegaS_eq_omegaT` proves it equals the T-side reconstruction, so
  the single `ω`-field satisfies *both* induction identities;
* `mu := muS`, `nu := nuT`, `delta := deltaS`, `deltaPrime := deltaPrimeT` — the induced
  exceptional characters and signs read off `certainTypeS`/`certainTypeT`'s `columnFamily`;
* `tau3 := tau3W` — the genuine §3.2 Dade σ-integral of the G-internal TI-cyclic structure on
  `W = S ∩ T`, supported on `Ẑ = W \ (W₁ ∪ W₂)` (built from the proven BG Theorem 14.7 TI fact and
  the general §4 Dade producer; `#print axioms` is `sorryAx`-free);
* `mu_definition := muS_definition`, `nu_definition := nuT_definition` — Peterfalvi (13.1.e),
  proven `sorry`-free.

**Vestigial fields** `Sset, Tset, A0S, A0T, tauS, tauT` carry honest placeholders (`∅`, `0`).
These are *not* consumed on the FT critical path: the §13/§16 contradiction in
`Peterfalvi.S16` (`S16_NonExistenceG`) is routed entirely through `eta = τ₃ ∘ ω` (the W-side
Dade grid), never through the S/T-side maximal-coherent isometries `τ_S, τ_T`.  The only
references to `tauS`/`tauT` are the (currently `sorry`-stubbed, *uncited*) coherence-wiring
lemmas in `S15_SAndT_Setup`, which lie off the FT path.  `Hypothesis` itself places no `Prop`
constraint on these six fields, so the placeholders introduce no unsound dependency — they are
genuine values of the right type for fields the formalized contradiction does not read.  (User
decision 2026-06-24, issue 1004: close the producer on the verified-vestigial finding rather
than build the off-path §7 maximal-coherent Dade theory.) -/
noncomputable def section16CharacterData_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) (tp : Section16TypePStructure mp) :
    Section16CharacterData mp tp := by
  -- The grid building blocks carry `[NeZero |certainType{S,T}.W₁|]` (the prime base-index
  -- normalization); discharge both from `|certainTypeS.W₁| = tp.q`, `|certainTypeT.W₁| = tp.p`.
  haveI : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
    ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
  haveI : NeZero (Nat.card ↥(mp.certainTypeT hG).W1) :=
    ⟨by rw [Section16CharacterData.cardCertainTypeT_W1 hG mp tp]; exact tp.p_prime.pos.ne'⟩
  exact
    { Sset := ∅
      Tset := ∅
      A0S := ∅
      A0T := ∅
      tauS := 0
      tauT := 0
      omega := Section16CharacterData.omegaS hG mp tp
      mu := Section16CharacterData.muS hG mp tp
      nu := Section16CharacterData.nuT hG mp tp
      delta := Section16CharacterData.deltaS hG mp tp
      deltaPrime := Section16CharacterData.deltaPrimeT hG mp tp
      delta_pm_one :=
        ⟨fun j => ((mp.certainTypeS hG).columnFamily
            (Section16CharacterData.chi2enum hG mp tp j)).sign_eq,
         fun i => ((mp.certainTypeT hG).columnFamily
            (Section16CharacterData.colT hG mp tp i)).sign_eq⟩
      mu_degree_modEq_delta := fun i j => by
        haveI : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
          ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
        obtain ⟨a, ha⟩ := (mp.certainTypeS hG).certainType_degree_modEq
          (Section16CharacterData.chi2enum hG mp tp j) (Section16CharacterData.eqQ hG mp tp i)
        refine ⟨a, ?_⟩
        have hq : (tp.q : ℂ) = (Nat.card ↥(mp.certainTypeS hG).W1 : ℂ) := by
          rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]
        simp only [Section16CharacterData.muS, Section16CharacterData.deltaS, hq]
        exact ha
      delta_zero_eq_one := by
        haveI : NeZero (Nat.card ↥(mp.certainTypeS hG).W1) :=
          ⟨by rw [Section16CharacterData.cardCertainTypeS_W1 hG mp tp]; exact tp.q_prime.pos.ne'⟩
        show Section16CharacterData.deltaS hG mp tp ⟨0, tp.p_prime.pos⟩ = 1
        rw [Section16CharacterData.deltaS, Section16CharacterData.chi2enum_zero]
        exact ((mp.certainTypeS hG).certainType_zero_column_anchor).1
      tau3 := Section16CharacterData.tau3W hG mp tp
      mu_definition := Section16CharacterData.muS_definition hG mp tp
      mu_irreducible := fun i j =>
        (((mp.certainTypeS hG).columnFamily (Section16CharacterData.chi2enum hG mp tp j)).mu
          (Section16CharacterData.eqQ hG mp tp i)).isIrreducible
      mu_col_injective := fun j i i' h =>
        (Section16CharacterData.eqQ hG mp tp).injective
          ((((mp.certainTypeS hG).columnFamily
            (Section16CharacterData.chi2enum hG mp tp j)).injective)
            (OddOrder.RepresentationTheory.IrreducibleCharacter.ext h))
      mu_orthonormal := Section16CharacterData.muS_orthonormal hG mp tp
      mu_diff_support := fun i {j k} hj0 hk0 hdeg =>
        Section16CharacterData.muS_diff_support hG mp tp i hj0 hk0 hdeg
      mu_apply_of_not_mem_W2 := fun i j w hwW hwS hw2 =>
        Section16CharacterData.muS_apply_of_not_mem_W2 hG mp tp i j w hwW hwS hw2
      mu_conj := Section16CharacterData.muS_conj hG mp tp
      tau3_omega_conj := Section16CharacterData.tau3W_omegaS_conj hG mp tp
      mu_colSum_eq_induce := fun j => by
        refine ⟨ClassFunction.restrict ((derivedInG mp.S).subgroupOf mp.S)
            (((mp.certainTypeS hG).columnFamily
              (Section16CharacterData.chi2enum hG mp tp j)).mu 0 : ClassFunction ↥mp.S ℂ),
          ?_, ?_, ?_⟩
        · exact (mp.certainTypeS hG).certainTypeRestrict_isIrreducible _
        · calc (∑ i : Fin tp.q, Section16CharacterData.muS hG mp tp i j)
              = ∑ i' : Fin (Nat.card ↥(mp.certainTypeS hG).W1),
                  (((mp.certainTypeS hG).columnFamily
                    (Section16CharacterData.chi2enum hG mp tp j)).mu i' :
                    ClassFunction ↥mp.S ℂ) := by
                simp only [Section16CharacterData.muS]
                exact Equiv.sum_comp (Section16CharacterData.eqQ hG mp tp)
                  (fun i' => (((mp.certainTypeS hG).columnFamily
                    (Section16CharacterData.chi2enum hG mp tp j)).mu i' :
                    ClassFunction ↥mp.S ℂ))
            _ = _ := ((mp.certainTypeS hG).induce_restrict_certainType_eq _).symm
        · intro hjne hsub
          have hχ₂ne : Section16CharacterData.chi2enum hG mp tp j ≠ 1 := by
            rw [← Section16CharacterData.chi2enum_zero hG mp tp]
            exact fun h => hjne ((Section16CharacterData.chi2enum hG mp tp).injective h)
          refine (mp.certainTypeS hG).not_subset_characterKernel_chiRestrict_of_ne_one
            hχ₂ne ?_
          have hseq : ((tp.W2.subgroupOf mp.S).subgroupOf
                ((derivedInG mp.S).subgroupOf mp.S))
              = (((mp.certainTypeS hG).W2).subgroupOf
                ((derivedInG mp.S).subgroupOf mp.S)) := by
            rw [Section16CharacterData.certainTypeS_W2_eq hG mp, tp.W2_eq_Kstar hG]
          exact hseq ▸ hsub
      mu_reducible_dichotomy := Section16CharacterData.muS_reducible_dichotomy hG mp tp
      nu_definition := Section16CharacterData.nuT_definition hG mp tp
      nu_irreducible := Section16CharacterData.nuT_irreducible hG mp tp
      nu_row_injective := Section16CharacterData.nuT_row_injective hG mp tp
      nu_orthonormal := Section16CharacterData.nuT_orthonormal hG mp tp
      nu_degree_modEq_deltaPrime :=
        Section16CharacterData.nuT_degree_modEq_deltaPrime hG mp tp
      deltaPrime_zero_eq_one := Section16CharacterData.deltaPrimeT_zero_eq_one hG mp tp
      nu_rowSum_eq_induce := Section16CharacterData.nuT_rowSum_eq_induce hG mp tp
      nu_reducible_dichotomy := Section16CharacterData.nuT_reducible_dichotomy hG mp tp
      nu_diff_support := Section16CharacterData.nuT_diff_support hG mp tp
      nu_apply_of_not_mem_W1 := Section16CharacterData.nuT_apply_of_not_mem_W1 hG mp tp
      nu_conj := Section16CharacterData.nuT_conj hG mp tp
      tau3_isometry := Section16CharacterData.tau3W_isometry hG mp tp
      tau3_trivial := Section16CharacterData.tau3W_trivial hG mp tp
      tau3_apply_of_regular := fun α w hwW hnot =>
        Section16CharacterData.tau3W_apply_of_regular hG mp tp α w hwW hnot
      tau3_mem_ZIrr := fun _ hz => Section16CharacterData.tau3W_mem_ZIrr hG mp tp hz
      omega_orthonormal := Section16CharacterData.omegaS_inner hG mp tp
      omega_apply_one := Section16CharacterData.omegaS_apply_one hG mp tp
      omega_mem_ZIrr := Section16CharacterData.omegaS_mem_ZIrr hG mp tp
      omega_mul := Section16CharacterData.omegaS_mul hG mp tp
      omega_col_zero_apply_of_mem_W2 :=
        Section16CharacterData.omegaS_col_zero_apply_of_mem_W2 hG mp tp
      omega_row_zero_apply_of_mem_W1 :=
        Section16CharacterData.omegaS_row_zero_apply_of_mem_W1 hG mp tp
      omega_pow_q_of_mem_W1 := Section16CharacterData.omegaS_pow_q_of_mem_W1 hG mp tp
      omega_pow_p_of_mem_W2 := Section16CharacterData.omegaS_pow_p_of_mem_W2 hG mp tp
      eta_complete_vanish := fun χ horth w hwW hnot =>
        Section16CharacterData.tau3W_omegaS_complete_vanish hG mp tp χ horth hwW hnot
      eta_fourcorner_vanish := fun i j hi hj x hx =>
        Section16CharacterData.tau3W_omegaS_fourcorner_vanish hG mp tp i j hi hj (by
          intro hmem
          obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hmem
          obtain ⟨c, hc⟩ := isConj_iff.mp hconj
          exact hx (OddOrder.GroupTheory.mem_conjClassSet.mpr ⟨a, ha, c, hc⟩))
      eta_row_vanish_of_one_zero := fun x h0 i hi =>
        Section16CharacterData.tau3W_omegaS_row_vanish_of_one_zero hG mp tp h0 i hi
      eta_row_galois_orbit :=
        Section16CharacterData.tau3W_omegaS_row_galois_orbit hG mp tp
      eta_column_galois_orbit :=
        Section16CharacterData.tau3W_omegaS_column_galois_orbit hG mp tp
      eta_intCast_of_coprime := fun g hg i j =>
        Section16CharacterData.tau3W_omegaS_intCast_of_coprime hG mp tp i j hg
      eta_pair_of_coprime := fun g hg i j =>
        Section16CharacterData.tau3W_omegaS_pair_of_coprime hG mp tp i j hg
      eta_principal_of_coprime := fun g hg =>
        Section16CharacterData.tau3W_omegaS_principal_of_coprime hG mp tp hg }

/-- **Assembly of `Section16Inputs` from the three lane producers** (`sorry`-free).
Each field of `Section16Inputs` is sourced from exactly one of `mp` / `tp` / `cd`;
the character fields unify because `mp.S, mp.T, tp.W, tp.q, tp.p` are the chosen
witnesses. -/
noncomputable def section16Inputs_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : Section16Inputs G :=
  let mp := section16MaximalPair_of_isMinimalSimpleOdd hG
  let tp := section16TypePStructure_of_isMinimalSimpleOdd hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG) mp
  let cd := section16CharacterData_of_isMinimalSimpleOdd hG mp tp
  { S := mp.S
    T := mp.T
    W1 := tp.W1
    W2 := tp.W2
    W := tp.W
    U := tp.U
    V := tp.V
    S_maximal := mp.S_maximal
    T_maximal := mp.T_maximal
    S_ne_T := mp.S_ne_T
    S_nonI := mp.S_nonI
    T_nonI := mp.T_nonI
    one_typeII := mp.one_typeII
    theorem88_caseB := mp.theorem88_caseB
    W_eq_inter := tp.W_eq_inter
    W_eq_join := tp.W_eq_join
    W1_inf_W2_eq_bot := tp.W1_inf_W2_eq_bot
    W1_commutes_W2 := tp.W1_commutes_W2
    W_cyclic := tp.W_cyclic
    S_deriv_eq_PU := tp.S_deriv_eq_PU
    T_deriv_eq_QV := tp.T_deriv_eq_QV
    V_inf_Q_eq_bot := tp.V_inf_Q_eq_bot
    W2_isComplement_T_deriv := tp.W2_isComplement_T_deriv
    W1_normalizes_U := tp.W1_normalizes_U
    W2_normalizes_V := tp.W2_normalizes_V
    q := tp.q
    p := tp.p
    q_prime := tp.q_prime
    p_prime := tp.p_prime
    q_eq_card_W1 := tp.q_eq_card_W1
    p_eq_card_W2 := tp.p_eq_card_W2
    u := tp.u
    v := tp.v
    c := tp.c
    d := tp.d
    c_eq_card_C := tp.c_eq_card_C
    d_eq_card_D := tp.d_eq_card_D
    card_U_eq_uc := tp.card_U_eq_uc
    card_V_eq_vd := tp.card_V_eq_vd
    Sset := cd.Sset
    Tset := cd.Tset
    A0S := cd.A0S
    A0T := cd.A0T
    tauS := cd.tauS
    tauT := cd.tauT
    omega := cd.omega
    mu := cd.mu
    nu := cd.nu
    delta := cd.delta
    deltaPrime := cd.deltaPrime
    delta_pm_one := cd.delta_pm_one
    mu_degree_modEq_delta := cd.mu_degree_modEq_delta
    delta_zero_eq_one := cd.delta_zero_eq_one
    tau3 := cd.tau3
    mu_definition := cd.mu_definition
    mu_irreducible := cd.mu_irreducible
    mu_col_injective := cd.mu_col_injective
    mu_orthonormal := cd.mu_orthonormal
    mu_diff_support := cd.mu_diff_support
    mu_apply_of_not_mem_W2 := cd.mu_apply_of_not_mem_W2
    mu_conj := cd.mu_conj
    tau3_omega_conj := cd.tau3_omega_conj
    mu_colSum_eq_induce := cd.mu_colSum_eq_induce
    mu_reducible_dichotomy := cd.mu_reducible_dichotomy
    nu_definition := cd.nu_definition
    nu_irreducible := cd.nu_irreducible
    nu_row_injective := cd.nu_row_injective
    nu_orthonormal := cd.nu_orthonormal
    nu_degree_modEq_deltaPrime := cd.nu_degree_modEq_deltaPrime
    deltaPrime_zero_eq_one := cd.deltaPrime_zero_eq_one
    nu_rowSum_eq_induce := cd.nu_rowSum_eq_induce
    nu_reducible_dichotomy := cd.nu_reducible_dichotomy
    nu_diff_support := cd.nu_diff_support
    nu_apply_of_not_mem_W1 := cd.nu_apply_of_not_mem_W1
    nu_conj := cd.nu_conj
    q_lt_p := tp.q_lt_p
    Sdata := tp.Sdata
    Sdata_U_eq := tp.Sdata_U_eq
    Sdata_W1_eq := tp.Sdata_W1_eq
    S_U_commutative := tp.S_U_commutative
    Sdata_W2_eq := tp.Sdata_W2_eq
    tau3_isometry := cd.tau3_isometry
    tau3_trivial := cd.tau3_trivial
    tau3_apply_of_regular := cd.tau3_apply_of_regular
    tau3_mem_ZIrr := cd.tau3_mem_ZIrr
    omega_orthonormal := cd.omega_orthonormal
    omega_apply_one := cd.omega_apply_one
    omega_mem_ZIrr := cd.omega_mem_ZIrr
    omega_mul := cd.omega_mul
    omega_col_zero_apply_of_mem_W2 := cd.omega_col_zero_apply_of_mem_W2
    omega_row_zero_apply_of_mem_W1 := cd.omega_row_zero_apply_of_mem_W1
    omega_pow_q_of_mem_W1 := cd.omega_pow_q_of_mem_W1
    omega_pow_p_of_mem_W2 := cd.omega_pow_p_of_mem_W2
    eta_complete_vanish := cd.eta_complete_vanish
    eta_fourcorner_vanish := cd.eta_fourcorner_vanish
    eta_row_vanish_of_one_zero := cd.eta_row_vanish_of_one_zero
    eta_row_galois_orbit := cd.eta_row_galois_orbit
    eta_column_galois_orbit := cd.eta_column_galois_orbit
    eta_intCast_of_coprime := cd.eta_intCast_of_coprime
    eta_pair_of_coprime := cd.eta_pair_of_coprime
    eta_principal_of_coprime := cd.eta_principal_of_coprime }

/-- **Assembly of the Section 16 configuration from named inputs** (`sorry`-free).

Given the `Section16Inputs` witnesses, this builds `Peterfalvi.S16.Hypothesis`
without any `sorry`.  Beyond carrying the input fields, it *derives* the fields of
`Peterfalvi.S15.Hypothesis` that are not independent data:

* `finiteG` from the ambient `[Finite G]`;
* the Fitting kernels `P := F(S)`, `Q := F(T)` (`maxNilpotentNormalHall`) and the
  centralizer complements `C := U ∩ C_G(P)`, `D := V ∩ C_G(Q)` definitionally, so
  `P_eq_SF`, `Q_eq_TF`, `C_eq`, `D_eq` are `rfl` — they are determined by
  `S, T, U, V`, not separate data;
* `q_odd`, `p_odd` from `Odd |G|` (subgroup orders divide `|G|`);
* `eta := τ₃ ∘ ω`, discharging **Peterfalvi (13.1.d)** `η_{ij} = ω_{ij}^{τ₃}`
  definitionally — `η` is the τ₃-image of the `ω`-grid, not separate data;
* `m` as the **(13.10)/(13.11)** rational formula in `p, q`, with `m_eq` by `rfl`.

These derivations are why `Section16Inputs` is a *strictly smaller* obligation
than `Peterfalvi.S16.Hypothesis`: discharging the menu does not require separately
producing `P, Q, C, D`, `η`, `m`, or the oddness facts. -/
noncomputable def sectionSixteenHypothesis_of_inputs {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (inp : Section16Inputs G) :
    Peterfalvi.S16.Hypothesis (G := G) where
  base :=
    { S := inp.S
      T := inp.T
      W1 := inp.W1
      W2 := inp.W2
      W := inp.W
      P := maxNilpotentNormalHall inp.S
      Q := maxNilpotentNormalHall inp.T
      U := inp.U
      V := inp.V
      C := inp.U ⊓ Subgroup.centralizer (maxNilpotentNormalHall inp.S : Set G)
      D := inp.V ⊓ Subgroup.centralizer (maxNilpotentNormalHall inp.T : Set G)
      S_maximal := inp.S_maximal
      T_maximal := inp.T_maximal
      S_ne_T := inp.S_ne_T
      S_nonI := inp.S_nonI
      T_nonI := inp.T_nonI
      one_typeII := inp.one_typeII
      theorem88_caseB := inp.theorem88_caseB
      W_eq_inter := inp.W_eq_inter
      W_eq_join := inp.W_eq_join
      W1_inf_W2_eq_bot := inp.W1_inf_W2_eq_bot
      W1_commutes_W2 := inp.W1_commutes_W2
      W_cyclic := inp.W_cyclic
      P_eq_SF := rfl
      Q_eq_TF := rfl
      S_deriv_eq_PU := inp.S_deriv_eq_PU
      T_deriv_eq_QV := inp.T_deriv_eq_QV
      Q_inf_V_eq_bot := inp.V_inf_Q_eq_bot
      W2_isComplement_T_deriv := inp.W2_isComplement_T_deriv
      C_eq := rfl
      D_eq := rfl
      W1_normalizes_U := inp.W1_normalizes_U
      W2_normalizes_V := inp.W2_normalizes_V
      q := inp.q
      p := inp.p
      q_prime := inp.q_prime
      p_prime := inp.p_prime
      q_odd := by
        rw [inp.q_eq_card_W1]
        exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card inp.W1)
      p_odd := by
        rw [inp.p_eq_card_W2]
        exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card inp.W2)
      q_eq_card_W1 := inp.q_eq_card_W1
      p_eq_card_W2 := inp.p_eq_card_W2
      u := inp.u
      v := inp.v
      c := inp.c
      d := inp.d
      c_eq_card_C := inp.c_eq_card_C
      d_eq_card_D := inp.d_eq_card_D
      card_U_eq_uc := inp.card_U_eq_uc
      card_V_eq_vd := inp.card_V_eq_vd
      Sset := inp.Sset
      Tset := inp.Tset
      A0S := inp.A0S
      A0T := inp.A0T
      tauS := inp.tauS
      tauT := inp.tauT
      omega := inp.omega
      eta := fun i j => inp.tau3 (inp.omega i j)
      mu := inp.mu
      nu := inp.nu
      delta := inp.delta
      deltaPrime := inp.deltaPrime
      delta_pm_one := inp.delta_pm_one
      mu_degree_modEq_delta := inp.mu_degree_modEq_delta
      delta_zero_eq_one := inp.delta_zero_eq_one
      tau3 := inp.tau3
      eta_eq_tau_omega := fun _ _ => rfl
      mu_definition := inp.mu_definition
      mu_irreducible := inp.mu_irreducible
      mu_col_injective := inp.mu_col_injective
      mu_orthonormal := inp.mu_orthonormal
      mu_diff_support := inp.mu_diff_support
      mu_apply_of_not_mem_W2 := inp.mu_apply_of_not_mem_W2
      mu_conj := inp.mu_conj
      eta_conj := inp.tau3_omega_conj
      mu_colSum_eq_induce := inp.mu_colSum_eq_induce
      mu_reducible_dichotomy := inp.mu_reducible_dichotomy
      nu_definition := inp.nu_definition
      m := 1 - 1 / ((inp.q : ℚ) - 1) - ((inp.q : ℚ) - 1) / (inp.q : ℚ) ^ inp.p +
        1 / (((inp.q : ℚ) - 1) * (inp.q : ℚ) ^ inp.p)
      m_eq := rfl
      Sdata := inp.Sdata
      Sdata_U_eq := inp.Sdata_U_eq
      Sdata_W1_eq := inp.Sdata_W1_eq
      S_U_commutative := inp.S_U_commutative
      Sdata_W2_eq := inp.Sdata_W2_eq
      tau3_isometry := inp.tau3_isometry
      tau3_trivial := inp.tau3_trivial
      tau3_apply_of_regular := inp.tau3_apply_of_regular
      tau3_mem_ZIrr := inp.tau3_mem_ZIrr
      omega_orthonormal := inp.omega_orthonormal
      omega_apply_one := inp.omega_apply_one
      omega_mem_ZIrr := inp.omega_mem_ZIrr
      omega_mul := inp.omega_mul
      omega_col_zero_apply_of_mem_W2 := inp.omega_col_zero_apply_of_mem_W2
      omega_row_zero_apply_of_mem_W1 := inp.omega_row_zero_apply_of_mem_W1
      omega_pow_q_of_mem_W1 := inp.omega_pow_q_of_mem_W1
      omega_pow_p_of_mem_W2 := inp.omega_pow_p_of_mem_W2
      eta_complete_vanish := inp.eta_complete_vanish
      eta_fourcorner_vanish := inp.eta_fourcorner_vanish
      eta_row_vanish_of_one_zero := inp.eta_row_vanish_of_one_zero
      eta_row_galois_orbit := inp.eta_row_galois_orbit
      eta_column_galois_orbit := inp.eta_column_galois_orbit
      eta_intCast_of_coprime := inp.eta_intCast_of_coprime
      eta_pair_of_coprime := inp.eta_pair_of_coprime
      eta_principal_of_coprime := inp.eta_principal_of_coprime }
  nuGridSupply :=
    { nu_irreducible := inp.nu_irreducible
      nu_row_injective := inp.nu_row_injective
      nu_orthonormal := inp.nu_orthonormal
      nu_degree_modEq_deltaPrime := inp.nu_degree_modEq_deltaPrime
      deltaPrime_zero_eq_one := inp.deltaPrime_zero_eq_one
      nu_rowSum_eq_induce := inp.nu_rowSum_eq_induce
      nu_reducible_dichotomy := inp.nu_reducible_dichotomy
      nu_diff_support := inp.nu_diff_support
      nu_apply_of_not_mem_W1 := inp.nu_apply_of_not_mem_W1
      nu_conj := inp.nu_conj }
  q_lt_p := inp.q_lt_p

/-- **Canonical pure ν-grid supply from named Section 16 inputs** (issue 1030).

The T-side Peterfalvi (4.3)--(4.9) facts are explicit fields of `Section16Inputs`.
Consequently they assemble into the pure `NuGridSupplyData` package at the same
axiom-clean boundary as `sectionSixteenHypothesis_of_inputs`; no generic row-translation
principle and no post-(14.9) commutativity fact is used. -/
theorem sectionSixteenNuGridSupplyData_of_inputs
    {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    (inp : Section16Inputs G) :
    Peterfalvi.S15.NuGridSupplyData (sectionSixteenHypothesis_of_inputs hodd inp).base := by
  exact (sectionSixteenHypothesis_of_inputs hodd inp).nuGridSupply

/-- **Canonical Section 16 configuration from a minimal simple odd-order group.**
The named Bender–Glauberman and Peterfalvi producers construct
`Section16Inputs G`, and the axiom-clean `sectionSixteenHypothesis_of_inputs`
assembles those inputs into the field-normalizer configuration of Peterfalvi (14.2).

Axiom audit (2026-07-15): this definition and
`section16Inputs_of_isMinimalSimpleOdd` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  In particular, the former gated input-menu
obligation is no longer the FT frontier.

The downstream `noMinimalSimpleOdd_of_section16` bridge, BG Appendix C final contradiction,
and `feitThompson` have now been audited against the same standard-three-axiom boundary. -/
noncomputable def sectionSixteenHypothesis_of_isMinimalSimpleOdd
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) :
    Peterfalvi.S16.Hypothesis (G := G) :=
  sectionSixteenHypothesis_of_inputs hG.odd (section16Inputs_of_isMinimalSimpleOdd hG)

end

/-- **No minimal simple group of odd order exists.** Combining the upstream
construction of the Section 16 configuration
(`sectionSixteenHypothesis_of_isMinimalSimpleOdd`) with the already-formalized
final contradiction (`noMinimalSimpleOdd_of_section16`). -/
theorem noMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : False :=
  noMinimalSimpleOdd_of_section16 hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG)
    (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
    (sectionSixteenHypothesis_of_isMinimalSimpleOdd hG)

/-! ## The minimal-counterexample reduction -/

/-- **Minimal-counterexample reduction** (pure group theory, `sorry`-free).

If no minimal simple group of odd order exists, then every finite group of odd
order is solvable.

The proof is strong induction on `Nat.card G`. If `G` were a non-solvable group of
odd order, then — using the induction hypothesis on its (smaller, odd-order) proper
subgroups and proper quotients — every proper subgroup is solvable and `G` is
simple: a proper nontrivial normal subgroup `N` would make `G` an extension of the
solvable group `N` by the solvable group `G ⧸ N`, hence solvable
(`solvable_of_ker_le_range`). Thus `G` would be a minimal simple group of odd
order, contradicting the hypothesis `hno`. -/
theorem feitThompson_of_noMinimalSimpleOdd
    (hno : ∀ (H : Type u) [Group H] [Finite H], IsMinimalSimpleOdd H → False)
    {G : Type u} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    IsSolvable G := by
  -- Strong induction on the order, generalized over all groups in this universe.
  suffices key : ∀ (n : ℕ) (K : Type u) [Group K] [Finite K],
      Nat.card K = n → Odd (Nat.card K) → IsSolvable K from key (Nat.card G) G rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ hcard hodd'
    subst hcard
    by_contra hns
    -- `K` is nontrivial: a subsingleton group is solvable.
    have hNT : Nontrivial K := by
      by_contra hc
      rw [not_nontrivial_iff_subsingleton] at hc
      haveI := hc
      exact hns inferInstance
    -- `K` is simple: a proper nontrivial normal subgroup splits `K` as a solvable
    -- extension of a solvable group, making `K` solvable.
    have hsimple : IsSimpleGroup K := by
      refine { toNontrivial := hNT, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hNbot, hNtop⟩ := hcon
      -- `N` is solvable (proper subgroup of odd order, induction hypothesis).
      have hN_odd : Odd (Nat.card ↥N) :=
        hodd'.of_dvd_nat (Subgroup.card_subgroup_dvd_card N)
      have hNlt : Nat.card ↥N < Nat.card K := by
        have hidx : 1 < N.index := Subgroup.one_lt_index_of_ne_top hNtop
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := ↥N)) hidx
        rwa [Subgroup.card_mul_index] at h
      haveI : IsSolvable ↥N := ih (Nat.card ↥N) hNlt ↥N rfl hN_odd
      -- `K ⧸ N` is solvable (proper quotient of odd order, induction hypothesis).
      have hQ_odd : Odd (Nat.card (K ⧸ N)) :=
        hodd'.of_dvd_nat (Subgroup.card_quotient_dvd_card N)
      have hQlt : Nat.card (K ⧸ N) < Nat.card K := by
        have hN1 : 1 < Nat.card ↥N :=
          Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot N).mpr hNbot)
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := K ⧸ N)) hN1
        rwa [← Subgroup.card_eq_card_quotient_mul_card_subgroup] at h
      haveI : IsSolvable (K ⧸ N) := ih (Nat.card (K ⧸ N)) hQlt (K ⧸ N) rfl hQ_odd
      -- Extension of a solvable group by a solvable group is solvable.
      have hfg : (QuotientGroup.mk' N).ker ≤ (N.subtype).range :=
        le_of_eq ((QuotientGroup.ker_mk' N).trans (Subgroup.subtype_range N).symm)
      exact hns (solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) hfg)
    -- Every proper subgroup is solvable (smaller, odd order, induction hypothesis).
    have hproper : ∀ M : Subgroup K, M < ⊤ → IsSolvable ↥M := by
      intro M hM
      have hM_odd : Odd (Nat.card ↥M) :=
        hodd'.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
      have hMlt : Nat.card ↥M < Nat.card K := by
        have hidx : 1 < M.index := Subgroup.one_lt_index_of_ne_top (ne_of_lt hM)
        have h := lt_mul_of_one_lt_right (Nat.card_pos (α := ↥M)) hidx
        rwa [Subgroup.card_mul_index] at h
      exact ih (Nat.card ↥M) hMlt ↥M rfl hM_odd
    -- `K` is then a minimal simple group of odd order — impossible.
    exact hno K ⟨hodd', hsimple, hns, hproper⟩

/-! ## The Feit–Thompson theorem -/

/-- **Feit-Thompson theorem**: every finite group of odd order is solvable.

This combines the `sorry`-free minimal-counterexample reduction
(`feitThompson_of_noMinimalSimpleOdd`) with the non-existence of a minimal simple
group of odd order (`noMinimalSimpleOdd`).  The complete theorem is axiom-clean:
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. -/
theorem feitThompson {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    IsSolvable G :=
  feitThompson_of_noMinimalSimpleOdd (fun _ _ _ hG => noMinimalSimpleOdd hG) hodd

end OddOrder
