/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndT_Setup.SubcoherenceInputs

/-!
# The S↔T swap of the Peterfalvi (13.1) hypothesis

Peterfalvi proves the `(S, T)`-asymmetric §13 facts — (13.18), (13.19.c) — once, in the
`S`-orientation, and obtains the dual statements by re-instantiating the whole section with the
pair roles interchanged (in Coq this is the double application of `Thirteen_17_to_19`).  The
repo analogue is a **constructor** `Hypothesis.swap : Hypothesis → Hypothesis` exchanging
`S ↔ T`, `P ↔ Q`, `U ↔ V`, `C ↔ D`, `W₁ ↔ W₂`, `q ↔ p`, `u ↔ v`, `c ↔ d`, `μ ↔ ν`
(transposed), `δ ↔ δ'`, and transposing the `ω`/`η`-grids.  Every `∀ hyp`-theorem of the
`S`-side (13.18)/(13.19) layer (`betaGrid_support`, `gammaGrid_defGamma`,
`typeIBetaL_eta_row_constant`, `typeI_caseC_dichotomy`, …) then holds at `hyp.swap` with no
further proof, and the `T`-side obligations (`typeIBetaL_eta_col_constant`,
`typeI_caseC_dual_dichotomy`) are the transported `swap`-instances.

## The ν-side supply

The swap constructor's genuinely missing inputs are the `ν`-grid analogues of the `μ`-side
grounding fields (`mu_orthonormal`, `mu_diff_support`, …): the §4/§6 prime-TI facts for the
`T`-side certain-type grid.  These are bundled here as `NuGridSupplyData` with signatures that
**exactly mirror** the `μ`-fields under the role swap, so the producer discharge is the
mechanical `certainTypeT`-instance of the proven `muS_*` supply chain
(`FeitThompson.lean`: `muS_orthonormal` / `muS_diff_support` / `muS_apply_of_not_mem_W2` /
`muS_conj` via `hyp46SmpCore` — the `T`-instances use `mp.certainTypeT hG`, which is already
constructed with the factor roles swapped, `W₁ = K*`, `W₂ = K`).  Until that producer threading
lands (a-owned carrier files, coordinated via the shared-infra claim), the supply is the single
sorried producer `Hypothesis.nuGridSupply`.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The ν-side §4/§6 grid supply** (the (13.19)-dual pins): the `T`-side certain-type facts
for the `ν`-grid, mirroring the `μ`-side grounding fields of `Hypothesis` under the role swap
`S ↔ T`, `W₁ ↔ W₂`, `q ↔ p`, `δ ↔ δ'`.  Each field is the exact swap-image of the
corresponding `μ`-field, so `Hypothesis.swap` can consume them verbatim:

* `nu_irreducible`/`nu_row_injective`/`nu_orthonormal` ↔ `mu_irreducible`/`mu_col_injective`/
  `mu_orthonormal` — Peterfalvi (13.1.e)/(4.3.b) at `T`;
* `nu_degree_modEq_deltaPrime` ↔ `mu_degree_modEq_delta` — (4.3.d) at `T` (`Res_{W₂}` value
  identity, modulus `p = |W₂|`);
* `deltaPrime_zero_eq_one` ↔ `delta_zero_eq_one` — the (4.4) trivial-row anchor `ν_{00} = 1_T`;
* `nu_rowSum_eq_induce` ↔ `mu_colSum_eq_induce` — (4.5.a) at `T`;
* `nu_diff_support` ↔ `mu_diff_support` — (4.8) at `T` (Coq `prDade_sub_TIirr_on`), stated for
  any `TypePData T` reconciled to the abstract `V`/`W₂`/`W₁` (the swap's `Sdata` is the
  `reconciled_typePData_T` witness, which is exactly such a datum);
* `nu_apply_of_not_mem_W1` ↔ `mu_apply_of_not_mem_W2` — (4.3.c) at `T` (Coq `prTIirr_id`);
* `nu_conj` ↔ `mu_conj` — (4.9.a) at `T`;
* `V_commutative` ↔ `S_U_commutative` — (13.2.a) at `T` (BG Lemma 15.1(b) for the
  `(κ∪σ)'`-Hall complement of `T`). -/
structure NuGridSupplyData [Finite G] (hyp : Hypothesis (G := G)) : Prop where
  /-- **Peterfalvi (13.1.e) at `T`**: each `ν_{ij}` is an irreducible character of `T`. -/
  nu_irreducible : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (hyp.nu i j)
  /-- **Peterfalvi (13.1.e) at `T`, row distinctness**: within a row `i` the `ν_{ij}` are
  pairwise distinct. -/
  nu_row_injective : ∀ i : Fin hyp.q, Function.Injective (fun j : Fin hyp.p => hyp.nu i j)
  /-- **Peterfalvi (4.3.b) at `T`, full-grid orthonormality**:
  `⟨ν_{ij}, ν_{kl}⟩ = [(i,j) = (k,l)]`. -/
  nu_orthonormal : ∀ (i k : Fin hyp.q) (j l : Fin hyp.p),
    OddOrder.RepresentationTheory.ClassFunction.inner (hyp.nu i j) (hyp.nu k l)
      = if i = k ∧ j = l then 1 else 0
  /-- **Peterfalvi (4.3.d) at `T`**: the degree congruence `ν_{ij}(1) ≡ δ'_i (mod p)`. -/
  nu_degree_modEq_deltaPrime : ∀ (i : Fin hyp.q) (j : Fin hyp.p), ∃ a : ℤ,
    hyp.nu i j 1 = (hyp.deltaPrime i : ℂ) + (hyp.p : ℂ) * (a : ℂ)
  /-- **Peterfalvi (4.4), the `T`-side base sign**: `δ'_0 = 1` (`ν_{00} = 1_T`, the trivial
  row's anchor). -/
  deltaPrime_zero_eq_one : hyp.deltaPrime ⟨0, hyp.q_prime.pos⟩ = 1
  /-- **Peterfalvi (4.5.a) for the `T`-grid**: each `ν`-row sum is induced from an irreducible
  character of `T' = [T,T]`, nontrivial on `W₁` off the anchor row. -/
  nu_rowSum_eq_induce : ∀ i : Fin hyp.q,
    ∃ ψ : ClassFunction ↥((derivedInG hyp.T).subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ j : Fin hyp.p, hyp.nu i j)
        = ClassFunction.induce ((derivedInG hyp.T).subgroupOf hyp.T) ψ ∧
      (i ≠ ⟨0, hyp.q_prime.pos⟩ →
        ¬ (((hyp.W1.subgroupOf hyp.T).subgroupOf ((derivedInG hyp.T).subgroupOf hyp.T) :
            Set ↥((derivedInG hyp.T).subgroupOf hyp.T)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  /-- **Peterfalvi (9.8)/(9.11) reverse dichotomy at `T`** (issue 9092, the ν-side swap-image of
  `mu_reducible_dichotomy`): a reducible member of the `T`-side kernel-filter family `S(X)` over
  `T' = derivedInG T` is a nonzero `ν`-row sum `∑_j ν_{ij}`, `i ≠ 0`.  Under the swap `S ↔ T`,
  `μ ↔ νᵀ`, this is exactly the swapped instance's `mu_reducible_dichotomy` (the roles of row/column
  transpose), so `Hypothesis.swap` consumes it verbatim. -/
  nu_reducible_dichotomy : ∀ {X : Subgroup ↥hyp.T} {ψ : ClassFunction ↥hyp.T ℂ},
    ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG hyp.T).subgroupOf hyp.T) X →
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ →
    ∃ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ ∧ ψ = ∑ j : Fin hyp.p, hyp.nu i j
  /-- **Peterfalvi (4.8) at `T`, `ν`-row-difference support** (Coq `prDade_sub_TIirr_on`): for
  nontrivial equal-degree rows `i, k ≠ 0`, the difference `ν_{ij} − ν_{kj}` is supported in
  `A₀(T) = A(T) ∪ (V_T)^T`, for any `TypePData T` reconciled to the abstract `V`/`W₂`/`W₁`. -/
  nu_diff_support : ∀ (Tdata : TypePData hyp.T), Tdata.U = hyp.V → Tdata.W1 = hyp.W2 →
    Tdata.W2 = hyp.W1 → ∀ (j : Fin hyp.p) {i k : Fin hyp.q},
    i ≠ ⟨0, hyp.q_prime.pos⟩ → k ≠ ⟨0, hyp.q_prime.pos⟩ →
    hyp.nu i j 1 = hyp.nu k j 1 →
    (hyp.nu i j - hyp.nu k j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.T Tdata) hyp.T
  /-- **Peterfalvi (4.3.c) at `T`, value identity** (Coq `prTIirr_id`): on `W ∖ W₁` the
  `ν`-grid is the signed `ω`-grid, `ν_{ij}(w) = δ'_i·ω_{ij}(w)`. -/
  nu_apply_of_not_mem_W1 : ∀ (i : Fin hyp.q) (j : Fin hyp.p) (w : G) (hwW : w ∈ hyp.W)
    (hwT : w ∈ hyp.T), w ∉ (hyp.W1 : Set G) →
    hyp.nu i j ⟨w, hwT⟩ = (hyp.deltaPrime i : ℂ) * hyp.omega i j ⟨w, hwW⟩
  /-- **Peterfalvi (4.9.a) at `T`**: CF-level conjugation symmetry `ν̄_{ij} = ν_{−i,−j}`. -/
  nu_conj : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
    (hyp.nu i j).conj = hyp.nu (finNeg hyp.q_prime.pos i) (finNeg hyp.p_prime.pos j)
  /-- **Peterfalvi (13.2.a), V-side**: the complement `V` is abelian (BG Lemma 15.1(b) for the
  `(κ∪σ)'`-Hall complement of `T`). -/
  V_commutative : IsMulCommutative ↥hyp.V

/-- **The ν-side grid supply, producer obligation**: the `T`-side certain-type facts for the
abstract `ν`-grid.  Discharge route (issue 2038 iter 26): the FT-layer producer identifies
`hyp.nu` with the `certainTypeT` grid (`Section16CharacterData.nuT`, roles already swapped:
`W₁ = K*`, `W₂ = K`) and reads each field off the `T`-instance of the proven `muS_*` supply
chain — `nuT_orthonormal`/`nuT_diff_support` (via a `hyp46TmpCore` mirror at
`mp.certainTypeT hG`)/`nuT_apply_of_not_mem_W1`/`nuT_conj` — threaded through the carrier
structures like the `μ`-side (9081 pattern).  The carrier files are a-owned
(`FeitThompson{,Setup}.lean`), so the threading is a coordinated field addition with
constructor supply (precedent: the `S_U_commutative`/`Sdata_W2_eq` additions). -/
theorem Hypothesis.nuGridSupply [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : NuGridSupplyData hyp := sorry

open scoped FiniteInduce in
/-- **The S↔T swap of the (13.1) hypothesis** (the Coq re-instantiation of
`Thirteen_17_to_19` with the pair roles interchanged).  Exchanges `S ↔ T`, `P ↔ Q`, `U ↔ V`,
`C ↔ D`, `W₁ ↔ W₂`, `q ↔ p`, `u ↔ v`, `c ↔ d`, `Sset ↔ Tset`, `τ_S ↔ τ_T`, `δ ↔ δ'`,
`μ ↔ ν` and transposes the `ω`/`η`-grids.  Inputs:

* `hT2` — `IsTypeP2 T`, the (14.9)-conclusional dual of the carrier field `S_typeP2`
  (exactly the parameter `tauTbetaGrid`/`typeI_caseC_dual_dichotomy` already take);
* `Tdata` with the `reconciled_typePData_T` reconciliations — the swap's `Sdata`;
* `pins : NuGridSupplyData hyp` — the ν-side §4/§6 grid facts (the swap's `μ`-side fields).

Everything else is filled from `hyp`'s own fields: symmetric pairs exchange, the shared-`W`
facts commute (`inf_comm`/`sup_comm`/`Set.union_comm`), the S-side duals of the T-side
structural fields are read off `hyp.Sdata` (`fitting_inf_U_eq_bot` for `P ⊓ U = ⊥`,
`M_complement` for `S = S' ⋊ W₁`), and the transposed grid facts re-index (with the
column-axis Galois orbit supplying the transposed row-vanishing transport).

Every `∀ hyp`-theorem of the S-side (13.18)/(13.19) layer then holds at `hyp.swap …`,
giving the `T`-side duals (`typeIBetaL_eta_col_constant`, `typeI_caseC_dual_dichotomy`)
with no further proof beyond index transport. -/
noncomputable def Hypothesis.swap [Finite G] (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (pins : NuGridSupplyData hyp) : Hypothesis (G := G) where
  finiteG := hyp.finiteG
  S := hyp.T
  T := hyp.S
  W1 := hyp.W2
  W2 := hyp.W1
  W := hyp.W
  P := hyp.Q
  Q := hyp.P
  U := hyp.V
  V := hyp.U
  C := hyp.D
  D := hyp.C
  S_maximal := hyp.T_maximal
  T_maximal := hyp.S_maximal
  S_ne_T := hyp.S_ne_T.symm
  S_nonI := hyp.T_nonI
  T_nonI := hyp.S_nonI
  one_typeII := hyp.one_typeII.symm
  S_typeP2 := hT2
  theorem88_caseB := fun M hM => (hyp.theorem88_caseB M hM).imp_right Or.symm
  W_eq_inter := by rw [hyp.W_eq_inter, inf_comm]
  W_eq_join := by rw [hyp.W_eq_join, sup_comm]
  W1_inf_W2_eq_bot := by rw [inf_comm]; exact hyp.W1_inf_W2_eq_bot
  W1_commutes_W2 := fun x hx y hy => (hyp.W1_commutes_W2 y hy x hx).symm
  W_cyclic := hyp.W_cyclic
  P_eq_SF := hyp.Q_eq_TF
  Q_eq_TF := hyp.P_eq_SF
  S_deriv_eq_PU := hyp.T_deriv_eq_QV
  T_deriv_eq_QV := hyp.S_deriv_eq_PU
  Q_inf_V_eq_bot := by
    have h := hyp.Sdata.fitting_inf_U_eq_bot
    rwa [hyp.Sdata_U_eq, ← hyp.P_eq_SF] at h
  W2_isComplement_T_deriv := by
    have h := hyp.Sdata.M_complement
    rwa [hyp.Sdata_W1_eq] at h
  C_eq := hyp.D_eq
  D_eq := hyp.C_eq
  W1_normalizes_U := hyp.W2_normalizes_V
  W2_normalizes_V := hyp.W1_normalizes_U
  q := hyp.p
  p := hyp.q
  q_prime := hyp.p_prime
  p_prime := hyp.q_prime
  q_odd := hyp.p_odd
  p_odd := hyp.q_odd
  q_eq_card_W1 := hyp.p_eq_card_W2
  p_eq_card_W2 := hyp.q_eq_card_W1
  u := hyp.v
  v := hyp.u
  c := hyp.d
  d := hyp.c
  c_eq_card_C := hyp.d_eq_card_D
  d_eq_card_D := hyp.c_eq_card_C
  card_U_eq_uc := hyp.card_V_eq_vd
  card_V_eq_vd := hyp.card_U_eq_uc
  Sset := hyp.Tset
  Tset := hyp.Sset
  A0S := hyp.A0T
  A0T := hyp.A0S
  tauS := hyp.tauT
  tauT := hyp.tauS
  omega := fun i j => hyp.omega j i
  eta := fun i j => hyp.eta j i
  mu := fun i j => hyp.nu j i
  nu := fun i j => hyp.mu j i
  delta := hyp.deltaPrime
  deltaPrime := hyp.delta
  delta_pm_one := ⟨hyp.delta_pm_one.2, hyp.delta_pm_one.1⟩
  mu_degree_modEq_delta := fun i j => pins.nu_degree_modEq_deltaPrime j i
  delta_zero_eq_one := pins.deltaPrime_zero_eq_one
  tau3 := hyp.tau3
  eta_eq_tau_omega := fun i j => hyp.eta_eq_tau_omega j i
  mu_definition := fun i j => hyp.nu_definition j i
  mu_irreducible := fun i j => pins.nu_irreducible j i
  mu_col_injective := pins.nu_row_injective
  mu_orthonormal := fun i k j l => by
    rw [pins.nu_orthonormal j l i k]
    by_cases h : j = l ∧ i = k
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]
  mu_colSum_eq_induce := pins.nu_rowSum_eq_induce
  mu_reducible_dichotomy := pins.nu_reducible_dichotomy
  nu_definition := fun i j => hyp.mu_definition j i
  m := 1 - 1 / ((hyp.p : ℚ) - 1) - ((hyp.p : ℚ) - 1) / (hyp.p : ℚ) ^ hyp.q +
    1 / (((hyp.p : ℚ) - 1) * (hyp.p : ℚ) ^ hyp.q)
  m_eq := rfl
  Sdata := Tdata
  Sdata_U_eq := hU
  Sdata_W1_eq := hW1
  S_U_commutative := pins.V_commutative
  Sdata_W2_eq := hW2
  mu_diff_support := fun i _ _ hj hk hdeg =>
    pins.nu_diff_support Tdata hU hW1 hW2 i hj hk hdeg
  mu_apply_of_not_mem_W2 := fun i j w hwW hwS hw =>
    pins.nu_apply_of_not_mem_W1 j i w hwW hwS hw
  mu_conj := fun i j => pins.nu_conj j i
  eta_conj := fun i j => hyp.eta_conj j i
  tau3_isometry := hyp.tau3_isometry
  tau3_trivial := hyp.tau3_trivial
  tau3_apply_of_regular := fun α w hwW hnot =>
    hyp.tau3_apply_of_regular α w hwW (by rwa [Set.union_comm] at hnot)
  tau3_mem_ZIrr := hyp.tau3_mem_ZIrr
  omega_orthonormal := fun i k j l => by
    rw [hyp.omega_orthonormal j l i k]
    by_cases h : j = l ∧ i = k
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]
  omega_apply_one := fun i j => hyp.omega_apply_one j i
  omega_mem_ZIrr := fun i j => hyp.omega_mem_ZIrr j i
  omega_mul := fun i j w w' => hyp.omega_mul j i w w'
  omega_col_zero_apply_of_mem_W2 := fun i w hw =>
    hyp.omega_row_zero_apply_of_mem_W1 i w hw
  omega_row_zero_apply_of_mem_W1 := fun j w hw =>
    hyp.omega_col_zero_apply_of_mem_W2 j w hw
  omega_pow_q_of_mem_W1 := fun i j w hw => hyp.omega_pow_p_of_mem_W2 j i w hw
  omega_pow_p_of_mem_W2 := fun i j w hw => hyp.omega_pow_q_of_mem_W1 j i w hw
  eta_complete_vanish := fun χ horth w hwW hnot =>
    hyp.eta_complete_vanish χ (fun i j => horth j i) w hwW
      (by rwa [Set.union_comm] at hnot)
  eta_fourcorner_vanish := fun i j hi hj x hx => by
    rw [Set.union_comm] at hx
    have h := hyp.eta_fourcorner_vanish j i hj hi x hx
    linear_combination h
  eta_row_vanish_of_one_zero := fun x h0 i hi => by
    obtain ⟨u, hu⟩ := hyp.eta_column_galois_orbit i hi
    rw [← hu, ClassFunction.mapRingEquiv_apply, h0, map_zero]
  eta_row_galois_orbit := fun i hi => hyp.eta_column_galois_orbit i hi
  eta_column_galois_orbit := fun j hj => hyp.eta_row_galois_orbit j hj
  eta_intCast_of_coprime := fun g hg i j =>
    hyp.eta_intCast_of_coprime g (by rwa [Nat.mul_comm] at hg) j i
  eta_pair_of_coprime := fun g hg i j =>
    hyp.eta_pair_of_coprime g (by rwa [Nat.mul_comm] at hg) j i
  eta_principal_of_coprime := fun g hg =>
    hyp.eta_principal_of_coprime g (by rwa [Nat.mul_comm] at hg)

end OddOrder.Peterfalvi.S15
