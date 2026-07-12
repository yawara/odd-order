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

end OddOrder.Peterfalvi.S15
