/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S14_MaximalI
import OddOrder.Peterfalvi.S07_Subcoherent
import OddOrder.Peterfalvi.S10_CoherenceWiring
import OddOrder.Peterfalvi.S09_CertificateDischarge
import OddOrder.Isaacs.Ch06_FrobeniusActions.OddComplement
import OddOrder.GroupTheory.MaximalSubgroupTypeConj
import OddOrder.GroupTheory.WielandtFixedPoint
import OddOrder.Algebra.GaloisRationalInteger
import OddOrder.GroupTheory.TISubsetCounting
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Peterfalvi Section 15: The Subgroups S and T — setup and numerical analysis

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 15, pp. 75--82.

This section works under the case-(b) alternative of Theorem (8.8), whose
existence was forced in Section 14.  It fixes the two maximal subgroups `S` and
`T`, their common cyclic subgroup `W = W_1 W_2`, the Fitting kernels `P` and
`Q`, and the Dade character grids `omega`, `eta`, `mu`, and `nu`.

This file is the **first half** of Peterfalvi §15, covering the setup and the
character-theoretic / numerical blocks:

* (13.1)--(13.4): setup, type determination, and character degrees;
* (13.5)--(13.10): norm estimates and the analytic inequality;
* (13.11)--(13.15): the numerical contradiction giving `c = 1` and `u`.

The structural blocks (13.16)--(13.19) (normalizers, Frobenius structure, and
type-I interaction) live in `OddOrder.Peterfalvi.S15_SAndT`, which imports this
file.  The split keeps each file under the merge-monitor size threshold.

The character-grid identities (13.1.d,e) are materialized as genuine equalities
`η_{ij} = τ(ω_{ij})` and `Ind_W^{S/T}(ω_{ij} − ω) = ±(μ/ν - μ/ν)` over carried
`ℂ`-linear transfer maps `tau3`/`indWS`/`indWT`.  This forces the `η`/`μ`/`ν`
grids to be linear images of the `ω`-grid (a genuine, non-vacuous constraint);
pinning those maps to the concrete (3.2)/(4.3) constructions is the remaining
§3/§4 layer.
-/

namespace OddOrder.Peterfalvi.S15
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- Negation `i ↦ -i ≡ (n − i) (mod n)` on `Fin n`, for `0 < n`.  This is the index map
realizing the conjugation pairing `(i,j) ↦ (−i,−j)` of the Dade `η`-grid in Peterfalvi
(3.9.a)/(14.11.3).  Defined identically to the (downstream) `S16.finNeg`, so the two are
definitionally equal — the `(3.9.a)` field `eta_pair_of_coprime` below (stated with this
`finNeg`) is thus citeable to fill `S16.EtaGenericData.eta_pair` (stated with `S16.finNeg`). -/
def finNeg {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩

/- Scoped instances that make canonical `ClassFunction.induce` usable inside the
`(13.1)` hypothesis-structure field types (`Ind_W^S`, `Ind_W^T`).  Kept `scoped`
so the `noncomputable` `Fintype`/`Invertible` data is contained: it is opened only
for the `Hypothesis` structure (and for proofs that manipulate `mu_definition` /
`nu_definition`), never leaking globally. -/
namespace FiniteInduce

noncomputable scoped instance finiteSubFintype [Finite G] (H : Subgroup G) :
    Fintype ↥H := Fintype.ofFinite _

noncomputable scoped instance natCardInvC [Finite G] (H : Subgroup G) :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

noncomputable scoped instance ambientFintype [Finite G] : Fintype G :=
  Fintype.ofFinite _

noncomputable scoped instance ambientNatCardInvC [Finite G] :
    Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end FiniteInduce

/-! ## (13.1): the `S,T` hypothesis -/

open scoped FiniteInduce in
/-- **Peterfalvi (13.1)**: the main setup for the two maximal subgroups `S` and
`T` in case (b) of Theorem (8.8).

`G` is finite (carried as the instance field `finiteG`, so consumers need not
re-assume `[Finite G]`); this finiteness is what makes the canonical inductions
`Ind_W^S`/`Ind_W^T` in `mu_definition`/`nu_definition` well-defined. -/
structure Hypothesis where
  [finiteG : Finite G]
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  P : Subgroup G
  Q : Subgroup G
  U : Subgroup G
  V : Subgroup G
  C : Subgroup G
  D : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  /-- **Peterfalvi (13.2.a) type determination (S-side)**: `S` is of BG type `P₂` (Peterfalvi
  type II).  This is the §16 carrier datum (`Section16MaximalPair.S_typeP2`, fixed by the κ-Hall
  ordering `q < p`, threaded through `Section16Inputs`) that lets (13.2.a)'s "`S` is type II"
  be read off sorry-free via `isTypeII_of_isTypeP2`; it pins the determinate side of the otherwise
  disjunctive `one_typeII`. -/
  S_typeP2 : OddOrder.BG.Ch4.S14.IsTypeP2 S
  theorem88_caseB :
    ∀ M : Subgroup G, M ∈ maximalSubgroups G →
      IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨
        (∃ g : G, MulAut.conj g • M = T)
  W_eq_inter : W = S ⊓ T
  W_eq_join : W = W1 ⊔ W2
  W1_inf_W2_eq_bot : W1 ⊓ W2 = ⊥
  W1_commutes_W2 : ∀ x ∈ W1, ∀ y ∈ W2, Commute x y
  W_cyclic : IsCyclic ↥W
  P_eq_SF : P = maxNilpotentNormalHall S
  Q_eq_TF : Q = maxNilpotentNormalHall T
  S_deriv_eq_PU : derivedInG S = P ⊔ U
  T_deriv_eq_QV : derivedInG T = Q ⊔ V
  /-- **Peterfalvi (13.1.b)/(13.2), T-side complement disjointness**: `Q ⊓ V = ⊥`.  The κ-Hall
  invariant complement `V` to `Q = T_F` in `T'` genuinely *complements* `Q` — a fact available
  ungated at the §16 construction (`exists_kappaHall_invariant_complement_to_MF` returns
  `M_F ⊓ U = ⊥` from `T`'s type-`P` structure, i.e. from `T_nonI`, **not** requiring (14.9)/`IsTypeP2 T`),
  but dropped by the abstract `T_deriv_eq_QV` (`T' = Q ⊔ V`, which alone does not force disjointness).
  Threading it exposes the T-side linchpin used by every V-side coprimality/complement argument
  (`isMulCommutative_V`, `coprime_card_V_card_Q_of_disjoint`, …), previously routed circularly through
  the sorried `reconciled_typePData_T` (`Q_inf_V_eq_bot_of_reconciled`). -/
  Q_inf_V_eq_bot : Q ⊓ V = ⊥
  /-- **Peterfalvi (13.1.b), T-side semidirect complement `T = T' ⋊ W₂`**: the cyclic factor `W₂`
  complements the derived subgroup `T'` in `T`.  Available ungated at the §16 construction from
  `typeP_derivedInG_isComplement_kappaHall` (BG 14.7(h), via `T`'s type-`P` structure `T_nonI`,
  **not** (14.9)); the abstract Hypothesis otherwise omits it.  Discharges the `M_complement` field
  of `reconciled_typePData_T` and lets the ungated `coprime_card_Q_card_VW2` build honestly. -/
  W2_isComplement_T_deriv :
    Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)
  C_eq : C = U ⊓ Subgroup.centralizer (P : Set G)
  D_eq : D = V ⊓ Subgroup.centralizer (Q : Set G)
  W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)
  W2_normalizes_V : W2 ≤ Subgroup.normalizer (V : Set G)
  q : ℕ
  p : ℕ
  q_prime : q.Prime
  p_prime : p.Prime
  q_odd : Odd q
  p_odd : Odd p
  q_eq_card_W1 : q = Nat.card ↥W1
  p_eq_card_W2 : p = Nat.card ↥W2
  u : ℕ
  v : ℕ
  c : ℕ
  d : ℕ
  c_eq_card_C : c = Nat.card ↥C
  d_eq_card_D : d = Nat.card ↥D
  card_U_eq_uc : Nat.card ↥U = u * c
  card_V_eq_vd : Nat.card ↥V = v * d
  Sset : Set (ClassFunction ↥S ℂ)
  Tset : Set (ClassFunction ↥T ℂ)
  A0S : Set ↥S
  A0T : Set ↥T
  tauS : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥S G
  tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥T G
  omega : Fin q → Fin p → ClassFunction ↥W ℂ
  eta : Fin q → Fin p → ClassFunction G ℂ
  mu : Fin q → Fin p → ClassFunction ↥S ℂ
  nu : Fin q → Fin p → ClassFunction ↥T ℂ
  delta : Fin p → ℤ
  deltaPrime : Fin q → ℤ
  /-- **Peterfalvi (13.1.e)**: the signs `δ_j`, `δ'_i` are `±1` (the (4.3.b) `sign_eq`). -/
  delta_pm_one : (∀ j : Fin p, delta j = 1 ∨ delta j = -1) ∧
    (∀ i : Fin q, deltaPrime i = 1 ∨ deltaPrime i = -1)
  /-- **Peterfalvi (4.3.d)**: the degree congruence `μ_{ij}(1) ≡ δ_j (mod q)`
  (`μ_{ij}(1) = δ_j + q·a` for an integer `a`, the `Res_{W₁}` value identity). -/
  mu_degree_modEq_delta : ∀ (i : Fin q) (j : Fin p), ∃ a : ℤ,
    mu i j 1 = (delta j : ℂ) + (q : ℂ) * (a : ℂ)
  /-- **Peterfalvi (4.4), the `S`-side base sign**: `δ_0 = 1` (`μ_{00} = 1_S`, the trivial
  column's `σ`-anchor). -/
  delta_zero_eq_one : delta ⟨0, p_prime.pos⟩ = 1
  /-- The Peterfalvi (3.2)/(3.3) transfer map `τ`, typed as an integral
  (virtual-character) map via the same `IntegralCharacterMap` convention as
  `tauS`/`tauT` — faithful to `τ` being defined on the `ℤ`-lattice of virtual
  characters.  Pinning `tau3` to the *concrete* (3.2) Dade isometry (built from a
  `S05.TICyclicHypothesis` for `W` through `S04.dadeIntegralCharacterMap`, with the
  `ω`-grid materialized as the (3.3) characters) is a dedicated §3/§5 construction;
  `eta_eq_tau_omega` already forces the `η`-grid to be the integral-linear image of
  the `ω`-grid. -/
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥W G
  /-- **Peterfalvi (13.1.d)**: `η_{ij} = ω_{ij}^τ`. -/
  eta_eq_tau_omega : ∀ (i : Fin q) (j : Fin p), eta i j = tau3 (omega i j)
  /-- **Peterfalvi (13.1.e)**: `Ind_W^S (ω_{ij} − ω_{0j}) = δ_j (μ_{ij} − μ_{0j})`,
  where the induction is the canonical `Ind_W^S = ClassFunction.induce (W.subgroupOf S)`
  (transporting the `W`-grid into `S` via `W ≤ S`) and `δ_j = ±1` is `delta`. -/
  mu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, q_prime.pos⟩ j)
  /-- **Peterfalvi (13.1.e), irreducibility**: each `μ_{ij}` is an irreducible character of `S`
  (the (1.4)/(4.3.b) column families consist of irreducibles; threaded from the
  `SignedIrreducibleDifferenceFamily` producer, issue 2035 μ-linkage). -/
  mu_irreducible : ∀ (i : Fin q) (j : Fin p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (mu i j)
  /-- **Peterfalvi (13.1.e), column distinctness**: within a column `j` the `μ_{ij}` are
  pairwise distinct (the (1.4) family `injective` field).  Makes the column sums
  `μ_j = ∑_i μ_{ij}` sums of `q ≥ 2` distinct irreducibles — hence reducible, the (13.3.a)
  entry condition. -/
  mu_col_injective : ∀ j : Fin p, Function.Injective (fun i : Fin q => mu i j)
  /-- **Peterfalvi (4.5.a) for the `S`-grid** (issue 2035 μ-linkage): each `μ`-column sum is
  induced from an irreducible character of `S' = [S,S]` — the §4 certain-type identity
  `μ_j = Ind_{S'}^S χ_j` (`induce_restrict_certainType_eq`), the constructive membership
  shape behind (13.3.a)'s `μ_j ∈ 𝒮(H₀)`. -/
  mu_colSum_eq_induce : ∀ j : Fin p,
    ∃ ψ : ClassFunction ↥((derivedInG S).subgroupOf S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ i : Fin q, mu i j) = ClassFunction.induce ((derivedInG S).subgroupOf S) ψ ∧
      (j ≠ ⟨0, p_prime.pos⟩ →
        ¬ (((W2.subgroupOf S).subgroupOf ((derivedInG S).subgroupOf S) :
            Set ↥((derivedInG S).subgroupOf S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  /-- **Peterfalvi (13.1.e)**: `Ind_W^T (ω_{ij} − ω_{i0}) = δ'_i (ν_{ij} − ν_{i0})`,
  with the canonical `Ind_W^T = ClassFunction.induce (W.subgroupOf T)` and
  `δ'_i = ±1` is `deltaPrime`. -/
  nu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, p_prime.pos⟩)
  m : ℚ
  m_eq : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
    1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)
  /-- **Peterfalvi (13.1.b) carrier (S-side)**: the type-`P` structure data of `S`
  (`S = (P ⋊ U) ⋊ W₁`), with its complement `U` and cyclic factor `W₁` reconciled to the
  hypothesis's `U`/`W1` (`Sdata_U_eq`/`Sdata_W1_eq`).  This is the §16-construction witness
  (`Section16TypePStructure.Sdata`, built from `mp.S_typeP2` = Pf (13.2.a)) that pins the otherwise
  unconstrained relationship between the abstract `Hypothesis` fields `U`/`W1`/`P` and the intrinsic
  type-`P` decomposition of `S`.  It supplies the U-side structural facts (`U` complements
  `M_F = P`, `W₁ ≤ N_G(U)`, `U` nilpotent) that Peterfalvi §15 reads off `S`. -/
  Sdata : TypePData S
  Sdata_U_eq : Sdata.U = U
  Sdata_W1_eq : Sdata.W1 = W1
  /-- **Peterfalvi (13.2.a), U-side**: the complement `U` is abelian.  Supplied at construction from
  BG Lemma 15.1(b) (`typeP_hall_derived_eq_and_abelian`, with `U` the `(κ∪σ)'`-Hall of `S`), so §15
  need not re-derive it; discharges the `U_commutative` field of `basic_structure_gated`. -/
  S_U_commutative : IsMulCommutative ↥U
  /-- **Reconciliation (W₂-side)**: the intrinsic dual factor `Sdata.W2 = C_{S'}(W₁#)` equals the
  abstract `W₂` (complement of `W₁` in the cyclic `W = S ∩ T`).  Supplied at construction as
  `Sdata.W2 = K*` (`typePData_of_kappaHall_hallComplement_W2`); discharges `card_P_eq` and hence
  `basic_structure_gated.P_order` (issue 3001/4014). -/
  Sdata_W2_eq : Sdata.W2 = W2
  /- ### Grid property fields (issue 3002)

  The (3.2)/(3.3)/(3.4) character-theoretic content of the Dade grid carriers `tau3`/`omega`,
  which the §15 norm cascade ((13.5)–(13.10)) consumes.  All are supplied at construction from
  the honest spine grid (`Section16CharacterData.omegaS`/`tau3W` in `FeitThompson.lean`):
  ω-orthonormality via `S05.TICyclicHypothesis.omega_inner`, the τ₃ facts via the (3.2)
  σ-isometry package (`S05.TICyclicHypothesis.sigmaIntegral_*`). -/
  /-- **Peterfalvi (3.2), isometry part**: `τ₃` preserves the class-function inner product. -/
  tau3_isometry : OddOrder.Peterfalvi.S07.IsIntegralIsometry tau3
  /-- **Peterfalvi (3.2)**: `τ₃` sends the trivial character to the trivial character. -/
  tau3_trivial : tau3 (trivialClassFunction ↥W) = trivialClassFunction G
  /-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `τ₃` is the
  identity: `(α^{τ₃})(w) = α(w)` for regular `w`. -/
  tau3_apply_of_regular : ∀ (α : ClassFunction ↥W ℂ) (w : G) (hwW : w ∈ W),
    w ∉ (W1 : Set G) ∪ (W2 : Set G) → tau3 α w = α ⟨w, hwW⟩
  /-- **Peterfalvi (3.2)**: `τ₃` sends virtual characters to virtual characters. -/
  tau3_mem_ZIrr : ∀ z ∈ ZIrr ↥W, tau3 z ∈ ZIrr G
  /-- **Peterfalvi (3.3)/(3.4)**: the `ω`-grid is orthonormal. -/
  omega_orthonormal : ∀ (i k : Fin q) (j l : Fin p),
    ClassFunction.inner (omega i j) (omega k l) = if i = k ∧ j = l then 1 else 0
  /-- The `ω_{ij}` are linear characters: `ω_{ij}(1) = 1`. -/
  omega_apply_one : ∀ (i : Fin q) (j : Fin p), omega i j 1 = 1
  /-- Each `ω_{ij}` is a virtual character (in fact an irreducible character of `W`). -/
  omega_mem_ZIrr : ∀ (i : Fin q) (j : Fin p), omega i j ∈ ZIrr ↥W
  /-- **Peterfalvi (3.3)** (issue 2033): each `ω_{ij}` is multiplicative — a linear character. -/
  omega_mul : ∀ (i : Fin q) (j : Fin p) (w w' : ↥W),
    omega i j (w * w') = omega i j w * omega i j w'
  /-- **Peterfalvi (3.3)** (issue 2033): the column-`0` characters `ω_{i0}` are trivial on `W₂`. -/
  omega_col_zero_apply_of_mem_W2 : ∀ (i : Fin q) (w : ↥W), (w : G) ∈ W2 →
    omega i ⟨0, p_prime.pos⟩ w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): the row-`0` characters `ω_{0j}` are trivial on `W₁`. -/
  omega_row_zero_apply_of_mem_W1 : ∀ (j : Fin p) (w : ↥W), (w : G) ∈ W1 →
    omega ⟨0, q_prime.pos⟩ j w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₁` the grid values are `q`-th roots of unity. -/
  omega_pow_q_of_mem_W1 : ∀ (i : Fin q) (j : Fin p) (w : ↥W), (w : G) ∈ W1 →
    omega i j w ^ q = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₂` the grid values are `p`-th roots of unity. -/
  omega_pow_p_of_mem_W2 : ∀ (i : Fin q) (j : Fin p) (w : ↥W), (w : G) ∈ W2 →
    omega i j w ^ p = 1
  /-- **Peterfalvi (3.2.d)** (issue 2034): a class function of `G` orthogonal to the whole
  `τ₃ω`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — the grid enumerates the
  `σ`-image, and every irreducible off the image vanishes on `Ŵ`. -/
  eta_complete_vanish : ∀ χ : ClassFunction G ℂ,
    (∀ (i : Fin q) (j : Fin p), ClassFunction.inner (tau3 (omega i j)) χ = 0) →
    ∀ w : G, w ∈ W → w ∉ (W1 : Set G) ∪ (W2 : Set G) → χ w = 0
  /-- **Peterfalvi (3.4)/(3.5), the four-corner vanishing** (issue 2036): off the conjugacy
  saturation of the regular set `Ŵ = W ∖ (W₁ ∪ W₂)`, the `(3.5)` relation collapses to
  `1 − (τ₃ω)_{i0}(x) − (τ₃ω)_{0j}(x) + (τ₃ω)_{ij}(x) = 0` for nonzero row/column indices. -/
  eta_fourcorner_vanish : ∀ (i : Fin q) (j : Fin p), i ≠ ⟨0, q_prime.pos⟩ →
    j ≠ ⟨0, p_prime.pos⟩ → ∀ x : G,
    x ∉ OddOrder.GroupTheory.conjClassSet ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) →
    (1 : ℂ) - tau3 (omega i ⟨0, p_prime.pos⟩) x - tau3 (omega ⟨0, q_prime.pos⟩ j) x
      + tau3 (omega i j) x = 0
  /-- **Peterfalvi (3.9.b), row-vanishing transport** (issue 2036): if `(τ₃ω)₁₀` vanishes at
  `x`, so do all `(τ₃ω)_{i0}` with `i ≠ 0` — the nontrivial row characters are Galois-conjugate
  powers of `ω₁₀`, and the twist fixes the vanishing value. -/
  eta_row_vanish_of_one_zero : ∀ x : G,
    tau3 (omega ⟨1, q_prime.one_lt⟩ ⟨0, p_prime.pos⟩) x = 0 →
    ∀ i : Fin q, i ≠ ⟨0, q_prime.pos⟩ → tau3 (omega i ⟨0, p_prime.pos⟩) x = 0
  /-- **Peterfalvi (3.9.c), the `η`-grid integrality on generic elements** (issue-3002
  keystone): for `g` of order prime to `pq`, each grid value `η_{ij}(g) = (τ₃ω)_{ij}(g)` is a
  rational integer.  The genuine §3/§5 Dade-Galois fact (`σ` intertwines the cyclotomic Galois
  action, so a value at `g` of order prime to the character order `|ξ_{ij}| ∣ pq` is fixed by
  every ring automorphism of `ℂ`, hence rational; a rational algebraic integer is an integer).
  Supplied from the honest spine grid (`Section16CharacterData.omegaS`/`tau3W`, whose value is
  `σ(ω(ξ_{ij}))(g)`) through `S05.exists_intCast_sigma_omega_apply`.  The c-side (`S16`) cites
  this after `MHypothesis.G0_orderOf_coprime` to fill `EtaGenericData.eta_int`. -/
  eta_intCast_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    ∀ (i : Fin q) (j : Fin p), ∃ m : ℤ, eta i j g = (m : ℂ)
  /-- **Peterfalvi (3.9.a), the conjugate-pair symmetry of the `η`-grid on generic elements**
  (issue-3002 keystone): for `g` of order prime to `pq`, the grid pairs under the index
  negation `(i,j) ↦ (−i,−j)` (`finNeg`), `η_{−i,−j}(g) = η_{ij}(g)`.  Peterfalvi's (3.9.a):
  the complex conjugate of `η_{ij}` is the grid character at the conjugate index, and the value at
  `g` (a rational integer by (3.9.c), hence real) equals its conjugate.  Stated with
  `S15.finNeg` (defeq to `S16.finNeg`) so the c-side (`S16`) cites it to fill
  `EtaGenericData.eta_pair`. -/
  eta_pair_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    ∀ (i : Fin q) (j : Fin p),
      eta (finNeg q_prime.pos i) (finNeg p_prime.pos j) g = eta i j g
  /-- **Peterfalvi (3.9), the principal grid value on generic elements** (issue-3002 keystone):
  for `g` of order prime to `pq` (in fact for every `g`), the principal entry is `η₀₀(g) = 1`.
  Since `ω₀₀ = 1_W` is the trivial character and `τ₃(1_W) = 1_G` (`tau3_trivial`), the value
  is `1`.  The c-side (`S16`) cites this to fill `EtaGenericData.eta_principal`. -/
  eta_principal_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    eta ⟨0, q_prime.pos⟩ ⟨0, p_prime.pos⟩ g = 1

namespace Hypothesis

/-- Peterfalvi's `H = P C` in (13.5)--(13.10). -/
def H (hyp : Hypothesis (G := G)) : Subgroup G :=
  hyp.P ⊔ hyp.C

/-- Peterfalvi's `K = Q D`, used symmetrically for `T`. -/
def K (hyp : Hypothesis (G := G)) : Subgroup G :=
  hyp.Q ⊔ hyp.D

/-- `H = PC ≤ S`: `P = S_F ≤ S` and `C = U ∩ C_G(P) ≤ U ≤ S' ≤ S`. -/
theorem H_le_S [Finite G] (hyp : Hypothesis (G := G)) : hyp.H ≤ hyp.S := by
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  show hyp.P ⊔ hyp.C ≤ hyp.S
  refine sup_le ?_ ?_
  · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  · rw [hyp.C_eq]; exact le_trans inf_le_left hUS

/-- The generic set `G_0 = G# - ((H#)^G union (Q#)^G)` from (13.9). -/
def G0 (hyp : Hypothesis (G := G)) : Set G :=
  sharpSubgroup (⊤ : Subgroup G) \
    (conjClassSet (sharpSubgroup hyp.H) ∪
      conjClassSet (sharpSubgroup hyp.Q))


/-- Under **Peterfalvi (13.1)**, the prime `q` is odd, hence not `2`. -/
theorem q_ne_two (hyp : Hypothesis (G := G)) : hyp.q ≠ 2 := by
  intro hq2
  have hodd : Odd 2 := by simpa [hq2] using hyp.q_odd
  rcases hodd with ⟨k, hk⟩
  omega

/-- Under **Peterfalvi (13.1)**, the prime `p` is odd, hence not `2`. -/
theorem p_ne_two (hyp : Hypothesis (G := G)) : hyp.p ≠ 2 := by
  intro hp2
  have hodd : Odd 2 := by simpa [hp2] using hyp.p_odd
  rcases hodd with ⟨k, hk⟩
  omega

/-- Under **Peterfalvi (13.1)**, `q` is at least `3`. -/
theorem three_le_q (hyp : Hypothesis (G := G)) : 3 ≤ hyp.q := by
  have htwo : 2 ≤ hyp.q := hyp.q_prime.two_le
  have hne : hyp.q ≠ 2 := hyp.q_ne_two
  omega

/-- Under **Peterfalvi (13.1)**, `p` is at least `3`. -/
theorem three_le_p (hyp : Hypothesis (G := G)) : 3 ≤ hyp.p := by
  have htwo : 2 ≤ hyp.p := hyp.p_prime.two_le
  have hne : hyp.p ≠ 2 := hyp.p_ne_two
  omega
end Hypothesis

/-! ## (13.2): basic structure -/

/-- Carrier for the basic structural conclusions of Peterfalvi (13.2). -/
structure BasicStructureData (hyp : Hypothesis (G := G)) where
  S_typeII_or_typeIII : IsTypeII hyp.S ∨ IsTypeIII hyp.S
  q_lt_p_forces_typeII : hyp.q < hyp.p → IsTypeII hyp.S
  U_commutative : IsMulCommutative ↥hyp.U
  UW1_frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥(hyp.U ⊔ hyp.W1) (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
      (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1))
  P_elementaryAbelian : IsElementaryAbelian hyp.p ↥hyp.P
  P_order : Nat.card ↥hyp.P = hyp.p ^ hyp.q
  u_bound : hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1)
  A0S_TI : Prop
  A0S_TI_holds : A0S_TI
  tauS_eq_induction : Prop
  tauS_eq_induction_holds : tauS_eq_induction

/-- **Peterfalvi (13.2.b,c,e) — the `M_F`-structure residual** (faithful obligation, §16-gated).

The genuinely §16-structural half of (13.2): the Fitting kernel `P = S_F` is elementary abelian of
order `p^q` (13.2.b,c), the complement `U` is abelian (13.2.a), `u ≤ (p^q − 1)/(p − 1)` (13.2.e),
and `A_0(S)` is a TI-subset (13.2.e).

Unlike the *type determination* and the `U W₁` *Frobenius structure* of (13.2.a) — both now read off
sorry-free from the carrier (`isTypeII_of_isTypeP2`, `typeP_uW1_frobenius` on `Sdata`) — these are
the σ-structure facts of the type-`P₂` member `S`: `M_σ = M_F` is the elementary-abelian `p`-group of
rank `q` on which the prime-order `κ`-Hall factor `W₁` acts (BG §10/§14 σ-theory), giving the
`u`-bound from the count of `W₁`-orbits.  No repo theorem yet states "`M_σ` elementary abelian of
order `p^q`"; declared here as the localized faithful gate (the
`card_Q_eq`/`coprime_card_U_card_P_of_disjoint` pattern) so that `basic_structure`'s assembly — its
honest type determination and Frobenius structure — are `sorry`-free. -/
structure BasicStructureGated (hyp : Hypothesis (G := G)) where
  U_commutative : IsMulCommutative ↥hyp.U
  P_elementaryAbelian : IsElementaryAbelian hyp.p ↥hyp.P
  P_order : Nat.card ↥hyp.P = hyp.p ^ hyp.q
  u_bound : hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1)
  A0S_TI : Prop
  A0S_TI_holds : A0S_TI
  tauS_eq_induction : Prop
  tauS_eq_induction_holds : tauS_eq_induction

/-- **The §9 type-II setup on `S`** (Peterfalvi (13.2.a) → (9.2)): the `TypesIIIIIIVSetup`
carrier for `S`, from the κ-Hall type-P₂ witness.  `maximal`/`typeP` are the carried
`S_maximal`/`Sdata`; the nontrivial core is witness-independent (`U ≠ ⊥` via the canonical index
`[S' : S_F]`, `|W₁| = q` prime, and the `A₀`-TI clause depends only on `S`); `type_alt` is
type II (`isTypeII_of_isTypeP2`).  Note the §9 machinery's `H` is `Sdata.H = S_F = P`, so the
§9 inertia subgroup `HC` is `PC = hyp.H` — the (13.3.a) `Ind_{PC}(linear)` shape.  Opens the §9
Clifford/degree machinery ((9.7)–(9.9), the `hcPsi`-induction analysis) on `S`. -/
noncomputable def Hypothesis.toTypesIIIIIIVSetupS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup hyp.S := by
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  have tdata : TypeIIData hyp.S := hSII.some
  have hUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hW1prime : (Nat.card ↥hyp.Sdata.W1).Prime := by
    rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]; exact hyp.q_prime
  exact { maximal := hyp.S_maximal
          typeP := hyp.Sdata
          nontrivial := ⟨hUne, hW1prime, tdata.common.2.2⟩
          type_alt := Or.inl hSII }

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **§9 character data on `S`** (S12-mk mirror; degree-only placeholders): `u = |Ū|` is
rfl-pinned to the `U`-action image; `tau := hyp.tauS`, `H0CprimeSupport := ∅` and
`quotientSemidirectFrobenius := True` are the documented count/degree-only placeholders (as in
`S12.Hypothesis.mkSection11CharacterData` — NOT for (9.11)-coherence consumption; the honest
support/tau construction is issue 2035 step 1b).  Opens `caseB_degree_qu`, the (9.9) counts and
the (9.9.c) `hcPsi`-induction exhaustion on `S` for the (13.3) μ-column facts. -/
noncomputable def Hypothesis.mkSection11CharacterDataS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      ((hyp.toTypesIIIIIIVSetupS hG).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)).subtype).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := ∅
  tau := hyp.tauS
  quotientSemidirectFrobenius := True

open scoped FiniteInduce in
/-- **`Ind_S^G` as a `ℂ`-linear map** `CF(S) →ₗ[ℂ] CF(G)` (issue 2035 step 1).  The
canonical class-function induction `ClassFunction.induce hyp.S`, bundled as a linear map;
linearity is `ClassFunction.induce_add` / `ClassFunction.induce_smul`.  This is the concrete
Peterfalvi (13.2.e)/(7.2) Dade isometry `τ = Ind_S^G` (the `(S, H^#)` isometry coincides with
induction), used as the honest `tau` of the §9 character data on `S`. -/
noncomputable def Hypothesis.indSLinearC [Finite G] (hyp : Hypothesis (G := G)) :
    ClassFunction ↥hyp.S ℂ →ₗ[ℂ] ClassFunction G ℂ where
  toFun := ClassFunction.induce hyp.S
  map_add' := ClassFunction.induce_add hyp.S
  map_smul' c θ := ClassFunction.induce_smul hyp.S c θ

open scoped FiniteInduce in
@[simp] theorem Hypothesis.indSLinearC_apply [Finite G] (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥hyp.S ℂ) :
    hyp.indSLinearC θ = ClassFunction.induce hyp.S θ := rfl

open scoped FiniteInduce in
/-- **`Ind_S^G` as an `IntegralCharacterMap ↥S G`** (issue 2035 step 1): the `ℤ`-linear
`Ind_S^G`, obtained by restricting scalars of the `ℂ`-linear `indSLinearC`.  This is the honest
`τ` value the §9 coherence (`coherent_H0C_commutator`) consumes for the (13.3) `S`-instance —
Peterfalvi's `τ = Ind_S^G` (13.2.e). -/
noncomputable def Hypothesis.indS [Finite G] (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G :=
  (hyp.indSLinearC).restrictScalars ℤ

open scoped FiniteInduce in
@[simp] theorem Hypothesis.indS_apply [Finite G] (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥hyp.S ℂ) :
    hyp.indS θ = ClassFunction.induce hyp.S θ := rfl

/-- **`C' = [C, C]` as a subgroup** (Peterfalvi (9.5), `S`-instance): the derived subgroup of
`C = C_U(P)`.  Definitionally matches the §9 `cprimeSub` (`= derivedInG (cSub …)`) once the
`S`-instance kernel `cSub = C` identification (`toTypesIIIIIIVSetupS_cSub_eq_C`) is applied. -/
def Hypothesis.Cprime (hyp : Hypothesis (G := G)) : Subgroup G := derivedInG hyp.C

/-! ### (13.2.e) The honest type-`P₂` Dade support `A(S)` and its (2.2) hypothesis

Peterfalvi (8.10) defines the type-`P` support as `A(M) = ⋃_{x∈M_σ^#} C_{M'}(x)^#`, indexed over
the **core** `M_σ^#`.  For the type-`P₂` maximal `S` this is `A(S) = centralizerSupport (M_σ^#) S'`
— the nonidentity elements of `S' = [S,S]` centralizing some nonidentity element of `S_σ = S_F`.
This is the honest (13.2.e) Dade-support set; the earlier `typePA = (S')^#` over-claim (issue 9008)
included the Frobenius-complement points `U^#` (`C_{S_σ} = 1`), which is false-as-stated for `P₂`.

Following 9008 Option A, `A(S)` reduces to the type-I `ASet` bridge: `A(S) ⊆ ASet S U₀` for a matched
`(κ∪σ)'`-Hall `U₀` (`typeP2_exists_matched_kappa_hall_pair`), since `S' = U₀ ⊔ S_σ`
(`typeP_hall_derived_eq_and_abelian`) and every `A(S)`-point centralizes a nonidentity `S_σ`-element
(so lies in `\widehat{S_σ}`).  The three (8.13) obligations then flow through the type-agnostic BG
Theorem-II machinery, exactly as in the type-I `dadeSupportHypotheses_typeI` assembly. -/

/-- **Peterfalvi (8.10), the honest type-`P₂` support `A(M) = ⋃_{x∈M_σ^#} C_{M'}(x)^#`.**  The
nonidentity elements of the derived subgroup `M' = derivedInG M` centralizing some nonidentity
element of `M_σ`.  This is the correct type-`P₂` `A(M)` (issue 9008), strictly smaller than the
`typePA = (M')^#` over-claim (it excludes the Frobenius-complement points `U^#`). -/
def honestTypeP2ASet (M : Subgroup G) : Set G :=
  OddOrder.GroupTheory.centralizerSupport
    (OddOrder.GroupTheory.sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)) (derivedInG M)

@[simp] theorem mem_honestTypeP2ASet {M : Subgroup G} {y : G} :
    y ∈ honestTypeP2ASet M ↔
      y ∈ derivedInG M ∧ y ≠ 1 ∧
        ∃ x ∈ OddOrder.GroupTheory.sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M),
          y ∈ Subgroup.centralizer ({x} : Set G) :=
  Iff.rfl

/-- Every element of `A(S)` is a nonidentity element of `G`. -/
theorem honestTypeP2ASet_subset_sharp {M : Subgroup G} :
    honestTypeP2ASet M ⊆ OddOrder.Peterfalvi.S04.sharp (Set.univ : Set G) := by
  rintro y ⟨-, hy1, -⟩
  exact OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ y, hy1⟩

/-- **`1 ∉ A(S)`**: the honest support consists of non-identity elements (it lies in
`sharp univ`, `honestTypeP2ASet_subset_sharp`).  This is the `h1notA` input the Dade-coherence
producer `S07.coherentEqualDegree_fromDade` requires (`1 ∉ A` guarantees the induced difference
`τ(χ_j − χ_0)` sees the whole Dade support). -/
theorem honestTypeP2ASet_one_not_mem {M : Subgroup G} : (1 : G) ∉ honestTypeP2ASet M := fun h =>
  (OddOrder.Peterfalvi.S04.mem_sharp.mp (honestTypeP2ASet_subset_sharp h)).2 rfl

/-- `A(S) ⊆ M'` (the support lives in the derived subgroup). -/
theorem honestTypeP2ASet_subset_derived {M : Subgroup G} :
    honestTypeP2ASet M ⊆ (derivedInG M : Set G) := fun _ hy => hy.1

/-- `A(S) ⊆ M`. -/
theorem honestTypeP2ASet_subset {M : Subgroup G} :
    honestTypeP2ASet M ⊆ (M : Set G) := fun _ hy =>
  Subgroup.map_subtype_le _ hy.1

/-- **`A(S)` is `M`-conjugation invariant.**  Both `M_σ` (`Msigma`) and `M' = derivedInG M` are
`M`-normal, so conjugating `y ∈ A(S)` and its centralized `M_σ`-witness by `m ∈ M` stays in `A(S)`. -/
theorem honestTypeP2ASet_conj_mem [Finite G] {M : Subgroup G} {m : G} (hm : m ∈ M) {y : G}
    (hy : y ∈ honestTypeP2ASet M) : m * y * m⁻¹ ∈ honestTypeP2ASet M := by
  obtain ⟨hyM', hy1, x, hxσ, hyC⟩ := hy
  have hmM' : m ∈ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) :=
    OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm
  have hmMσ : m ∈ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hm
  refine ⟨?_, ?_, m * x * m⁻¹, ?_, ?_⟩
  · -- `m·y·m⁻¹ ∈ M'` since `m ∈ M ≤ N_G(M')`.
    exact (Subgroup.mem_normalizer_iff.mp hmM' y).mp hyM'
  · exact fun h => hy1 (by
      have hyeq : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [hyeq, h]; group)
  · exact OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem hmMσ hxσ
  · -- `m·y·m⁻¹` centralizes `m·x·m⁻¹`.
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    calc m * y * m⁻¹ * (m * x * m⁻¹)
        = m * (y * x) * m⁻¹ := by group
      _ = m * (x * y) * m⁻¹ := by rw [hyC]
      _ = m * x * m⁻¹ * (m * y * m⁻¹) := by group

/-- **`A(S) ⊆ hatMsigma S`** (BG Theorem-E notation): every `A(S)`-point centralizes a nonidentity
`M_σ`-element, so `M_σ ⊓ C_G(y) ≠ ⊥`, and lies in `M' ≤ M`. -/
theorem honestTypeP2ASet_subset_hatMsigma [Finite G] {M : Subgroup G} :
    honestTypeP2ASet M ⊆ OddOrder.BG.Ch4.S16.hatMsigma M := by
  rintro y ⟨hyM', -, x, hxσ, hyC⟩
  obtain ⟨hxMσ, hx1⟩ := (Set.mem_diff _).mp hxσ
  refine ⟨Subgroup.map_subtype_le _ hyM', ?_⟩
  -- `x ∈ M_σ ⊓ C_G(y)` is a nonidentity witness (`y ∈ C_G(x) ↔ x ∈ C_G(y)`).
  intro hbot
  have hxCy : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    exact hyC.symm
  have : x ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_inf.mpr ⟨SetLike.mem_coe.mp hxMσ, hxCy⟩
  rw [hbot] at this
  exact hx1 (Set.mem_singleton_iff.mpr (Subgroup.mem_bot.mp this))

/-- **The type-`P₂` `ASet` bridge (9008 Option A): `A(S) ⊆ ASet S U₀`** for a matched `(κ∪σ)'`-Hall
`U₀`.  Since `A(S) ⊆ M' = U₀ ⊔ M_σ` (`typeP_hall_derived_eq_and_abelian`, BG Lemma 15.1(b)) and
`A(S) ⊆ hatMsigma M` (each point centralizes a nonidentity `M_σ`-element), the definitional
`ASet M U₀ = hatMsigma M ∩ (U₀ ⊔ M_σ)` receives `A(S)`.  This is the reduction of the honest
type-`P₂` support to BG's type-agnostic Theorem-E set, feeding `theoremII_tame_embedding` and
`mem_sigmaSharp_of_mem_aSet_of_escape`. -/
theorem honestTypeP2ASet_subset_ASet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K₀ ≤ M) (hUM : U₀ ≤ M)
    (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M)) :
    honestTypeP2ASet M ⊆ OddOrder.BG.Ch4.S16.ASet M U₀ := by
  have hderiv : derivedInG M = U₀ ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
    (OddOrder.BG.Ch4.S15.typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  intro y hy
  refine ⟨honestTypeP2ASet_subset_hatMsigma hy, ?_⟩
  have hyM' : y ∈ derivedInG M := hy.1
  rw [hderiv] at hyM'
  exact hyM'

/-- **(8.13.b) for the type-`P₂` support: escaping `A(S)`-points are `σ`-sharp.**  An escaping point
of `A(S)` lies in `ASet S U₀` (`honestTypeP2ASet_subset_ASet`), so BG Theorem-II's `D ⊆ M_σ^#`
reduction (`mem_sigmaSharp_of_mem_aSet_of_escape`, type-agnostic) puts it in `M_σ^#`. -/
theorem escaping_honestTypeP2ASet_mem_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K₀ ≤ M) (hUM : U₀ ≤ M)
    (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (honestTypeP2ASet M)) :
    a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := by
  obtain ⟨haA, haesc⟩ := ha
  exact OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU (Or.inl rfl)
    (honestTypeP2ASet_subset_ASet hG hM hKM hUM hKne hK hU haA) haA.2.1 haesc

/-- **(8.13.c2) coprimality for the type-`P₂` support** (the `σ`-decomposition core, `P₂` form).  For
an escaping `a ∈ M_σ^#` and any `w ∈ A(S)`, no prime `p ∈ σ(N[a])` divides `|C_S(w)|`.  Mirrors the
type-I `escaping_sigma_disjoint_centralizer`: a common prime `p ∈ σ(N[a]) ∩ π(S)` fires
`non_disjoint_signalizer_frobenius`, making `S` Frobenius with kernel `S_σ`; the `A(S)`-point `w`
centralizes a nonidentity `S_σ`-element, so Frobenius-kernel absorption
(`IsFrobeniusGroup.centralizer_kernel_le`) gives `w ∈ S_σ`, whence the `σ`-generic
`escaping_sigmaSharp_disjoint_centralizer` closes the contradiction. -/
theorem coprime_FT_signalizer_centralizerIn_honestTypeP2ASet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {a : G} (haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (haesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M)
    {w : G} (hw : w ∈ honestTypeP2ASet M) :
    Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
      (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M w)) := by
  classical
  by_contra hnc
  obtain ⟨p, hpp, hpR, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  -- `p ∈ σ(N[a])` since `p ∣ |R(a)| ∣ |M_σ(N[a])|`.
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
    refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup (OddOrder.BG.Ch4.S16.FT_signalizerBase a) p
      (Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩)
    refine hpR.trans (Subgroup.card_dvd_of_le ?_)
    rw [OddOrder.BG.Ch4.S16.FT_signalizer]
    exact inf_le_left
  -- escape ⟹ `1 < |𝓜_σ(a)|`.
  have ha1 : a ≠ 1 := haσ.2
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard := by
    by_contra h
    exact haesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM haσ.1 ha1
      (not_lt.mp h))
  -- `p ∈ π(S)` (it divides `|C_S(w)| ∣ |S|`), so Lemma 14.13(a) fires.
  have hpS : p ∈ OddOrder.BG.Ch4.S14.piSet M := by
    refine Nat.mem_primeFactors.mpr ⟨hpp, hpC.trans ?_, Nat.card_pos.ne'⟩
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨-, -, Ufr, -, hfrobU⟩ :=
    OddOrder.BG.Ch4.S16.non_disjoint_signalizer_frobenius hG hM haσ hgt ⟨p, hpσ, hpS⟩
  -- Frobenius kernel absorption: a `w`-point centralizing a nonidentity `M_σ`-element lands in `M_σ`.
  have hker : ∀ {u v : G}, u ∈ M → v ∈ OddOrder.BG.Ch3.S10.Msigma M → v ≠ 1 →
      Commute u v → u ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    intro u v huM hvMσ hv1 hcomm
    have hvM : v ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hvMσ
    have hcent := OddOrder.Isaacs.Ch06.IsFrobeniusGroup.centralizer_kernel_le hfrobU
      (⟨v, hvM⟩ : ↥M) (Subgroup.mem_subgroupOf.mpr hvMσ)
      (fun h1 => hv1 (congrArg Subtype.val h1))
    have humem : (⟨u, huM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨v, hvM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hcomm.eq
    exact Subgroup.mem_subgroupOf.mp (hcent humem)
  -- `w ∈ M_σ`: `w ∈ A(S)` centralizes a nonidentity `M_σ`-element `x`.
  obtain ⟨hwM', hw1, x, hxσ, hwC⟩ := hw
  obtain ⟨hxMσ, hx1⟩ := (Set.mem_diff _).mp hxσ
  have hx1' : x ≠ 1 := fun he => hx1 (Set.mem_singleton_iff.mpr he)
  have hwM : w ∈ M := Subgroup.map_subtype_le _ hwM'
  have hwMσ : w ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    refine hker hwM (SetLike.mem_coe.mp hxMσ) hx1' ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hwC
    exact (Commute.symm (this : Commute w x)).symm
  exact OddOrder.Peterfalvi.S10.escaping_sigmaSharp_disjoint_centralizer hG hM haσ haesc hwMσ hw1
    hpp hpσ hpC

/-- **(8.13.a) for the type-`P₂` support: `G`-conjugate `A(S)`-points are `M`-conjugate.**  BG §16
Theorem II conjunct 1 (`theoremII_tame_embedding`, first conjunct), whose `X = ASet M U₀` branch
receives `A(S)` via `honestTypeP2ASet_subset_ASet`.  The matched κ-Hall / `(κ∪σ)'`-Hall inputs are
`K₀`/`U₀`. -/
theorem honestTypeP2ASet_isConj_conj_in_M [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K₀ ≤ M) (hUM : U₀ ≤ M)
    (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    {a b : G} (ha : a ∈ honestTypeP2ASet M) (hb : b ∈ honestTypeP2ASet M) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  have hII := OddOrder.BG.Ch4.S16.theoremII_tame_embedding hG hM hKM hUM hK hU
    (X := OddOrder.BG.Ch4.S16.ASet M U₀) (Or.inl rfl)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  obtain ⟨m, hmM, hmb⟩ := hII.1 a (honestTypeP2ASet_subset_ASet hG hM hKM hUM hKne hK hU ha)
    b (honestTypeP2ASet_subset_ASet hG hM hKM hUM hKne hK hU hb) ⟨g, hg.symm⟩
  exact ⟨m, hmM, hmb.symm⟩

/-- **Peterfalvi (8.15) for the type-`P₂` support `A(S)`: the Dade (2.2) support hypotheses hold.**
The honest (13.2.e) foundation.  Assembles the `σ`-decomposition-generic engine
(`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`) with the type-`P₂` pins obtained from the
matched κ-Hall / `(κ∪σ)'`-Hall pair (`typeP2_exists_matched_kappa_hall_pair`): escaping points are
`σ`-sharp (`escaping_honestTypeP2ASet_mem_sigmaSharp`, (8.13.b)), `G`-conjugacy is `M`-conjugacy
(`honestTypeP2ASet_isConj_conj_in_M`, (8.13.a)), and the coprimality
(`coprime_FT_signalizer_centralizerIn_honestTypeP2ASet`, (8.13.c2)), plus the set-facts (`A(S) ⊆ M`,
non-identity, nonempty, `M`-conjugation-invariant).

This is the honest type-`P₂` Dade support (issue 9008 Option A / issue 1017 update #9): its `.dade`
field is the `S04.Hypothesis G (A(S)) M` (the `τ = Ind_M^G` Dade isometry lives on `A(S)`), replacing
the likely-unsound `sibleyTarget_H0C` route for the (13.3) `S`-instance coherence. -/
theorem dadeSupportHypothesisData_honestTypeP2ASet [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 M) :
    Nonempty (OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M (honestTypeP2ASet M)) := by
  classical
  obtain ⟨K₀, U₀, hKM, hUM, hUne, hK, hU, -, -⟩ :=
    OddOrder.BG.Ch4.S16.typeP2_exists_matched_kappa_hall_pair hG hM hP2
  -- `K₀ ≠ ⊥` (else `κ(M)` is empty, contradicting type `P₂ ⟹ κ(M) ≠ ∅`).
  have hKne : K₀ ≠ ⊥ := by
    intro hK0bot
    obtain ⟨p, hp⟩ := (OddOrder.BG.Ch4.S14.isTypeP_of_isTypeP2 hP2)
    -- `p ∈ κ(M) ⊆ π(M) = primeFactors |M|` (a κ-prime has `pRank_M p = 1 > 0`).
    haveI : Fact p.Prime := ⟨OddOrder.BG.Ch4.S14.prime_of_mem_kappa hp⟩
    have hprk : 0 < pRank ↥M p := by
      rcases OddOrder.BG.Ch4.S14.kappa_subset_tau1_union_tau3 hp with hτ1 | hτ3
      · rw [((OddOrder.BG.Ch3.S12.mem_tau1_iff M p).mp hτ1).2.2]; norm_num
      · rw [((OddOrder.BG.Ch3.S12.mem_tau3_iff M p).mp hτ3).2.2]; norm_num
    have hppi : p ∈ (Nat.card ↥M).primeFactors :=
      OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank hprk
    obtain ⟨hpp, hpdvdM, hMne⟩ := Nat.mem_primeFactors.mp hppi
    -- `κ(M)`-Hall `K₀.subgroupOf M`: as `p ∈ κ(M)`, `p` avoids the index, so `p ∣ |K₀.subgroupOf M|`.
    have hcardMeq : Nat.card ↥(K₀.subgroupOf M) * (K₀.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    have hpKcard : p ∣ Nat.card ↥(K₀.subgroupOf M) := by
      rcases (hpp.dvd_mul.mp (hcardMeq ▸ hpdvdM)) with h | h
      · exact h
      · exact absurd hp (hK.2 p (Nat.mem_primeFactors.mpr
          ⟨hpp, h, Subgroup.index_ne_zero_of_finite⟩))
    -- but `K₀ = ⊥` makes `K₀.subgroupOf M = ⊥` of order `1`, which `p` cannot divide.
    rw [hK0bot, Subgroup.bot_subgroupOf, Subgroup.card_bot] at hpKcard
    exact hpp.one_lt.ne' (Nat.dvd_one.mp hpKcard)
  refine OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_of_subset_escaping_sigmaSharp hG hM
    honestTypeP2ASet_subset (fun x hx => hx.2.1)
    (fun a ha => escaping_honestTypeP2ASet_mem_sigmaSharp hG hM hKM hUM hKne hK hU ha)
    (fun a ha b hb hab => honestTypeP2ASet_isConj_conj_in_M hG hM hKM hUM hKne hK hU ha hb hab)
    (fun a ha b hb => coprime_FT_signalizer_centralizerIn_honestTypeP2ASet hG hM
      (escaping_honestTypeP2ASet_mem_sigmaSharp hG hM hKM hUM hKne hK hU ha) ha.2 hb)
    ?_ ?_
  · -- `A(S)` nonempty: `M_σ^# ⊆ A(S)` (a nonidentity `M_σ`-element centralizes itself).
    obtain ⟨a, ha1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haMσ : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := a.2
    have haM' : (a : G) ∈ derivedInG M := OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM haMσ
    refine ⟨a.1, haM', ha1', a.1, ?_, ?_⟩
    · exact (Set.mem_diff _).mpr ⟨SetLike.mem_coe.mpr haMσ, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · -- `M`-conjugation invariance.
    intro m x hm
    exact ⟨fun h => by
      have := honestTypeP2ASet_conj_mem (inv_mem hm) h
      rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at this,
      fun h => honestTypeP2ASet_conj_mem hm h⟩

/-- **(13.2.e) `S`-instance Dade hypothesis** (issue 1017 update #10, step 1): the `Hypothesis`-level
instantiation of `dadeSupportHypothesisData_honestTypeP2ASet` at the type-`P₂` maximal `S`
(via `hyp.S_maximal`/`hyp.S_typeP2`), packaging the honest §16 support
`A(S) = ⋃_{x∈S_σ#} C_{S'}(x)#` (`honestTypeP2ASet hyp.S`) as an `S04.Hypothesis`.  This is the concrete
`S04` Dade datum for `S` (previously only available as the standalone theorem taking `hM`/`hP2`); its
`.fullDadeIsometryData` (given the support's `HConjInvariant`) materialises the Dade isometry
`τ = Ind_S^G` on the `ℤ`-lattice of virtual characters — the (13.2.e) foundation the §9 subcoherence
assembly (`S07.irrSubcoherent`) consumes to re-ground `coherent_H0Cprime_S` off the unsound
`sibleyTarget_H0C`.  (Sorry-provenance parity with `dadeSupportHypothesisData_honestTypeP2ASet`: the
inherited shared BG §16 Theorem-II pins, at exact parity with the accepted on-path
`dadeSupportHypotheses_typeI`; no lane-`b` sorry introduced.) -/
noncomputable def Hypothesis.dadeHypS [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S04.Hypothesis G (honestTypeP2ASet hyp.S) hyp.S :=
  (dadeSupportHypothesisData_honestTypeP2ASet hG hyp.S_maximal hyp.S_typeP2).some.dade

/-- **(13.2.e) `S`-instance Dade `H`-conjugation invariance** (issue 1017): the `HConjInvariant` of
`dadeHypS`, carried by the underlying `DadeSupportHypothesisData` (Peterfalvi (8.14)/(8.15), the
kernels `R(x)` are `S`-conjugation equivariant `R(x^m) = R(x)^m`).  This is the `hconj` input the
(5.3.a) R-datum constructor `S07.dadeCharacterDifferenceImageOfDiff` consumes to build each family
member's `CharacterDifferenceImage` `τ(φ − φ̄) = ±(μ − ν)` — the same `.some` witness as `dadeHypS`,
so the isometry `dadeHypS.fullDadeIsometryData dadeHypS_hconj` is well-defined. -/
theorem Hypothesis.dadeHypS_hconj [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (hyp.dadeHypS hG).HConjInvariant :=
  (dadeSupportHypothesisData_honestTypeP2ASet hG hyp.S_maximal hyp.S_typeP2).some.hconj

open scoped FiniteInduce in
/-- **(13.2.e) `S`-instance `dade = Ind` bridge** (issue 1017): for the honest type-`P₂` maximal `S`,
on a class function `f` supported in a trivial-`H` sub-support `A₁ ⊆ A(S)` (an `S`-invariant subset
on which the `S`-instance Dade stabilizers vanish), the honest (13.2.e) Dade isometry
`τ = dadeIntegralCharacterMap (dadeHypS hG) …` acts as plain induction `Ind_S^G`.  This is the exact
`S`-instance analogue of the type-I bridge `S14.typeI_tau_eq_induce_of_supported_trivial_H`,
instantiating the general step-3 bridge `S14.dadeMap_eq_induce_of_supported_on_trivial_H` at the
`S`-instance Dade map `dadeHypS hG` (via `dadeIntegralCharacterMap_apply_of_support`, which rewrites
the lifted integral map as the §4 `dadeMap` on the supported carrier; `inclusion` widens the support
from `A₁` to `A(S)`).  The trivial-`H` sub-support facts (`hA₁A`, `hA₁norm`, `hH₁`, `hf`) are taken
as hypotheses, exactly as the type-I version defers them to the caller.  This is the `dade = Ind`
identity the (13.2.e)/(7.2) coherence route (`τ = Ind_S^G`, Peterfalvi (13.2.e)) rests on, matching
the honest `indS` value. -/
theorem Hypothesis.sInstance_dade_eq_induce_of_supported_trivial_H [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {A₁ : Set G} (hA₁A : A₁ ⊆ honestTypeP2ASet hyp.S)
    (hA₁norm : ∀ (l : ↥hyp.S) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hH₁ : ∀ a, ((hyp.dadeHypS hG).restrict hA₁A hA₁norm).H a = ⊥)
    {f : ClassFunction ↥hyp.S ℂ}
    (hf : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ hyp.S) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) f
      = ClassFunction.induce hyp.S f := by
  have hfA : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hf.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA₁A)
  have h1 : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) f
      = (hyp.dadeHypS hG).dadeMap (k := ℂ)
        ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hfA⟩ :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) hfA
  rw [h1]
  -- `⟨f, hfA⟩` is defeq to `inclusion hA₁A ⟨f, hf⟩` (same carrier `f`), so step 3 applies directly.
  exact OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H (hyp.dadeHypS hG)
    hA₁A hA₁norm hH₁ ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

/-- **(Rung B, reduction step 1) `dadeHypS.H a = ftSupportKernel S (A(S)) a`.**  The `S`-instance Dade
stabilizer at a support point `a` is the faithful per-`x` (8.14) signalizer kernel
`R(a) = ftSupportKernel S (A(S)) a`, read off the `H_eq_ftSupportKernel` field of the underlying
`DadeSupportHypothesisData` (the very `.some` witness `dadeHypS` is projected from).  This is the
concrete formula `H(a) = R(a)` of Peterfalvi (8.15)/(8.14), specialised to the honest type-`P₂`
support `A(S)`. -/
theorem Hypothesis.dadeHypS_H_eq_ftSupportKernel [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (a : {a : G // a ∈ honestTypeP2ASet hyp.S}) :
    (hyp.dadeHypS hG).H a =
      OddOrder.Peterfalvi.S10.ftSupportKernel hyp.S (honestTypeP2ASet hyp.S) a.1 :=
  (dadeSupportHypothesisData_honestTypeP2ASet hG hyp.S_maximal hyp.S_typeP2).some.H_eq_ftSupportKernel a

/-- **(Rung B, reduction) No escaping `A(S)`-points ⟹ all `S`-instance Dade stabilizers vanish.**
For the honest type-`P₂` support, `dadeHypS.H a = ftSupportKernel S (A(S)) a`
(`dadeHypS_H_eq_ftSupportKernel`), and the faithful kernel is `⊥` off the escaping set
(`ftSupportKernel_eq_bot_of_not_escaping`).  So if `A(S)` has no escaping point
(`∀ a ∈ A(S), a ∉ escapingCentralizerSet S (A(S))`, the Coq `FTtypeP_facts` (e) `normedTI` core,
Rung C), then `∀ a, dadeHypS.H a = ⊥` — the exact input `S04.isDadeMap_induce_of_forall_H_eq_bot` /
`sInstance_dade_eq_induce_of_supported_trivial_H` need to run `τ = Ind_S^G` on the *full* `A(S)`. -/
theorem Hypothesis.forall_dadeHypS_H_eq_bot_of_not_escaping [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hno : ∀ a ∈ honestTypeP2ASet hyp.S,
      a ∉ OddOrder.GroupTheory.escapingCentralizerSet hyp.S (honestTypeP2ASet hyp.S)) :
    ∀ a : {a : G // a ∈ honestTypeP2ASet hyp.S}, (hyp.dadeHypS hG).H a = ⊥ := by
  intro a
  rw [hyp.dadeHypS_H_eq_ftSupportKernel hG a]
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping (hno a.1 a.2)

/-- **(Rung B, reduction) `IsTISubset (A(S)) S ⟹ all `S`-instance Dade stabilizers vanish.**  A
TI-subset `A` has `C_G(x) ≤ L` for every `x ∈ A` (`IsTISubset.centralizer_le`), so no `A(S)`-point
escapes `S`; then `forall_dadeHypS_H_eq_bot_of_not_escaping` applies.  This is the direction of
Peterfalvi (2.3) that turns the `normedTI` conclusion (Rung C/D) into the trivial-stabilizer datum
the honest `dade = Ind` bridge consumes. -/
theorem Hypothesis.forall_dadeHypS_H_eq_bot_of_isTISubset [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTI : OddOrder.GroupTheory.IsTISubset (honestTypeP2ASet hyp.S) hyp.S) :
    ∀ a : {a : G // a ∈ honestTypeP2ASet hyp.S}, (hyp.dadeHypS hG).H a = ⊥ :=
  hyp.forall_dadeHypS_H_eq_bot_of_not_escaping hG
    (fun a ha hesc => hesc.2 (hTI.centralizer_le ha))

/-- **(Rung B, the equivalence, Peterfalvi (2.3) for the honest `S`-instance)**: the three forms of
the (13.2.e) `normedTI` gate coincide —
`IsTISubset (A(S)) S` ⟺ every `A(S)`-point is non-escaping ⟺ every `S`-instance Dade stabilizer
`dadeHypS.H a` is trivial.

The `A(S)`-set is sharp (`honestTypeP2ASet_subset_sharp`, `1 ∉ A(S)`), lies in `S`
(`honestTypeP2ASet_subset`), and is `S`-conjugation invariant (`honestTypeP2ASet_conj_mem`), so the
general `S04.isTISubset_iff_exists_hypothesis_with_trivial_H` (2.3) applies; but here we get the
*specific* `dadeHypS` stabilizers, via the (8.14) kernel formula.  This closes Rung B: reducing the
missing input of `sInstance_dade_eq_induce_of_supported_trivial_H` (with `A₁ = A(S)` full) to the
single TI fact `IsTISubset (A(S)) S` = Coq `FTtypeP_facts` (e). -/
theorem Hypothesis.isTISubset_honestTypeP2ASet_iff_forall_dadeHypS_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (honestTypeP2ASet hyp.S) hyp.S ↔
      ∀ a : {a : G // a ∈ honestTypeP2ASet hyp.S}, (hyp.dadeHypS hG).H a = ⊥ := by
  refine ⟨hyp.forall_dadeHypS_H_eq_bot_of_isTISubset hG, fun hH => ?_⟩
  -- The reverse direction is Peterfalvi (2.3): trivial Dade stabilizers ⟹ TI.
  exact (hyp.dadeHypS hG).isTISubset_of_forall_H_eq_bot hH

/-- **The honest `(H₀ ⊔ C')^#`-support for the `S`-instance, `= (C')^#`** (issue 2035 step 2).
For the `S`-instance the chief kernel is trivial (`toTypesIIIIIIVSetupS_chief_N_eq_bot`, giving
`H₀ = ⊥`), so the §9 `H₀C'`-support degenerates to `(C')^#` — the non-identity elements of
`C' = [C, C]`, viewed inside `↥S` via `C' ≤ C ≤ U ≤ S`.  This is the genuine `H0CprimeSupport`
of the honest §9 character data on `S`, replacing the `∅`-placeholder of `mkSection11CharacterDataS`. -/
def Hypothesis.cprimeSharpS (hyp : Hypothesis (G := G)) : Set ↥hyp.S :=
  OddOrder.Peterfalvi.S04.sharp ((hyp.Cprime).subgroupOf hyp.S : Set ↥hyp.S)

@[simp] theorem Hypothesis.mem_cprimeSharpS (hyp : Hypothesis (G := G)) {x : ↥hyp.S} :
    x ∈ hyp.cprimeSharpS ↔ (x : G) ∈ hyp.Cprime ∧ x ≠ 1 := by
  simp only [Hypothesis.cprimeSharpS, OddOrder.Peterfalvi.S04.mem_sharp, SetLike.mem_coe,
    Subgroup.mem_subgroupOf]

/-- **`C' = [C, C] = ⊥` for the type-`P₂` maximal `S`** (Peterfalvi (13.2.a): `abelian U`).
`C ≤ U` (`C = U ⊓ C_S(P)`) and `U` is abelian (`S_U_commutative`, BG Lemma 15.1(b)), so `C` is
abelian, whence its derived subgroup `C' = derivedInG C = (commutator ↥C).map C.subtype = ⊥`.

This is the exact repo analogue of the Coq step `derG1P (abelianS _ cUU)` in `FTtypeP_facts`
(PFsection13.v:221), which reduces the `H0C'` coherence support to `H0` alone in the type-`P₂`
case.  It dissolves **Blocker 2** (the `dade = Ind` bridge on the `(C')^#`-supported span): with
`C' = ⊥` the coherence support `(C')^# = cprimeSharpS` is *empty* (`cprimeSharpS_eq_empty`), so the
`IsCoherent.extends_on_supported` obligation carries no content that would require the Dade
isometry to agree with plain induction on any nonzero function. -/
theorem Hypothesis.Cprime_eq_bot (hyp : Hypothesis (G := G)) : hyp.Cprime = ⊥ := by
  have hCab : IsMulCommutative ↥hyp.C := by
    have hCU : hyp.C ≤ hyp.U := hyp.C_eq ▸ inf_le_left
    exact ⟨⟨fun a b => Subtype.ext (by
      have h := hyp.S_U_commutative.is_comm.comm
        (⟨(a : G), hCU a.2⟩ : ↥hyp.U) ⟨(b : G), hCU b.2⟩
      simpa using congrArg Subtype.val h)⟩⟩
  -- `↥C` commutative ⇒ `commutator ↥C = ⊥`, so `derivedInG C = (⊥).map _ = ⊥`.
  have hcomm : commutator ↥hyp.C = ⊥ := by
    rw [eq_bot_iff]
    refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := ⊥)).mpr (fun a _ b _ => ?_)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact hCab.is_comm.comm a b
  show derivedInG hyp.C = ⊥
  rw [derivedInG, hcomm, Subgroup.map_bot]

/-- **`(C')^#` is empty for the type-`P₂` maximal `S`** (immediate from `Cprime_eq_bot`).  Since
`C' = ⊥`, the `S`-restriction `(C').subgroupOf S = ⊥`, whose only element is `1`, so its sharp part
`cprimeSharpS = ({1} : Set ↥S) \ {1} = ∅`.

Consequence for the honest §9 coherence route (issue 1017, Blocker 2): the coherence support
`H0CprimeSupport = cprimeSharpS` of `mkSection11CharacterDataS_honest` is empty, hence
`zSupportedSpan 𝒮 ∅ = {0}` and `IsCoherent.extends_on_supported` is vacuous on that support.  The
`dade = Ind` identity the downstream `tau1S_apply_induce_sub` needs is therefore *not* required on
`(C')^#`; the genuine support of the equal-degree family differences is the honest Dade support
`A(S)` (via `sSet_member_diffsupp`), which is where the actual `dade = Ind` question lives — but the
`(C')^#`-support degeneration this lemma records means that particular blocker framing is a
misdirection. -/
theorem Hypothesis.cprimeSharpS_eq_empty (hyp : Hypothesis (G := G)) :
    hyp.cprimeSharpS = (∅ : Set ↥hyp.S) := by
  ext x
  simp only [hyp.mem_cprimeSharpS, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hxne
  -- `x ∈ C' = ⊥` forces `x = 1` in `↥S`, contradicting `x ≠ 1`.
  rw [hyp.Cprime_eq_bot, Subgroup.mem_bot] at hx
  exact hxne (Subtype.ext hx)

/-- **`(C')^# ⊆ A(S)` (as an `S`-support)** (issue 1017): the honest §9 coherence support `(C')^#`
is contained in the `S`-restriction of the Dade support `A(S) = ⋃_{x∈S_σ#} C_{S'}(x)#`.  `C' = [C,C]
≤ C ≤ U ≤ S' = derivedInG S` gives the derived-membership; and `C ≤ C_S(P)` (from `C = U ⊓ C_S(P)`)
with `P = S_σ` (type-II `maxNilpotentNormalHall S = M_σ`) puts every `(C')^#`-element in `C_{S'}(z)`
for any `z ∈ S_σ^#` (nonempty by `Msigma_ne_bot`).  This bridges the coherence support to the Dade
support — the `hdiffsupp` half the (5.3.a) R-datum `dadeCharacterDifferenceImageOfDiff` needs (its
support hypothesis is w.r.t. `A(S)`, while the §9 family differences are `(C')^#`-supported). -/
theorem Hypothesis.cprimeSharpS_subset_supportA [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.cprimeSharpS ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
  have hPeq : hyp.P = OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hyp.S_maximal
      (Or.inr (OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2))
  have hCcentP : hyp.C ≤ Subgroup.centralizer (hyp.P : Set G) := by
    rw [hyp.C_eq]; exact inf_le_right
  have hCderiv : hyp.C ≤ derivedInG hyp.S := by
    rw [hyp.S_deriv_eq_PU, hyp.C_eq]; exact le_trans inf_le_left le_sup_right
  have hCpC : hyp.Cprime ≤ hyp.C := Subgroup.map_subtype_le _
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hyp.S_maximal)
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  intro x hx
  rw [hyp.mem_cprimeSharpS] at hx
  obtain ⟨hxCp, hxne⟩ := hx
  have hxC : (x : G) ∈ hyp.C := hCpC hxCp
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, mem_honestTypeP2ASet]
  refine ⟨hCderiv hxC, fun h => hxne (Subtype.ext h), (z : G),
    (Set.mem_diff _).mpr ⟨SetLike.mem_coe.mpr z.2, fun h => hz1' (Set.mem_singleton_iff.mp h)⟩, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzP : (z : G) ∈ hyp.P := by rw [hPeq]; exact z.2
  exact (Subgroup.mem_centralizer_iff.mp (hCcentP hxC) (z : G) hzP).symm

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (4.7), `S`-instance induced support**: `Supp Ind_{HU}^S ξ ⊆ A(S) ∪ {1}` for every
`ξ ∈ 𝒳` (Peterfalvi (9.5)'s family, `H ⊄ Ker ξ`), where `A(S) = ⋃_{x∈S_σ#} C_{S'}(x)#` is the honest
type-`P₂` Dade support (`honestTypeP2ASet hyp.S`).

This is the honest §9 instance of the (4.7) support fact underlying the (5.3.a) R-datum's `hdiffsupp`
input (the family differences of `𝒮` must vanish off `A(S)`).  The proof **mirrors** the S06 (4.7)
induced-support lemma `S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel`
(the S06 statement is bound to the `Hypothesis46` structure and cannot be instantiated for the §9
`TypesIIIIIIVSetup`, so we replay its three steps directly in the `↥S` ambient):

* `support_induce_subset_conjugatesIntoSet`: a nonvanishing point `x` of `Ind_{HU}^S ξ` is
  `S`-conjugate to a point `w ∈ HU` of `Supp ξ`;
* the (4.7) **core** (Peterfalvi (1.2), `irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`
  contrapositive) forces a nontrivial `d ∈ H = P = S_σ` centralizing `w`, and the covering
  condition puts `w ∈ A(S)` (via `mem_honestTypeP2ASet`: `w ∈ S' = M'`, `w ≠ 1`, `w` centralizes
  `d ∈ S_σ#`);
* `honestTypeP2ASet_conj_mem` ((4.7)'s `L_normalizes_A` replacement): `A(S)` is `S`-conjugation
  invariant, so the image of `x` lies in `A(S) ∪ {1}` too.

The `H = P = S_σ` identification is exactly the `hyp.P_eq_SF` + type-II
`maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II` chain used in `cprimeSharpS_subset_supportA`. -/
theorem Hypothesis.sSet_member_support_subset_A [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupS hG)) :
    (induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S ∪ {1} := by
  classical
  -- `H = P = S_σ` (type-II Fitting = maximal nilpotent normal Hall = `Msigma`).
  have hHP : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    show hyp.Sdata.H = hyp.P
    rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hPeq : hyp.P = OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG
      hyp.S_maximal
      (Or.inr (OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2))
  -- the (4.7) core: a nonvanishing `w ∈ HU` with `(w:S) ≠ 1` maps into `A(S)`.
  have hcore : ∀ w : ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)),
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) w ≠ 0 →
      ((w : ↥hyp.S) : G) ≠ 1 →
      ((w : ↥hyp.S) : G) ∈ honestTypeP2ASet hyp.S := by
    intro w hwval hwne
    -- (1.2) contrapositive: `C_{hInHu}(w) ≠ ⊥`.
    haveI := hInHu_normal (hyp.toTypesIIIIIIVSetupS hG)
    have hCne : OddOrder.Peterfalvi.S03.centralizerInSubgroup
        (hInHu (hyp.toTypesIIIIIIVSetupS hG)) w ≠ ⊥ := fun hbot =>
      hwval
        (OddOrder.Peterfalvi.S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot
          ξ hξ hbot)
    -- extract a nontrivial `d ∈ hInHu` centralizing `w`.
    obtain ⟨d, hd_mem, hd_ne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCne
    rw [OddOrder.Peterfalvi.S03.mem_centralizerInSubgroup] at hd_mem
    obtain ⟨hd_H, hd_comm⟩ := hd_mem
    -- `d`'s ambient image lies in `H = P` and is nontrivial; it commutes with `w`.
    have hdS_H : (d : ↥hyp.S) ∈ (hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S :=
      (Subgroup.mem_subgroupOf).mp hd_H
    have hdH_G : ((d : ↥hyp.S) : G) ∈ (hyp.toTypesIIIIIIVSetupS hG).H :=
      (Subgroup.mem_subgroupOf).mp hdS_H
    have hdG_ne : ((d : ↥hyp.S) : G) ≠ 1 := fun he => hd_ne (by
      apply Subtype.ext; apply Subtype.ext; exact he)
    have hcommG : ((d : ↥hyp.S) : G) * ((w : ↥hyp.S) : G)
        = ((w : ↥hyp.S) : G) * ((d : ↥hyp.S) : G) := by
      have := congrArg (fun t : ↥hyp.S => (t : G)) (Subtype.ext_iff.mp hd_comm)
      simpa using this
    -- covering condition: `(w:S) ∈ A(S)` via `mem_honestTypeP2ASet` with witness `d ∈ S_σ#`.
    rw [mem_honestTypeP2ASet]
    refine ⟨?_, hwne, ((d : ↥hyp.S) : G), ?_, ?_⟩
    · -- `w ∈ S' = M'` since `w ∈ HU = (derivedInG S).subgroupOf S`.
      have hwHU : (w : ↥hyp.S) ∈ (derivedInG hyp.S).subgroupOf hyp.S := by
        rw [← huSub_eq_derivedInG_subgroupOf]; exact w.2
      exact (Subgroup.mem_subgroupOf).mp hwHU
    · -- `d ∈ S_σ# = (Msigma S)#`.
      refine (Set.mem_diff _).mpr ⟨?_, fun he => hdG_ne (Set.mem_singleton_iff.mp he)⟩
      have hdP : ((d : ↥hyp.S) : G) ∈ hyp.P := hHP ▸ hdH_G
      exact SetLike.mem_coe.mpr (hPeq ▸ hdP)
    · -- `w` centralizes `d`.
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommG.symm
  -- assemble via `support_induce_subset_conjugatesIntoSet` + conjugation invariance.
  intro x hx
  rw [Set.mem_union, Set.mem_singleton_iff]
  by_cases hx1 : x = 1
  · exact Or.inr hx1
  -- `x` is `S`-conjugate into `Supp ξ`.
  have hxsupp : (induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)) x ≠ 0 :=
    ClassFunction.mem_support.mp hx
  have hx_conj : x ∈ ClassFunction.conjugatesIntoSet (huSub (hyp.toTypesIIIIIIVSetupS hG))
      ((ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).support := by
    have hind : induceHU (hyp.toTypesIIIIIIVSetupS hG)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
        = ClassFunction.induce (huSub (hyp.toTypesIIIIIIVSetupS hG))
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) := rfl
    refine ClassFunction.support_induce_subset_conjugatesIntoSet (subset_refl _) ?_
    rw [← hind]; exact hxsupp
  rw [ClassFunction.mem_conjugatesIntoSet] at hx_conj
  obtain ⟨c, hc, hcsupp⟩ := hx_conj
  set w : ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) := ⟨c⁻¹ * x * c, hc⟩ with hw_def
  have hw_val : (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) w ≠ 0 :=
    ClassFunction.mem_support.mp hcsupp
  -- `(w:S) = c⁻¹ x c`; `x = c (w:S) c⁻¹` with `c ∈ S`.
  have hwS_eq : ((w : ↥hyp.S) : G) = (c : G)⁻¹ * (x : G) * (c : G) := rfl
  have hxeq : (x : G) = (c : G) * ((w : ↥hyp.S) : G) * (c : G)⁻¹ := by
    rw [hwS_eq]; group
  have hwne : ((w : ↥hyp.S) : G) ≠ 1 := by
    intro he
    apply hx1
    have hxG : (x : G) = 1 := by rw [hxeq, he]; group
    exact Subtype.ext hxG
  have hwA : ((w : ↥hyp.S) : G) ∈ honestTypeP2ASet hyp.S := hcore w hw_val hwne
  -- conjugate back: `A(S)` is `S`-conjugation invariant.
  refine Or.inl ?_
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hxeq]
  exact honestTypeP2ASet_conj_mem c.2 hwA

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.3.a) per-member difference support** (issue 1017): the Dade-image support hypothesis
`((Ind ξ)̄ − Ind ξ).support ⊆ A(S)` (as an `S`-support) that `S07.dadeCharacterDifferenceImageOfDiff`
consumes to build the `CharacterDifferenceImage` of an irreducible §9 member.  From
`sSet_member_support_subset_A` (support `⊆ A(S) ∪ {1}`), removing the identity: the difference
`(Ind ξ)̄ − Ind ξ` vanishes at `1` (the degree `Ind ξ(1) = q·ξ(1)` is a positive real, self-conjugate).
This is the `hdiffsupp` half of the R-datum — the S-instance `R1_diffsupp` (Peterfalvi §12/§5). -/
theorem Hypothesis.sSet_member_diffsupp [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupS hG)) :
    ((induceHU (hyp.toTypesIIIIIIVSetupS hG)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
        - induceHU (hyp.toTypesIIIIIIVSetupS hG)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
  set φ : ClassFunction ↥hyp.S ℂ :=
    induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) with hφ
  have hsupp_eq : φ.conj.support = φ.support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : (φ.conj - φ) x ≠ 0 := hx
  have hxsupp : x ∈ φ.support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases hyp.sSet_member_support_subset_A hG hξ (hφ ▸ hxsupp) with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ :=
      OddOrder.RepresentationTheory.irreducibleCharacter_apply_one_eq_pos_natCast ξ
    apply hx0
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hφ, induceHU_apply_one_eq_q_mul, hd,
      star_mul', star_natCast, star_natCast, sub_self]

/-! ### Dade-independent subcoherence inputs for the §9 induced family `𝒮`

The (5.3.a) subcoherence assembler `S07.irrSubcoherent` needs, besides the Dade isometry, the family
properties `hconj`/`hreal`/`hortho` of `𝒮 = Ind_{HU}^M 𝒳`.  These are **Dade-independent** — provable
directly from the induced-character conjugation identity and the orthogonality of distinct-orbit
inductions — so they can be discharged ahead of the (13.2.e) Dade-isometry foundation.  Here we land
`hconj` (conjugate-closure); it feeds the honest §9 subcoherence assembly that re-grounds
`coherent_H0Cprime_S` off the unsound `sibleyTarget_H0C`. -/

open OddOrder.Peterfalvi.S11 in
/-- **`𝒳` is closed under complex conjugation** (Peterfalvi (9.5)): for `χ ∈ 𝒳` (irreducible,
`H ⊄ Ker χ`), the conjugate `χ̄` is again irreducible (`IsIrreducibleCharacter.conj`) with the same
kernel (`characterKernel_conj`), so `H ⊄ Ker χ̄`, i.e. `χ̄ ∈ 𝒳`. -/
theorem conj_mem_xiSet {M : Subgroup G} [Finite G] {data : TypesIIIIIIVSetup M}
    {χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub data)}
    (hχ : χ ∈ xiSet data) :
    (⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩ :
      OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  -- Membership unfolds (rfl) to a `characterKernel`-containment on the conjugate coe, which is
  -- defeq `(↑χ).conj`; `characterKernel_conj` rewrites it back to `characterKernel ↑χ` = `hχ`.
  show ¬ (↑(hInHu data) ⊆ OddOrder.Peterfalvi.S03.characterKernel
    ((χ : ClassFunction ↥(huSub data) ℂ).conj))
  rw [OddOrder.Peterfalvi.S03.characterKernel_conj]
  exact hχ

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮` is closed under complex conjugation** (Peterfalvi (9.5), subcoherence input (5.2.a)).
For `φ = Ind_{HU}^M χ ∈ 𝒮` with `χ ∈ 𝒳`, the conjugate is `φ̄ = Ind_{HU}^M χ̄` (`conj_induce`), and
`χ̄ ∈ 𝒳` (`conj_mem_xiSet`), so `φ̄ ∈ 𝒮`.  This is the `hconj` input the (5.3.a) subcoherence
assembler `S07.irrSubcoherent` consumes for the §9 induced family — a Dade-independent family
property, provable directly from the induced-character conjugation identity `conj_induce`. -/
theorem sSet_closedUnderConjugate {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (sSet data) := by
  rintro _ ⟨χ, hχ, rfl⟩
  refine ⟨⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩,
    conj_mem_xiSet hχ, ?_⟩
  -- `(Ind_{HU}^M χ)̄ = Ind_{HU}^M χ̄` (`conj_induce`); `induceHU` bakes in its own `Invertible`
  -- instance, so `convert` absorbs the (subsingleton) instance mismatch.
  show (induceHU data (χ : ClassFunction ↥(huSub data) ℂ)).conj
    = induceHU data ((χ : ClassFunction ↥(huSub data) ℂ).conj)
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  simp only [induceHU]
  convert OddOrder.RepresentationTheory.conj_induce (χ : ClassFunction ↥(huSub data) ℂ) using 2

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`𝒮` is pairwise orthogonal** (Peterfalvi (9.5), subcoherence input (5.2)).  Distinct members
`Ind_{HU}^M χ ≠ Ind_{HU}^M χ'` arise from non-`M`-conjugate irreducible sources `χ ≁ χ'`
(`induce_eq_induce_iff_conj`), so the cross-Mackey orthogonality `inner_induce_eq_zero_of_not_conj`
gives `⟨Ind χ, Ind χ'⟩ = 0` — a Dade-independent family property (the `𝒮`-instance of the general
`inducedKernelFamily_pairwise_orthogonal`).  The `FiniteInduce`-scoped `Fintype`/`Invertible`
instances are the ones `induceHU` bakes in, so `induceHU = Ind` reduces definitionally.  This is the
`pairwise_orthogonal` input the (5.3.a) assembler `S07.irrSubcoherent` consumes for the honest §9
induced family. -/
theorem sSet_pairwiseOrthogonal {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal (sSet data) := by
  rintro _ _ ⟨χ, hχ, rfl⟩ ⟨χ', hχ', rfl⟩ hne
  -- non-conjugate sources: else the inductions—hence the members—coincide, contradicting `hne`.
  have hnc : ∀ g : ↥M, IrreducibleCharacter.conjBy g χ ≠ χ' := fun g hg => hne (by
    show ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (χ' : ClassFunction ↥(huSub data) ℂ)
    exact (induce_eq_induce_iff_conj χ χ').mpr ⟨g, hg⟩)
  show ClassFunction.inner (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ))
      (ClassFunction.induce (huSub data) (χ' : ClassFunction ↥(huSub data) ℂ)) = 0
  exact inner_induce_eq_zero_of_not_conj χ χ' hnc

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`𝒮` has no real members** (Peterfalvi (9.5)/(1.1), subcoherence input (5.2)), for `M` of odd
order.  A real `Ind_{HU}^M χ` would force `χ̄ = χ^g` for some `g ∈ M` (`induce_conj` +
`induce_eq_induce_iff_conj`), impossible in odd order (`conjBy_ne_conj_of_odd`: a nontrivial
irreducible of an odd-order group is never `M`-conjugate to its dual).  `𝒳`-membership `H ⊄ Ker χ`
supplies the nontriviality (`Ker 1 = univ ⊇ hInHu`).  The `𝒮`-instance of the general
`inducedKernelFamily_hasNoRealCharacters`; the `no_real_characters` input for `S07.irrSubcoherent`. -/
theorem sSet_hasNoRealCharacters {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M)
    (hodd : Odd (Nat.card ↥M)) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (sSet data) := by
  rintro _ ⟨χ, hχ, rfl⟩ hreal
  -- `χ` nontrivial: else `Ker χ = univ ⊇ hInHu`, contradicting `χ ∈ 𝒳`.
  have hχne : (χ : ClassFunction ↥(huSub data) ℂ) ≠ trivialClassFunction ↥(huSub data) := by
    intro h
    apply hχ
    rw [h, OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  let χc : IrreducibleCharacter ↥(huSub data) :=
    ⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩
  -- realness of `Ind χ` transfers to the sources: `Ind χ = (Ind χ)̄ = Ind χ̄`.
  have hind : ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (χc : ClassFunction ↥(huSub data) ℂ) := by
    have h1 : (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)).conj
        = ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ) := hreal
    calc ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
        = (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)).conj := h1.symm
      _ = ClassFunction.induce (huSub data) (χc : ClassFunction ↥(huSub data) ℂ) :=
          ClassFunction.induce_conj (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj χ χc).mp hind
  refine conjBy_ne_conj_of_odd hodd χ.isIrreducible hχne g ?_
  have hcoe := congrArg
    (fun η : IrreducibleCharacter ↥(huSub data) => (η : ClassFunction ↥(huSub data) ℂ)) hg
  simpa [IrreducibleCharacter.coe_conjBy, χc] using hcoe

/-- **`Odd |S|`** for the maximal subgroup `S` of the minimal simple group `G` of odd order
(issue 1017, subcoherence input for the §9 induced family).  `|S| ∣ |G|` (subgroup) and `|G|` is odd
(`hG.odd`), so `|S|` is odd — the hypothesis `sSet_hasNoRealCharacters` (the (5.2.a) realness input)
needs. -/
theorem Hypothesis.oddCardS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Odd (Nat.card ↥hyp.S) := by
  rcases hG.odd with ⟨k, hk⟩
  -- From `|S| ∣ |G|` and `|G|` odd, deduce `|S|` odd (a divisor of an odd number is odd).
  have hdvd : Nat.card ↥hyp.S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.S
  rcases Nat.even_or_odd (Nat.card ↥hyp.S) with heven | hodd
  · exfalso
    have h2 : (2 : ℕ) ∣ Nat.card G := (even_iff_two_dvd.mp heven).trans hdvd
    rw [hk] at h2
    omega
  · exact hodd

open OddOrder.Peterfalvi.S11 in
/-- **The per-irreducible-member Dade `CharacterDifferenceImage` for a `𝒮 = sSet`-member**
(Peterfalvi (5.3.a) R-datum, issue 1017 Part B).  Given an irreducible source `ξ ∈ 𝒳` whose induced
`Ind_{HU}^S ξ` is **itself irreducible** (the irreducible sub-family of the mixed §9 family — the
reducible residues `μ_j` are handled separately, as a `CharacterPsiDecomposition.imageFamily` of
variable length, *not* through this 2-element `CharacterDifferenceImage`), this packages the signed
difference image `(Ind ξ − (Ind ξ)̄)^τ = ±(μ − ν)` under the honest (13.2.e) Dade map
`τ = dadeIntegralCharacterMap (dadeHypS hG) …`.

Assembled entirely from landed inputs:
* the Dade hypothesis `dadeHypS hG` and its `HConjInvariant` `dadeHypS_hconj hG`;
* the member's non-realness `sSet_hasNoRealCharacters` (needs `oddCardS`);
* the difference support `sSet_member_diffsupp` (`((Ind ξ)̄ − Ind ξ).support ⊆ A(S)`),
  fed through `dadeCharacterDifferenceImageOfDiff`.

This is the exact `S`-instance analogue of the §14 `R1cdi` (`S14_MaximalI.lean:744`), which builds
the same per-member R-datum for the (12.2) family via `dadeCharacterDifferenceImageOfDiff`.  It is
the per-member piece that `S07.irrSubcoherent` consumes on the irreducible sub-family (the (9.11)
base + Galois glue), and the (9.11) pair-adjoining induction consumes (as `Da`/`Dmem` decomposition
data) for the whole family. -/
noncomputable def Hypothesis.sSet_member_differenceImage [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥hyp.S) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      (induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)) := by
  -- Bundle the (irreducible) member as an `IrreducibleCharacter ↥S`.
  set φ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S :=
    ⟨induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ), hirr⟩ with hφ_def
  -- Non-realness of the member (the `¬IsReal` input), from the family property + `Odd |S|`.
  have hreal : ¬ ClassFunction.IsReal (φ : ClassFunction ↥hyp.S ℂ) :=
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) ⟨ξ, hξ, rfl⟩
  -- The difference support `((φ)̄ − φ).support ⊆ supportInSubgroup A(S) S` (the `hdiffsupp` input).
  have hdiffsupp :
      ((φ : ClassFunction ↥hyp.S ℂ).conj - (φ : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S :=
    hyp.sSet_member_diffsupp hG hξ
  -- Package via the general (5.3.a) Dade R-datum constructor.
  exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
    (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) φ hreal hdiffsupp

open OddOrder.Peterfalvi.S11 in
/-- **The uniform-degree irreducible sub-family `S₁(d) = {φ ∈ 𝒮 | φ irreducible, φ(1) = d}`**
(issue 1017, the (9.11) base / Galois glue per update #17).  The honest §9 family `𝒮 = sSet` is
*mixed*-degree — both across the `p−1` reducible residues `μ_j` and across the irreducible members
`Ind ξ` of source degree `ξ(1)` (degree `q·ξ(1)`).  Since the (0099) weakening, the
(5.2)-subcoherence `S07.Hypothesis` *is* instantiable on mixed-degree families (its
`tau_isometry_diff` field only demands the isometry on the `A(S)`-supported sublattice `ℤ[S, A]`);
what still needs equal degrees is the **(5.7) equal-degree coherence producer**
(`coherent_of_constant_degree`'s `hconst`/`hsuppdiff` inputs — member differences must vanish at
`1`).  Fixing a single degree value `d` carves out the uniform-degree conjugate-closed irreducible
sub-family on which that producer fires; the (9.11) base case (`d = q·a`) and the whole Galois case
(`d = q·u`) are the two instances the coherence route consumes. -/
noncomputable def Hypothesis.sSetIrrDeg [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (d : ℂ) : Set (ClassFunction ↥hyp.S ℂ) :=
  { φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) |
      OddOrder.RepresentationTheory.IsIrreducibleCharacter φ ∧ (φ : ↥hyp.S → ℂ) 1 = d }

open OddOrder.Peterfalvi.S11 in
theorem Hypothesis.sSetIrrDeg_subset_sSet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (d : ℂ) :
    hyp.sSetIrrDeg hG d ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := fun _ h => h.1

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The `S07.Hypothesis` (5.2)-subcoherence structure for the uniform-degree irreducible
sub-family `S₁(d)`** (issue 1017, update #17 — the first honest stage of the (9.11) coherence route).
Assembled from the honest (13.2.e) Dade isometry `τ = Ind_S^G` (`dadeHypS`) and the landed
Dade-independent family inputs:
* `Rdatum` = `sSet_member_differenceImage` per irreducible member;
* `hconj` = `sSet_closedUnderConjugate` (conj of an irreducible degree-`d` member is again one — the
  conjugate `φ̄` is irreducible with `φ̄(1) = conj(φ(1)) = d` as `d = q·s` is a positive real);
* `hreal` = `sSet_hasNoRealCharacters` (via `oddCardS`), restricted to `S₁(d) ⊆ 𝒮`;
* `hortho` = `sSet_pairwiseOrthogonal`, restricted to `S₁(d) ⊆ 𝒮`;
* `hconjsupp` = conjugate differences `χ − χ̄` are `A(S)`-supported: `χ̄ ∈ S₁(d)` (conj-closedness,
  `star d = d`) and equal degrees make the difference vanish at `1`
  (`sSet_member_support_subset_A` minus the identity);
* `hiso` = the (0099) `zSupportedSpan`-form lattice isometry, unconditional from the Dade pair
  brick `dadeIntegralCharacterMap_inner_eq_of_supported` (only the supportedness halves are used).

The `hconj` field requires `d` to be real (`star d = d`); this holds for the genuine degree values
`d = q·s` (positive natural), supplied by the caller.  This is the (5.3.a) subcoherence hypothesis on
a uniform-degree family, ready for `coherent_subset_of_constant_degree` (the (9.11) base + Galois). -/
noncomputable def Hypothesis.sSetIrrDeg_subcoherent [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    (d : ℂ) (hd : star d = d) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.S) (G := G)
      (hyp.sSetIrrDeg hG d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S) := by
  classical
  -- The honest (13.2.e) Dade isometry `τ = Ind_S^G`.
  set τ := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
    ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)) with hτ
  -- Conjugation stability of `S₁(d)` (uses `star d = d`).
  have hconjmem : ∀ φ ∈ hyp.sSetIrrDeg hG d, φ.conj ∈ hyp.sSetIrrDeg hG d := by
    intro φ hφ
    refine ⟨sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hφ.1, hφ.2.1.conj, ?_⟩
    rw [ClassFunction.conj_apply, hφ.2.2, hd]
  -- Members are supported in `A(S) ∪ {1}`.
  have hmem_supp : ∀ φ ∈ hyp.sSetIrrDeg hG d,
      φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S ∪ {1} := by
    rintro φ ⟨hφsSet, _⟩
    obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
    rw [hφeq]
    exact hyp.sSet_member_support_subset_A hG hξ
  -- `x - y` with `x, y ∈ S₁(d)` (hence `x(1) = d = y(1)`) is supported in `A(S)`.
  have hdiff_of_mem : ∀ x ∈ hyp.sSetIrrDeg hG d, ∀ y ∈ hyp.sSetIrrDeg hG d,
      (x - y).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S := by
    intro x hx y hy z hz
    have hz0 : (x - y) z ≠ 0 := hz
    have hdeg : (x : ↥hyp.S → ℂ) 1 = (y : ↥hyp.S → ℂ) 1 := by rw [hx.2.2, hy.2.2]
    rcases (ClassFunction.support_sub_subset x y hz) with h | h
    · rcases hmem_supp x hx h with h' | h'
      · exact h'
      · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
        exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
    · rcases hmem_supp y hy h with h' | h'
      · exact h'
      · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
        exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  refine OddOrder.Peterfalvi.S07.irrSubcoherent τ
    (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)
    (fun φ hφ => ?_) ?_ ?_ ?_ ?_ ?_
  · -- `Rdatum`: `φ ∈ S₁(d) ⇒ ∃ ξ ∈ 𝒳, φ = Ind ξ` (irreducible).  The `∃` witness is extracted via
    -- `choose` (not `obtain`) so it may be eliminated into the data goal `CharacterDifferenceImage`.
    have hφsSet : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) := hφ.1
    have hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ := hφ.2.1
    obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
    rw [hφeq] at hirr ⊢
    exact hyp.sSet_member_differenceImage hG hξ hirr
  · -- `hconj`: conjugate of a degree-`d` irreducible member of `𝒮` is again one (uses `star d = d`).
    intro φ hφ
    exact hconjmem φ hφ
  · -- `hreal`: no real members, restricted to `S₁(d) ⊆ 𝒮`.
    exact (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG)).mono
      (hyp.sSetIrrDeg_subset_sSet hG d)
  · -- `hortho`: pairwise orthogonal, restricted to `S₁(d) ⊆ 𝒮`.  The `FiniteInduce`-scoped instances
    -- baked into `sSet_pairwiseOrthogonal`'s `inner` are (subsingleton-)equal to the section ones.
    intro φ ψ hφ hψ hne
    convert sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hφ.1 hψ.1 hne using 2 <;>
      exact Subsingleton.elim _ _
  · -- `hconjsupp`: the conjugate difference `χ − χ̄` is `A(S)`-supported (`χ̄ ∈ S₁(d)` + equal degree).
    intro χ hχ
    exact hdiff_of_mem χ hχ χ.conj (hconjmem χ hχ)
  · -- `hiso`: the (0099) `zSupportedSpan`-form lattice isometry — unconditional from the Dade
    -- pair brick (only the supportedness halves of the `ℤ[S₁(d), A(S)]` memberships are used).
    intro φ ψ hφ hψ
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hφ.2 hψ.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) base / Galois coherence of the uniform-degree irreducible sub-family `S₁(d)`**
(issue 1017, update #18 — the honest (9.11) base coherence).  Feeds the landed subcoherence
`sSetIrrDeg_subcoherent` into `coherent_subset_of_constant_degree` (Peterfalvi (5.7)∘(5.3.a),
`S07_Subcoherent.lean:246`) with `S' = S = sSetIrrDeg d` (the uniform subset of itself), producing
`Nonempty (IsCoherent τ (S₁ d) A)` for the honest Dade map `τ = Ind_S^G` (`dadeHypS`) and support
`A(S)`.  This is the whole **Galois case** (`d = q·u`) and the **base case `S₁`** (`d = q·a`) of the
(9.11) `Ptype_core_coherence` derived-series induction (Coq `PFsection9.v:1484`).

The `coherent_subset_of_constant_degree` hypotheses discharge as follows, all *internally* from the
landed §9 family lemmas — **except `hcard` (≥ 2 membership)**, which is *exposed as a parameter*
`h2`: no `2 ≤ (S₁ d).ncard` fact exists yet in the repo (the degree-`d` count is the §9 (9.8.d)
counting content — `caseA_exists_irreducible_source_degree_qa`, `S11:6437`, and its `M`-induction
strengthening at `S11:12250`, give an *existence* `∃ ζ`, not two distinct members).  Exposing it
keeps this def sorry-free and defers the genuine upstream count to the caller — the honest pattern.

Internal discharges:
* `hconj'` = `sSetIrrDeg_subcoherent`'s own `.conjugate_closed` field (conj of a degree-`d`
  irreducible member is again one, uses `star d = d`);
* `hSfin` = `S₁ d ⊆ range (IrreducibleCharacter.toClassFunction)` (finite range of a `Finite` type);
* `hirr` = `IsIrreducibleCharacter.inner_self_eq_one` (each member is irreducible by definition);
* `hZIrr` = `dadeIntegralCharacterMap_mem_ZIrr_of_supported` — the member difference `a − b` is
  `A(S)`-supported (equal degree, vanishes at `1`) and a virtual character (difference of two
  irreducibles), so the honest Dade map sends it into `ℤ[Irr G]`;
* `hconst` = definitional uniform degree `φ(1) = d`;
* `hdeg0` = exposed `d ≠ 0`;
* `h1A` = `honestTypeP2ASet_one_not_mem` (`1 ∉ A(S)`);
* `hsuppdiff` = the equal-degree two-member support fact (member differences `A(S)`-supported),
  the same argument `sSetIrrDeg_subcoherent`'s `hiso` uses internally. -/
noncomputable def Hypothesis.sSetIrrDeg_coherent [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    (d : ℂ) (hd : star d = d) (hd0 : d ≠ 0)
    (h2 : 2 ≤ (hyp.sSetIrrDeg hG d).ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData (hyp.dadeHypS_hconj hG)))
      (hyp.sSetIrrDeg hG d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S)) := by
  classical
  set A := OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2ASet hyp.S) hyp.S with hA
  -- The landed (5.3.a) subcoherence structure on `S₁(d)`; its `.tau` is the honest Dade map.
  set hyp' := hyp.sSetIrrDeg_subcoherent hG d hd with hhyp'
  -- `hSfin`: `S₁(d)` injects into `IrreducibleCharacter ↥S` (a `Finite` type).
  have hSfin : (hyp.sSetIrrDeg hG d).Finite := by
    apply Set.Finite.subset (Set.finite_range
      (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
        (χ : ClassFunction ↥hyp.S ℂ)))
    rintro φ ⟨_, hirr, _⟩
    exact ⟨⟨φ, hirr⟩, rfl⟩
  -- `hirr`: each member is an irreducible character, so has self-inner `1`.
  have hirr : ∀ ζ ∈ hyp.sSetIrrDeg hG d, ClassFunction.inner ζ ζ = 1 :=
    fun ζ hζ => hζ.2.1.inner_self_eq_one
  -- `hconst`: uniform degree `φ(1) = d` (definitional membership).
  have hconst : ∀ a ∈ hyp.sSetIrrDeg hG d, ∀ b ∈ hyp.sSetIrrDeg hG d,
      ((a : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 = ((b : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 :=
    fun a ha b hb => by rw [ha.2.2, hb.2.2]
  -- `hdeg0`: nonzero degree (exposed `d ≠ 0`).
  have hdeg0 : ∀ a ∈ hyp.sSetIrrDeg hG d, ((a : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 ≠ 0 :=
    fun a ha => by rw [ha.2.2]; exact hd0
  -- `h1A`: `1 ∉ A(S)`.
  have h1A : (1 : ↥hyp.S) ∉ A := by
    rw [hA, OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    simpa using honestTypeP2ASet_one_not_mem (M := hyp.S)
  -- `hsuppdiff`: for `x, y ∈ S₁(d)`, `(x − y).support ⊆ A(S)` (equal degree ⇒ vanish at `1`).
  have hmem_supp : ∀ φ ∈ hyp.sSetIrrDeg hG d, φ.support ⊆ A ∪ {1} := by
    rintro φ ⟨hφsSet, _⟩
    obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
    rw [hφeq]
    exact hyp.sSet_member_support_subset_A hG hξ
  have hsuppdiff : ∀ x ∈ hyp.sSetIrrDeg hG d, ∀ y ∈ hyp.sSetIrrDeg hG d,
      ((x - y : ClassFunction ↥hyp.S ℂ)).support ⊆ A := by
    intro x hx y hy z hz
    have hz0 : (x - y) z ≠ 0 := hz
    have hdeg : (x : ↥hyp.S → ℂ) 1 = (y : ↥hyp.S → ℂ) 1 := by rw [hx.2.2, hy.2.2]
    rcases (ClassFunction.support_sub_subset x y hz) with h | h
    · rcases hmem_supp x hx h with h' | h'
      · exact h'
      · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
        exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
    · rcases hmem_supp y hy h with h' | h'
      · exact h'
      · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
        exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  -- `hZIrr`: the honest Dade map sends `A(S)`-supported virtual-character differences into `ℤ[Irr G]`.
  have hZIrr : ∀ a ∈ hyp.sSetIrrDeg hG d, ∀ b ∈ hyp.sSetIrrDeg hG d,
      hyp'.tau (a - b) ∈ OddOrder.RepresentationTheory.ZIrr G := by
    intro a ha b hb
    have hab_supp : (a - b : ClassFunction ↥hyp.S ℂ).support ⊆ A := hsuppdiff a ha b hb
    have hab_Z : (a - b : ClassFunction ↥hyp.S ℂ) ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
      Submodule.sub_mem _ ha.2.1.mem_ZIrr hb.2.1.mem_ZIrr
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypS hG) (hyp.dadeHypS_hconj hG) hab_supp hab_Z
  -- Fire the (5.7)∘(5.3.a) uniform-degree coherence producer on `S' = S = S₁(d)`.
  exact OddOrder.Peterfalvi.S07.coherent_subset_of_constant_degree hyp'
    (subset_refl _) hyp'.conjugate_closed hSfin h2 hirr hZIrr hconst hdeg0 h1A hsuppdiff

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Honest §9 character data on `S`** (issue 2035 step 3): the `mkSection11CharacterDataS`
mirror with the *genuine* coherence inputs — `tau := Ind_S^G` (`indS`, Peterfalvi (13.2.e)) and
`H0CprimeSupport := (C')^#` (`cprimeSharpS`, the `S`-instance degeneration of `(H₀ ⊔ C')^#` via
`H₀ = ⊥`) — instead of the `∅`/`tauS` degree-only placeholders.  Fed to `coherent_H0C_commutator`
to extract the coherent extension `τ₁` (the (13.2.d)⇐(9.11) route to the (13.3) `τ₁`-fields).  `u`
and `u_eq_card_quotient` are unchanged (rfl-pinned to the `U`-action image, as in the placeholder). -/
noncomputable def Hypothesis.mkSection11CharacterDataS_honest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      ((hyp.toTypesIIIIIIVSetupS hG).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)).subtype).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := hyp.cprimeSharpS
  tau := hyp.indS
  quotientSemidirectFrobenius := True

open scoped FiniteInduce in
/-- **(9.11)-coherence of the honest `S`-instance §9 data** (issue 2035 step 4).  Applies the
(6.8)-wired `coherent_H0C_commutator` (via the §14-gated `sibleyTarget_H0C`) to the honest
character data (`mkSection11CharacterDataS_honest`), yielding `IsCoherent Ind_S^G 𝒮 (C')^#` — the
Peterfalvi (13.2.d)⇐(9.11) coherence for `S(H₀C')` with the genuine Dade map `τ = Ind_S^G` and
support `(C')^#`.  The only gap is `sibleyTarget_H0C` (§14 structural witness, sorried-cite). -/
noncomputable def Hypothesis.coherent_H0Cprime_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IsCoherent (hyp.mkSection11CharacterDataS_honest hG chief).tau
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport :=
  OddOrder.Peterfalvi.S11.coherent_H0C_commutator (hyp.mkSection11CharacterDataS_honest hG chief)

open scoped FiniteInduce in
/-- **The coherent extension `τ₁` for the honest `S`-instance** (issue 2035 step 4): the
`.extension` of the (9.11)-coherence `coherent_H0Cprime_S`.  This is the (13.2.d) `τ₁ :
IntegralCharacterMap ↥S G` that the (13.3) degree analysis threads (the `μ_j^{τ₁}` machinery).
Sorried-cite via `sibleyTarget_H0C` (§14). -/
noncomputable def Hypothesis.tau1S_ofHonest [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G :=
  (hyp.coherent_H0Cprime_S hG chief).extension

open scoped FiniteInduce in
/-- **Type-alignment probe for the (13.3) `τ₁` route** (issue 2035 step 4 verification): confirms
`coherent_H0Cprime_S` obtains and its `.extension` is definitionally `tau1S_ofHonest`, of the
expected `IntegralCharacterMap ↥S G` type; and that `extends_on_supported` gives
`τ₁ φ = Ind_S^G φ` on the supported span (`tau1S_apply_induce` on the family) — the input to the
(13.3) `tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` fields. -/
theorem Hypothesis.tau1S_ofHonest_extends_on_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (φ : ClassFunction ↥hyp.S ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.mkSection11CharacterDataS_honest hG chief).S
      (hyp.mkSection11CharacterDataS_honest hG chief).H0CprimeSupport) :
    hyp.tau1S_ofHonest hG chief φ = ClassFunction.induce hyp.S φ := by
  have h := (hyp.coherent_H0Cprime_S hG chief).extends_on_supported φ hφ
  -- `.extension φ = chars.tau φ = indS φ = Ind_S^G φ`
  simpa [Hypothesis.tau1S_ofHonest, Hypothesis.mkSection11CharacterDataS_honest,
    Hypothesis.indS_apply] using h

set_option linter.unusedFintypeInType false in
/-- **Constituent kernel step for (1.5.a)** (Coq `S1cases` inner kernel argument), stated
generically.  For subgroups `P0, K'` of a finite group `Γ`, an irreducible `s ∈ Irr(Γ)`, and an
irreducible `θ'` of `K'` with `P0.subgroupOf K' ⊄ ker θ'`: if `θ'` is a constituent of
`Res_{K'} s` (`⟨θ', Res_{K'} s⟩ ≠ 0`), then `P0 ⊄ ker s`.

**Contrapositive.**  `P0 ⊆ ker s` makes `Res_{K'} s` trivial on `P0.subgroupOf K'`
(`characterKernel_restrict_subgroupOf`); `θ'`, a constituent of the genuine character `Res_{K'} s`
(`isCharacter_restrict`), inherits the containment
(`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), so `P0.subgroupOf K' ⊆ ker θ'`,
contradicting the hypothesis.  This is the `S`-instance analogue of the leaf
`PrimeTIResidue.constituent_P_not_subset_ker`, grounded on the honest `S'`-family — no
`PrimeTIResidueData` and no prime-TI dichotomy is used. -/
private theorem constituent_P_not_subset_characterKernel {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] (P0 K' : Subgroup Γ) [Fintype ↥K']
    [Invertible (Nat.card ↥K' : ℂ)]
    (θ' : ClassFunction ↥K' ℂ)
    (hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθ'P : ¬ ((P0.subgroupOf K' : Set ↥K') ⊆ OddOrder.Peterfalvi.S03.characterKernel θ'))
    (s : OddOrder.RepresentationTheory.IrreducibleCharacter Γ)
    (hs : ClassFunction.inner θ' (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) ≠ 0) :
    ¬ ((P0 : Set Γ) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction Γ ℂ)) := by
  intro hker
  have hResChar : IsCharacter (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter K'
  have hinner' : ClassFunction.inner
      (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) θ' ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    exact star_ne_zero.mpr hs
  have hResker : ((P0.subgroupOf K') : Set ↥K') ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.restrict K' (s : ClassFunction Γ ℂ)) :=
    OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf K' hker
  exact hθ'P fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hθ'irr hinner' (hResker hx)

open scoped FiniteInduce in
/-- **Peterfalvi (13.5) preamble / (1.5.a) — the family membership `Ind_{PC}^S θ ∈ ℤ[𝒮]`**
(issue 2035 step 5a).

For an irreducible character `θ` of `H = PC` **whose kernel does not contain `P`**, the induced
character `Ind_{PC}^S θ` lies in `ℤ[𝒮]` (`zSpan` of the honest §9 family `𝒮 = sSet`).  In
Coq's `PFsection13` this is `sS1S : {subset calS1 <= 'Z[calS]}` (with `calS1 = seqIndD H S P 1`,
`calS = seqIndD PU S P 1`), used implicitly throughout (13.5)–(13.8).

**Honest proof, grounded on the S06 §4 residue theory** (issue 9014 session 8).  The family
`𝒮 = sSet = {Ind_{S'}^S χ | χ ∈ Irr(S'), P ⊄ ker χ}` is *exactly* the set of inductions
from the derived subgroup `S' = huSub` of `P`-nonlinear irreducibles (`P = data.H`), so **membership
is by witness** — no dichotomy on the induced character is needed.  Writing the single-stage
`Ind_{PC}^S θ` as the two-stage `Ind_{S'}^S (Ind_{PC'}^{S'} θ')` (`induce_induce_subgroupOf`, with
`PC' = (PC).subgroupOf S'` and `θ'` the transport of `θ`) and expanding the inner induction into
`S'`-constituents `Ind_{PC'}^{S'} θ' = ∑_{s ∈ Irr(S')} ⟨θ', Res s⟩ • s`
(`induce_eq_sum_inner_restrict_smul`), each constituent `s` with nonzero (necessarily `ℕ`)
coefficient has `P ⊄ ker s` (`constituent_P_not_subset_characterKernel`), so `Ind_{S'}^S s`
lies in `sSet` by witness `s`; the coefficient-weighted `ℤ`-sum lands in `zSpan sSet`.  This
grounds the family
membership on the proven S06 setup (`typePData_toS06Hypothesis` for `S` supplies the certain-type
Hypothesis, though only its `S'`-family shape is needed here); no prime-TI residue dichotomy is used. -/
theorem Hypothesis.induce_H_mem_zSpan_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∈
      OddOrder.Peterfalvi.S07.zSpan (hyp.mkSection11CharacterDataS_honest hG chief).S := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- Target family is `sSet data` with `data = toTypesIIIIIIVSetupS hG`.
  rw [OddOrder.Peterfalvi.S11.Section11CharacterData.S_eq]
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  -- Work with the §9 induction carrier `HU = huSub data`, equal to `S' = derivedInG S` in `↥S`.
  set HU : Subgroup ↥hyp.S := OddOrder.Peterfalvi.S11.huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf data
  letI : Fintype ↥HU := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥HU : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `PC = H.subgroupOf S ≤ S' = HU`.
  have hHderiv : hyp.H ≤ derivedInG hyp.S := by
    show hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hKle : hyp.H.subgroupOf hyp.S ≤ HU := by
    rw [hHUeq]; exact Subgroup.subgroupOf_mono hyp.S hHderiv
  letI : Fintype ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The transport `θ' = θ ∘ e` of `θ` onto `PC' = (PC).subgroupOf HU ≤ HU`.
  have hθ'irr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hKle).surjective hθ
  -- Two-stage induction: `Ind_{PC}^S θ = Ind_{HU}^S (Ind_{PC'}^{HU} θ')`.
  rw [← OddOrder.RepresentationTheory.induce_induce_subgroupOf hKle θ]
  -- Expand the inner induction into `HU`-constituents and push `Ind_{HU}^S` inside.
  rw [OddOrder.RepresentationTheory.induce_eq_sum_inner_restrict_smul
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ),
    ClassFunction.induce_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [ClassFunction.induce_smul]
  -- The coefficient `⟨θ', Res s⟩` is a non-negative integer `(k : ℂ)`.
  have hResChar : IsCharacter (ClassFunction.restrict
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU) (s : ClassFunction ↥HU ℂ)) :=
    OddOrder.Peterfalvi.S08.isCharacter_restrict s.isIrreducible.isCharacter _
  obtain ⟨k, hk⟩ := hResChar.exists_natCast_inner_irreducible hθ'irr
  have hc : ClassFunction.inner
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
      (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
        (s : ClassFunction ↥HU ℂ)) = (k : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hk, star_natCast]
  rw [hc, Nat.cast_smul_eq_nsmul ℂ k (ClassFunction.induce HU (s : ClassFunction ↥HU ℂ))]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · refine nsmul_mem ?_ k
    -- `P (in HU) ⊄ ker s`: kernel step from `P ⊄ ker θ'` (from `hθP`) and constituent `θ'`.
    have hθ'P : ¬ ((((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
          ((hyp.H.subgroupOf hyp.S).subgroupOf HU) :
        Set ↥((hyp.H.subgroupOf hyp.S).subgroupOf HU)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)) := by
      rw [OddOrder.RepresentationTheory.subset_characterKernel_compHom_iff]
      -- The image of `((P.subgroupOf S).subgroupOf HU).subgroupOf (PC.subgroupOf HU)` under `e`
      -- is `(P.subgroupOf S).subgroupOf (PC.subgroupOf S)`, which `hθP` does not kill.
      have himg : (((hyp.P.subgroupOf hyp.S).subgroupOf HU).subgroupOf
            ((hyp.H.subgroupOf hyp.S).subgroupOf HU)).map
            (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          = (hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) := by
        ext y
        rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        rfl
      rw [himg]; exact hθP
    refine Submodule.subset_span ?_
    rw [OddOrder.Peterfalvi.S11.mem_sSet]
    refine ⟨s, ?_, rfl⟩
    -- `s ∈ xiSet data`: `hInHu data ⊄ ker s`, with `hInHu = (P.subgroupOf S).subgroupOf HU`.
    show ¬ ((OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (s : ClassFunction ↥HU ℂ))
    have hHInHu : (OddOrder.Peterfalvi.S11.hInHu data : Set ↥HU)
        = ((hyp.P.subgroupOf hyp.S).subgroupOf HU : Set ↥HU) := by
      congr 1
      show (data.H.subgroupOf hyp.S).subgroupOf HU = (hyp.P.subgroupOf hyp.S).subgroupOf HU
      have hPeq : data.H = hyp.P := by
        show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
      rw [hPeq]
    rw [hHInHu]
    -- The generic kernel step: `θ'` is a constituent of `Res s` (coefficient `k > 0`), and
    -- `P (in HU) ⊄ ker θ'` (`hθ'P`), so `P (in HU) ⊄ ker s`.
    have hs : ClassFunction.inner
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ)
        (ClassFunction.restrict ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
          (s : ClassFunction ↥HU ℂ)) ≠ 0 := by
      rw [hc]; exact_mod_cast hk0.ne'
    exact constituent_P_not_subset_characterKernel ((hyp.P.subgroupOf hyp.S).subgroupOf HU)
      ((hyp.H.subgroupOf hyp.S).subgroupOf HU)
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom θ) hθ'irr hθ'P s hs

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ isometry on the `H`-induced family** (issue 2035 step 5a): `τ₁ = tau1S_ofHonest`
preserves inner products of `Ind_{PC}^S θ` for irreducible `θ` of `H = PC` with `P ⊄ Ker θ`.  From
the coherence field `extension_inner_eq` (isometric on all of `ℤ[𝒮]`) together with the family
membership `induce_H_mem_zSpan_S`.  This is the honest engine for the `CharacterDegreeData`
`tau1S_inner_induce` field (with the `P ⊄ Ker` hypothesis the (13.3) consumers actually satisfy —
`μ_j`, `λ` all have `P ⊄ Ker`). -/
theorem Hypothesis.tau1S_ofHonest_inner_induce [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθ' : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ')
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hθ'P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ')) :
    ClassFunction.inner
        (hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
        (hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
      = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ') := by
  exact (hyp.coherent_H0Cprime_S hG chief).extension_inner_eq _ _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)
    (hyp.induce_H_mem_zSpan_S hG chief θ' hθ' hθ'P)

open scoped FiniteInduce in
/-- **(13.2.d) τ₁ sends the `H`-induced family into `ℤ[Irr G]`** (issue 2035 step 5a): for
irreducible `θ` of `H = PC` with `P ⊄ Ker θ`, `τ₁ (Ind_{PC}^S θ) ∈ ℤ[Irr G]`.  From the coherence
field `extension_mem_ZIrr` (virtual-character codomain on all of `ℤ[𝒮]`) and the family membership
`induce_H_mem_zSpan_S`.  Honest engine for the `CharacterDegreeData` `tau1S_induce_mem_ZIrr` field. -/
theorem Hypothesis.tau1S_ofHonest_induce_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    hyp.tau1S_ofHonest hG chief (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G :=
  (hyp.coherent_H0Cprime_S hG chief).extension_mem_ZIrr _
    (hyp.induce_H_mem_zSpan_S hG chief θ hθ hθP)

/-- **Peterfalvi (13.2.b), order part**: the Fitting kernel `P = S_F` has order `p^q`.

This is the order half of (13.2.b) ("`P` is elementary abelian of order `p^q`").  `S` is of Type II
from the κ-Hall carrier `S_typeP2` (`isTypeII_of_isTypeP2`), so §11's Wielandt fixed-point order
relation `typeII_III_IV_order_relations` (Peterfalvi (9.3)) applies to the type-II setup on `S` with
`typeP := Sdata`, giving `|S_F| = |W₂|^q`.

The one input not derivable from the bare `Hypothesis` fields is the reconciliation `Sdata.W2 = W2`
between the *intrinsic* type-`P` `W₂` of `S` (`Sdata.W2 = C_{S'}(W₁#)`) and the abstract `W₂`
(complement of `W₁` in the cyclic `W = S ∩ T`) — the `W₂`-analogue of the carried
`Sdata_U_eq` / `Sdata_W1_eq`.  It is honest §16-carrier content (`Section16TypePStructure`, which
builds `Sdata`); taken here as an explicit hypothesis so the order computation is unconditional on
its proof.  See issue 3001 for threading it through the carrier (then `basic_structure_gated`'s
`P_order` field discharges). -/
theorem Hypothesis.card_P_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hSdataW2 : hyp.Sdata.W2 = hyp.W2) :
    Nat.card ↥hyp.P = hyp.p ^ hyp.q := by
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  -- (9.3) Wielandt order relation for the type-II setup on `S` (`toTypesIIIIIIVSetupS`).
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    (hyp.toTypesIIIIIIVSetupS hG)).1 hSII
  have hord2 : Nat.card ↥hyp.Sdata.H
      = Nat.card ↥hyp.Sdata.W2 ^ Nat.card ↥hyp.Sdata.W1 := hord.2
  have hW2card : Nat.card ↥hyp.Sdata.W2 = hyp.p := by
    rw [hSdataW2, ← hyp.p_eq_card_W2]
  rw [hyp.Sdata.H_eq, ← hyp.P_eq_SF, hW2card, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at hord2
  exact hord2

/-- **The `S`-instance chief kernel `N` is trivial**: `P = S_F` has order `p^q`
(`card_P_eq`), and the chief factor `H̄ = P/H₀ ≅ ↥P ⧸ N` already has order `(chief.p)^q`
(`chiefFactor_quotient_card`), so `chief.p = p` and `|N| = 1`, i.e. `N = ⊥`.  Thus `↥P ⧸ N ≅ ↥P`
— `P` itself is the chief factor.  The source of both `H₀ = ⊥` (below) and `cSub = C_U(P) = C`
(the `C_U(H̄) = C_U(P)` identification once `H̄ = P`). -/
theorem Hypothesis.toTypesIIIIIIVSetupS_chief_N_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.N = ⊥ := by
  haveI := chief.N_normal
  have hHeq : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    show hyp.Sdata.H = hyp.P
    rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    show Nat.card ↥hyp.Sdata.W1 = hyp.q
    rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [show ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P from hHeq]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hq] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  -- `p^q = chief.p^q · |N|` forces `chief.p = p` and `|N| = 1`
  have hdvd : chief.p ∣ hyp.p ^ hyp.q := by
    refine dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.p :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  rw [hpp] at hsplit
  have hN1 : Nat.card ↥chief.N = 1 := by
    have := hsplit.symm
    nlinarith [Nat.card_pos (α := ↥chief.N), pow_pos hyp.p_prime.pos hyp.q]
  exact Subgroup.card_eq_one.mp hN1

/-- **The `S`-instance chief `H₀` is trivial** (`toTypesIIIIIIVSetupS_chief_N_eq_bot`, mapped):
`H₀ = N.map subtype = ⊥`.  Collapses the §9 families of the `S`-instance (`𝒳(H₀) = 𝒳(⊥)`), making
the (13.3.a) kernel condition `H₀ ⊆ Ker χ_j` automatic. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_chief_H0_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.H0 = ⊥ := by
  rw [chief.H0_eq, hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief]
  exact Subgroup.map_bot _

/-- **Peterfalvi (13.2.b)/(11.7) for the `S`-instance**: `P = S_F` is elementary abelian of
exponent `p`.  Assembled from the §11 chief-factor data of `S` (`exists_chiefFactorData` on
`toTypesIIIIIIVSetupS`): the chief kernel `N = ⊥` (`toTypesIIIIIIVSetupS_chief_N_eq_bot`), so
`P/⊥ ≅ P` *is* the chief factor and carries `ChiefFactorData.quotient_elementaryAbelian` at the
chief prime `chief.p = p` (forced by `|P| = p^q`).  **Ungated** — the `S`-instance `H₀ = ⊥` is
proven (`P` itself is the chief factor), unlike the generic sorried `chief_H0_eq_bot`.  Discharges
`basic_structure_gated.P_elementaryAbelian`. -/
theorem Hypothesis.P_elementaryAbelian [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsElementaryAbelian hyp.p ↥hyp.P := by
  classical
  obtain ⟨chief, _⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
    show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hN : chief.N = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief
  -- `chief.p = p` from `|P| = p^q = chief.p^q · |N|` with `|N| = 1`.
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    show Nat.card ↥hyp.Sdata.W1 = hyp.q; rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hq] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  have hdvd : chief.p ∣ hyp.p ^ hyp.q := by
    refine dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.p :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  -- Transport `quotient_elementaryAbelian` along `↥H ⧸ ⊥ ≃* ↥H`, then rewrite `H = P`.
  have hEA : IsElementaryAbelian hyp.p ↥(hyp.toTypesIIIIIIVSetupS hG).H := by
    have h := chief.quotient_elementaryAbelian
    rw [hpp] at h
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
  rwa [hHeq] at hEA

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **`C_U(H̄) = C`** for the `S`-instance: the §9 kernel `cSub` (`= C_U(H̄)`) equals Peterfalvi's
`C = C_U(P) = U ⊓ C_G(P)`.  The reverse `C ≤ cSub` is general (an element of `U` centralizing
`H = P` acts trivially on any quotient of `H`, so lies in the action kernel); the forward
`cSub ≤ C` uses `H₀ = ⊥` (`toTypesIIIIIIVSetupS_chief_H0_eq_bot`): with `H̄ = P/H₀ = P` the kernel
`cSub` centralizes `H = P` (`⁅cSub, H⁆ ≤ H₀ = ⊥`, `commutator_cSub_H_le_H0`).  This is the
last spelling piece of the (13.3.a) `μ_j = Ind_{PC}(linear)`: `HC = P·C = P·cSub`. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_cSub_eq_C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief = hyp.C := by
  haveI := hyp.finiteG
  haveI := chief.N_normal
  have hUeq : (hyp.toTypesIIIIIIVSetupS hG).U = hyp.U := hyp.Sdata_U_eq
  have hHeq : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  apply le_antisymm
  · -- forward: `cSub ≤ U ⊓ C_G(P)`
    rw [hyp.C_eq]
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨hUeq ▸ OddOrder.Peterfalvi.S11.cSub_le_U _ chief hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    -- `⁅cSub, H⁆ ≤ H₀ = ⊥`, so `g` centralizes `H = P`
    have hcomm : ⁅OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief,
        (hyp.toTypesIIIIIIVSetupS hG).H⁆ ≤ ⊥ := by
      rw [← hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief]
      exact OddOrder.Peterfalvi.S11.commutator_cSub_H_le_H0 _ chief
    have hpH : p ∈ (hyp.toTypesIIIIIIVSetupS hG).H := hHeq ▸ hp
    have hcm := hcomm (Subgroup.commutator_mem_commutator hg hpH)
    rw [Subgroup.mem_bot, commutatorElement_def] at hcm
    -- `g p g⁻¹ p⁻¹ = 1 ⟹ p g = g p`
    have hpg : g * p * g⁻¹ = p := by
      have h1 : g * p * g⁻¹ * p⁻¹ * p = p := by rw [hcm, one_mul]
      rwa [inv_mul_cancel_right] at h1
    have hgp : g * p = p * g := by
      have h2 : g * p * g⁻¹ * g = p * g := by rw [hpg]
      rwa [inv_mul_cancel_right] at h2
    exact hgp.symm
  · -- reverse: `U ⊓ C_G(P) ≤ cSub`
    rw [hyp.C_eq]
    intro g hg
    obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgUdata : g ∈ (hyp.toTypesIIIIIIVSetupS hG).U := hUeq ▸ hgU
    have hgUW1 : g ∈ (hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔
        (hyp.toTypesIIIIIIVSetupS hG).typeP.W1 :=
      (le_sup_left : (hyp.toTypesIIIIIIVSetupS hG).typeP.U ≤ _) hgUdata
    set bUW1 : ↥((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔
        (hyp.toTypesIIIIIIVSetupS hG).typeP.W1) := ⟨g, hgUW1⟩ with hbUW1def
    have hbUW1mem : bUW1 ∈ ((hyp.toTypesIIIIIIVSetupS hG).typeP.U).subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1) :=
      Subgroup.mem_subgroupOf.mpr hgUdata
    -- `bUW1` acts trivially on `H̄`: `g` centralizes `H = P`
    have haut : quotientMulAutHom chief.N_aInvariant bUW1 = 1 := by
      ext q
      refine QuotientGroup.induction_on q ?_
      intro x
      rw [OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply
        chief.N_aInvariant bUW1 x, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [OddOrder.Peterfalvi.S11.typeP_conjAction_apply]
      have hxP : ((x : G)) ∈ hyp.P := hHeq ▸ x.2
      have hcx : g * (x : G) = (x : G) * g :=
        (Subgroup.mem_centralizer_iff.mp hgC (x : G) hxP).symm
      show (bUW1 : G) * (x : G) * (bUW1 : G)⁻¹ = (x : G)
      rw [hbUW1def]
      show g * (x : G) * g⁻¹ = (x : G)
      rw [hcx]; group
    have hbker : (⟨bUW1, hbUW1mem⟩ : ↥(((hyp.toTypesIIIIIIVSetupS hG).typeP.U).subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)))
        ∈ (OddOrder.Peterfalvi.S11.uActionHom (hyp.toTypesIIIIIIVSetupS hG) chief).ker := by
      rw [MonoidHom.mem_ker, OddOrder.Peterfalvi.S11.uActionHom, MonoidHom.comp_apply]
      exact haut
    -- assemble `g ∈ cSub`
    simp only [OddOrder.Peterfalvi.S11.cSub, Subgroup.mem_map]
    exact ⟨bUW1, ⟨⟨bUW1, hbUW1mem⟩, hbker, rfl⟩, rfl⟩



/-- **Peterfalvi (13.2.b,c,e)** structural producer: the `M_F`-structure of the type-`P₂` member
`S`.  Faithful obligation on the §16 σ-structure (`BasicStructureGated` docstring).

`U_commutative` (13.2.a U-side) and `P_order` (13.2.b order part) are now **genuine**:
* `U_commutative` from the carried `S_U_commutative` (BG Lemma 15.1(b) `typeP_hall_derived_eq_and_abelian`, `U` the `(κ∪σ)'`-Hall, supplied at construction);
* `P_order` = `|P| = p^q` from `card_P_eq` fed by the carried `Sdata_W2_eq` (the intrinsic dual factor `Sdata.W2 = C_{S'}(W₁#)` equals the abstract `W₂ = K*`, via `typePData_of_kappaHall_hallComplement_W2`).

The `A_0(S)`/`τ_S` clauses are the opaque scaffold Props (`True`).  The two remaining concrete
residuals are the genuinely upstream σ-structure facts:
* `P_elementaryAbelian` — Pf (11.7) = `S13_MaximalIII_IV.H_elementaryAbelian` (lane a §11);
* `u_bound` — Pf (9.7) Singer-field bound `u ∣ (p^q−1)/(p−1)` (lane a §9). -/
noncomputable def basic_structure_gated [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : BasicStructureGated hyp where
  U_commutative := hyp.S_U_commutative
  P_elementaryAbelian := hyp.P_elementaryAbelian hG
  P_order := hyp.card_P_eq hG hyp.Sdata_W2_eq
  u_bound := sorry
  A0S_TI := True
  A0S_TI_holds := trivial
  tauS_eq_induction := True
  tauS_eq_induction_holds := trivial

/-- **Peterfalvi (13.2.a--c,e)**: `S` is type II or III, `P` is elementary
abelian of order `p^q`, `u` is bounded, and `A_0(S)` is a TI-subset.

The **type determination** (13.2.a) is discharged `sorry`-free from the §16 carrier `S_typeP2`
(`isTypeII_of_isTypeP2`): `S` is type II, hence the `IsTypeII ∨ IsTypeIII` and `q < p → IsTypeII`
fields hold with the type-II side.  The remaining `M_F`-structure data (13.2.b,c,e) is read off the
faithful §16-gated producer `basic_structure_gated`. -/
theorem basic_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : BasicStructureData hyp,
      (IsTypeII hyp.S ∨ IsTypeIII hyp.S) ∧ IsElementaryAbelian hyp.p ↥hyp.P ∧
        Nat.card ↥hyp.P = hyp.p ^ hyp.q ∧
        hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ∧ data.A0S_TI := by
  -- (13.2.a) type determination: `S` is type II, sorry-free from the carrier `S_typeP2`.
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 _hG hyp.S_maximal hyp.S_typeP2
  -- `U ≠ ⊥`: the carrier `Sdata.U` has the same order as the type-II witness's `typeP.U`
  -- (`card_U_eq_index = [M' : M_F]`), and the latter is `≠ ⊥` (`TypePNontrivialCore`).
  have tdata : TypeIIData hyp.S := hSII.some
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  -- (13.2.a) `U W₁` Frobenius: sorry-free from the carrier `Sdata` (`typeP_uW1_frobenius`,
  -- reconciled `Sdata.U = U`, `Sdata.W1 = W1`).
  have hUW1frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.U ⊔ hyp.W1) (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
        (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    rwa [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at h
  -- (13.2.b,c,e) `M_F`-structure: the localized faithful §16 producer.
  let core := basic_structure_gated _hG hyp
  refine ⟨{ S_typeII_or_typeIII := Or.inl hSII
            q_lt_p_forces_typeII := fun _ => hSII
            U_commutative := core.U_commutative
            UW1_frobenius := hUW1frob
            P_elementaryAbelian := core.P_elementaryAbelian
            P_order := core.P_order
            u_bound := core.u_bound
            A0S_TI := core.A0S_TI
            A0S_TI_holds := core.A0S_TI_holds
            tauS_eq_induction := core.tauS_eq_induction
            tauS_eq_induction_holds := core.tauS_eq_induction_holds }, ?_⟩
  exact ⟨Or.inl hSII, core.P_elementaryAbelian, core.P_order, core.u_bound, core.A0S_TI_holds⟩

/-- **Structural input for Peterfalvi (13.2.d) — ⚠ VESTIGIAL, do not complete as stated**
(hub ruling 2026-07-02; provenance: closed issues 1004/4014).

The S-side maximal-coherent Dade route (`tauS`/`Sset`/`A0S`) is **off the FT path**: the §13/§16
contradiction is routed through the W-side grid `eta = tau3 ∘ omega` and the carrier supplies
`tauS = 0` as a placeholder, so nothing on the spine consumes this witness.  Building it as
stated would prove an unconsumed S-side statement.  Anyone touching the (13.5)–(13.9) cascade
must first restate it W-side or retire it — see the 2026-07-02 hub section of
`notes/peterfalvi/s16_w4_char_cascade.md` (and note (6.8) `S08.sibleySetup_is_coherent` itself
is already proven; the old "once lane B supplies (6.8)" framing is obsolete). -/
noncomputable def sibleyTarget_S [Fintype G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) [Fintype ↥hyp.S]
    [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)] :
    CoherenceWiring.SibleyTarget hyp.tauS hyp.Sset hyp.A0S := sorry

/-- **Peterfalvi (13.2.d)**: the family `S` is coherent — ⚠ VESTIGIAL endpoint (0 spine cites).

Wired to the proven (6.8) capstone `S08.sibleySetup_is_coherent` through the coherence-wiring
bridge; the only gap is `sibleyTarget_S`, which is ruled **do-not-complete-as-stated** (see its
docstring — the spine routes through the W-side `eta` grid, `tauS = 0` placeholder).  Kept for
statement fidelity to Pf (13.2.d); do not invest proof effort here. -/
theorem S_coherent [Finite G] [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) [Fintype ↥hyp.S]
    [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tauS hyp.Sset hyp.A0S) :=
  CoherenceWiring.coherent_of_sibleyTarget (sibleyTarget_S hG hyp)

/-! ## (13.3)--(13.4): character degrees and the first case split -/

open scoped Classical in
/-- **The `μ`-column sums are reducible** ((13.3.a) entry condition): `μ_j = ∑_i μ_{ij}` is a
sum of `q ≥ 2` *distinct* irreducible characters (`mu_irreducible`, `mu_col_injective`), so its
norm is `q ≠ 1` — not an irreducible character.  This is the membership shape that puts `μ_j`
among the `p − 1` reducible members of `𝒮(H₀)` in the §9 analysis (Pf (9.8.b)/(9.9.b)). -/
theorem Hypothesis.mu_colSum_not_irreducible [Finite G] (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) :
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter (∑ i : Fin hyp.q, hyp.mu i j) := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro hirr
  set a : Fin hyp.q → OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S :=
    fun i => ⟨hyp.mu i j, hyp.mu_irreducible i j⟩ with ha
  have hcond : ∀ i i' : Fin hyp.q, a i = a i' ↔ i = i' := by
    intro i i'
    constructor
    · intro h
      exact hyp.mu_col_injective j (congrArg
        (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
          (χ : ClassFunction ↥hyp.S ℂ)) h)
    · rintro rfl
      rfl
  have hinner : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i j)
      (∑ i : Fin hyp.q, hyp.mu i j) = (hyp.q : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ i : Fin hyp.q, ClassFunction.inner (hyp.mu i j) (∑ i' : Fin hyp.q, hyp.mu i' j)
        = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q, ClassFunction.inner (hyp.mu i j) (hyp.mu i' j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q, if i = i' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
          have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
            (a i) (a i')
          rw [ha] at hite
          exact hite.trans (if_congr (hcond i i') rfl rfl)
      _ = ∑ _i : Fin hyp.q, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp
      _ = (hyp.q : ℂ) := by simp
  have h1 : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i j)
      (∑ i : Fin hyp.q, hyp.mu i j) = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨∑ i : Fin hyp.q, hyp.mu i j, hirr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (⟨∑ i : Fin hyp.q, hyp.mu i j, hirr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
    simpa using hite
  rw [hinner] at h1
  have : hyp.q = 1 := by exact_mod_cast h1
  exact hyp.q_prime.one_lt.ne' this

open scoped FiniteInduce in
/-- Character-degree and Dade-extension data from Peterfalvi (13.3).

W-side restate (issue 2034, hub 裁定 2026-07-02 §2): the former `lambda_mem : lambda ∈ hyp.Sset`
field is dropped — the spine supplies the vestigial `Sset := ∅`, which made this structure
uninhabited at the consuming instantiation (`character_degree_analysis` unprovable).  The
formerly opaque `Prop` fields `lambda_irreducible`/`lambda_induced_from_PC_linear` are
materialized as their honest statements (Pf (13.3.b): `λ` is an irreducible character of `S` of
degree `uq` induced from a linear character of `H = PC`). -/
structure CharacterDegreeData (hyp : Hypothesis (G := G)) where
  tau1S : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G
  tau1T : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G
  lambda : ClassFunction ↥hyp.S ℂ
  lambda_irreducible : OddOrder.RepresentationTheory.IsIrreducibleCharacter lambda
  lambda_degree : lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ)
  lambda_induced_from_PC_linear :
    haveI := hyp.finiteG
    ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        lambda = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
        ∃ x : ↥(hyp.H.subgroupOf hyp.S), ((x : ↥hyp.S) : G) ∈ hyp.P ∧
          x ∉ OddOrder.Peterfalvi.S03.characterKernel θ
  /-- **(13.2.e)+(7.2), τ₁-extension semantics** (issue 2034): on zero-degree differences of
  `H`-induced irreducibles (the (7.6)-family lattice `ℤ[𝒮₁, H^#]`), `τ₁` agrees with the Dade
  isometry, which is `Ind_S^G` (the `A₀(S)` TI-subset makes `τ = Ind`). -/
  tau1S_apply_induce_sub :
    haveI := hyp.finiteG
    ∀ θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ' →
      tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
          - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
        = ClassFunction.induce hyp.S
            (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
              - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
  /-- **The τ₁ coherence isometry on the induced family** (issue 2034): `τ₁` preserves inner
  products of `H`-induced irreducibles ((13.2.d)-extension isometry restricted to `𝒮₁`). -/
  tau1S_inner_induce :
    haveI := hyp.finiteG
    ∀ θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ' →
      ClassFunction.inner (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
          (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
        = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
            (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
  /-- **τ₁ sends family members to virtual characters** (issue 2034). -/
  tau1S_induce_mem_ZIrr :
    haveI := hyp.finiteG
    ∀ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G
  /-- **Peterfalvi (13.3.a)+(13.3.c), the distinguished `μ`-column** (issue 2035/(13.9.a)): there
  is a column `j` whose sum `μ_j = ∑_i μ_{ij}` is induced from a linear character of `H = PC`
  (13.3.a) and whose `τ₁`-image is `±∑_i η_{i1}` — the (13.3.c) formula routed to the `η`-column
  `1` (`j = 1, δ = 1` normally; the `p = 3` sign-flip exception gives `δ = -1`).  What (13.9.a)
  reads: `λ^{τ₁}` agrees with `δ ∑_i η_{i1}` on `G₀` through `Ind(μ_j − λ)`-vanishing. -/
  mu_col_tau1_eta_col_one :
    haveI := hyp.finiteG
    ∃ (j : Fin hyp.p) (δ : ℤ) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      (δ = 1 ∨ δ = -1) ∧
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
      (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
      tau1S (∑ i : Fin hyp.q, hyp.mu i j)
        = (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩
  /-- **Peterfalvi (4.1)+(5.3.b): the `η`-grid is orthogonal to the τ₁-image of the induced
  family** (issue 2034): the coherence extension lands in the orthogonal complement of the
  `σ`-image grid.  With the (3.2.d) completeness (`vanish_of_inner_eta_eq_zero`) this forces
  `λ^{τ₁}` to vanish on the regular set `Ŵ` (`lambda_tau1_apply_mul_eq_zero`). -/
  tau1S_induce_inner_eta :
    haveI := hyp.finiteG
    ∀ (i : Fin hyp.q) (j : Fin hyp.p) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ClassFunction.inner (hyp.eta i j)
        (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0
  /-- **Peterfalvi (13.3.a)** (materialized, issue 2034): every nonzero column sum
  `μ_j = ∑_i μ_{ij}` is induced from a linear character of `H = PC` (hence of degree
  `uq = [S : H]`). -/
  mu_j_linear_induced :
    haveI := hyp.finiteG
    ∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
          (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
  /-- **Peterfalvi (13.3.c)**: the signs `δ_j`, `δ'_i` of (13.1.e) are all equal
  to `1` (materialized as a concrete statement about `delta`/`deltaPrime`). -/
  delta_eq_one : (∀ j : Fin hyp.p, hyp.delta j = 1) ∧ (∀ i : Fin hyp.q, hyp.deltaPrime i = 1)
  /-- **Peterfalvi (13.3.c)** (materialized, issue 2034): the `τ₁`-images of the nonzero
  column sums are the `η`-column sums — either uniformly (`δ = 1`), or (`p = 3` sign-flip
  exception) with a negative sign and the columns `1, 2` swapped. -/
  mu_tau1_formula :
    (∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      tau1S (∑ i : Fin hyp.q, hyp.mu i j) = ∑ i : Fin hyp.q, hyp.eta i j) ∨
    (hyp.p = 3 ∧ ∀ j j' : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      j' ≠ ⟨0, hyp.p_prime.pos⟩ → j ≠ j' →
      tau1S (∑ i : Fin hyp.q, hyp.mu i j) = -∑ i : Fin hyp.q, hyp.eta i j')

/-- **Peterfalvi (13.3)**: the `mu_j` have degree `u q`, the signs are `1`,
and the `tau_1` images are controlled by the `eta_ij` grid. -/
theorem character_degree_analysis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (CharacterDegreeData hyp) := by
  sorry

open scoped FiniteInduce in
/-- **The `η`-grid is orthonormal** ((13.1.d) + (3.2)/(3.3), issue 9013 (13.4)-prep): the grid
`η_{ij} = ω_{ij}^{τ₃}` inherits the (3.3) orthonormality of the `ω`-grid through the (3.2)
isometry `τ₃`.  The bookkeeping input of the (13.4) cross-expansion. -/
theorem Hypothesis.eta_orthonormal [Finite G] (hyp : Hypothesis (G := G))
    (i k : Fin hyp.q) (j l : Fin hyp.p) :
    ClassFunction.inner (hyp.eta i j) (hyp.eta k l)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [hyp.eta_eq_tau_omega, hyp.eta_eq_tau_omega, hyp.tau3_isometry.inner_eq,
    hyp.omega_orthonormal]

/-- **Peterfalvi (13.4), inner-product endgame** (abstract bookkeeping, issue 9013 追記⁶ core (d)):
for an orthonormal grid `η` and vectors `λ°, θ°` orthogonal to each other and to every grid
member, `⟨λ° − δ·∑ᵢ η_{is}, θ° − δ'·∑ⱼ η_{rj}⟩ = δ·δ' ≠ 0` for signs `δ, δ' = ±1` — the only
surviving term of the bilinear expansion is the shared grid entry `⟨η_{rs}, η_{rs}⟩ = 1`.

In (13.4) the left side is `(α^τ, β^τ)` for `α = λ − μ_s ∈ ℤ[𝒮, H^#]`, `β = θ − ν_r ∈ ℤ[𝒯, K^#]`,
which *vanishes* because `(H^#)^G` and `(K^#)^G` are disjoint TI-supports — the contradiction
closing (13.4). -/
theorem eta_cross_expansion_ne_zero [Fintype G] [Invertible (Nat.card G : ℂ)] {q p : ℕ}
    (eta : Fin q → Fin p → ClassFunction G ℂ)
    (horth : ∀ (i k : Fin q) (j l : Fin p),
      ClassFunction.inner (eta i j) (eta k l) = if i = k ∧ j = l then 1 else 0)
    (lam theta : ClassFunction G ℂ) (r : Fin q) (s : Fin p)
    (hlam_eta : ∀ (i : Fin q) (j : Fin p), ClassFunction.inner lam (eta i j) = 0)
    (heta_theta : ∀ (i : Fin q) (j : Fin p), ClassFunction.inner (eta i j) theta = 0)
    (hlam_theta : ClassFunction.inner lam theta = 0)
    {δ δ' : ℤ} (hδ : δ = 1 ∨ δ = -1) (hδ' : δ' = 1 ∨ δ' = -1) :
    ClassFunction.inner (lam - (δ : ℂ) • ∑ i : Fin q, eta i s)
      (theta - (δ' : ℂ) • ∑ j : Fin p, eta r j) ≠ 0 := by
  have hgrid : ClassFunction.inner (∑ i : Fin q, eta i s) (∑ j : Fin p, eta r j) = 1 := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    have hrow : ∀ i : Fin q,
        ClassFunction.inner (eta i s) (∑ j : Fin p, eta r j)
          = if i = r then (1 : ℂ) else 0 := by
      intro i
      rw [OddOrder.RepresentationTheory.inner_sum_right]
      by_cases hir : i = r
      · subst hir
        simp only [horth]
        simp
      · simp only [horth]
        simp [hir]
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    simp
  have hexp : ClassFunction.inner (lam - (δ : ℂ) • ∑ i : Fin q, eta i s)
      (theta - (δ' : ℂ) • ∑ j : Fin p, eta r j) = (δ : ℂ) * (δ' : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_right, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_right, star_intCast, hlam_theta, hgrid]
    have hlam_sum : ClassFunction.inner lam (∑ j : Fin p, eta r j) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_sum_right]
      exact Finset.sum_eq_zero fun j _ => hlam_eta r j
    have hsum_theta : ClassFunction.inner (∑ i : Fin q, eta i s) theta = 0 := by
      rw [OddOrder.RepresentationTheory.inner_sum_left]
      exact Finset.sum_eq_zero fun i _ => heta_theta i s
    rw [hlam_sum, hsum_theta]
    ring
  rw [hexp]
  rcases hδ with rfl | rfl <;> rcases hδ' with rfl | rfl <;> norm_num

/-- **Peterfalvi (13.4), conjugate-disjointness core** (abstract form, issue 9013 追記⁶ core (d)):
if every point of `A_M ⊆ M` is centralized by `R`, every point of `A_N ⊆ N` has its centralizer
inside `N` (the TI-shape), and no conjugate of `R` fits inside `N`, then no element of `G` is
simultaneously conjugate into `A_M` and into `A_N`.

In (13.4): `M = S`, `A_M = H^#` with `R = P` (`P_le_centralizer_of_mem_H`); `N = T`,
`A_N = K^# ⊆ A₀(T)` (the (13.2.e) TI-property for `T` bounds the centralizers); and `P^w ≤ T` is
impossible since `|P| = p^q` exceeds the `p`-part `p` of `|T|` — the latter two are the T-side
gates of the (13.4) reduction. -/
theorem disjoint_conjugatesIntoSet_of_centralizer {M N R : Subgroup G}
    {A_M : Set ↥M} {A_N : Set ↥N}
    (hcent : ∀ y ∈ A_M, R ≤ Subgroup.centralizer ({((y : ↥M) : G)} : Set G))
    (hTI : ∀ z ∈ A_N, Subgroup.centralizer ({((z : ↥N) : G)} : Set G) ≤ N)
    (hnot : ∀ w : G, ¬ ∀ r ∈ R, w⁻¹ * r * w ∈ N) :
    Disjoint (ClassFunction.conjugatesIntoSet M A_M)
      (ClassFunction.conjugatesIntoSet N A_N) := by
  rw [Set.disjoint_left]
  rintro g ⟨a, ha, hyA⟩ ⟨b, hb, hzA⟩
  -- The `A_M`-point is `a⁻¹ g a`, the `A_N`-point is `b⁻¹ g b = w⁻¹ (a⁻¹ g a) w` for `w = a⁻¹ b`.
  -- Every `R`-conjugate `w⁻¹ r w` centralizes it, hence lies in `N` — contradicting `hnot`.
  refine hnot (a⁻¹ * b) fun r hr => ?_
  have hrx : (a⁻¹ * g * a) * r = r * (a⁻¹ * g * a) := by
    have h := hcent _ hyA hr
    rw [Subgroup.mem_centralizer_iff] at h
    exact h (a⁻¹ * g * a) rfl
  refine hTI _ hzA ?_
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hs' : s = b⁻¹ * g * b := hs
  rw [hs']
  calc (b⁻¹ * g * b) * ((a⁻¹ * b)⁻¹ * r * (a⁻¹ * b))
      = (a⁻¹ * b)⁻¹ * ((a⁻¹ * g * a) * r) * (a⁻¹ * b) := by group
    _ = (a⁻¹ * b)⁻¹ * (r * (a⁻¹ * g * a)) * (a⁻¹ * b) := by rw [hrx]
    _ = ((a⁻¹ * b)⁻¹ * r * (a⁻¹ * b)) * (b⁻¹ * g * b) := by group

open scoped FiniteInduce in
/-- **Cross-Dade inner-product vanishing on disjoint conjugate supports** ((13.4) core (d)):
the inductions of `α` (supported in `A_M ⊆ M`) and `β` (supported in `A_N ⊆ N`) to `G` have
disjoint supports when nothing is conjugate into both `A_M` and `A_N`, so their inner product
vanishes.  This is Peterfalvi's `(α^τ, β^τ) = 0` for `α ∈ ℤ[𝒮, H^#]`, `β ∈ ℤ[𝒯, K^#]` (both Dade
isometries being `Ind` by (13.2.e), the supports lie in `(H^#)^G` resp. `(K^#)^G`). -/
theorem inner_induce_induce_eq_zero_of_disjoint [Fintype G] [Invertible (Nat.card G : ℂ)]
    {M N : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card ↥N : ℂ)]
    {A_M : Set ↥M} {A_N : Set ↥N}
    {α : ClassFunction ↥M ℂ} {β : ClassFunction ↥N ℂ}
    (hα : α.support ⊆ A_M) (hβ : β.support ⊆ A_N)
    (hdisj : Disjoint (ClassFunction.conjugatesIntoSet M A_M)
      (ClassFunction.conjugatesIntoSet N A_N)) :
    ClassFunction.inner (ClassFunction.induce M α) (ClassFunction.induce N β) = 0 :=
  ClassFunction.inner_eq_zero_of_disjoint_support
    (hdisj.mono (ClassFunction.support_induce_subset_conjugatesIntoSet hα)
      (ClassFunction.support_induce_subset_conjugatesIntoSet hβ))


/-! ## (13.5)--(13.10): norm estimates -/

/-- **Self inner-sum as a real squared-norm sum** (general `ClassFunction` identity).

For any class function `α : H → ℂ`, the unscaled self inner sum `Σ_g α(g)·conj(α(g))` equals the
real sum of squared norms `Σ_g ‖α(g)‖²` cast to `ℂ`.  This is the bridge between the abstract
`ClassFunction.innerSum`/`inner` API and the concrete `Σ |α(g)|²` quantities of Peterfalvi's norm
estimates (13.6)–(13.10); combined with `Σ_{H#} = Σ_H − |α(1)|²` it converts every Dade-norm
inequality into an elementary squared-norm sum.  A general fact for any finite group `H`. -/
theorem innerSum_self_eq_sum_normSq {H : Type*} [Group H] [Fintype H]
    (α : ClassFunction H ℂ) :
    ClassFunction.innerSum α α = ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) := by
  rw [ClassFunction.innerSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← starRingEnd_apply, RCLike.mul_conj]
  norm_cast

/-- **Parseval identity for class functions** (general): `Σ_g ‖α(g)‖² = |H| · ⟨α, α⟩`.

The full squared-norm sum equals `|H|` times the normalized self inner product `⟨α,α⟩ = ‖α‖²`.
Combined with `Σ_{H#} = Σ_H − ‖α(1)‖²` this is precisely the Parseval relation `s + d² = |H|·n`
consumed by `caseB_eta_norm_core` (the (13.7) core): it lets the cascade read off `s = ∑_{H#}|α|²`
from the abstract inner product `n = ⟨α,α⟩`.  Immediate from `innerSum_self_eq_sum_normSq` and
`ClassFunction.card_mul_inner`. -/
theorem sum_normSq_eq_card_mul_inner {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (α : ClassFunction H ℂ) :
    ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) = (Nat.card H : ℂ) * ClassFunction.inner α α := by
  rw [← innerSum_self_eq_sum_normSq, ClassFunction.card_mul_inner]

/-- **The self inner product of a virtual character is a natural number**: `⟨φ,φ⟩ ∈ ℤ`
(`inner_mem_ZIrr_int`) and `|H|·⟨φ,φ⟩ = ∑‖φ‖² ≥ 0` (`sum_normSq_eq_card_mul_inner`), so the
integer is nonnegative.  The `n = ‖α‖²` of the (13.7) Parseval bookkeeping. -/
theorem exists_nat_inner_self_of_mem_ZIrr {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] {φ : ClassFunction H ℂ}
    (hφ : φ ∈ OddOrder.RepresentationTheory.ZIrr H) :
    ∃ n : ℕ, ClassFunction.inner φ φ = (n : ℂ) := by
  obtain ⟨z, hz⟩ := ClassFunction.inner_mem_ZIrr_int hφ hφ
  have hsum := sum_normSq_eq_card_mul_inner φ
  rw [hz] at hsum
  have hcard : (0 : ℝ) < (Nat.card H : ℝ) := by exact_mod_cast Nat.card_pos
  have hzr : ((Nat.card H : ℝ) * (z : ℝ) : ℂ) = ((∑ g : H, ‖φ g‖ ^ 2 : ℝ) : ℂ) := by
    rw [hsum]
    push_cast
    ring
  have hzreal : (Nat.card H : ℝ) * (z : ℝ) = ∑ g : H, ‖φ g‖ ^ 2 := by exact_mod_cast hzr
  have hz0 : (0 : ℤ) ≤ z := by
    by_contra hneg
    push_neg at hneg
    have h1 : (z : ℝ) < 0 := by exact_mod_cast hneg
    have h2 : (Nat.card H : ℝ) * (z : ℝ) < 0 := mul_neg_of_pos_of_neg hcard h1
    have h3 : (0 : ℝ) ≤ ∑ g : H, ‖φ g‖ ^ 2 :=
      Finset.sum_nonneg (fun g _ => by positivity)
    linarith [hzreal ▸ h2]
  refine ⟨z.toNat, ?_⟩
  rw [hz]
  have := Int.toNat_of_nonneg hz0
  exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) this.symm

/-- **Parseval expansion of a real-scalar linear combination** (the algebraic core of Peterfalvi
(13.5.b)).  For complex functions `f, g` on a finite index set and a real scalar `κ`,
`∑‖κ·f + g‖² = κ²∑‖f‖² + 2κ·Re(∑ f·ḡ) + ∑‖g‖²`.  In (13.5.b) this is applied with `κ = a/‖ζ₁‖²`,
`f = ζ₁`, `g = α` on `H#`; together with the (13.5) sum facts `∑_{H#}|ζ₁|² = |S|‖ζ₁‖² − ζ₁(1)²` and
`∑_{H#} ζ₁ᾱ = −ζ₁(1)α(1)` it yields the (13.5.b) norm decomposition consumed by `caseB_lambda_norm_core`
(13.6) and `caseB_eta01_norm_core` (13.8). -/
theorem sum_normSq_real_smul_add {ι : Type*} (s : Finset ι) (κ : ℝ) (f g : ι → ℂ) :
    (∑ x ∈ s, ‖(κ : ℂ) * f x + g x‖ ^ 2)
      = κ ^ 2 * (∑ x ∈ s, ‖f x‖ ^ 2)
        + 2 * κ * (∑ x ∈ s, f x * (starRingEnd ℂ) (g x)).re
        + (∑ x ∈ s, ‖g x‖ ^ 2) := by
  have hpt : ∀ x ∈ s, ‖(κ : ℂ) * f x + g x‖ ^ 2
      = κ ^ 2 * ‖f x‖ ^ 2 + 2 * κ * (f x * (starRingEnd ℂ) (g x)).re + ‖g x‖ ^ 2 := by
    intro x _
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
    rw [show ((κ : ℂ) * f x) * (starRingEnd ℂ) (g x) = (κ : ℂ) * (f x * (starRingEnd ℂ) (g x)) by ring,
      Complex.re_ofReal_mul]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum]

open scoped Classical in
/-- **Peterfalvi (13.5), `ζ₁`-norm sum** (the (13.5.b) `firstTerm`): for a function `ζ` on `S`
vanishing outside the subgroup `H ≤ S`, the squared-norm sum over `H# = H ∖ {1}` equals the full sum
over `S` minus the value at `1`.  In (13.5) `ζ = ζ₁` vanishes on `S − H` (induced from `H`, with `P`
off the kernels), so combined with Parseval `∑_{x∈S}‖ζ₁‖² = |S|·‖ζ₁‖²` (`sum_normSq_eq_card_mul_inner`)
this gives `∑_{H#}|ζ₁|² = |S|‖ζ₁‖² − ζ₁(1)²`, the `firstTerm` consumed by `caseB_lambda_norm_core`
(13.6) and `caseB_eta01_norm_core` (13.8). -/
theorem sum_normSq_sharp_eq_total_sub_one {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ : S → ℂ) (hvanish : ∀ x : S, x ∉ H → ζ x = 0) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase (1 : S), ‖ζ x‖ ^ 2
      = (∑ x : S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2 := by
  have hHfull : (∑ x : S, ‖ζ x‖ ^ 2) = ∑ x ∈ Finset.univ.filter (· ∈ H), ‖ζ x‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    rw [hvanish x (by simpa using hx)]; simp
  rw [hHfull, ← Finset.sum_erase_add (Finset.univ.filter (· ∈ H)) (fun x => ‖ζ x‖ ^ 2)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, H.one_mem⟩)]
  ring

open scoped Classical in
/-- **Peterfalvi (13.5), cross-term sum** (the (13.5.b) `−2a ζ₁(1)α(1)/‖ζ₁‖²` term): when the inner
sum `∑_{x∈H} ζ₁(x)·conj(α(x))` over the subgroup `H` vanishes — which holds in (13.5) because
`Res_H ζ₁` is a sum of characters with `P` *off* their kernels while every component of `α` has `P`
*in* its kernel (orthogonal constituents) — the sum over `H# = H ∖ {1}` collapses to the single
identity term: `∑_{H#} ζ₁·ᾱ = −ζ₁(1)·conj(α(1))`.  Supplies the cross term of the (13.5.b)
decomposition `sum_normSq_real_smul_add` (with `f = ζ₁`, `g = α`). -/
theorem sum_mul_conj_sharp_eq_neg_of_inner_zero {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α : S → ℂ)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ζ x * (starRingEnd ℂ) (α x)
      = -(ζ 1 * (starRingEnd ℂ) (α 1)) := by
  rw [← Finset.sum_erase_add (Finset.univ.filter (· ∈ H))
    (fun x => ζ x * (starRingEnd ℂ) (α x))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, H.one_mem⟩)] at hinner
  exact eq_neg_of_add_eq_zero_left hinner

open scoped Classical in
/-- **Peterfalvi (13.5.b), norm-sum decomposition**: assembling the (13.5.a) point formula
`χ = κ·ζ₁ + α` (on `H#`, here the hypothesis `hχ`) with Parseval (`sum_normSq_real_smul_add`),
the `ζ₁`-vanishing fact (`sum_normSq_sharp_eq_total_sub_one`, needs `hvanish`) and the cross-term
fact (`sum_mul_conj_sharp_eq_neg_of_inner_zero`, needs `hinner` = `(Res_H ζ₁, α) = 0`) gives

  `∑_{H#}|χ|² = κ²(∑_S|ζ₁|² − ζ₁(1)²) − 2κ·Re(ζ₁(1)·conj α(1)) + ∑_{H#}|α|²`.

Specialised with `κ = a/‖ζ₁‖²` and the norm identity `∑_S|ζ₁|² = |S|‖ζ₁‖²`, this is the textbook
(13.5.b) `(a²/‖ζ₁‖²)(|S| − ζ₁(1)²/‖ζ₁‖²) − 2a·ζ₁(1)α(1)/‖ζ₁‖² + ∑_{H#}|α|²`, the decomposition
consumed by `caseB_lambda_norm_core` (13.6) / `caseB_eta_norm_core` (13.7) /
`caseB_eta01_norm_core` (13.8).  Generic in `(ζ₁, α, χ, κ)`; the three character-theoretic
hypotheses (`hvanish`, `hinner`, `hχ`) are discharged per-case from the (13.5.a) data. -/
theorem sum_normSq_sharp_chi_decomp {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α χ : S → ℂ) (κ : ℝ)
    (hvanish : ∀ x : S, x ∉ H → ζ x = 0)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0)
    (hχ : ∀ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, χ x = (κ : ℂ) * ζ x + α x) :
    ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2
      = κ ^ 2 * ((∑ x : S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2)
        - 2 * κ * (ζ 1 * (starRingEnd ℂ) (α 1)).re
        + ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖α x‖ ^ 2 := by
  have hstep : ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2
      = ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖(κ : ℂ) * ζ x + α x‖ ^ 2 :=
    Finset.sum_congr rfl (fun x hx => by rw [hχ x hx])
  rw [hstep, sum_normSq_real_smul_add, sum_normSq_sharp_eq_total_sub_one H ζ hvanish,
    sum_mul_conj_sharp_eq_neg_of_inner_zero H ζ α hinner, Complex.neg_re]
  ring

open scoped Classical in
/-- **Permutation-character value**: `(Ind_H^G 1_H)(g) = |H|⁻¹ · |{x ∈ G : x⁻¹gx ∈ H}|`.

The induced trivial character is the permutation character of `G` acting on the cosets `G/H`; at
`g` its value is `|H|⁻¹` times the number of conjugators carrying `g` into `H`.  Every summand of
the induction sum over that conjugator set is `1` (the trivial character is constant `1`), so the
sum is the cardinality.  Foundation for the Frobenius induced-trivial-character norm of Peterfalvi
(13.18.b) `‖Ind_E^F 1‖² = (|K|−1)/|E| + 1` (via Frobenius reciprocity + the Frobenius
double-coset count). -/
theorem induce_one_apply {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    [Invertible (Nat.card ↥H : ℂ)] (g : G) :
    ClassFunction.induce H (trivialClassFunction ↥H) g
      = ⅟(Nat.card ↥H : ℂ) *
        ((Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ H)).card : ℂ) := by
  rw [ClassFunction.induce_apply_eq_sum_filter]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))
      (fun x hx => by
        rw [Finset.mem_filter] at hx
        rw [ClassFunction.induceTerm_of_mem (trivialClassFunction ↥H) hx.2]
        rfl),
    Finset.sum_const, nsmul_eq_mul, mul_one]

open scoped Classical in
/-- **Kernel-vanishing of the Frobenius permutation character** (second piece of (13.18.b)).

For a normal subgroup `N` with `N ⊓ A = ⊥`, the induced trivial character `Ind_A^G 1_A` vanishes on
`N#`: a conjugate `x⁻¹gx` of `g ∈ N` again lies in `N` (normality), so if it also lay in `A` it
would lie in `N ⊓ A = ⊥`, forcing `g = 1`.  Hence the conjugator set `{x : x⁻¹gx ∈ A}` is empty.
In the Frobenius case `F = N ⋊ A` this is `γ(g) = 0` for `g ∈ N#`, one of the three value cases
behind `‖Ind_A^F 1‖² = (|N|−1)/|A| + 1` (13.18.b). -/
theorem induce_one_eq_zero_of_mem_normal_inf_bot {G : Type*} [Group G] [Fintype G]
    {N A : Subgroup G} (hN : N.Normal) (hNA : N ⊓ A = ⊥)
    [Invertible (Nat.card ↥A : ℂ)] {g : G} (hg : g ∈ N) (hg1 : g ≠ 1) :
    ClassFunction.induce A (trivialClassFunction ↥A) g = 0 := by
  rw [induce_one_apply]
  have hempty : (Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ A)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _ hmem
    have hxN : x⁻¹ * g * x ∈ N := by simpa using hN.conj_mem g hg x⁻¹
    have hbot : x⁻¹ * g * x ∈ N ⊓ A := ⟨hxN, hmem⟩
    rw [hNA, Subgroup.mem_bot] at hbot
    apply hg1
    calc g = x * (x⁻¹ * g * x) * x⁻¹ := by group
      _ = x * 1 * x⁻¹ := by rw [hbot]
      _ = 1 := by group
  rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]

open scoped Classical in
/-- **Frobenius permutation char is `1` on the complement #** (third value case of (13.18.b)).

For a Frobenius group `G = N ⋊ A`, the induced trivial character `Ind_A^G 1` takes value `1` on
`A#`: the conjugator set `{x : x⁻¹ax ∈ A}` is exactly `A`.  `x ∈ A` clearly works; conversely
`x⁻¹ax ∈ A` puts `a ∈ A ⊓ A^x`, which is `⊥` for `x ∉ A` by the Frobenius trivial-intersection
property (`IsFrobeniusGroup.trivialIntersection`), forcing `a = 1`.  So the count is `|A|` and the
value is `⅟|A| · |A| = 1`. -/
theorem induce_one_eq_one_of_mem_complement {G : Type*} [Group G] [Fintype G]
    {N A : Subgroup G} (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G N A)
    [Invertible (Nat.card ↥A : ℂ)] {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ClassFunction.induce A (trivialClassFunction ↥A) a = 1 := by
  rw [induce_one_apply]
  have hfilter : (Finset.univ.filter (fun x : G => x⁻¹ * a * x ∈ A))
      = Finset.univ.filter (fun x : G => x ∈ A) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro hmem
      by_contra hxA
      have hmemmap : a ∈ A ⊓ Subgroup.map (MulAut.conj x).toMonoidHom A := by
        rw [Subgroup.mem_inf]
        refine ⟨ha, Subgroup.mem_map.mpr ⟨x⁻¹ * a * x, hmem, ?_⟩⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
      rw [hFrob.trivialIntersection x hxA, Subgroup.mem_bot] at hmemmap
      exact ha1 hmemmap
    · intro hxA
      exact A.mul_mem (A.mul_mem (A.inv_mem hxA) ha) hxA
  rw [hfilter]
  have hcard : (Finset.univ.filter (fun x : G => x ∈ A)).card = Nat.card ↥A := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_subtype]
  rw [hcard, invOf_mul_self]

open scoped Classical in
/-- **Frobenius induced-trivial-character norm — Peterfalvi (13.18.b)**:
`‖Ind_A^G 1‖² = (|N| − 1)/|A| + 1` for a Frobenius group `G = N ⋊ A`.

Here `‖Ind_A^G 1‖² = ⅟|A|·(|G:A| + |A| − 1)`; with `|G:A| = |N|` (the complement index) this is
`(|N|−1)/|A| + 1`.  Proof: Frobenius reciprocity turns the norm into `⅟|A|·Σ_{a∈A} γ(a)` where
`γ = Ind_A^G 1` is the permutation character (its values are real, so the conjugate-star drops);
the sum splits as `γ(1) = |G:A|` plus `|A|−1` terms `γ(a) = 1` (`a ∈ A#`, by the three value lemmas
`induce_apply_one` / `induce_one_eq_one_of_mem_complement`).  This is the `‖Ind_{PW₁}^S 1‖²
= (u−1)/q + 1` used in `‖β_j‖² = (u−1)/q + 2` of (13.18.b). -/
theorem norm_induce_one_frobenius {G : Type*} [Group G] [Fintype G]
    {N A : Subgroup G} (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G N A)
    [Invertible (Nat.card ↥A : ℂ)] [Invertible (Nat.card G : ℂ)] :
    ClassFunction.inner (ClassFunction.induce A (trivialClassFunction ↥A))
        (ClassFunction.induce A (trivialClassFunction ↥A))
      = ⅟(Nat.card ↥A : ℂ) * ((A.index : ℂ) + (Nat.card ↥A : ℂ) - 1) := by
  have hreal : ∀ a : ↥A, star ((ClassFunction.induce A (trivialClassFunction ↥A)) (↑a : G))
      = (ClassFunction.induce A (trivialClassFunction ↥A)) (↑a : G) := by
    intro a
    rw [induce_one_apply, invOf_eq_inv, star_mul', star_natCast, star_inv₀, star_natCast]
  rw [ClassFunction.inner_induce_eq_inner_restrict, ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.innerSum]
  have hterm : ∀ a : ↥A,
      (trivialClassFunction ↥A) a *
          star ((ClassFunction.restrict A (ClassFunction.induce A (trivialClassFunction ↥A))) a)
        = (ClassFunction.induce A (trivialClassFunction ↥A)) (↑a : G) := by
    intro a
    rw [ClassFunction.restrict_apply, hreal a, show (trivialClassFunction ↥A) a = 1 from rfl, one_mul]
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  congr 1
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : ↥A))]
  have h1 : (ClassFunction.induce A (trivialClassFunction ↥A)) ((1 : ↥A) : G) = (A.index : ℂ) := by
    rw [Subgroup.coe_one, ClassFunction.induce_apply_one,
      show (trivialClassFunction ↥A) (1 : ↥A) = 1 from rfl, mul_one]
  have herase : ∑ a ∈ Finset.univ.erase (1 : ↥A),
      (ClassFunction.induce A (trivialClassFunction ↥A)) (↑a : G) = (Nat.card ↥A : ℂ) - 1 := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) (fun a ha => ?_)]
    · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card, Nat.cast_sub Nat.card_pos, Nat.cast_one]
    · have ha1 : (↑a : G) ≠ 1 := fun h =>
        (Finset.mem_erase.mp ha).1 (Subtype.ext (h.trans (Subgroup.coe_one (H := A)).symm))
      exact induce_one_eq_one_of_mem_complement hFrob a.2 ha1
  rw [h1, herase]; ring

/-- **Arithmetic core of [Isaacs] Lemma 3.14 / Peterfalvi (13.9.b)**: if a finite family of positive
reals has product `≥ 1`, then their sum is at least the count.

`∏ xᵢ ≥ 1 ∧ xᵢ > 0  ⟹  Σ xᵢ ≥ |s|`.  In (13.9.b) the `xᵢ = |χ(aᵏ)|²` are the squared norms of the
Galois conjugates of a nonzero character value `χ(a)`; their product `|∏ χ(aᵏ)|² = |N(χ(a))|²` is a
nonzero rational integer, hence `≥ 1`, and this bound gives `Σ_{⟨x⟩=⟨a⟩} |χ(x)|² ≥ |{x : ⟨x⟩=⟨a⟩}|`.
Proof (AM-GM-free, via `log x ≤ x − 1`): `Σ xᵢ ≥ Σ (1 + log xᵢ) = |s| + log (∏ xᵢ) ≥ |s|`. -/
theorem card_le_sum_of_one_le_prod {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < x i) (hprod : 1 ≤ ∏ i ∈ s, x i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, x i := by
  have hlog : ∀ i ∈ s, 1 + Real.log (x i) ≤ x i := fun i hi => by
    have := Real.log_le_sub_one_of_pos (hpos i hi); linarith
  have hsum_log : (0 : ℝ) ≤ ∑ i ∈ s, Real.log (x i) := by
    rw [← Real.log_prod fun i hi => (hpos i hi).ne']
    exact Real.log_nonneg hprod
  calc (s.card : ℝ)
      = (∑ _i ∈ s, (1 : ℝ)) + 0 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, add_zero]
    _ ≤ (∑ _i ∈ s, (1 : ℝ)) + ∑ i ∈ s, Real.log (x i) := by linarith [hsum_log]
    _ = ∑ i ∈ s, (1 + Real.log (x i)) := by rw [Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ s, x i := Finset.sum_le_sum hlog

/-- **Inflation norm lower bound — the carrier-free core of Peterfalvi (13.5.c)**.

If a function `α : H → ℂ` is constant on a finite subgroup `P ≤ H` (equal to `α 1` on all of `P`)
— the situation when `P` lies in the kernel of every irreducible constituent of `α`, so `α` is
inflated from `H/P` — then its squared-norm sum over the nonidentity elements `H#` is at least
`(|P| − 1)·|α(1)|²`.  This is exactly Peterfalvi (13.5.c)
`∑_{x∈H#} |α(x)|² ≥ (|P|−1)·α(1)²` in self-contained, carrier-free form: it uses only that `α`
equals `α 1` on `P` and that the remaining squared norms are nonnegative (one sums over the
nonidentity elements of `P` alone, `P# ⊆ H#`).  Specialises to `H = ↥hyp.H`, `P = S_F` in the full
(13.5) TI-subset calculation. -/
theorem sum_normSq_erase_one_ge_of_const_on_subgroup {H : Type*} [Group H] [Fintype H]
    (P : Subgroup H) (α : H → ℂ) (hP : ∀ x ∈ P, α x = α 1) :
    ((Nat.card ↥P : ℝ) - 1) * ‖α 1‖ ^ 2 ≤ (∑ x : H, ‖α x‖ ^ 2) - ‖α 1‖ ^ 2 := by
  classical
  -- card of the subgroup as a filtered finset.
  have hcard : (Finset.univ.filter (· ∈ P)).card = Nat.card ↥P := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_subtype]
  -- the `P`-sum equals `|P|·‖α 1‖²` (every term is `‖α 1‖²`).
  have hPsum : ∑ x ∈ Finset.univ.filter (· ∈ P), ‖α x‖ ^ 2 = (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => ‖α 1‖ ^ 2)
        (fun x hx => by rw [hP x (Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul, hcard]
  -- the `P`-sum is at most the full sum (squared norms nonnegative).
  have hmono : ∑ x ∈ Finset.univ.filter (· ∈ P), ‖α x‖ ^ 2 ≤ ∑ x : H, ‖α x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => by positivity)
  have hkey : (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 ≤ ∑ x : H, ‖α x‖ ^ 2 := hPsum ▸ hmono
  have hexp : ((Nat.card ↥P : ℝ) - 1) * ‖α 1‖ ^ 2
      = (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 - ‖α 1‖ ^ 2 := by ring
  rw [hexp]; linarith [hkey]

/-- **Arithmetic bridge of Peterfalvi (13.2.c)**: `(p−1)^{q−1} ≤ (p^q − 1)/(p − 1)`.

Peterfalvi (13.2.c) gets `u ≤ (p^q − 1)/(p − 1)` from the fixed-point-free bound `u ≤ (p−1)^{q−1}`
(of (9.7)) via this inequality.  Pure ℕ-arithmetic: `(p−1)^{q−1}·(p−1) = (p−1)^q < p^q`, so
`(p−1)^q ≤ p^q − 1`, and dividing by `p−1` gives the claim.  Together with `|P| = p^q` and `p ≥ 3`
this yields `u ≤ (|P|−1)/2` — the hypothesis of `caseB_quadratic_nonneg` (and hence of the (13.6)
norm bound). -/
theorem caseB_u_bound_arith {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  have hpow : (p - 1) ^ (q - 1) * (p - 1) = (p - 1) ^ q := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow]
  have hlt : (p - 1) ^ q < p ^ q := Nat.pow_lt_pow_left (by omega) (by omega)
  omega

/-- **Key nonnegativity of Peterfalvi (13.6)**: the quadratic correction term is `≥ 0`.

In (13.6) the inflation degree satisfies `α(1) = q·b` for an integer `b`, and the bound reduces to
`(|P|−1)·α(1)² − 2·λ(1)·α(1) = q²·((|P|−1)·b² − 2u·b) ≥ 0`, using `u ≤ (|P|−1)/2` from (13.2.c).
This is exactly that nonnegativity `0 ≤ (|P|−1)·b² − 2u·b` (here `Pm1 = |P| − 1`), pure ℤ-arithmetic:
`(|P|−1)b² − 2ub = (|P|−1−2u)·b² + 2u·b(b−1)`, both summands `≥ 0` (the first by `2u ≤ |P|−1`, the
second since consecutive integers `b(b−1) ≥ 0`).  Carrier-free core of the (13.6) estimate. -/
theorem caseB_quadratic_nonneg {Pm1 u : ℕ} (hu : 2 * u ≤ Pm1) (b : ℤ) :
    0 ≤ (Pm1 : ℤ) * b ^ 2 - 2 * (u : ℤ) * b := by
  have h2u : (2 * u : ℤ) ≤ (Pm1 : ℤ) := by exact_mod_cast hu
  have hb : 0 ≤ b * (b - 1) := by
    by_cases h : 1 ≤ b
    · exact mul_nonneg (by linarith) (by linarith)
    · push_neg at h
      calc 0 ≤ (-b) * (-(b - 1)) := mul_nonneg (by omega) (by omega)
        _ = b * (b - 1) := by ring
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (Pm1 : ℤ) - 2 * u) (sq_nonneg b),
    mul_nonneg (by positivity : (0 : ℤ) ≤ 2 * (u : ℤ)) hb]

/-- **Arithmetic assembly of Peterfalvi (13.6)**: the norm lower bound `∑_{x∈H#}|λ^{τ₁}(x)|² ≥ |S| − λ(1)²`.

For the irreducible `λ ∈ S` of degree `λ(1) = u q` induced from a linear character of `H = PC`
(`‖λ‖² = 1`, `a = 1`), the (13.5) decomposition gives `s = (|S| − λ(1)²) − 2λ(1)α(1) + sₐ` where
`s = ∑_{H#}|λ^{τ₁}|²`, `sₐ = ∑_{H#}|α|²`.  By (13.5.a)+(1.10) the correction `α(1) = q b` is divisible
by `q`, by (13.5.c) `(|P|−1)α(1)² ≤ sₐ`, and by (13.2.c) `2u ≤ |P|−1`.  The cross terms are then
nonnegative — `−2λ(1)α(1) + (|P|−1)α(1)² = q²((|P|−1)b² − 2ub) ≥ 0` (`caseB_quadratic_nonneg`) — whence
`|S| − λ(1)² ≤ s`.  Carrier-free arithmetic core (`Scard, Pm1, u, q` abstract naturals; the
character-theoretic decomposition is supplied by the cascade once the (13.5) engine lands). -/
theorem caseB_lambda_norm_core {Scard Pm1 u q : ℕ} {s sₐ lam1 : ℝ} {b : ℤ}
    (hlam1 : lam1 = (u : ℝ) * q)
    (hdecomp : s = ((Scard : ℝ) - lam1 ^ 2) - 2 * lam1 * ((q : ℝ) * b) + sₐ)
    (hinfl : (Pm1 : ℝ) * ((q : ℝ) * b) ^ 2 ≤ sₐ)
    (hu : 2 * u ≤ Pm1) :
    (Scard : ℝ) - lam1 ^ 2 ≤ s := by
  have hquad : (0 : ℤ) ≤ (Pm1 : ℤ) * b ^ 2 - 2 * (u : ℤ) * b := caseB_quadratic_nonneg hu b
  have hquadR : (0 : ℝ) ≤ (Pm1 : ℝ) * (b : ℝ) ^ 2 - 2 * (u : ℝ) * (b : ℝ) := by exact_mod_cast hquad
  have hcross : 0 ≤ -2 * lam1 * ((q : ℝ) * b) + sₐ := by
    have hfac : -2 * lam1 * ((q : ℝ) * b) + (Pm1 : ℝ) * ((q : ℝ) * b) ^ 2
        = (q : ℝ) ^ 2 * ((Pm1 : ℝ) * (b : ℝ) ^ 2 - 2 * (u : ℝ) * (b : ℝ)) := by
      rw [hlam1]; ring
    nlinarith [hinfl, hfac, mul_nonneg (sq_nonneg (q : ℝ)) hquadR]
  linarith [hdecomp, hcross]

open scoped Classical in
/-- **Peterfalvi (13.6), character-theoretic bound**: the norm lower bound
`∑_{x∈H#}|λ^{τ₁}(x)|² ≥ |S| − λ(1)²`, assembled from the (13.5) machinery.

For the irreducible `λ ∈ S` of degree `λ(1) = uq` induced from a linear character of `H = PC`
(so `‖λ‖² = 1`, `a = 1`, hence `κ = 1`), this chains the generic (13.5.b) decomposition
`sum_normSq_sharp_chi_decomp` (with `ζ = λ`, `χ = λ^{τ₁}`, `κ = 1`) into the arithmetic core
`caseB_lambda_norm_core`.  The character-theoretic content is exposed as explicit honest
hypotheses, each discharged from the (13.6) setup once it lands:
* `hvanish` — `λ` vanishes on `S − H` (induced from `H`, `H ⊴ S`);
* `hinner` — `(Res_H λ, α) = 0` (the `P`-kernel orthogonality of (13.5.a));
* `hχ` — the (13.5.a) point formula `λ^{τ₁} = λ + α` on `H#` (orthogonality from `S`-coherence);
* `hT` — `∑_S|λ|² = |S|` (`sum_normSq_eq_card_mul_inner` with `‖λ‖² = 1`);
* `hζ1`, `hcross` — `λ(1) = lam1` real and `Re(λ(1)·conj α(1)) = lam1·qb` (the `α(1) = qb`
  congruence of (13.5.a)+(1.10));
* `hinfl` — `(|P|−1)(qb)² ≤ ∑_{H#}|α|²` (Peterfalvi (13.5.c)); `hu` — `2u ≤ |P|−1` (13.2.c). -/
theorem caseB_lambda_norm_bound {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α χ : S → ℂ) {Scard Pm1 u q : ℕ} {lam1 : ℝ} {b : ℤ}
    (hvanish : ∀ x : S, x ∉ H → ζ x = 0)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0)
    (hχ : ∀ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, χ x = ζ x + α x)
    (hT : ∑ x : S, ‖ζ x‖ ^ 2 = (Scard : ℝ))
    (hζ1 : ‖ζ 1‖ ^ 2 = lam1 ^ 2)
    (hcross : (ζ 1 * (starRingEnd ℂ) (α 1)).re = lam1 * ((q : ℝ) * b))
    (hlam1 : lam1 = (u : ℝ) * q)
    (hinfl : (Pm1 : ℝ) * ((q : ℝ) * b) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖α x‖ ^ 2)
    (hu : 2 * u ≤ Pm1) :
    (Scard : ℝ) - lam1 ^ 2 ≤ ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2 := by
  refine caseB_lambda_norm_core hlam1 ?_ hinfl hu
  rw [sum_normSq_sharp_chi_decomp H ζ α χ 1 hvanish hinner
    (by intro x hx; rw [hχ x hx, Complex.ofReal_one, one_mul]), hT, hζ1, hcross]
  ring

/-- **Arithmetic core of Peterfalvi (13.7)**: the norm lower bound `∑_{x∈H#}|η₁₀(x)|² ≥ |H#|`.

In (13.7), for `α = η₁₀` on `H#` with `α(1) = d` and squared norm `‖α‖² = n`, one has:
* the Parseval relation `s + d² = |H|·n` where `s = ∑_{H#}|α|²` (from `∑_{x∈H}|α|² = |H|‖α‖²`);
* the inflation bound `(|P|−1)·d² ≤ s` (Peterfalvi (13.5.c));
* `n ≥ 1` (`α` a nonzero virtual character), `|P| ≥ 2`, and — `H` being abelian — `n = 1 ⟹ d² = 1`.

Then `s ≥ |H| − 1 = |H#|`.  Carrier-free arithmetic core (`H, P, d, n, s` abstract naturals; the
character-theoretic inputs are supplied by the cascade).  Proof: `n = 1` gives `s = |H| − 1`
directly; for `n ≥ 2`, multiplying through by `|P|` reduces to `|P|(|H|−1) ≤ |H|n(|P|−1)`
(true since `n, |P| ≥ 2`) together with `|P|·d² ≤ |H|n` (from the inflation bound). -/
theorem caseB_eta_norm_core {H P d n s : ℕ}
    (hP : 2 ≤ P) (hn : 1 ≤ n) (hParseval : s + d ^ 2 = H * n)
    (hInflation : (P - 1) * d ^ 2 ≤ s) (habelian : n = 1 → d ^ 2 = 1) :
    H - 1 ≤ s := by
  by_cases hn2 : 2 ≤ n
  · -- `n ≥ 2`
    have hPos : 1 ≤ P := by omega
    have hcast_infl : ((P : ℤ) - 1) * (d : ℤ) ^ 2 ≤ (s : ℤ) := by
      have h : ((P - 1 : ℕ) : ℤ) * (d : ℤ) ^ 2 ≤ (s : ℤ) := by exact_mod_cast hInflation
      rwa [Nat.cast_sub hPos, Nat.cast_one] at h
    have hPar : (s : ℤ) + (d : ℤ) ^ 2 = (H : ℤ) * n := by exact_mod_cast hParseval
    have hH : (0 : ℤ) ≤ (H : ℤ) := by positivity
    have hn2' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn2
    have hP2' : (2 : ℤ) ≤ (P : ℤ) := by exact_mod_cast hP
    have hPd2 : (P : ℤ) * (d : ℤ) ^ 2 ≤ (H : ℤ) * n := by nlinarith [hcast_infl, hPar]
    have hkey : (P : ℤ) * ((H : ℤ) - 1) ≤ (H : ℤ) * n * ((P : ℤ) - 1) := by
      nlinarith [mul_nonneg (mul_nonneg hH (by linarith : (0:ℤ) ≤ (n:ℤ) - 2))
          (by linarith : (0:ℤ) ≤ (P:ℤ) - 1),
        mul_nonneg hH (by linarith : (0:ℤ) ≤ (P:ℤ) - 2), hP2']
    have hs_eq : (s : ℤ) = (H : ℤ) * n - (d : ℤ) ^ 2 := by linarith [hPar]
    have hPpos : (0 : ℤ) < (P : ℤ) := by linarith
    have hmul : (P : ℤ) * ((H : ℤ) - 1) ≤ (P : ℤ) * (s : ℤ) := by
      rw [hs_eq]; nlinarith [hkey, hPd2]
    have hfin : (H : ℤ) - 1 ≤ (s : ℤ) := le_of_mul_le_mul_left hmul hPpos
    omega
  · -- `n = 1`
    have hn_eq : n = 1 := by omega
    subst hn_eq
    rw [mul_one] at hParseval
    have hd : d ^ 2 = 1 := habelian rfl
    omega

/-- **Peterfalvi (13.7), character-theoretic bound**: the norm lower bound
`∑_{x∈H#}|η₁₀(x)|² ≥ |H#|`, assembled from the (13.5) machinery.

For `χ = η₁₀` the (13.5) hypothesis holds with `a = 0`, so the (13.5.a) point formula collapses to
`η₁₀ = α` on `H#` (no `ζ₁` term — `hχ`); hence `∑_{H#}|η₁₀|² = ∑_{H#}|α|²`.  The character-theoretic
sum is an integer `s` (`hs`: `∑_{H#}|α|² = s`, since `∑_{x∈H}|α|² = |H|‖α‖²` is an integer and
`α(1) ∈ ℤ`), and the arithmetic core `caseB_eta_norm_core` gives `s ≥ |H| − 1 = |H#|`.  Bridges the
nat-valued core to the real-valued cascade input consumed by the (13.10) analytic inequality.
Honest hypotheses: `hχ` the (13.5.a) `a = 0` point formula; `hs` integrality; `hParseval`
`s + α(1)² = |H|‖α‖²`; `hInflation` (13.5.c); `habelian` (13.2.b, `H` abelian + `α` faithful). -/
theorem caseB_eta_norm_bound {S : Type*} [Group S] [Fintype S]
    (α χ : S → ℂ) (A : Finset S) {Hcard P d n s : ℕ}
    (hH : 1 ≤ Hcard)
    (hχ : ∀ x ∈ A, χ x = α x)
    (hs : ∑ x ∈ A, ‖α x‖ ^ 2 = (s : ℝ))
    (hP : 2 ≤ P) (hn : 1 ≤ n) (hParseval : s + d ^ 2 = Hcard * n)
    (hInflation : (P - 1) * d ^ 2 ≤ s) (habelian : n = 1 → d ^ 2 = 1) :
    ((Hcard : ℝ) - 1) ≤ ∑ x ∈ A, ‖χ x‖ ^ 2 := by
  have hsum : ∑ x ∈ A, ‖χ x‖ ^ 2 = ∑ x ∈ A, ‖α x‖ ^ 2 :=
    Finset.sum_congr rfl (fun x hx => by rw [hχ x hx])
  rw [hsum, hs]
  have hnat : Hcard - 1 ≤ s := caseB_eta_norm_core hP hn hParseval hInflation habelian
  have h := (Nat.cast_le (α := ℝ)).mpr hnat
  rwa [Nat.cast_sub hH, Nat.cast_one] at h

/-- **Arithmetic assembly of Peterfalvi (13.8)**: the norm lower bound `∑_{x∈H#}|η₀₁(x)|² ≥ |S'| − u²`.

By (13.3.c) there are `j` and `δ = ±1` with `μ_j^{τ₁} = δ ∑_{0≤i<q} η_{i1}`, so the (13.5) hypothesis
holds with `ζ₁ = μ_j` (degree `qu`, `‖μ_j‖² = q`), `χ = η₀₁`, `a = δ`.  The (13.5.b) decomposition then
gives `s = firstTerm − 2δu·α(1) + sₐ` where `firstTerm = (1/q)(|S| − (qu)²/q) = |S|/q − u² = |S'| − u²`
(as `[S:S'] = q`) and `sₐ = ∑_{H#}|α|²`.  With `(|P|−1)α(1)² ≤ sₐ` (13.5.c), `α(1) ∈ ℤ`, `δ² = 1`, and
`2u ≤ |P|−1` (13.2.c), the cross terms are nonnegative — setting `b = δ·α(1)`,
`−2δu·α(1) + (|P|−1)α(1)² = (|P|−1)b² − 2ub ≥ 0` (`caseB_quadratic_nonneg`) — whence `firstTerm ≤ s`.
Carrier-free arithmetic core; the character-theoretic decomposition is supplied by the (13.5) engine. -/
theorem caseB_eta01_norm_core {Pm1 u : ℕ} {firstTerm s sₐ : ℝ} {α1 δ : ℤ}
    (hδ : δ ^ 2 = 1)
    (hdecomp : s = firstTerm - 2 * (δ : ℝ) * u * α1 + sₐ)
    (hinfl : (Pm1 : ℝ) * (α1 : ℝ) ^ 2 ≤ sₐ)
    (hu : 2 * u ≤ Pm1) :
    firstTerm ≤ s := by
  have hquad : (0 : ℤ) ≤ (Pm1 : ℤ) * (δ * α1) ^ 2 - 2 * (u : ℤ) * (δ * α1) :=
    caseB_quadratic_nonneg hu (δ * α1)
  have hquadR : (0 : ℝ) ≤ (Pm1 : ℝ) * ((δ : ℝ) * α1) ^ 2 - 2 * (u : ℝ) * ((δ : ℝ) * α1) := by
    exact_mod_cast hquad
  have hδR : (δ : ℝ) ^ 2 = 1 := by exact_mod_cast hδ
  have hcross : 0 ≤ -2 * (δ : ℝ) * u * α1 + sₐ := by
    have hsq : ((δ : ℝ) * α1) ^ 2 = (α1 : ℝ) ^ 2 := by rw [mul_pow, hδR, one_mul]
    have hfac : (Pm1 : ℝ) * ((δ : ℝ) * α1) ^ 2 - 2 * (u : ℝ) * ((δ : ℝ) * α1)
        = (Pm1 : ℝ) * (α1 : ℝ) ^ 2 - 2 * (δ : ℝ) * u * α1 := by rw [hsq]; ring
    nlinarith [hinfl, hfac, hquadR]
  linarith [hdecomp, hcross]

open scoped Classical in
/-- **Peterfalvi (13.8), character-theoretic bound**: the norm lower bound
`∑_{x∈H#}|η₀₁(x)|² ≥ firstTerm` (textbook `|S'| − u²`), assembled from the (13.5) machinery.

For `χ = η₀₁` the (13.5) hypothesis holds with `ζ = μ_j` (`‖μ_j‖² = 1`) and `a = δ = ±1`, so the
inflation factor is `κ = δ`.  This chains `sum_normSq_sharp_chi_decomp` (with `κ = δ`) into the
arithmetic core `caseB_eta01_norm_core`; `δ² = 1` collapses the `ζ`-term coefficient.  The
character-theoretic content is exposed as explicit honest hypotheses (discharged from the (13.8)
setup): `hvanish`/`hinner` as in (13.6); `hχ` the (13.5.a) point formula `η₀₁ = δ·μ_j + α` on `H#`;
`hfirstTerm` identifies `∑_S|μ_j|² − μ_j(1)²` with `firstTerm`; `hcross` the cross term
`Re(μ_j(1)·conj α(1)) = u·α(1)`; `hinfl` (13.5.c); `hu` (13.2.c). -/
theorem caseB_eta01_norm_bound {S : Type*} [Group S] [Fintype S]
    (H : Subgroup S) (ζ α χ : S → ℂ) {Pm1 u : ℕ} {firstTerm : ℝ} {α1 δ : ℤ}
    (hvanish : ∀ x : S, x ∉ H → ζ x = 0)
    (hinner : ∑ x ∈ Finset.univ.filter (· ∈ H), ζ x * (starRingEnd ℂ) (α x) = 0)
    (hχ : ∀ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, χ x = (δ : ℂ) * ζ x + α x)
    (hfirstTerm : (∑ x : S, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2 = firstTerm)
    (hcross : (ζ 1 * (starRingEnd ℂ) (α 1)).re = (u : ℝ) * (α1 : ℝ))
    (hδ : δ ^ 2 = 1)
    (hinfl : (Pm1 : ℝ) * (α1 : ℝ) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖α x‖ ^ 2)
    (hu : 2 * u ≤ Pm1) :
    firstTerm ≤ ∑ x ∈ (Finset.univ.filter (· ∈ H)).erase 1, ‖χ x‖ ^ 2 := by
  refine caseB_eta01_norm_core hδ ?_ hinfl hu
  have hδR : (δ : ℝ) ^ 2 = 1 := by exact_mod_cast hδ
  rw [sum_normSq_sharp_chi_decomp H ζ α χ (δ : ℝ) hvanish hinner
    (by intro x hx; rw [hχ x hx]; push_cast; ring), hcross, hfirstTerm, hδR]
  push_cast; ring

/- `TISubsetOrthogonalityData` + its five `∃`-True-Prop scaffold theorems
(`tiSubset_character_orthogonality`, `lambda_norm_lower`, `eta10_norm_lower`,
`eta01_norm_lower`, `global_character_bound`) were retired (issue 2034, 07-05): the real
(13.5)–(13.9) content is the proven `H_sharp_*` machinery, `exists_caseB_data_*` packages and
sharp bounds above/below; the scaffolds were uncited. -/

/-- **Peterfalvi (8.5.a)**: `H = PC = F(S)`.  The type-`P` carrier `Sdata` records (8.5.a),
`F(S) = M_F · C_U(M_F) = M_F ⊔ (U ⊓ C_S(M_F))`, as its `fitting_eq` field (`TypePData.fitting_eq`,
whose left side is the ambient realization `(fitting ↥S).map S.subtype = fittingInG S`).
Reconciled through `P = M_F = Sdata.H` (`P_eq_SF`/`Sdata.H_eq`) and `Sdata.U = U` (`Sdata_U_eq`),
the right side is exactly `P ⊔ (U ⊓ C_S(P)) = P ⊔ C = H`.  This §8 identity makes the (13.5)
ρ-machinery unconditional, superseding the σ-structure-gated P-abelian route of issue 4013:
`Sdata.fitting_eq` *is* (8.5.a). -/
theorem Hypothesis.H_eq_fittingInG (hyp : Hypothesis (G := G)) :
    hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := by
  have hPH : hyp.P = hyp.Sdata.H := by rw [hyp.P_eq_SF, hyp.Sdata.H_eq]
  change hyp.P ⊔ hyp.C = OddOrder.BG.Ch2.S08.fittingInG hyp.S
  rw [hyp.C_eq, hPH, ← hyp.Sdata_U_eq]
  exact hyp.Sdata.fitting_eq.symm

/-- **Peterfalvi (8.5.a)/(8.6.a)**: `H^# = (PC)^#` is a TI-subset of `G` with normalizer `S` —
distinct `G`-conjugates of `H^#` meet trivially, and any conjugator landing `H^#` back in `H^#` lies
in `S`.  The §8 structural input to the (13.5) ρ-machinery.

Proof: `H = F(S)` (`H_eq_fittingInG`, the carrier's (8.5.a) `fitting_eq`), and `F(S)^#` is a
TI-subset with normalizer `N_G(F(S)) = S` — BG (15.7)(a) `fittingIsTI_of_isTypeP2` (from the
type-`P₂` carrier `S_typeP2`) with `normalizer_fittingInAmbient_eq_self` pinning the bound to `S`.
Rewriting `H^# = F(S)^#` closes it. -/
theorem H_sharp_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S := by
  have hHF : hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := hyp.H_eq_fittingInG
  have hTI : OddOrder.BG.Ch4.S15.FittingIsTI hyp.S :=
    OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  have hnorm : Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) = hyp.S :=
    OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  have hTI0 : OddOrder.GroupTheory.IsTISubset (OddOrder.BG.Ch4.S15.fittingSharp hyp.S)
      (Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G)) := hTI
  rw [hnorm] at hTI0
  -- `H^# = F(S)^#` as sets, so the TI property transfers.
  have hset : OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)
      = OddOrder.BG.Ch4.S15.fittingSharp hyp.S := by
    change (hyp.H : Set G) \ {1}
      = (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) \ {1}
    rw [hHF]
  rw [hset]
  exact hTI0

/-- **Peterfalvi (8.5.a)**: `S` normalizes `H^# = (PC)^#` (the `S`-side of `S = N_G(H^#)`).

Proof: `H = F(S)` (`H_eq_fittingInG`) and `S = N_G(F(S))` (`normalizer_fittingInAmbient_eq_self`),
so every `l ∈ S` normalizes `F(S)`; conjugation keeps `a ∈ F(S)^#` inside `F(S)` and
nonidentity. -/
theorem S_normalizes_H_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ (l : hyp.S) ⦃a : G⦄, a ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) →
      (l : G) * a * (l : G)⁻¹ ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) := by
  have hHF : hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := hyp.H_eq_fittingInG
  have hnorm : Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) = hyp.S :=
    OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  intro l a ha
  rw [OddOrder.Peterfalvi.S04.mem_sharp] at ha ⊢
  obtain ⟨haH, ha1⟩ := ha
  rw [hHF] at haH ⊢
  have hlnorm : (l : G) ∈
      Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) := by
    rw [hnorm]; exact l.2
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hlnorm a).mp haH, ?_⟩
  intro heq
  refine ha1 ?_
  calc a = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * (l : G) := by group
    _ = 1 := by rw [heq]; group

/-- **Peterfalvi (13.5)/(7.1)**: the §4 Dade hypothesis for the TI-subset `(S, H^#)`.  Since `H^#` is a
TI-subset of `G` with normalizer `S` ((8.5.a)/(8.6.a)), `S04.of_isTISubset` builds the Dade datum
(whose local subgroups `H(a) = ⊥`) whose isometry is the `τ = Ind_S^G` powering the (13.5) ρ-machinery
((7.7.a) `chiRho_explicit_formula` applied to `(S, H^#)`).  The structural inputs `H^# ⊆ G^#` and
`H = PC ≤ S` (`P = S_F ≤ S`, `C ≤ U ≤ M' = [S,S] ≤ S`) are discharged here; the TI/normalizer content
is the §8 obligation `H_sharp_isTISubset`/`S_normalizes_H_sharp`.  The Dade foundation of the (13.5)
engine. -/
noncomputable def H_sharp_dadeHypothesis [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S04.Hypothesis G (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S := by
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  have hHS : hyp.H ≤ hyp.S := by
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  refine OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset ?_ ?_ (S_normalizes_H_sharp hG hyp)
    (H_sharp_isTISubset hG hyp)
  · intro x hx
    exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩
  · intro x hx
    exact hHS (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1

/-- The (13.5) Dade datum `(S, H^#)` is `S`-conjugation invariant: for the TI-subset construction the
local subgroups `H(a) = ⊥`, so `HConjInvariant` holds vacuously (`HConjInvariant.of_forall_H_eq_bot`). -/
theorem H_sharp_hconj [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (H_sharp_dadeHypothesis hG hyp).HConjInvariant :=
  OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Peterfalvi (13.5)/(7.1)**: the (7.1) ρ-hypothesis for `(S, H^#)`.  Mirrors `S14.toHypothesis71`:
the Dade isometry `τ` is the `fullDadeIsometryData` of the (13.5) Dade datum `H_sharp_dadeHypothesis`,
and conjugation invariance is `H_sharp_hconj`.  This is the (7.1) datum on which `chiRho` (the `ρ`
map) and — once the coherence datum is supplied — the (7.7.a) `chiRho_explicit_formula` of the (13.5)
point formula are evaluated. -/
noncomputable def H_sharp_hypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S :=
  { hyp := H_sharp_dadeHypothesis hG hyp
    τ := ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
      (H_sharp_hconj hG hyp)).toDadeIsometryData.toDadeMap
    isDadeMap := ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
      (H_sharp_hconj hG hyp)).toDadeIsometryData.isDadeMap
    hConjInvariant := H_sharp_hconj hG hyp }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Peterfalvi (13.5)/(7.6)**: the (7.6) coherent-family datum for `(S, H^#)`, with its (7.7.a)
certificate.  Built from the (7.1) ρ-hypothesis `H_sharp_hypothesis71` and the Dade-isometry property
via `S09.hypothesis76OfDade` (issue-1013: the whole `Hypothesis76`, *including* the (7.7.a)
`chiRho_decomp`, is constructible from `(7.1)` data alone — the induced family `{Ind_H^S θ}` is the
`exists_distinct_induced_family` enumeration, the certificate is `chiRho_decomp_induced`).  The normal
subgroup is `H = PC ⊴ S` (`S` normalizes `H^#` ⟹ normalizes `H`).  This is the datum on which the
(13.5.a) point formula `chiRho_explicit_formula` (7.7.a) is read off. -/
noncomputable def H_sharp_hypothesis76 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S := by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeTrivialBase (H_sharp_hypothesis71 hG hyp) ?_ hyp.H ?_ ?_ rfl
  · exact ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
      (H_sharp_hconj hG hyp)).toDadeIsometryData.isDadeIsometry
  · have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  · intro l h hh
    by_cases h1 : h = 1
    · subst h1; simpa using hyp.H.one_mem
    · have hsh : h ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) :=
        OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hh, h1⟩
      exact (OddOrder.Peterfalvi.S04.mem_sharp.mp (S_normalizes_H_sharp hG hyp l hsh)).1

open scoped FiniteInduce in
/-- **The `H`-side family base is the induced principal character**: `ζ₀ = Ind_H^S 1_H` — the
trivial-base normalization of `hypothesis76OfDadeTrivialBase`.  This is what forces the
(13.5)/(13.6) distinguished `λ = Ind_H^S θ` (`P ⊄ Ker θ`) to sit at a *positive* family index
(`exists_lambda_index`). -/
theorem H_sharp_zeta_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (H_sharp_hypothesis76 hG hyp).zeta 0
      = ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter
              ↥(hyp.H.subgroupOf hyp.S) :
            OddOrder.RepresentationTheory.IrreducibleCharacter _) :
              ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) := by
  unfold H_sharp_hypothesis76
  exact OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeTrivialBase_zeta_zero _ _ _ _ _ _

open scoped FiniteInduce in
/-- **Peterfalvi (13.2.e)/(7.2): the `(S, H^#)` Dade isometry is `Ind_S^G`.**  For the
TI-subset construction (all local subgroups trivial) the Dade map and the induction agree
pointwise: on the conjugacy saturation of `H^#` both take the base value `α(a)`
(`map_eq_of_isConj_of_forall_H_eq_bot` vs `IsTISubset.induce_apply_of_mem_conj`), and both
vanish off it.  This is the "`τ` coincides with `Ind_S^G`" clause of (13.2.e), the link
between the (7.7.a) coefficients `c_i = ⟨τψ_i, χ⟩` and the τ₁-extension field
`tau1S_apply_induce_sub` (issue 2034). -/
theorem H_sharp_tau_eq_induce [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S) :
    (H_sharp_hypothesis71 hG hyp).τ α
      = ClassFunction.induce hyp.S (α : ClassFunction ↥hyp.S ℂ) := by
  classical
  have hAL : OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) ⊆ (hyp.S : Set G) := fun x hx =>
    hyp.H_le_S (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1
  have hsupp : ∀ w : ↥hyp.S, (w : G) ∉ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) →
      (α : ClassFunction ↥hyp.S ℂ) w = 0 := by
    intro w hw
    by_contra hne
    exact hw (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp
      (α.2 (ClassFunction.mem_support.mpr hne)))
  have hstab : ∀ l ∈ hyp.S,
      MulAut.conj l • (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G))
        = OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) := by
    intro l hl
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      simp only [MulAut.smul_def, MulAut.conj_apply]
      exact S_normalizes_H_sharp hG hyp ⟨l, hl⟩ ha
    · intro hx
      refine ⟨l⁻¹ * x * l, ?_, ?_⟩
      · have := S_normalizes_H_sharp hG hyp (⟨l, hl⟩ : ↥hyp.S)⁻¹ hx
        simpa using this
      · simp only [MulAut.smul_def, MulAut.conj_apply]
        group
  ext g
  by_cases hg : g ∈ OddOrder.GroupTheory.conjClassSet
      (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G))
  · obtain ⟨a, ha, y, hy⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hg
    rw [OddOrder.Peterfalvi.S04.map_eq_of_isConj_of_forall_H_eq_bot
        (H_sharp_hypothesis71 hG hyp).isDadeMap (fun _ => rfl) α ha
        (isConj_iff.mpr ⟨y, hy⟩),
      OddOrder.GroupTheory.IsTISubset.induce_apply_of_mem_conj (H_sharp_isTISubset hG hyp)
        hAL hstab (α : ClassFunction ↥hyp.S ℂ) hsupp ha hy.symm]
  · have hg' : g ∉ Group.conjugatesOfSet (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) := by
      intro hmem
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hmem
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      exact hg (OddOrder.GroupTheory.mem_conjClassSet.mpr ⟨a, ha, c, hc⟩)
    rw [OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
        (H_sharp_hypothesis71 hG hyp).isDadeMap (fun _ => rfl) α hg',
      OddOrder.GroupTheory.IsTISubset.induce_apply_of_not_mem_conjClassSet
        (α : ClassFunction ↥hyp.S ℂ) hsupp hg]

/-- **TI-subset `ρ`-map collapse** (the `χ = χ^ρ` bridge of Peterfalvi (13.5.a)): when the local
subgroups of a (7.1) datum are trivial (`H(a) = ⊥`, as for the TI-subset Dade construction
`H_sharp_dadeHypothesis`), the `ρ`-map is the identity on the support — `χ^ρ(a) = χ(a)` for `a ∈ A`.
Direct from the `chiRho` definition: the average `|H(a)|⁻¹ ∑_{x∈H(a)} χ(a·x)` over `H(a) = ⊥` is the
single term `χ(a·1) = χ(a)`.  This identifies the (13.5.a) point formula's left side with `χ` itself,
so the (7.7.a) `chiRho_explicit_formula` decomposition reads off `χ(x)` on `H^#` directly. -/
theorem chiRho_eq_self_of_H_eq_bot {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    (H71 : OddOrder.Peterfalvi.S09.Hypothesis71 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H71.hyp.H a = ⊥)
    (χ : ClassFunction G ℂ) (a : L) (ha : (a : G) ∈ A) :
    H71.chiRho χ a = χ (a : G) := by
  rw [OddOrder.Peterfalvi.S09.Hypothesis71.chiRho, dif_pos ha, hHbot ⟨(a : G), ha⟩,
    Subgroup.card_bot, Nat.cast_one, inv_one, one_mul]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [show ((default : ↥(⊥ : Subgroup G)) : G) = 1 from
    Subgroup.mem_bot.mp (default : ↥(⊥ : Subgroup G)).2, mul_one]

section GenericAlpha

/-! ### The (13.5.a) machinery over an abstract (7.6) datum

Generic forms of the point formula and the correction-term `α` cluster, over any
`H76 : Hypothesis76 G A L` whose `ρ` is the identity on `A` (the TI case) and any
"kernel" subgroup `P' ≤ L`.  Instantiated by the `S`-side (`H_sharp_*`, `P' = P.subgroupOf S`)
and the `T`-side ((13.8): `Q_sharp_hypothesis76`, `P' = Q.subgroupOf T`). -/

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) point formula, `a = 0` form: if every `P'`-non-kernel coefficient of `χ`
vanishes, then on `A` the character `χ` is its `P'`-kernel tail. -/
theorem hypothesis76_point_formula_kernel_only [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H76.hyp71.hyp.H a = ⊥)
    (P' : Subgroup ↥L) (χ : ClassFunction G ℂ)
    (hall : ∀ i : Fin (H76.n + 1), 0 < i →
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) →
      H76.cCoeff χ i = 0)
    (a : ↥L) (ha : (a : G) ∈ A) :
    χ (a : G) =
      ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a := by
  classical
  have hbase : χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a :=
    (chiRho_eq_self_of_H_eq_bot H76.hyp71 hHbot χ a ha).symm.trans
      (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula H76 χ ha)
  rw [hbase, ← Finset.sum_filter_add_sum_filter_not (Finset.Ioi 0)
    (fun i => (P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))]
  have hmid0 : ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter (fun i =>
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter] at hi
    rw [hall i (Finset.mem_Ioi.mp hi.1) hi.2, star_zero, zero_div, zero_mul]
  rw [hmid0, add_zero]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) point formula with a distinguished index (`a ≠ 0` form): the `P'`-non-kernel
middle coefficients vanish, leaving the `i₁`-term plus the `P'`-kernel tail. -/
theorem hypothesis76_point_formula [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H76.hyp71.hyp.H a = ⊥)
    (P' : Subgroup ↥L) (χ : ClassFunction G ℂ)
    (i₁ : Fin (H76.n + 1)) (hi₁ : 0 < i₁)
    (hi₁ker : ¬ ((P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i₁)))
    (hmiddle : ∀ i : Fin (H76.n + 1), 0 < i → i ≠ i₁ →
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) →
      H76.cCoeff χ i = 0)
    (a : ↥L) (ha : (a : G) ∈ A) :
    χ (a : G) =
      (star (H76.cCoeff χ i₁) / H76.zetaNormSq i₁) * H76.zeta i₁ a
      + ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a := by
  classical
  have hbase : χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a :=
    (chiRho_eq_self_of_H_eq_bot H76.hyp71 hHbot χ a ha).symm.trans
      (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula H76 χ ha)
  rw [hbase, ← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr hi₁)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ioi 0).erase i₁)
      (fun i => (P' : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))]
  have hmid0 : ∑ i ∈ ((Finset.Ioi 0).erase i₁).filter (fun i =>
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_erase] at hi
    rw [hmiddle i (Finset.mem_Ioi.mp hi.1.2) hi.1.1 hi.2, star_zero, zero_div, zero_mul]
  have hi₁notin : i₁ ∉ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
      (fun i => (P' : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) := by
    rw [Finset.mem_filter]
    exact fun h => hi₁ker h.2
  rw [hmid0, add_zero, Finset.filter_erase, Finset.erase_eq_self.mpr hi₁notin]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) correction term: the `P'`-kernel tail of the (7.7.a) decomposition. -/
noncomputable def hypothesis76AlphaFun [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) : ↥L → ℂ :=
  fun a =>
    ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (P' : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic correction is constant on `P'`. -/
theorem hypothesis76AlphaFun_const [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x ∈ P', hypothesis76AlphaFun H76 P' χ x = hypothesis76AlphaFun H76 P' χ 1 := by
  classical
  intro x hx
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hker := (Finset.mem_filter.mp hi).2
  rw [show H76.zeta i x = H76.zeta i 1 from hker hx]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic correction vanishes off `H76.H`. -/
theorem hypothesis76AlphaFun_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x : ↥L, (x : G) ∉ H76.H → hypothesis76AlphaFun H76 P' χ x = 0 := by
  classical
  intro x hx
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [H76.zeta_eq_zero_of_not_mem_H i x hx, mul_zero]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.c): the inflation bound for the correction over any sharp `Finset` of the
`H76.H`-members (instance-free `F`-interface). -/
theorem hypothesis76AlphaFun_inflation [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (F : Finset ↥L) (hF : ∀ x : ↥L, x ∈ F ↔ ((x : G) ∈ H76.H ∧ x ≠ 1))
    (hP'H : ∀ x : ↥L, x ∈ P' → (x : G) ∈ H76.H) :
    ((Nat.card ↥P' : ℝ) - 1) * ‖hypothesis76AlphaFun H76 P' χ 1‖ ^ 2
      ≤ ∑ x ∈ F, ‖hypothesis76AlphaFun H76 P' χ x‖ ^ 2 := by
  classical
  set α := hypothesis76AlphaFun H76 P' χ with hαdef
  have hcore := sum_normSq_erase_one_ge_of_const_on_subgroup P' α
    (hypothesis76AlphaFun_const H76 P' χ)
  -- The ambient `↥L`-sum equals the `F`-sum plus the identity term (α vanishes off `H76.H`).
  have hFeq : F = (Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  have hsupp : ∑ x : ↥L, ‖α x‖ ^ 2
      = ∑ x ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H), ‖α x‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : ↥L => (x : G) ∈ H76.H)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x : ↥L => ¬ (x : G) ∈ H76.H), ‖α x‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hαdef, hypothesis76AlphaFun_eq_zero H76 P' χ x (Finset.mem_filter.mp hx).2]
      simp
    rw [h0, add_zero]
  have h1mem : (1 : ↥L) ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [OneMemClass.coe_one]
    exact H76.H.one_mem
  have hsharp : ∑ x ∈ F, ‖α x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H), ‖α x‖ ^ 2)
        - ‖α 1‖ ^ 2 := by
    rw [hFeq, ← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsharp, ← hsupp]
  exact hcore

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Generic (13.5.a) `P'`-kernel orthogonality**: the full-`↥L` pairing of a `P'`-non-kernel
family member `ζ_{i₁}` against the `P'`-kernel tail `α` vanishes — each tail constituent is a
family member of a *different* fibre (the kernel property separates them), and distinct-fibre
induced characters are orthogonal (`inner_induce_eq_zero_of_not_conj` via `zeta_induced`). -/
theorem hypothesis76_zeta_inner_alphaFun_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) (i₁ : Fin (H76.n + 1))
    (hi₁ker : ¬ ((P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i₁))) :
    ∑ x : ↥L, H76.zeta i₁ x * (starRingEnd ℂ) (hypothesis76AlphaFun H76 P' χ x) = 0 := by
  classical
  haveI hKn : (H76.H.subgroupOf L).Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  -- The sum is `|L|·⟨ζ_{i₁}, alphaCF⟩` with `alphaCF` the class-function form of the tail.
  set alphaCF : ClassFunction ↥L ℂ :=
    ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (P' : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) • H76.zeta i with halphaCF
  have happly : ∀ x : ↥L, alphaCF x = hypothesis76AlphaFun H76 P' χ x := by
    intro x
    rw [halphaCF, OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
      hypothesis76AlphaFun]
    exact Finset.sum_congr rfl (fun i _ => by rw [ClassFunction.smul_apply])
  have hsum : ∑ x : ↥L, H76.zeta i₁ x * (starRingEnd ℂ)
      (hypothesis76AlphaFun H76 P' χ x)
      = ClassFunction.innerSum (H76.zeta i₁) alphaCF := by
    rw [ClassFunction.innerSum]
    exact Finset.sum_congr rfl (fun x _ => by rw [happly, starRingEnd_apply])
  rw [hsum, ← ClassFunction.card_mul_inner]
  have hinner0 : ClassFunction.inner (H76.zeta i₁) alphaCF = 0 := by
    rw [halphaCF, inner_sum_right]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [OddOrder.RepresentationTheory.inner_smul_right]
    have hjker := (Finset.mem_filter.mp hj).2
    have hzne : H76.zeta i₁ ≠ H76.zeta j := fun heq => hi₁ker (heq ▸ hjker)
    obtain ⟨θ, hθ⟩ := H76.zeta_induced i₁
    obtain ⟨θ', hθ'⟩ := H76.zeta_induced j
    have hz0 : ClassFunction.inner (H76.zeta i₁) (H76.zeta j) = 0 := by
      rw [hθ, hθ']
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ θ'
        (fun g hconj => ?_)
      refine hzne ?_
      rw [hθ, hθ', ← hconj, OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy,
        OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq]
    rw [hz0, mul_zero]
  rw [hinner0, mul_zero]

end GenericAlpha

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Peterfalvi (13.5.a), base decomposition**: on `H^#`, `χ` equals the (7.7.a) `ρ`-decomposition
`∑_{i≥1} (c̄_i / ‖ζ_i‖²) ζ_i` of the coherent datum `H_sharp_hypothesis76`.  Combines the `χ = χ^ρ`
bridge `chiRho_eq_self_of_H_eq_bot` (TI case, `H(a) = ⊥`) with `chiRho_explicit_formula` (7.7.a).  The
full (13.5.a) point formula `χ = (a/‖ζ₁‖²)ζ₁ + α` (with `P` off the kernels of `α`) then follows by
extracting the distinguished `ζ₁` term and grouping the `P`-kernel tail of this sum. -/
theorem H_sharp_chiRho_eq_explicit [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) (a : hyp.S)
    (ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) :
    χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
          (H_sharp_hypothesis76 hG hyp).zetaNormSq i) *
        (H_sharp_hypothesis76 hG hyp).zeta i a :=
  (chiRho_eq_self_of_H_eq_bot (H_sharp_hypothesis71 hG hyp) (fun _ => rfl) χ a ha).symm.trans
    (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula (H_sharp_hypothesis76 hG hyp) χ ha)

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5.a), point formula**: on `H^#`, the test character `χ` decomposes as the
distinguished term `(c̄_{i₁}/‖ζ_{i₁}‖²) ζ_{i₁}` plus the **`P`-kernel tail** `α = ∑_{P⊆ker ζ_i, i≥1}`.
From the base decomposition `H_sharp_chiRho_eq_explicit` (χ = ∑_{i≥1} of the `ρ`-coefficients) one
extracts the distinguished index `i₁` (which is `P`-non-kernel, `hi1_ker`) and drops the `S₁`-middle
indices (`P`-non-kernel, `≠ i₁`) whose coefficients vanish by the (13.5) orthogonality hypothesis
`hmiddle` (`χ ⊥ (ζ_i − ζ_0)^τ`); what remains is the distinguished term and the `P⊆ker` tail.  The
tail `α` is constant on `P` (each `ζ_i` has `P` in its kernel), feeding (13.5.c). -/
theorem H_sharp_point_formula [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (χ : ClassFunction G ℂ)
    (i1 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)) (hi1 : 0 < i1)
    (hi1_ker : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i1)))
    (hmiddle : ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i → i ≠ i1 →
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
      (H_sharp_hypothesis76 hG hyp).cCoeff χ i = 0)
    (a : hyp.S) (ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) :
    χ (a : G) =
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i1) /
          (H_sharp_hypothesis76 hG hyp).zetaNormSq i1) * (H_sharp_hypothesis76 hG hyp).zeta i1 a
      + ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
          (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
            (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a := by
  classical
  rw [H_sharp_chiRho_eq_explicit hG hyp χ a ha,
    ← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr hi1)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ioi 0).erase i1)
      (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i))]
  have hmid0 : ∑ i ∈ ((Finset.Ioi 0).erase i1).filter (fun i =>
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i))),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
        (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_erase] at hi
    rw [hmiddle i (Finset.mem_Ioi.mp hi.1.2) hi.1.1 hi.2, star_zero, zero_div, zero_mul]
  have hi1notin : i1 ∉ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
      (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) := by
    rw [Finset.mem_filter]; exact fun h => hi1_ker h.2
  rw [hmid0, add_zero, Finset.filter_erase, Finset.erase_eq_self.mpr hi1notin]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5.a), point formula for `a = 0`**: if *every* `P`-non-kernel coefficient of
`χ` vanishes (the (13.5) hypothesis with `a = 0`, as for `χ = η₁₀` which is orthogonal to all of
`S^{τ₁}`), then on `H^#` the character `χ` *is* its `P`-kernel tail.  The `i₁`-free variant of
`H_sharp_point_formula`. -/
theorem H_sharp_point_formula_kernel_only [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (χ : ClassFunction G ℂ)
    (hall : ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i →
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
      (H_sharp_hypothesis76 hG hyp).cCoeff χ i = 0)
    (a : hyp.S) (ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) :
    χ (a : G) =
      ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
          (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
            (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a := by
  classical
  rw [H_sharp_chiRho_eq_explicit hG hyp χ a ha,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Ioi 0)
      (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i))]
  have hmid0 : ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter (fun i =>
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i))),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
        (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter] at hi
    rw [hall i (Finset.mem_Ioi.mp hi.1) hi.2, star_zero, zero_div, zero_mul]
  rw [hmid0, add_zero]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5.a) correction term `α`** for a test character `χ`: the `P`-kernel tail
`α = ∑_{i≥1, P⊆ker ζ_i} (c̄_i/‖ζ_i‖²)·ζ_i` of the (7.7.a) decomposition, as a function on `↥S`.
By `H_sharp_point_formula` (resp. the `a = 0` variant), `χ = (distinguished term) + α` (resp.
`χ = α`) on `H^#`; it is constant on `P` (`H_sharp_alphaFun_const_on_P`) and vanishes off `H`
(`H_sharp_alphaFun_eq_zero_of_not_mem`), which drive the (13.5.c) inflation bound. -/
noncomputable def H_sharp_alphaFun [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) : ↥hyp.S → ℂ :=
  fun a =>
    ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
          (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
            OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
        (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
          (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (13.5.a) correction `α` is **constant on `P`** — each `ζ_i` in the tail has `P` in its
kernel (`ζ_i(x) = ζ_i(1)` for `x ∈ P`), so the tail is `P`-constant.  The kernel input to
(13.5.c). -/
theorem H_sharp_alphaFun_const_on_P [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) :
    ∀ x ∈ hyp.P.subgroupOf hyp.S, H_sharp_alphaFun hG hyp χ x = H_sharp_alphaFun hG hyp χ 1 := by
  classical
  intro x hx
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hker := (Finset.mem_filter.mp hi).2
  have hx1 : (H_sharp_hypothesis76 hG hyp).zeta i x
      = (H_sharp_hypothesis76 hG hyp).zeta i 1 := hker hx
  rw [hx1]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (13.5.a) correction `α` **vanishes off `H`** — each induced `ζ_i` does
(`zeta_eq_zero_of_not_mem_H`). -/
theorem H_sharp_alphaFun_eq_zero_of_not_mem [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) :
    ∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → H_sharp_alphaFun hG hyp χ x = 0 := by
  classical
  intro x hx
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have h0 : (H_sharp_hypothesis76 hG hyp).zeta i x = 0 := by
    refine (H_sharp_hypothesis76 hG hyp).zeta_eq_zero_of_not_mem_H i x ?_
    intro hmem
    exact hx (Subgroup.mem_subgroupOf.mpr (by
      rwa [show (H_sharp_hypothesis76 hG hyp).H = hyp.H from rfl] at hmem))
  rw [h0, mul_zero]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5.c) for the concrete correction `α`**: the inflation bound
`(|P|−1)·‖α(1)‖² ≤ ∑_{x∈H^#}‖α(x)‖²` — `α` is `P`-constant (`H_sharp_alphaFun_const_on_P`), so
the `P^#`-part of the sharp sum already contributes `(|P|−1)·‖α(1)‖²` (`|P| = p^q` by
`card_P_eq`), and `α` vanishes off `H` so the ambient `↥S`-sum *is* the `H`-filtered sum. -/
theorem H_sharp_alphaFun_inflation [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) :
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ‖H_sharp_alphaFun hG hyp χ 1‖ ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖H_sharp_alphaFun hG hyp χ x‖ ^ 2 := by
  classical
  set α := H_sharp_alphaFun hG hyp χ with hαdef
  -- The core bound over all of `↥S`.
  have hcore := sum_normSq_erase_one_ge_of_const_on_subgroup (hyp.P.subgroupOf hyp.S) α
    (H_sharp_alphaFun_const_on_P hG hyp χ)
  -- `|P.subgroupOf S| = |P| = p^q`.
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hcard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = hyp.p ^ hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- The ambient sum equals the `H`-filtered sum (`α` vanishes off `H`).
  have hsupp : ∑ x : ↥hyp.S, ‖α x‖ ^ 2
      = ∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S), ‖α x‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ hyp.H.subgroupOf hyp.S)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.H.subgroupOf hyp.S), ‖α x‖ ^ 2
        = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hαdef, H_sharp_alphaFun_eq_zero_of_not_mem hG hyp χ x (Finset.mem_filter.mp hx).2]
      simp
    rw [h0, add_zero]
  -- The sharp sum is the filtered sum minus the identity term.
  have h1mem : (1 : ↥hyp.S) ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hyp.H.subgroupOf hyp.S).one_mem⟩
  have hsharp : ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1, ‖α x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S), ‖α x‖ ^ 2) - ‖α 1‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsharp, ← hsupp]
  calc ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ‖α 1‖ ^ 2
      = ((Nat.card ↥(hyp.P.subgroupOf hyp.S) : ℝ) - 1) * ‖α 1‖ ^ 2 := by
        rw [hcard]
        congr 1
        have h1 : (1 : ℕ) ≤ hyp.p ^ hyp.q :=
          Nat.one_le_pow _ _ (by have := hyp.three_le_p; omega)
        rw [Nat.cast_sub h1]
        norm_num
    _ ≤ (∑ x : ↥hyp.S, ‖α x‖ ^ 2) - ‖α 1‖ ^ 2 := hcore

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5.a) correction as a class function on `↥S`**: `H_sharp_alphaFun` is the
underlying function of the `ℂ`-combination `∑_{i≥1, P⊆ker ζ_i} (c̄_i/‖ζ_i‖²) • ζ_i`. -/
noncomputable def H_sharp_alphaCF [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) : ClassFunction ↥hyp.S ℂ :=
  ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
        (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
        (H_sharp_hypothesis76 hG hyp).zetaNormSq i) • (H_sharp_hypothesis76 hG hyp).zeta i

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
@[simp] theorem H_sharp_alphaCF_apply [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) (a : ↥hyp.S) :
    H_sharp_alphaCF hG hyp χ a = H_sharp_alphaFun hG hyp χ a := by
  rw [H_sharp_alphaCF, H_sharp_alphaFun,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [ClassFunction.smul_apply])

/-- `H = PC` is normal in `S` (it is the Fitting subgroup, `H_eq_fittingInG`) — as an
instance on the `subgroupOf` form, so that `conjBy`/`inertia` statements over `↥S` elaborate. -/
instance H_sharp_subgroupOf_normal (hyp : Hypothesis (G := G)) :
    (hyp.H.subgroupOf hyp.S).Normal := by
  rw [hyp.H_eq_fittingInG]
  exact OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal hyp.S

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Restriction of a (7.6) family member is `‖ζ_j‖²` times its conjugate-orbit sum**
(extraction of the Mackey computation shared by the ZIrr-membership and the (13.5.a)
inner-product orthogonality): there is an inducing irreducible `θ` with
`ζ_j = Ind_K^S θ` and `Res_K ζ_j = ‖ζ_j‖² • ∑_{ψ ∈ orbit(θ)} ψ`. -/
theorem H_sharp_restrict_zeta_eq_orbitSum [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)) :
    ∃ θ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S),
      (H_sharp_hypothesis76 hG hyp).zeta j
        = ClassFunction.induce ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
            (θ : ClassFunction ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S) ℂ) ∧
      (haveI : ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S).Normal :=
        H_sharp_subgroupOf_normal hyp
      ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
          ((H_sharp_hypothesis76 hG hyp).zeta j)
        = (H_sharp_hypothesis76 hG hyp).zetaNormSq j •
            ∑ ψ ∈ Finset.univ.image (fun x : ↥hyp.S =>
              ClassFunction.conjBy x⁻¹
                (θ : ClassFunction ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S) ℂ)), ψ) := by
  classical
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  obtain ⟨θ₀, hθ₀⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
  have hθ : (H_sharp_hypothesis76 hG hyp).zeta j
      = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  refine ⟨θ₀, hθ, ?_⟩
  have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have horbit := OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
    (G := ↥hyp.S) (H := K) (k := ℂ) (θ₀ : ClassFunction ↥K ℂ)
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥hyp.S) (H := K) θ₀
  have hnormval : (Nat.card ↥K : ℂ) * (H_sharp_hypothesis76 hG hyp).zetaNormSq j
      = (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hIKnorm : ((Nat.card ↥K : ℂ))⁻¹ * (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) = (H_sharp_hypothesis76 hG hyp).zetaNormSq j := by
    rw [← hnormval]
    field_simp
  have h1 : (Nat.card ↥K : ℂ) • ClassFunction.restrict K
      ((H_sharp_hypothesis76 hG hyp).zeta j)
      = ((Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
          (θ₀ : ClassFunction ↥K ℂ)) : ℕ) : ℂ) • ∑ ψ ∈ Finset.univ.image
            (fun x : ↥hyp.S => ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ)] at horbit
    rw [hθ]
    exact horbit
  have h2 := congrArg (fun φ => ((Nat.card ↥K : ℂ))⁻¹ • φ) h1
  simp only [smul_smul, inv_mul_cancel₀ hK0, one_smul] at h2
  rw [h2, hIKnorm]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Restriction of the (13.5.a) correction as a combination of family restrictions**
(pointwise linearity; extraction shared by the ZIrr-membership and the inner-product
orthogonality). -/
theorem H_sharp_restrict_alphaCF_decomp [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) :
    ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
        (H_sharp_alphaCF hG hyp χ)
      = ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
          (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
            (H_sharp_hypothesis76 hG hyp).zetaNormSq i) •
            ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
              ((H_sharp_hypothesis76 hG hyp).zeta i) := by
  classical
  ext x
  rw [ClassFunction.restrict_apply, H_sharp_alphaCF,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.restrict_apply])

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **`(1/‖ζ_i‖²)·Res_H ζ_i` is a virtual character of `H`** — the "`Res ζ_i/‖ζ_i‖²` is a
character" step of Peterfalvi (13.5.a).  `ζ_i = Ind_K^S θ_i` (`zeta_induced`), so by the Mackey
orbit form (`card_smul_restrict_induce_eq_inertia_smul_orbitSum`) and the inertia norm
(`card_mul_inner_self_induce_eq_card_inertia`), `Res_K ζ_i = ‖ζ_i‖² · (sum of the distinct
conjugates of θ_i)` — an ℕ-combination of irreducibles (`orbitSum_mem_ZIrr`). -/
theorem H_sharp_inv_normSq_restrict_zeta_mem_ZIrr [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)) :
    ((H_sharp_hypothesis76 hG hyp).zetaNormSq i)⁻¹ •
        ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
          ((H_sharp_hypothesis76 hG hyp).zeta i)
      ∈ ZIrr ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S) := by
  classical
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  obtain ⟨θ₀, hθ₀⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced i
  -- Re-type across the definitional equality `(H_sharp_hypothesis76 hG hyp).H = hyp.H`, and
  -- bridge the canonical `Fintype`/`Invertible` instances (both subsingleton classes).
  have hθ : (H_sharp_hypothesis76 hG hyp).zeta i
      = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  -- The Mackey orbit form, divided by `|K|`.
  have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have horbit := OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
    (G := ↥hyp.S) (H := K) (k := ℂ) (θ₀ : ClassFunction ↥K ℂ)
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥hyp.S) (H := K) θ₀
  -- `‖ζ_i‖² ≠ 0` (it is `|I|/|K|` with `|I| ≥ 1`).
  have hnormval : (Nat.card ↥K : ℂ) * (H_sharp_hypothesis76 hG hyp).zetaNormSq i
      = (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hI0 : (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm0 : (H_sharp_hypothesis76 hG hyp).zetaNormSq i ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnormval
    exact hI0 hnormval.symm
  -- `Res ζ_i = ‖ζ_i‖² • orbitSum θ₀`, hence `(1/‖ζ_i‖²)·Res ζ_i` is the orbit sum.
  have hIKnorm : ((Nat.card ↥K : ℂ))⁻¹ * (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) = (H_sharp_hypothesis76 hG hyp).zetaNormSq i := by
    rw [← hnormval]
    field_simp
  have hres : ClassFunction.restrict K ((H_sharp_hypothesis76 hG hyp).zeta i)
      = (H_sharp_hypothesis76 hG hyp).zetaNormSq i •
          ∑ ψ ∈ Finset.univ.image (fun x : ↥hyp.S =>
            ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    have h1 : (Nat.card ↥K : ℂ) • ClassFunction.restrict K
        ((H_sharp_hypothesis76 hG hyp).zeta i)
        = ((Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
            (θ₀ : ClassFunction ↥K ℂ)) : ℕ) : ℂ) • ∑ ψ ∈ Finset.univ.image
              (fun x : ↥hyp.S => ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
      rw [← Nat.cast_smul_eq_nsmul (R := ℂ)] at horbit
      rw [hθ]
      exact horbit
    have h2 := congrArg (fun φ => ((Nat.card ↥K : ℂ))⁻¹ • φ) h1
    simp only [smul_smul, inv_mul_cancel₀ hK0, one_smul] at h2
    rw [h2, hIKnorm]
  have hmain : ((H_sharp_hypothesis76 hG hyp).zetaNormSq i)⁻¹ •
      ClassFunction.restrict K ((H_sharp_hypothesis76 hG hyp).zeta i)
      = ∑ ψ ∈ Finset.univ.image (fun x : ↥hyp.S =>
          ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    rw [hres, smul_smul, inv_mul_cancel₀ hnorm0, one_smul]
  rw [hmain]
  exact OddOrder.RepresentationTheory.orbitSum_mem_ZIrr (G := ↥hyp.S) θ₀

/-- **`H = PC` is abelian** (Peterfalvi (13.2.a,b)): `P` is (elementary) abelian
(`basic_structure`), `C ≤ U` is abelian (`S_U_commutative`), and `C` centralizes `P`
(`C = U ⊓ C_S(P)`), so the join is abelian (`isMulCommutative_sup_of_le_centralizer`).
The `habelian` input of the (13.7) Parseval bookkeeping. -/
theorem Hypothesis.H_mulCommutative [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : IsMulCommutative ↥hyp.H := by
  obtain ⟨-, -, hPel, -, -, -⟩ := basic_structure hG hyp
  have hPab : IsMulCommutative ↥hyp.P := ⟨⟨hPel.1⟩⟩
  have hCab : IsMulCommutative ↥hyp.C := by
    have hCU : hyp.C ≤ hyp.U := hyp.C_eq ▸ inf_le_left
    exact ⟨⟨fun a b => Subtype.ext (by
      have h := hyp.S_U_commutative.is_comm.comm
        (⟨(a : G), hCU a.2⟩ : ↥hyp.U) ⟨(b : G), hCU b.2⟩
      simpa using congrArg Subtype.val h)⟩⟩
  have hCP : hyp.C ≤ Subgroup.centralizer (hyp.P : Set G) := hyp.C_eq ▸ inf_le_right
  show IsMulCommutative ↥(hyp.P ⊔ hyp.C)
  rw [sup_comm]
  exact OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer hCab hPab hCP

/-- **`P` centralizes every element of `H = PC`** (Peterfalvi (13.4), disjointness ingredient):
for `x ∈ H`, `P ≤ C_G(x)`.  Immediate from `H` abelian (`H_mulCommutative`) and `P ≤ H`.  This is
the first half of the (13.4) conjugate-disjointness `(H^#)^G ∩ (K^#)^G = ∅`: a common point `x`
would have `P ≤ C_G(x) ≤ T^g` (the `A₀(T^g)` TI-property), impossible since `|P| = p^q` exceeds
the `p`-part `p` of `|T|`. -/
theorem Hypothesis.P_le_centralizer_of_mem_H [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {x : G} (hx : x ∈ hyp.H) :
    hyp.P ≤ Subgroup.centralizer ({x} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  have hyH : y ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.P ⊔ hyp.C) hy
  have hcomm := (hyp.H_mulCommutative hG).is_comm.comm (⟨x, hx⟩ : ↥hyp.H) ⟨y, hyH⟩
  simpa using congrArg Subtype.val hcomm


open scoped Classical in
/-- **Sharp-set Parseval bookkeeping** (the `s + d² = |H|·n` shape of Peterfalvi (13.7)): for a
function `f` agreeing on `K` with a class function `ψ` of self inner product `n`, the
squared-norm sum over the nonidentity `K`-members is `|K|·n − ‖f(1)‖²`. -/
theorem sum_filter_erase_one_normSq_eq {L : Type*} [Group L] [Fintype L]
    {K : Subgroup L} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (f : L → ℂ) (ψ : ClassFunction ↥K ℂ) (hagree : ∀ k : ↥K, f ↑k = ψ k)
    {n : ℕ} (hn : ClassFunction.inner ψ ψ = (n : ℂ)) :
    ∑ x ∈ (Finset.univ.filter (· ∈ K)).erase 1, ‖f x‖ ^ 2
      = (Nat.card ↥K : ℝ) * (n : ℝ) - ‖f 1‖ ^ 2 := by
  classical
  -- The full `K`-sum is `|K|·n` (Parseval on `↥K`).
  have htotal : ∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2
      = (Nat.card ↥K : ℝ) * (n : ℝ) := by
    have hbij : ∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2 = ∑ k : ↥K, ‖ψ k‖ ^ 2 := by
      refine Finset.sum_bij' (fun x hx => (⟨x, (Finset.mem_filter.mp hx).2⟩ : ↥K))
        (fun k _ => (k : L)) ?_ ?_ ?_ ?_ ?_
      · intro x hx; exact Finset.mem_univ _
      · intro k _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.2⟩
      · intro x hx; rfl
      · intro k _; rfl
      · intro x hx
        rw [hagree ⟨x, (Finset.mem_filter.mp hx).2⟩]
    have hpars : ((∑ k : ↥K, ‖ψ k‖ ^ 2 : ℝ) : ℂ) = (Nat.card ↥K : ℂ) * (n : ℂ) := by
      rw [sum_normSq_eq_card_mul_inner, hn]
    have hpars' : ∑ k : ↥K, ‖ψ k‖ ^ 2 = (Nat.card ↥K : ℝ) * (n : ℝ) := by
      exact_mod_cast hpars
    rw [hbij, hpars']
  have h1mem : (1 : L) ∈ Finset.univ.filter (· ∈ K) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.one_mem⟩
  have hsplit : ∑ x ∈ (Finset.univ.filter (· ∈ K)).erase 1, ‖f x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2) - ‖f 1‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsplit, htotal]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5.a) correction restricted to `H` is a virtual character of `H`**: with integer
(7.7.a) coefficients `c_i ∈ ℤ` (the `χ ∈ ℤ[Irr G]` case), the `P`-kernel tail
`α = ∑ (c̄_i/‖ζ_i‖²) • ζ_i` restricts to `∑ c_i • ((1/‖ζ_i‖²)·Res ζ_i) ∈ ℤ[Irr H]`
(each normalized restriction is the conjugate-orbit character,
`H_sharp_inv_normSq_restrict_zeta_mem_ZIrr`).  The integrality carrier of Peterfalvi (13.5):
it makes `‖α‖²_H ∈ ℕ` and `α(1) ∈ ℤ` available to the (13.7)/(13.8) Parseval bookkeeping. -/
theorem H_sharp_alphaCF_restrict_mem_ZIrr [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ)
    (hc : ∀ i, ∃ z : ℤ, (H_sharp_hypothesis76 hG hyp).cCoeff χ i = (z : ℂ)) :
    ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
        (H_sharp_alphaCF hG hyp χ)
      ∈ ZIrr ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S) := by
  classical
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  -- Restriction is pointwise, so it commutes with the defining sum.
  have hlin : ClassFunction.restrict K (H_sharp_alphaCF hG hyp χ)
      = ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
          (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
            (H_sharp_hypothesis76 hG hyp).zetaNormSq i) •
            ClassFunction.restrict K ((H_sharp_hypothesis76 hG hyp).zeta i) := by
    ext x
    rw [ClassFunction.restrict_apply, H_sharp_alphaCF,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.restrict_apply])
  rw [hlin]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  obtain ⟨z, hz⟩ := hc i
  rw [hz, star_intCast, div_eq_mul_inv, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ z (H_sharp_inv_normSq_restrict_zeta_mem_ZIrr hG hyp i)

/-- Carrier for the norm cascade (13.6)--(13.10). -/
structure NormCascadeData (hyp : Hypothesis (G := G)) where
  chars : CharacterDegreeData hyp
  lambda_norm_lower : Prop
  eta10_norm_lower : Prop
  eta01_norm_lower : Prop
  global_cover : Prop
  global_norm_lower : Prop
  analytic_inequality : Prop

/-! ### The (13.10) atoms

The (13.6)–(13.9) estimates are stated for shared rational atoms: `slam`/`seta` are the `G₀`
squared-norm sums of `λ^{τ₁}`/`η₁₀` (rational by the Galois integrality
`OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed`), and `g0`/`HS` are counting
ratios.  Materializing them as definitions lets the four estimates be stated (and attacked) as
independent producers while `analyticInequalityEstimates` assembles them `sorry`-free. -/

/-- The generic set `G₀` of (13.9) as a `Finset`. -/
noncomputable def Hypothesis.G0Finset [Finite G] (hyp : Hypothesis (G := G)) : Finset G :=
  (Set.toFinite hyp.G0).toFinset

open scoped Classical in
/-- **The squared-norm sum `Σ_{x∈A}‖χ(x)‖²` as a rational number** — defined as the natural
number it equals when the Galois-integrality applies (`χ ∈ ℤ[Irr]`, `A` cyclic-closed:
`exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed`), and junk `0` otherwise.  The (13.10) atoms
`slam`/`seta` are `normSqSumQ G₀ χ / |G|`. -/
noncomputable def normSqSumQ {H : Type*} [Group H] (A : Finset H) (χ : ClassFunction H ℂ) : ℚ :=
  if h : ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2 then ((Classical.choose h : ℕ) : ℚ) else 0

/-- The defining property of `normSqSumQ` on its good domain. -/
theorem normSqSumQ_spec {H : Type*} [Group H] {A : Finset H} {χ : ClassFunction H ℂ}
    (h : ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2) :
    ((normSqSumQ A χ : ℚ) : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2 := by
  rw [normSqSumQ, dif_pos h]
  exact_mod_cast Classical.choose_spec h

/-- **A subgroup of coprime `p`-order lies in a normal subgroup of `p`-coprime index.**  If
`W ≤ S`, `P.subgroupOf S ⊴ S`, `p` is coprime to `[S : P]`, and every `w ∈ W` has order dividing
`p`, then `W ≤ P`: each `w`'s image in `S/P` has order dividing both `p` and `[S : P]`, hence `1`.
This is the substantive core of `pgroup_le_of_normal_coprime_index`, taking the prime-vs-index
coprimality **directly** (so it applies when `p ∣ |P|` is unknown/false but `p ∤ [S : P]`, e.g. to
place `W₁` — of order `q ≠ p` — inside `T'` whose index is `p`). -/
theorem subgroup_le_of_normal_coprime_index_prime [Finite G]
    {S P W : Subgroup G} {p : ℕ}
    (hWS : W ≤ S) (hPnorm : (P.subgroupOf S).Normal)
    (hcop : Nat.Coprime p (P.subgroupOf S).index)
    (hWp : ∀ w ∈ W, orderOf w ∣ p) : W ≤ P := by
  haveI := hPnorm
  intro w hw
  have hwS : w ∈ S := hWS hw
  have horder : orderOf w ∣ p := hWp w hw
  have hmk : QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩ = 1 := by
    rw [← orderOf_eq_one_iff]
    have hd1 : orderOf (QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩) ∣ p := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [show orderOf (⟨w, hwS⟩ : ↥S) = orderOf w from
        (orderOf_injective S.subtype Subtype.coe_injective ⟨w, hwS⟩).symm]
      exact horder
    have hd2 : orderOf (QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩) ∣
        (P.subgroupOf S).index := orderOf_dvd_natCard _
    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
  have hmem : (⟨w, hwS⟩ : ↥S) ∈ P.subgroupOf S := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact hmk
  rwa [Subgroup.mem_subgroupOf] at hmem

/-- **A `p`-subgroup lies in a normal subgroup of coprime-to-`p` index.**  If `W ≤ S`,
`P.subgroupOf S ⊴ S`, `[S : P]` is coprime to `|P|`, and `p ∣ |P|`, then every element of `W` of
order dividing `p` lies in `P`: its image in `S/P` has order dividing both `p` and `[S : P]`, hence
`1`.  Generic group theory (used to place the prime-order factors `W₁`, `W₂` inside the Fitting
kernels `Q`, `P`).  Reduces to `subgroup_le_of_normal_coprime_index_prime` via `Coprime |P| [S:P]`
and `p ∣ |P|` ⟹ `p ∤ [S:P]` ⟹ `Coprime p [S:P]`. -/
theorem pgroup_le_of_normal_coprime_index [Finite G]
    {S P W : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hWS : W ≤ S) (hPnorm : (P.subgroupOf S).Normal)
    (hcop : Nat.Coprime (Nat.card ↥P) (P.subgroupOf S).index)
    (hpP : p ∣ Nat.card ↥P) (hWp : ∀ w ∈ W, orderOf w ∣ p) : W ≤ P := by
  have hcop2 : Nat.Coprime p (P.subgroupOf S).index :=
    (hp.coprime_iff_not_dvd).mpr fun hdvd =>
      Nat.Prime.not_dvd_one hp (hcop ▸ Nat.dvd_gcd hpP hdvd)
  exact subgroup_le_of_normal_coprime_index_prime hWS hPnorm hcop2 hWp

/-- **Peterfalvi (13.2.b)/(14.2.a): `W₂ ≤ P`.**  `W₂` is a `p`-group (`|W₂| = p`) inside `S`
(`W₂ ≤ W = S ⊓ T ≤ S`), while `P = S_F` is the normal Hall `p`-subgroup of `S` of order `p^q`
(`basic_structure`); hence `W₂ ≤ P` — the `F_p ⊆ F` identification of (14.2.a). -/
theorem W2_le_P [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W2 ≤ hyp.P := by
  obtain ⟨_, _, _, hP_card, _, _⟩ := basic_structure _hG hyp
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  refine pgroup_le_of_normal_coprime_index (S := hyp.S) hyp.p_prime ?_ ?_ ?_ ?_ ?_
  · have h1 : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have h2 : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
    exact h1.trans h2
  · rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.S
  · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
    rw [← hyp.P_eq_SF] at hHall
    have hcard_eq : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
    exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
  · rw [hP_card]; exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
  · intro w hw
    have heq : orderOf (⟨w, hw⟩ : ↥hyp.W2) = orderOf w :=
      (orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨w, hw⟩).symm
    have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W2) ∣ Nat.card ↥hyp.W2 := orderOf_dvd_natCard _
    rw [heq, ← hyp.p_eq_card_W2] at h1
    exact h1

set_option maxHeartbeats 1600000 in
open scoped Classical in
/-- **`μ_j ∈ 𝒮(H₀)` for the `S`-instance** ((13.3.a) membership): the nonzero `μ`-column sum
lies in the §9 family `𝒮(H₀)` of `toTypesIIIIIIVSetupS`.  The (4.5.a) witness `ψ`
(`mu_colSum_eq_induce`) transports along `huSub = S'` (`huSub_eq_derivedInG_subgroupOf`,
`induce_compHom_subgroupCongr`); the `𝒳`-conditions are `H₀ = ⊥ ⊆ Ker`
(`toTypesIIIIIIVSetupS_chief_H0_eq_bot`) and `H = P ⊄ Ker` from the (4.7) `W₂`-nonkernel
conjunct with `W₂ ≤ P` (`W2_le_P`). -/
theorem Hypothesis.mu_colSum_mem_sOf_H0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    (∑ i : Fin hyp.q, hyp.mu i j)
      ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG) chief.H0 := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Fintype ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) :=
    Fintype.ofFinite _
  letI : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨ψ, hψirr, hψeq, hψker⟩ := hyp.mu_colSum_eq_induce j
  have hKeq : OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)
      = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf _
  set χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ :=
    ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom ψ with hχdef
  have hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hKeq).surjective hψirr
  rw [OddOrder.Peterfalvi.S11.mem_sOf]
  refine ⟨⟨χ, hχirr⟩, ?_, ?_⟩
  · rw [OddOrder.Peterfalvi.S11.mem_xiOf]
    constructor
    · -- `H ⊄ Ker χ` (`xiSet`): a kernel containment would violate the `W₂`-nonkernel conjunct
      intro hsub
      apply hψker hj
      intro c hc
      have hcW2 : ((c : ↥hyp.S) : G) ∈ hyp.W2 :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hc))
      set x : ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) :=
        (MulEquiv.subgroupCongr hKeq).symm c with hxdef
      have hxval : ((x : ↥hyp.S) : G) = ((c : ↥hyp.S) : G) := by
        rw [hxdef]
        exact congrArg Subtype.val (MulEquiv.subgroupCongr_symm_apply hKeq c)
      have hxhInHu : x ∈ OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupS hG) := by
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
        show ((x : ↥hyp.S) : G) ∈ hyp.Sdata.H
        rw [hxval, hyp.Sdata.H_eq, ← hyp.P_eq_SF]
        exact W2_le_P hG hyp hcW2
      have hxker := hsub (SetLike.mem_coe.mpr hxhInHu)
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hxker
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
      have hxker' : χ x = χ 1 := hxker
      rw [hχdef, ClassFunction.compHom_apply, ClassFunction.compHom_apply, hxdef,
        MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] at hxker'
      exact hxker'
    · -- `H₀ = ⊥ ⊆ Ker χ`
      rw [hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief]
      intro x hx
      have hx1 : x = 1 := by
        have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp
          (SetLike.mem_coe.mp hx))
        rw [Subgroup.mem_bot] at h2
        exact Subtype.ext (Subtype.ext h2)
      rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
  · -- `∑ μ_{ij} = Ind_{HU}^S χ`
    rw [hψeq]
    have h1 : OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG) χ
        = ClassFunction.induce
            (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) χ := by
      unfold OddOrder.Peterfalvi.S11.induceHU
      congr! <;> exact Subsingleton.elim _ _
    have h2 : ClassFunction.induce ((derivedInG hyp.S).subgroupOf hyp.S) ψ
        = OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG) χ := by
      rw [h1, hχdef]
      exact (OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq ψ).symm
    exact h2

set_option maxHeartbeats 1600000 in
open scoped Classical FiniteInduce in
/-- **Peterfalvi (13.3.a)**: each nonzero `μ`-column sum `μ_j = ∑_i μ_{ij}` is induced from a
*linear* (degree-one) irreducible character of `H = PC`.

This is the honest statement of the `CharacterDegreeData.mu_j_linear_induced` field
(materializing (13.3.a) at the `S`-instance).  Assembly of the campaign pieces: `μ_j` lies in
the §9 family `𝒮(H₀)` (`mu_colSum_mem_sOf_H0`) and is reducible (`mu_colSum_not_irreducible`, a
sum of `q ≥ 2` distinct irreducibles), so the case-agnostic §9 `isIndHC`
(`reducible_sOf_H0_isIndHC`) gives `μ_j = Ind_{HC}(ψ)` with `ψ` linear irreducible; the `M`-level
`HC` is `(H ⊔ C).subgroupOf S = (PC).subgroupOf S` (`hcRealized_map_subtype_eq`,
`toTypesIIIIIIVSetupS_cSub_eq_C`, `H = P ⊔ C`), through which `ψ` transports to the required `θ`
on `hyp.H.subgroupOf hyp.S`. -/
theorem Hypothesis.mu_j_isIndPC [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        (∑ i : Fin hyp.q, hyp.mu i j)
          = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ := by
  classical
  haveI := hyp.finiteG
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  letI : Fintype ↥(OddOrder.Peterfalvi.S11.huSub data) := Fintype.ofFinite _
  letI : Fintype ↥(OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map
      (OddOrder.Peterfalvi.S11.huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map
      (OddOrder.Peterfalvi.S11.huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `μ_j ∈ 𝒮(H₀)`, reducible → `isIndHC`
  have hmem := hyp.mu_colSum_mem_sOf_H0 hG chief j hj
  have hred := hyp.mu_colSum_not_irreducible j
  obtain ⟨ψ, hψirr, hψone, hψeq⟩ :=
    OddOrder.Peterfalvi.S11.reducible_sOf_H0_isIndHC hG (hyp.mkSection11CharacterDataS hG chief)
      hmem hred
  -- `HC.map subtype = (H ⊔ C).subgroupOf S = (PC).subgroupOf S = hyp.H.subgroupOf S`
  have hHeq : data.H = hyp.P := by show hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ OddOrder.Peterfalvi.S11.cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map (OddOrder.Peterfalvi.S11.huSub data).subtype
      = hyp.H.subgroupOf hyp.S := by
    rw [OddOrder.Peterfalvi.S11.hcRealized_map_subtype_eq chief, hsupeq]
  -- transport `ψ` back to `hyp.H.subgroupOf S`
  set θ := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ with hθdef
  refine ⟨θ, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθdef, ClassFunction.compHom_apply, map_one, hψone]
  · rw [hψeq, hθdef,
      OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ]

/-- The distinguished `η₁₀ = τ₃(ω₁₀)` of the (13.7)/(13.9) estimates. -/
noncomputable def Hypothesis.eta10 (hyp : Hypothesis (G := G)) : ClassFunction G ℂ :=
  hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩

open scoped FiniteInduce in
/-- **`η₁₀` is a virtual character of `G`** — real content of the 3002-threaded grid:
`η₁₀ = τ₃(ω₁₀)` (`eta_eq_tau_omega`), `ω₁₀ ∈ ZIrr W` (`omega_mem_ZIrr`), and `τ₃` preserves
virtual characters (`tau3_mem_ZIrr`). -/
theorem Hypothesis.eta10_mem_ZIrr [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.eta10 ∈ ZIrr G := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)

/-- **Regularity of mixed products**: for `x ∈ W₁ ∖ {1}` and `y ∈ W₂ ∖ {1}` the product `x·y`
avoids `W₁ ∪ W₂` — otherwise one factor would lie in `W₁ ⊓ W₂ = ⊥`.  The membership feed of
`tau3_apply_of_regular` in the (1.10) congruence computations. -/
theorem Hypothesis.mul_notMem_W1_union_W2 (hyp : Hypothesis (G := G))
    {x y : G} (hx : x ∈ hyp.W1) (hy : y ∈ hyp.W2) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x * y ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := by
  rintro (hmem | hmem)
  · have hyW1 : y ∈ hyp.W1 := by
      have h := mul_mem (inv_mem hx) hmem
      rwa [inv_mul_cancel_left] at h
    have hbot : y ∈ hyp.W1 ⊓ hyp.W2 := ⟨hyW1, hy⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
    exact hy1 hbot
  · have hxW2 : x ∈ hyp.W2 := by
      have h := mul_mem hmem (inv_mem hy)
      rwa [mul_inv_cancel_right] at h
    have hbot : x ∈ hyp.W1 ⊓ hyp.W2 := ⟨hx, hxW2⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
    exact hx1 hbot

/-- **Peterfalvi (13.7), the (1.10) congruence for `η₁₀`**: for `y ∈ W₂^#`,
`η₁₀(y) ≡ 1 (mod (1 − ε))` in the algebraic integers, `ε` a primitive `q`-th root of unity.

Route: pick `x ∈ W₁^#`; `x` commutes with `y`, `x^q = 1`, and `η₁₀ ∈ ℤ[Irr G]`, so the
(1.10.a) congruence (`exists_integral_apply_sub_of_commute`) gives `η₁₀(xy) ≡ η₁₀(y)`.  The
product `xy` is `τ₃`-regular (`mul_notMem_W1_union_W2`), so `η₁₀(xy) = ω₁₀(xy)` ((3.2.c));
the (3.3) grid semantics factorize `ω₁₀(xy) = ω₁₀(x)·ω₁₀(y) = ω₁₀(x)` (issue 2033:
`omega_mul`, `omega_col_zero_apply_of_mem_W2`), a `q`-th root of unity
(`omega_pow_q_of_mem_W1`), which is `≡ 1 (mod (1 − ε))` by the geometric-sum identity. -/
theorem Hypothesis.eta10_apply_sub_one_integral [Finite G] (hyp : Hypothesis (G := G))
    {ε : ℂ} (hε : IsPrimitiveRoot ε hyp.q) {y : G} (hyW2 : y ∈ hyp.W2) (hy1 : y ≠ 1) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ hyp.eta10 y - 1 = (1 - ε) * z := by
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  -- pick `x ∈ W₁^#`
  obtain ⟨x, hxW1, hx1⟩ : ∃ x : G, x ∈ hyp.W1 ∧ x ≠ 1 := by
    haveI : Nontrivial ↥hyp.W1 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.q_eq_card_W1]; exact hyp.q_prime.one_lt)
    obtain ⟨x', hx'⟩ := exists_ne (1 : ↥hyp.W1)
    exact ⟨x', x'.2, fun h => hx' (Subtype.ext h)⟩
  -- `x^q = 1`
  have hxq : x ^ hyp.q = 1 := by
    have h1 : (⟨x, hxW1⟩ : ↥hyp.W1) ^ hyp.q = 1 := by
      rw [hyp.q_eq_card_W1]; exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  -- (1.10.a): `η₁₀(xy) − η₁₀(y) = (1 − ε)·z₁`
  obtain ⟨z₁, hz₁int, hz₁⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hyp.eta10_mem_ZIrr hxq (hyp.W1_commutes_W2 x hxW1 y hyW2)
  -- `τ₃`-regular value: `η₁₀(xy) = ω₁₀(xy)`
  have hxyW : x * y ∈ hyp.W := mul_mem (hW1W hxW1) (hW2W hyW2)
  have hreg : hyp.eta10 (x * y)
      = hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x * y, hxyW⟩ := by
    rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
    exact hyp.tau3_apply_of_regular _ _ hxyW (hyp.mul_notMem_W1_union_W2 hxW1 hyW2 hx1 hy1)
  -- factorize: `ω₁₀(xy) = ω₁₀(x)·ω₁₀(y) = ω₁₀(x)` (issue-2033 grid semantics)
  have hfact : hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x * y, hxyW⟩
      = hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x, hW1W hxW1⟩ := by
    have hmul : (⟨x * y, hxyW⟩ : ↥hyp.W) = ⟨x, hW1W hxW1⟩ * ⟨y, hW2W hyW2⟩ := rfl
    rw [hmul, hyp.omega_mul,
      hyp.omega_col_zero_apply_of_mem_W2 _ ⟨y, hW2W hyW2⟩ hyW2, mul_one]
  -- `ω₁₀(x)` is a `q`-th root of unity: `= ε^k`
  have hpow : hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x, hW1W hxW1⟩ ^ hyp.q
      = 1 := hyp.omega_pow_q_of_mem_W1 _ _ ⟨x, hW1W hxW1⟩ hxW1
  haveI : NeZero hyp.q := ⟨hyp.q_prime.pos.ne'⟩
  obtain ⟨k, -, hk⟩ := hε.eq_pow_of_pow_eq_one hpow
  -- `ε^k − 1 = (1 − ε)·z₂` with `z₂` integral (geometric sum)
  have hε_mem : ε ∈ integralClosure ℤ ℂ := hε.isIntegral hyp.q_prime.pos
  have hz₂int : IsIntegral ℤ (-(∑ i ∈ Finset.range k, ε ^ i)) :=
    (Subalgebra.sum_mem _ (fun i _ => Subalgebra.pow_mem _ hε_mem i) :
      IsIntegral ℤ (∑ i ∈ Finset.range k, ε ^ i)).neg
  have hz₂ : ε ^ k - 1 = (1 - ε) * (-(∑ i ∈ Finset.range k, ε ^ i)) := by
    rw [← geom_sum_mul ε k]; ring
  -- combine: `η₁₀(y) − 1 = (η₁₀(xy) − (1−ε)z₁) − 1 = (ε^k − 1) − (1−ε)z₁`
  refine ⟨-(∑ i ∈ Finset.range k, ε ^ i) - z₁, hz₂int.sub hz₁int, ?_⟩
  have hyval : hyp.eta10 y = hyp.eta10 (x * y) - (1 - ε) * z₁ := by linear_combination -hz₁
  rw [hyval, hreg, hfact, ← hk]
  linear_combination hz₂

/-! ### The (13.9)/(13.10) counting layer

The Parseval estimates (13.10.1)/(13.10.2) and the disjoint-cover count (13.10.3) rest on one
counting skeleton: `G` splits as `{1} ⊔ G₀ ⊔ (H^#)^G ⊔ (Q^#)^G` — the two saturations are
disjoint (element orders: `q ∤ |H|` while every nonidentity element of `Q` has order a positive
power of `q`) — and a conjugation-invariant sum over a saturation collapses to `[G : N]` times
the local sum (`IsTISubset.sum_conjClassSet`, issue 9011).  The `H`-side TI input is the proven
`H_sharp_isTISubset`; the `Q`-side is its `T`-mirror below. -/

section CountingLayer

open OddOrder.GroupTheory

/-- Under **Peterfalvi (13.1)**, the prime parameters are distinct: `W₁` and `W₂` are nontrivial
subgroups of the *cyclic* `W` with trivial intersection, so if `p = q` the `q`-element count of
`W` would exceed `φ(q)` (`IsCyclic.card_orderOf_eq_totient`): `W₁^#` supplies `q − 1` elements of
order `q` and `W₂^#` a further one outside `W₁`. -/
theorem Hypothesis.p_ne_q [Finite G] (hyp : Hypothesis (G := G)) : hyp.p ≠ hyp.q := by
  intro hpq
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  haveI : IsCyclic ↥hyp.W := hyp.W_cyclic
  haveI : Fintype ↥hyp.W := Fintype.ofFinite _
  classical
  set W1' : Subgroup ↥hyp.W := hyp.W1.subgroupOf hyp.W with hW1def
  set W2' : Subgroup ↥hyp.W := hyp.W2.subgroupOf hyp.W with hW2def
  have hc1 : Nat.card ↥W1' = hyp.q := by
    rw [hW1def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1W).toEquiv, ← hyp.q_eq_card_W1]
  have hc2 : Nat.card ↥W2' = hyp.q := by
    rw [hW2def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2W).toEquiv, ← hpq,
      ← hyp.p_eq_card_W2]
  have hinf : W1' ⊓ W2' = ⊥ := by
    ext a
    simp only [Subgroup.mem_inf, Subgroup.mem_bot, Subgroup.mem_subgroupOf, hW1def, hW2def]
    constructor
    · rintro ⟨h1, h2⟩
      have hmem : (a : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨h1, h2⟩
      rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hmem
      exact OneMemClass.coe_eq_one.mp hmem
    · rintro rfl; exact ⟨one_mem _, one_mem _⟩
  -- Nonidentity elements of an order-`q` subgroup have order `q`.
  have horder : ∀ (V : Subgroup ↥hyp.W), Nat.card ↥V = hyp.q →
      ∀ a : ↥hyp.W, a ∈ V → a ≠ 1 → orderOf a = hyp.q := by
    intro V hV a ha ha1
    have hdvd : orderOf a ∣ hyp.q := by
      have h1 : orderOf (⟨a, ha⟩ : ↥V) ∣ Nat.card ↥V := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk a ha, hV] at h1
    rcases (Nat.dvd_prime hyp.q_prime).mp hdvd with h1 | hq
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact hq
  -- The order-`q` element count of the cyclic `W` is `φ(q) = q − 1`.
  have hqdvd : hyp.q ∣ Fintype.card ↥hyp.W := by
    rw [← Nat.card_eq_fintype_card, ← hc1]
    exact Subgroup.card_subgroup_dvd_card W1'
  have htot := IsCyclic.card_orderOf_eq_totient (α := ↥hyp.W) hqdvd
  -- ... but `W₁^# ∪ {y}` (`y ∈ W₂^#`) already has `q` elements of order `q`.
  obtain ⟨y', hy'⟩ : ∃ y' : ↥W2', y' ≠ 1 := by
    haveI : Nontrivial ↥W2' := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [hc2]; exact hyp.q_prime.one_lt)
    exact exists_ne 1
  have hy1 : (y' : ↥hyp.W) ≠ 1 := by
    intro h
    exact hy' (OneMemClass.coe_eq_one.mp h)
  have hyW2 : (y' : ↥hyp.W) ∈ W2' := y'.2
  set F : Finset ↥hyp.W :=
    insert (y' : ↥hyp.W) ((Finset.univ.filter (· ∈ W1')).erase 1) with hFdef
  have hynotin : (y' : ↥hyp.W) ∉ (Finset.univ.filter (· ∈ W1')).erase 1 := by
    intro hmem
    have hyW1 : (y' : ↥hyp.W) ∈ W1' := (Finset.mem_filter.mp (Finset.mem_erase.mp hmem).2).2
    have : (y' : ↥hyp.W) ∈ W1' ⊓ W2' := ⟨hyW1, hyW2⟩
    rw [hinf] at this
    exact hy1 this
  have hW1card : (Finset.univ.filter (· ∈ W1')).card = hyp.q := by
    rw [← hc1, Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype]
  have hFcard : F.card = hyp.q := by
    rw [hFdef, Finset.card_insert_of_notMem hynotin,
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, W1'.one_mem⟩),
      hW1card]
    have := hyp.q_prime.two_le
    omega
  have hFsub : F ⊆ Finset.univ.filter (fun a => orderOf a = hyp.q) := by
    intro a ha
    rw [hFdef, Finset.mem_insert] at ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | ha
    · exact horder W2' hc2 _ hyW2 hy1
    · obtain ⟨ha1, hamem⟩ := Finset.mem_erase.mp ha
      exact horder W1' hc1 a (Finset.mem_filter.mp hamem).2 ha1
  have hle : hyp.q ≤ hyp.q.totient := by
    calc hyp.q = F.card := hFcard.symm
      _ ≤ (Finset.univ.filter (fun a => orderOf a = hyp.q)).card := Finset.card_le_card hFsub
      _ = hyp.q.totient := htot
  rw [Nat.totient_prime hyp.q_prime] at hle
  have := hyp.q_prime.two_le
  omega

/-- **`W₁ ≤ T'`** (local, pairing-free): the cyclic factor `W₁` (prime order `q`) lies in the derived
subgroup `T'`.  `W₁ ≤ W ≤ T`, `T' ⊴ T` with index `[T : T'] = |W₂| = p` (`W2_isComplement_T_deriv`),
and `q ≠ p` (`p_ne_q`); so the `q`-group `W₁` lands in the `p`-coprime-index normal `T'`
(`subgroup_le_of_normal_coprime_index_prime`).  Unlike the `T`-side `W₁ ≤ Q` (which needs the (8.4.d)
dual pairing), this containment is immediate from the abstract `Hypothesis` and feeds the `W₂`-side
centralizer localisation `W₁ ≤ T' ⊓ C(W₂)` used by `reconciled_typePData_T`. -/
theorem Hypothesis.W1_le_derivedInG_T [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ derivedInG hyp.T := by
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hWT : hyp.W ≤ hyp.T := by rw [hyp.W_eq_inter]; exact inf_le_right
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  have hW2T : hyp.W2 ≤ hyp.T := hW2W.trans hWT
  -- `T' ⊴ T`
  have hid : (derivedInG hyp.T).subgroupOf hyp.T = commutator ↥hyp.T :=
    Subgroup.comap_map_eq_self_of_injective hyp.T.subtype_injective (commutator ↥hyp.T)
  haveI hM'norm : ((derivedInG hyp.T).subgroupOf hyp.T).Normal := by rw [hid]; infer_instance
  -- `[T : T'] = |W₂| = p`
  have hindex : ((derivedInG hyp.T).subgroupOf hyp.T).index = hyp.p := by
    rw [hyp.W2_isComplement_T_deriv.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2T).toEquiv, ← hyp.p_eq_card_W2]
  refine subgroup_le_of_normal_coprime_index_prime (p := hyp.q) (hW1W.trans hWT) hM'norm ?_ ?_
  · rw [hindex]
    exact (Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr hyp.p_ne_q.symm
  · intro w hw
    have heq : orderOf (⟨w, hw⟩ : ↥hyp.W1) = orderOf w :=
      (orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨w, hw⟩).symm
    have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W1) ∣ Nat.card ↥hyp.W1 := orderOf_dvd_natCard _
    rw [heq, ← hyp.q_eq_card_W1] at h1
    exact h1

/-- `Q = T_F` is nontrivial: any type-`P` witness on `T` (available from `T_nonI` via
`typePData_of_isTypeNonI`) records `H = T_F` noncyclic, and `⊥` is cyclic. -/
theorem Hypothesis.Q_ne_bot [Finite G] (hyp : Hypothesis (G := G)) : hyp.Q ≠ ⊥ := by
  obtain ⟨tpd⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  intro hbot
  apply tpd.H_noncyclic
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hbot]
  infer_instance

/-- **`N_G(Q) = T`** — the `T`-side mirror of the (8.5.a) normalizer identity: `Q = T_F` is a
nontrivial `T`-normal subgroup of the maximal `T` of the minimal simple `G`, hence
self-normalizing at `T` (`normalizer_eq_self_of_subgroupOf_normal_of_ne_bot`). -/
theorem normalizer_Q_eq_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.Q : Set G) = hyp.T := by
  refine OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
    hyp.T_maximal ?_ ?_ hyp.Q_ne_bot
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.T

/-- Elements of the set-normalizer of `(K : Set G)` stabilize the sharp `K^# = K − 1` under
conjugation — the `hstab` input shape of `IsTISubset.sum_conjClassSet`. -/
theorem conj_smul_sharpSubgroup_eq {K N : Subgroup G}
    (hnorm : Subgroup.normalizer (K : Set G) = N) {l : G} (hl : l ∈ N) :
    MulAut.conj l • sharpSubgroup K = sharpSubgroup K := by
  have hlnorm : l ∈ Subgroup.normalizer (K : Set G) := hnorm ▸ hl
  rw [Subgroup.mem_set_normalizer_iff] at hlnorm
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply, sharpSubgroup, Set.mem_diff,
    Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨v, ⟨hvK, hv1⟩, rfl⟩
    refine ⟨(hlnorm v).mp hvK, fun heq => hv1 ?_⟩
    calc v = l⁻¹ * (l * v * l⁻¹) * l := by group
      _ = 1 := by rw [heq]; group
  · rintro ⟨hxK, hx1⟩
    refine ⟨l⁻¹ * x * l, ⟨?_, fun heq => hx1 ?_⟩, by group⟩
    · have := (hlnorm (l⁻¹ * x * l)).mpr
      rw [show l * (l⁻¹ * x * l) * l⁻¹ = x from by group] at this
      exact this hxK
    · calc x = l * (l⁻¹ * x * l) * l⁻¹ := by group
        _ = 1 := by rw [heq]; group

/-- **`N_G(H) = S`** (Peterfalvi (8.5.a)): `H = PC = F(S)` (`H_eq_fittingInG`) and
`N_G(F(S)) = S` (`normalizer_fittingInAmbient_eq_self`). -/
theorem normalizer_H_eq_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.H : Set G) = hyp.S := by
  have hHF : hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := hyp.H_eq_fittingInG
  have hnorm : Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) = hyp.S :=
    OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  rw [hHF]; exact hnorm

/-- **`V` is nilpotent** — the `U`-factor of `T`'s reconciled type-`P` datum.  `V` and any type-`P`
complement `tpd0.U` (from `typePData_of_isTypeNonI T_nonI`) both complement `Q = T_F` in `T' = QV`
(`derived_complement` / `Q_inf_V_eq_bot` + `T_deriv_eq_QV`), so Schur–Zassenhaus conjugacy inside
`↥T'` (`IsComplement'.exists_conj_of_coprime`, coprimality from `Q` being Hall in `T`) conjugates
`tpd0.U` onto `V`, transporting `Group.IsNilpotent` (`tpd0.U_nilpotent`).  Structurally the mirror of
the `S16` complement-conjugacy transport `isMulCommutative_typePData_U_of_V`.  Discharges the
`U_nilpotent` field of `reconciled_typePData_T` without matching the full `T`-side type-`P` datum. -/
theorem Hypothesis.isNilpotent_V [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : Group.IsNilpotent ↥hyp.V := by
  obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  have hQtpd : tpd0.H = hyp.Q := by rw [tpd0.H_eq, ← hyp.Q_eq_TF]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hU_le : tpd0.U ≤ derivedInG hyp.T := tpd0.U_le
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  -- `Q` complements `V` in `T'`.
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
          (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  -- `Q` complements `tpd0.U` in `T'` (from `tpd0.derived_complement`, `tpd0.H = Q`).
  have hUcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tpd0.U.subgroupOf (derivedInG hyp.T)) := by
    rw [← hQtpd]; exact tpd0.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)))
      ((hyp.Q.subgroupOf (derivedInG hyp.T)).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    have hcard : Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.Q.subgroupOf (derivedInG hyp.T)).index ∣
        (hyp.Q.subgroupOf hyp.T).index := by
      have htower : hyp.Q.relIndex (derivedInG hyp.T) *
          (derivedInG hyp.T).relIndex hyp.T = hyp.Q.relIndex hyp.T :=
        Subgroup.relIndex_mul_relIndex hyp.Q (derivedInG hyp.T) hyp.T hQ_le hM'_le_T
      show hyp.Q.relIndex (derivedInG hyp.T) ∣ hyp.Q.relIndex hyp.T
      exact ⟨(derivedInG hyp.T).relIndex hyp.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1)
  haveI hQsolv : IsSolvable ↥hyp.Q := hG.solvable_of_lt_top hyp.Q hQ_lt_top
  have hsolv : IsSolvable ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) ∨
      IsSolvable (↥(derivedInG hyp.T) ⧸ hyp.Q.subgroupOf (derivedInG hyp.T)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  -- Schur–Zassenhaus conjugates `tpd0.U` onto `V` inside `T'`; push nilpotency forward.
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hUcompl hVcompl
  haveI : Group.IsNilpotent ↥tpd0.U := tpd0.U_nilpotent
  have h1 : Group.IsNilpotent ↥(tpd0.U.subgroupOf (derivedInG hyp.T)) :=
    nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hU_le).symm
  haveI := h1
  have h2 : Group.IsNilpotent
      ↥((tpd0.U.subgroupOf (derivedInG hyp.T)).map (MulAut.conj n).toMonoidHom) :=
    nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective)
  have h3 : Group.IsNilpotent ↥(hyp.V.subgroupOf (derivedInG hyp.T)) := hn ▸ h2
  haveI := h3
  exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hV_le)

/-- **A type-`P` datum on `T` whose complement is the abstract `V` (and whose kernel is `Q`).**
The §13-level producer `typePData_of_isTypeNonI T_nonI` gives *some* `tpd0 : TypePData T`; its
complement `tpd0.U` and the §16-chosen `V` both complement `Q = T_F` in `T' = QV`, so Schur–Zassenhaus
inside `↥T'` (`IsComplement'.exists_conj_of_coprime`) conjugates `tpd0.U` onto `V` by an element
`g ∈ T'` (hence `g ∈ T`).  Because `g ∈ T`, conjugation by `g` fixes both `T` and its normal
`Q = T_F`, so whole-datum conjugation `tpd0.conj (MulAut.conj g)` — which transports *every* field of
`TypePData` (including `fitting_eq` and `secondDerived_le_fitting`) — again lands on `T`, with its
`U`-field equal to `V` and its `H`-field equal to `Q`.  This is the honest engine behind the
`fitting_eq`/`secondDerived_le_fitting`/`U_nilpotent` fields of `reconciled_typePData_T`. -/
theorem Hypothesis.exists_typePData_U_eq_V [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ d : TypePData hyp.T, d.U = hyp.V ∧ d.H = hyp.Q := by
  obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  have hQtpd : tpd0.H = hyp.Q := by rw [tpd0.H_eq, ← hyp.Q_eq_TF]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hU_le : tpd0.U ≤ derivedInG hyp.T := tpd0.U_le
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  -- `Q` complements `V` in `T'` (verbatim from `isNilpotent_V`).
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
          (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hUcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tpd0.U.subgroupOf (derivedInG hyp.T)) := by
    rw [← hQtpd]; exact tpd0.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)))
      ((hyp.Q.subgroupOf (derivedInG hyp.T)).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    have hcard : Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.Q.subgroupOf (derivedInG hyp.T)).index ∣
        (hyp.Q.subgroupOf hyp.T).index := by
      have htower : hyp.Q.relIndex (derivedInG hyp.T) *
          (derivedInG hyp.T).relIndex hyp.T = hyp.Q.relIndex hyp.T :=
        Subgroup.relIndex_mul_relIndex hyp.Q (derivedInG hyp.T) hyp.T hQ_le hM'_le_T
      show hyp.Q.relIndex (derivedInG hyp.T) ∣ hyp.Q.relIndex hyp.T
      exact ⟨(derivedInG hyp.T).relIndex hyp.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1)
  haveI hQsolv : IsSolvable ↥hyp.Q := hG.solvable_of_lt_top hyp.Q hQ_lt_top
  have hsolv : IsSolvable ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) ∨
      IsSolvable (↥(derivedInG hyp.T) ⧸ hyp.Q.subgroupOf (derivedInG hyp.T)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hUcompl hVcompl
  -- The conjugator, coerced to `G`.
  set g : G := (↑n : G) with hgdef
  have hg_mem_T' : g ∈ derivedInG hyp.T := n.2
  have hg_mem_T : g ∈ hyp.T := hM'_le_T hg_mem_T'
  -- Lift the `subgroupOf`-level conjugacy `hn` to a `G`-level equation `conj g • U = V`.
  have hcomp : (derivedInG hyp.T).subtype.comp (MulAut.conj n).toMonoidHom
      = (MulAut.conj g).toMonoidHom.comp (derivedInG hyp.T).subtype := by
    ext k
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hgdef, Subgroup.coe_mul, Subgroup.coe_inv]
  have hUmap : tpd0.U.map (MulAut.conj g).toMonoidHom = hyp.V := by
    have key := congrArg (Subgroup.map (derivedInG hyp.T).subtype) hn
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hU_le, Subgroup.map_subgroupOf_eq_of_le hV_le] at key
    exact key
  have hUV : (MulAut.conj g) • tpd0.U = hyp.V := by
    rw [pointwise_mulAut_smul_eq_map]; exact hUmap
  -- Conjugation by `g ∈ T` fixes `T` and its normal `Q`.
  have hgT : (MulAut.conj g) • hyp.T = hyp.T := Subgroup.conj_smul_eq_self_of_mem hg_mem_T
  have hgQ : (MulAut.conj g) • hyp.Q = hyp.Q := by
    have hgN : ∀ h, h ∈ hyp.Q ↔ g * h * g⁻¹ ∈ hyp.Q := by
      have := Subgroup.mem_set_normalizer_iff.mp (hT_le_NQ hg_mem_T)
      simpa only [SetLike.mem_coe] using this
    ext x
    rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hgN y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hgN (g⁻¹ * x * g)).mpr ?_, ?_⟩
      · rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x from by group]
      · show MulAut.conj g (g⁻¹ * x * g) = x
        simp only [MulAut.conj_apply]; group
  -- Whole-datum conjugation, cast back to `TypePData T`.  The `.U`/`.H` projections have constant
  -- codomain `Subgroup G`, so they commute with the `▸` cast on the index (proved by `subst` on a
  -- fresh index variable — `hgT` itself has `T` on both sides, so casing it directly fails).
  have hcastU : ∀ {S : Subgroup G} (h : S = hyp.T) (d : TypePData S), (h ▸ d).U = d.U := by
    intro S h d; subst h; rfl
  have hcastH : ∀ {S : Subgroup G} (h : S = hyp.T) (d : TypePData S), (h ▸ d).H = d.H := by
    intro S h d; subst h; rfl
  refine ⟨hgT ▸ tpd0.conj (MulAut.conj g), ?_, ?_⟩
  · rw [hcastU hgT, show (tpd0.conj (MulAut.conj g)).U = (MulAut.conj g) • tpd0.U from rfl, hUV]
  · rw [hcastH hgT, show (tpd0.conj (MulAut.conj g)).H = (MulAut.conj g) • tpd0.H from rfl, hQtpd,
      hgQ]

/-- **`M'` is a Hall subgroup of a type-`P` maximal** (`Coprime |M'| [M:M']`).  A `κ(M)`-Hall `K`
exists (`exists_isHallSubgroup_kappa_ge`, `X := ⊥`), is cyclic (Theorem 14.7 `typeP_duality`:
`K ⊔ K*` cyclic) and complements `M'` (`typeP_derivedInG_isComplement_kappaHall`); then
`coprime_card_derived_kappaHall_of_isComplement'` gives `(|M'|, |K|) = 1` with `|K| = [M : M']`.

This is the coprimality behind the Schur–Zassenhaus conjugacy of complements to `M'` — it is
**ungated** (needs only `IsTypeP M`), so the earlier belief that `p ∤ |T'|` requires
`FieldNormalizerData` (via `W2_card_coprime_Q_card`/`Q_elementaryAbelian`) was too pessimistic: the
`κ`-Hall route supplies it directly.  Used to align a type-`P` datum's `κ`-factor to any given
complement of `M'` (e.g. the abstract `W₂` on `T`, `W2_isComplement_T_deriv`). -/
theorem coprime_card_derivedInG_index_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP M) :
    Nat.Coprime (Nat.card ↥(derivedInG M)) ((derivedInG M).subgroupOf M).index := by
  classical
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (bot_le (a := M))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstar
  haveI hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hKM hKhall hKstar
    haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcompl :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hKhall
  have hcop :=
    OddOrder.BG.Ch4.S14.coprime_card_derived_kappaHall_of_isComplement' hKhall hcompl
  have h1 : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
  have h2 : Nat.card ↥(K.subgroupOf M) = ((derivedInG M).subgroupOf M).index :=
    (hcompl.symm.index_eq_card).symm
  rwa [h1, h2] at hcop

/-- **Fact A: `W₂` is a `κ`-Hall of `T`** (ungated).  `W₂` complements `T'`
(`W2_isComplement_T_deriv`); a produced `κ(T)`-Hall `K` (`exists_isHallSubgroup_kappa_ge`, cyclic,
also complementing `T'`) is `T`-conjugate to `W₂` by Schur–Zassenhaus
(`IsComplement'.exists_conj_of_coprime`, coprimality `coprime_card_derivedInG_index_of_isTypeP`);
Hall-ness transfers along the conjugation (`IsHallSubgroup.mulAut_smul`).  This discharges the `hFactA`
residual of `reconciled_typePData_T` with no `FieldNormalizerData`/(14.9) input. -/
theorem Hypothesis.W2_isKappaHall_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.T)
      (hyp.W2.subgroupOf hyp.T) := by
  classical
  have hP := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.T_maximal hyp.T_nonI
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hyp.T_maximal (bot_le (a := hyp.T))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (K : Set G) with hKstar
  haveI hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hyp.T_maximal hP hKM hKhall hKstar
    haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcomplK :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hyp.T_maximal hP hKM hKhall
  haveI : IsSolvable ↥hyp.T := hG.solvable_of_mem_maximalSubgroups hyp.T_maximal
  haveI hNnorm : ((derivedInG hyp.T).subgroupOf hyp.T).Normal := by
    rw [show (derivedInG hyp.T).subgroupOf hyp.T = commutator ↥hyp.T from
      Subgroup.comap_map_eq_self_of_injective hyp.T.subtype_injective (commutator ↥hyp.T)]
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T))
      ((derivedInG hyp.T).subgroupOf hyp.T).index := by
    have hderivM_le : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
    have hcard : Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T) = Nat.card ↥(derivedInG hyp.T) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hderivM_le).toEquiv
    rw [hcard]
    exact coprime_card_derivedInG_index_of_isTypeP hG hyp.T_maximal hP
  obtain ⟨n, -, hn⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance)
    hcomplK hyp.W2_isComplement_T_deriv
  have hHall := hKhall.mulAut_smul (MulAut.conj n)
  rw [pointwise_mulAut_smul_eq_map] at hHall
  rw [show ((MulAut.conj n).toMonoidHom : ↥hyp.T →* ↥hyp.T) = ↑(MulAut.conj n) from rfl] at hn
  rwa [hn] at hHall

/-- **A complement of `M'` in a type-`P` maximal is a `κ(M)`-Hall subgroup** (ungated, generic).
Extracted from the `W₂`/`T` argument (`W2_isKappaHall_T`): a produced `κ(M)`-Hall `K` is cyclic and
complements `M'` (`typeP_derivedInG_isComplement_kappaHall`); Schur–Zassenhaus
(`coprime_card_derivedInG_index_of_isTypeP`) conjugates it onto any given complement `W` of `M'` in
`M`, and Hall-ness transfers along the conjugation (`IsHallSubgroup.mulAut_smul`).  Used for the
`S`-side Fact A (`W₁` κ-Hall of `S`, via the carried `Sdata.M_complement`). -/
theorem isKappaHall_of_isComplement_derivedInG [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M W : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hWcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (W.subgroupOf M)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (W.subgroupOf M) := by
  classical
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (bot_le (a := M))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstar
  haveI hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hKM hKhall hKstar
    haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcomplK :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hKhall
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  haveI hNnorm : ((derivedInG M).subgroupOf M).Normal := by
    rw [show (derivedInG M).subgroupOf M = commutator ↥M from
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)]
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      ((derivedInG M).subgroupOf M).index := by
    have hderivM_le : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hcard : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hderivM_le).toEquiv
    rw [hcard]
    exact coprime_card_derivedInG_index_of_isTypeP hG hM hP
  obtain ⟨n, -, hn⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance)
    hcomplK hWcompl
  have hHall := hKhall.mulAut_smul (MulAut.conj n)
  rw [pointwise_mulAut_smul_eq_map] at hHall
  rw [show ((MulAut.conj n).toMonoidHom : ↥M →* ↥M) = ↑(MulAut.conj n) from rfl] at hn
  rwa [hn] at hHall

/-- **Fact A (`S`-side): `W₁` is a `κ`-Hall of `S`** (ungated).  `W₁` complements `S'`
(the carried `Sdata.M_complement`, reconciled to `W₁` via `Sdata_W1_eq`), so
`isKappaHall_of_isComplement_derivedInG` applies.  The `S`-side companion of `W2_isKappaHall_T`,
used to feed `typeP_duality`/`exists_partner`/`kappaHall_primes_subset_sigma_partner` on `S`. -/
theorem Hypothesis.W1_isKappaHall_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.S)
      (hyp.W1.subgroupOf hyp.S) := by
  have hPS := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  have hW1compl : Subgroup.IsComplement' ((derivedInG hyp.S).subgroupOf hyp.S)
      (hyp.W1.subgroupOf hyp.S) := by
    have h := hyp.Sdata.M_complement
    rwa [hyp.Sdata_W1_eq] at h
  exact isKappaHall_of_isComplement_derivedInG hG hyp.S_maximal hPS hW1compl

/-- **Fact B (`S`-side): `M_σ(S) ⊓ C_G(W₁) = W₂`** (the (8.4.d) centralizer law for `S`, ungated).
`⊆`: `M_σ(S) ≤ S'` (`Msigma_le_derived`), then `S' ⊓ C(W₁) = W₂` is the carried datum
`Sdata.derivedInG_inf_centralizer_W1_eq` (reconciled via `Sdata_W1_eq`/`Sdata_W2_eq`).  `⊇`:
`W₂ = Sdata.W2 ≤ Sdata.H = M_F(S) = M_σ(S)` (type-II `S`, `maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`)
and `W₂ ≤ C(W₁)` (`W1_commutes_W2`).  This is the `Kstar = W₂` identification that lets
`typeP_duality`/`typeP_partner_structure` on `S` output Fact B (`W₁ = M_σ(Mstar) ⊓ C(W₂)`) for the
partner. -/
theorem Hypothesis.Msigma_S_inf_centralizer_W1_eq_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) = hyp.W2 := by
  classical
  have hSder : derivedInG hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) = hyp.W2 := by
    have h := hyp.Sdata.derivedInG_inf_centralizer_W1_eq
    rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq] at h
    exact h
  have hMFeq : maxNilpotentNormalHall hyp.S = OddOrder.BG.Ch3.S10.Msigma hyp.S :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hyp.S_maximal
      (Or.inr (OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2))
  refine le_antisymm ?_ (le_inf ?_ ?_)
  · calc OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G)
        ≤ derivedInG hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) :=
          inf_le_inf_right _ (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hyp.S_maximal)
      _ = hyp.W2 := hSder
  · rw [← hMFeq]
    calc hyp.W2 = hyp.Sdata.W2 := hyp.Sdata_W2_eq.symm
      _ ≤ hyp.Sdata.H := le_trans hyp.Sdata.W2_le inf_le_left
      _ = maxNilpotentNormalHall hyp.S := hyp.Sdata.H_eq
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hyp.W1_commutes_W2 x hx y hy

/-- **`opiCoreInG` is conjugation-equivariant** (public form of the S14/S10 private helpers, needed
for the `Msigma` conjugation used in the `S15` pairing carve-out).  `φ • O_π(H) = O_π(φ • H)` via
`oPiCore.map_eq_of_mulEquiv` transported along the conjugation isomorphism `↥H ≃* ↥(φ • H)`. -/
theorem opiCoreInG_conj_smul [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • OddOrder.GroupTheory.opiCoreInG π H
      = OddOrder.GroupTheory.opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H := (pointwise_mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • OddOrder.GroupTheory.opiCoreInG π H
      = (OddOrder.GroupTheory.opiCoreInG π H).map (φ : G →* G) := pointwise_mulAut_smul_eq_map φ _
    _ = ((OddOrder.Isaacs.Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by
        rw [Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥H).map
          ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((OddOrder.Isaacs.Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map
          (φ • H).subtype := by rw [← Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv]

/-- **`M_σ` is conjugation-equivariant** (`M_σ(Mᵍ) = M_σ(M)ᵍ`, public form).  From
`opiCoreInG_conj_smul` and `sigma_conj_smul_eq` (`σ(Mᵍ) = σ(M)`). -/
theorem Msigma_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M)
      = MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
  simp only [OddOrder.BG.Ch3.S10.Msigma]
  rw [OddOrder.BG.Ch4.S14.sigma_conj_smul_eq, ← opiCoreInG_conj_smul]

/-- **Fact B (`T`-side): `W₁ = M_σ(T) ⊓ C_G(W₂)`** (the (8.4.d)-dual centralizer law for `T`, ungated
via the type-`P` pairing — Coq `PFsection8` `typeP_cent_compl`/`FTtypeP_pair_witness`).

This is the last residual of `reconciled_typePData_T` (issue 9073); it is genuine §13 pairing content
proved *without* assuming `(14.9)`/`IsTypeII T`, by descending to `S`'s type-`P` structure:

* Apply `typeP_duality`/`exists_partner`/`typeP_partner_structure` to `S` (`hKS` = Fact A for `S`,
  `hKstarSW2` = Fact B for `S`, `Kstar = W₂`): the partner `Mstar` satisfies Fact B *for* `Mstar`,
  `W₁ = M_σ(Mstar) ⊓ C(W₂)` (`hKeq`), plus `W₂` is a `κ`-Hall of `Mstar` and the pair is
  nonconjugate to `S`.
* `Mstar` is `G`-conjugate to `T`: `theorem88_caseB` at `Mstar` (type-`P`, non-`I`, `≁ S`) leaves
  only `∃g, Mstarᵍ = T`.
* `⊇`: `q ∈ σ(Mstar) = σ(T)` (`kappaHall_primes_subset_sigma_partner` + `sigma_conj_smul_eq`), so the
  `q`-group `W₁ ≤ T` lands in the normal Hall `σ(T)`-subgroup `M_σ(T)`
  (`sigma_subgroup_le_Msigma_of_isHall`), and `W₁ ≤ C(W₂)` (`W1_commutes_W2`).
* `⊆`/cardinality: a fix-`W` correction (`exists_conj_eq_of_isHall_subgroupOf`, matching the two
  `κ`-Halls `W₂` of `T`, `Mstar`) gives `n` with `Tⁿ = Mstar`, `W₂ⁿ = W₂`, whence
  `(M_σ(T) ⊓ C(W₂))ⁿ = M_σ(Mstar) ⊓ C(W₂) = W₁`, so `|M_σ(T) ⊓ C(W₂)| = |W₁|`; with `⊇` and
  `eq_of_le_of_card_ge` this forces equality. -/
theorem Hypothesis.W1_eq_Msigma_T_inf_centralizer_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.W1 = OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G) := by
  classical
  -- `S`-side data.
  have hPS := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  have hW1S : hyp.W1 ≤ hyp.S :=
    (by rw [hyp.W_eq_join]; exact le_sup_left : hyp.W1 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_left)
  have hW2T : hyp.W2 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_right : hyp.W2 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hKS := hyp.W1_isKappaHall_S hG
  set KstarS : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) with hKstarSdef
  have hKstarSW2 : KstarS = hyp.W2 := by
    rw [hKstarSdef]; exact hyp.Msigma_S_inf_centralizer_W1_eq_W2 hG
  haveI : IsSolvable ↥hyp.S := hG.solvable_of_mem_maximalSubgroups hyp.S_maximal
  obtain ⟨US, hUS'⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥hyp.S)
    ((OddOrder.BG.Ch4.S14.kappa hyp.S ∪ OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ)
  have hU_S : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa hyp.S ∪ OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ)
      ((US.map hyp.S.subtype).subgroupOf hyp.S) := by
    have hUSeq : (US.map hyp.S.subtype).subgroupOf hyp.S = US :=
      Subgroup.comap_map_eq_self_of_injective hyp.S.subtype_injective US
    rw [hUSeq]; exact hUS'
  -- Partner `Mstar` of `S` (Theorem 14.7), with Fact B *for* `Mstar`.
  obtain ⟨Mstar, hMstarne, hmem, hpart⟩ :=
    OddOrder.BG.Ch4.S14.exists_partner hG (OddOrder.BG.Ch4.S14.dummySigmaDecomposition G)
      hyp.S_maximal hPS hW1S hKS hKstarSdef hU_S
  obtain ⟨hMstarmax, hMstarP, hKstarleMstar, hKstar_hall, hKeq⟩ :=
    OddOrder.BG.Ch4.S14.typeP_partner_structure hG hyp.S_maximal hPS hW1S hKS hKstarSdef hU_S
      hmem hMstarne hpart
  rw [hKstarSW2] at hKeq hKstarleMstar hKstar_hall
  -- `hKeq : W₁ = M_σ(Mstar) ⊓ C(W₂)`; `hKstar_hall : W₂ κ-Hall of Mstar`; `W₂ ≤ Mstar`.
  have hncSMstar : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup hyp.S Mstar :=
    OddOrder.BG.Ch4.S14.typeP_family_pairwise_nonconjugate hG hyp.S_maximal hPS hW1S hKS
      hKstarSdef hU_S (Or.inl rfl) hmem (Ne.symm hMstarne)
  have hMstarNotI : ¬ OddOrder.GroupTheory.IsTypeI Mstar := by
    intro hI
    exact absurd ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarmax).1.mp hI)
      (Set.nonempty_iff_ne_empty.mp hMstarP)
  -- `Mstar` is `G`-conjugate to `T`.
  obtain ⟨g, hg⟩ : ∃ g : G, MulAut.conj g • Mstar = hyp.T := by
    rcases hyp.theorem88_caseB Mstar hMstarmax with hI | hS | hT
    · exact absurd hI hMstarNotI
    · exact absurd
        (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.symm
          (hS : OddOrder.BG.Ch4.S14.IsConjugateSubgroup Mstar hyp.S)) hncSMstar
    · exact hT
  -- `q ∈ σ(T)`, hence `W₁ ≤ M_σ(T)` (normal Hall `σ`-subgroup contains every `σ`-subgroup).
  have hqK : hyp.q ∣ Nat.card ↥hyp.W1 := ⟨1, by rw [mul_one]; exact hyp.q_eq_card_W1.symm⟩
  have hqMstar : hyp.q ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
    OddOrder.BG.Ch4.S14.kappaHall_primes_subset_sigma_partner hG hyp.S_maximal hPS hW1S hKS
      hKstarSdef hU_S hpart hyp.q_prime hqK
  have hqT : hyp.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.T := by
    rw [← hg, OddOrder.BG.Ch4.S14.sigma_conj_smul_eq]; exact hqMstar
  have hW1T : hyp.W1 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_left : hyp.W1 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hW1piT : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
      (OddOrder.BG.Ch3.S10.sigma hyp.T) hyp.W1 := by
    intro r hr
    have hpf : (Nat.card ↥hyp.W1).primeFactors = {hyp.q} := by
      rw [← hyp.q_eq_card_W1, Nat.Prime.primeFactors hyp.q_prime]
    rw [hpf, Finset.mem_singleton] at hr
    rw [hr]; exact hqT
  have hW1MsigmaT : hyp.W1 ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hyp.T_maximal) hW1T hW1piT
  have hSupset : hyp.W1 ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G) :=
    le_inf hW1MsigmaT (by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hyp.W1_commutes_W2 x hx y hy).symm.eq)
  -- fix-`W` correction: a conjugator `n` with `Tⁿ = Mstar` and `W₂ⁿ = W₂`.
  have hg0 : MulAut.conj g⁻¹ • hyp.T = Mstar := by
    rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hW2hallT := hyp.W2_isKappaHall_T hG
  have hconjW2hall := OddOrder.BG.Ch4.S14.isHall_kappa_subgroupOf_conj g⁻¹ hg0 hW2T hW2hallT
  have hconjW2le : MulAut.conj g⁻¹ • hyp.W2 ≤ Mstar := by
    rw [← hg0]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hW2T
  haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
  obtain ⟨w, hwMstar, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf
    inferInstance hconjW2le hKstarleMstar hconjW2hall hKstar_hall
  set n : G := w * g⁻¹ with hn_def
  have hnW2 : MulAut.conj n • hyp.W2 = hyp.W2 := by
    rw [hn_def, map_mul, mul_smul]; exact hw
  have hnT : MulAut.conj n • hyp.T = Mstar := by
    rw [hn_def, map_mul, mul_smul, hg0]
    exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwMstar)
  -- `(M_σ(T) ⊓ C(W₂))ⁿ = M_σ(Mstar) ⊓ C(W₂) = W₁`.
  have hconj_eq : MulAut.conj n •
      (OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G)) = hyp.W1 := by
    rw [Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul, hnW2,
      ← Msigma_conj_smul_eq, hnT]
    exact hKeq.symm
  -- cardinality: `|M_σ(T) ⊓ C(W₂)| = |W₁|`, and with `⊇`, equality.
  have hcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓
      Subgroup.centralizer (hyp.W2 : Set G)) = Nat.card ↥hyp.W1 := by
    rw [← hconj_eq, Subgroup.pointwise_smul_def]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective).toEquiv
  exact Subgroup.eq_of_le_of_card_ge hSupset (le_of_eq hcard)

/-- **`reconciled_typePData_T` の 2 residual を pairing facts から** (Fact A ∧ Fact B → 両 field, 実証明).
`W₂` が `T` の `κ`-Hall (**Fact A**) かつ `W₁ = M_σ(T) ⊓ C(W₂)` (**Fact B**) — `typeP_partner_structure`
(`S14`) が `S` の partner に対して供給する 2 つの (8.4.d)-dual pairing facts — があれば、既存の一般
type-`P` 機構 (`typeP_kstar_in_mf` / `typeP_derivedInG_inf_centralizer_kappaElement_eq`, いずれも
`M := T`, `K := W₂`, `K* := W₁`) が `reconciled_typePData_T` の両 field を discharge する:
`W₁ ≤ Q ⊓ T''` (`W2_le` field) と `∀ x ∈ W₂#, T' ⊓ C(x) = W₁` (`centralizer_W1` field)。

これは gated-endpoint skeleton (issue 9073): 2 sorry を **精密な pairing 2 facts** (κ-Hall + Kstar 同定)
に還元し、その **十分性を実証明で verify**。残余 Fact A + Fact B は `typeP_partner_structure` を `S` に
適用 (κ-Hall `W₁`, `Kstar = M_σ(S)⊓C(W₁) = W₂`) すれば partner `Mstar = T` に対し供給される
(S-side κ-Hall setup + Z-family covering の wiring が次段)。 -/
theorem Hypothesis.reconciled_residuals_of_pairing_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hFactA : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.T)
      (hyp.W2.subgroupOf hyp.T))
    (hFactB : hyp.W1 = OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G)) :
    hyp.W1 ≤ hyp.Q ⊓ secondDerivedInAmbient hyp.T ∧
      (∀ x ∈ hyp.W2, x ≠ 1 →
        derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) = hyp.W1) := by
  have hW2T : hyp.W2 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_right : hyp.W2 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hP := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.T_maximal hyp.T_nonI
  refine ⟨?_, ?_⟩
  · -- `W2_le`: `W₁ = K* ≤ M_F(T) ⊓ T''` from `typeP_kstar_in_mf` (Corollary 15.6).
    have hk := OddOrder.BG.Ch4.S15.typeP_kstar_in_mf hG hyp.T_maximal hP hW2T hFactA hFactB
    rw [hyp.Q_eq_TF]
    exact le_inf hk.2.2.1 hk.2.2.2.1
  · -- `centralizer_W1`: `T' ⊓ C(x) = K* = W₁` for `x ∈ W₂#` (Theorem A(5) + Dedekind).
    exact OddOrder.BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq
      hG hyp.T_maximal hP hW2T hFactA hFactB

/-- **T-side type-`P` structure reconciled to the abstract `V`/`W₂`** (the honest replacement for the
withdrawn `Tdata` spine carrier; HUB tick² 2026-06-30).  `T` is type non-I (`T_nonI`), hence type-`P`,
and the §16-chosen complement `V` (κ-Hall-invariant) / cyclic factor `W₂` form a type-`P`
decomposition of `T`: there is a `TypePData T` with `.U = V`, `.W1 = W₂`, and `.W2 = W₁` (the dual
cyclic factor `C_{T'}(W₂#)` of `T`'s type-`P` structure is exactly the shared `W₁`).

This is the genuine §13 reconciliation — **TRUE**, and the right §13-level statement: it asserts only
the *general* type-`P` structure of `T` (available from `T_nonI` at §13), reconciled to the abstract
`V`/`W₂`.  (The sharper `IsTypeP2 T` is *equivalent* to the (14.9) conclusion `IsTypeII T` by the BG
type dictionary `proposition_type_classification` — `IsTypeII M ↔ IsTypeP2 M` — but is not needed for
the reconciliation itself, so this stays a clean §13 obligation.)  It lives **off the FT spine**: the
`V`-side helpers cite this obligation, keeping `section16TypePStructure_of_isMinimalSimpleOdd`
sorry-free.  Gated on §13; declared sorried.  (Relocated from `S15_SAndT` for the (13.9)/(13.10)
counting layer — the type-V exclusion of `Q_sharp_isTISubset` and the `|T|` decomposition read it.) -/
theorem reconciled_typePData_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : TypePData hyp.T, data.U = hyp.V ∧ data.W1 = hyp.W2 ∧ data.W2 = hyp.W1 := by
  -- `W₂, W₁ ≤ W` from the (13.1) join `W = W₁ ⊔ W₂`, and `W ≤ T` from `W = S ⊓ T`.
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hWT : hyp.W ≤ hyp.T := by rw [hyp.W_eq_inter]; exact inf_le_right
  haveI hWcyc : IsCyclic ↥hyp.W := hyp.W_cyclic
  -- Cyclic factors: a subgroup of the cyclic `W` is cyclic (transport along `subgroupOfEquivOfLe`).
  have hW2cyc : IsCyclic ↥hyp.W2 :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hW2W).surjective
  have hW1cyc : IsCyclic ↥hyp.W1 :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hW1W).surjective
  -- **(8.4.d)-dual pairing residuals** for the `W2_le`/`centralizer_W1` fields.  These are exactly the
  -- two facts `typeP_partner_structure` (applied to `S`) supplies for its partner `T`: `W₂` a `κ`-Hall
  -- of `T` (**Fact A**) and `W₁ = M_σ(T) ⊓ C(W₂)` (**Fact B**).  Their *sufficiency* is verified by
  -- `reconciled_residuals_of_pairing_facts` (via `typeP_kstar_in_mf` /
  -- `typeP_derivedInG_inf_centralizer_kappaElement_eq`); the two residuals are honestly gated on the
  -- §13 `typeP_partner` port (issue 9073) whose remaining step wires `typeP_partner_structure`'s inputs
  -- (S-side κ-Hall + Z-family covering) from the abstract `Hypothesis`.
  -- **Fact A** (`W₂` κ-Hall of `T`) is now proven ungated (`W2_isKappaHall_T`, via the produced
  -- κ-Hall + Schur–Zassenhaus).  **Fact B** (`W₁ = M_σ(T) ⊓ C(W₂)`) remains the sole residual — the
  -- reverse cyclic-factor identification, supplied by `typeP_partner_structure` applied to `S`.
  have hFactA := hyp.W2_isKappaHall_T hG
  have hFactB : hyp.W1 =
      OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G) :=
    hyp.W1_eq_Msigma_T_inf_centralizer_W2 hG
  obtain ⟨hW2le_pf, hCentW1_pf⟩ := hyp.reconciled_residuals_of_pairing_facts hG hFactA hFactB
  refine ⟨{
    H := hyp.Q
    U := hyp.V
    W1 := hyp.W2
    W2 := hyp.W1
    W := hyp.W
    H_eq := hyp.Q_eq_TF
    H_le := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
    U_le := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
    W1_le := hW2W.trans hWT
    -- **Precise residual (`W2_le`, goal `hyp.W1 ≤ hyp.Q ⊓ secondDerivedInAmbient hyp.T`).**
    -- This is the T-side dual of the *carried* S-side field `Sdata.W2_le` (`W₂ ≤ P ⊓ S''`).  Both
    -- halves are `IsTypeP2 hyp.T` (≡ `IsTypeII hyp.T`, BG (14.9))-gated, which is unavailable at
    -- §13 (`IsTypeII hyp.T` lives in `S16` = import-downstream; see `T_typeII`):
    --   • `hyp.W1 ≤ hyp.Q`: needs `hyp.q ∣ Nat.card ↥hyp.Q`; every route (`card_Q_eq`,
    --     `exists_sylow_coe_eq_Q`, `pgroup_le_of_normal_coprime_index` dualizing `W2_le_P`) requires
    --     `IsTypeII hyp.T` — `q ∣ |Q|` is provably NOT derivable from `hG`+`hyp` alone.  (The S-side
    --     `W2_le_P` is likewise NOT type-free: it consumes `|P| = p^q` from `card_P_eq`, which uses
    --     the *carried* `S_typeP2` field.  `T` has no analogous carrier.)
    --   • `hyp.W1 ≤ secondDerivedInAmbient hyp.T`: needs the intrinsic identification
    --     `hyp.W1 = tpd.W2 = C_{T'}(W₂#)` for a type-`P` datum `tpd` whose `.W1 = W₂`.  The datum
    --     `d` from `exists_typePData_U_eq_V` only pins `d.U = V`, `d.H = Q` (the Schur–Zassenhaus
    --     conjugator controls the *complement*, not the cyclic factors), so `d.W1`/`d.W2` need not be
    --     the abstract `W₂`/`W₁`.  The alignment is the `typeP_pair` content (Coq PFsection8
    --     `FTtypeP_pair_witness`/`of_typeP_pair`: the shared `W = S ⊓ T` forces T's swapped
    --     decomposition `xdefW : W₂ \x W₁ = W`, whose (8.4.d) component gives `W₁ ⊆ H ⊓ T''`) —
    --     unported to Lean, and equivalent to supplying `IsTypeP2 hyp.T`.
    -- Discharged from the pairing residuals `hFactA`/`hFactB` via the verified reduction
    -- `reconciled_residuals_of_pairing_facts` (`typeP_kstar_in_mf`: `K* ≤ M_F ⊓ M''`).  See the
    -- preamble; the residual is now the precise Fact A + Fact B (`typeP_partner_structure` inputs).
    W2_le := hW2le_pf
    W_eq := by rw [hyp.W_eq_join, sup_comm]
    W_cyclic := hyp.W_cyclic
    W1_nontrivial := by
      intro h; have hp := hyp.p_prime.one_lt
      rw [hyp.p_eq_card_W2, h, Subgroup.card_bot] at hp; exact absurd hp (by norm_num)
    W2_nontrivial := by
      intro h; have hq := hyp.q_prime.one_lt
      rw [hyp.q_eq_card_W1, h, Subgroup.card_bot] at hq; exact absurd hq (by norm_num)
    W1_cyclic := hW2cyc
    W2_cyclic := hW1cyc
    -- `T = T' ⋊ W₂`: the honest field `W2_isComplement_T_deriv` (ungated, threaded from the §16
    -- `typeP_derivedInG_isComplement_kappaHall`).  No longer `sorry`.
    M_complement := hyp.W2_isComplement_T_deriv
    W1_normalizes_U := hyp.W2_normalizes_V
    U_nilpotent := hyp.isNilpotent_V hG
    -- `V` complements `Q = T_F` in `T'`: disjointness is the honest field `Q_inf_V_eq_bot`
    -- (ungated, threaded from the §16 `exists_kappaHall_invariant_complement_to_MF`); the join
    -- `Q ⊔ V = T'` is `T_deriv_eq_QV`.  No longer `sorry`.
    derived_complement := by
      have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
      have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
      have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
      have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
      haveI hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [disjoint_iff]
        ext ⟨x, hx⟩
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
          OneMemClass.coe_one]
        refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
        have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
        rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
      · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
            (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
        have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
          (hyp.V.subgroupOf (derivedInG hyp.T))
        rw [hsup, Subgroup.coe_top] at hmul
        exact hmul.symm
    H_noncyclic := by
      -- `H := Q = maxNilpotentNormalHall T` is the *intrinsic* Fitting Hall (choice-independent),
      -- so `¬ IsCyclic ↥Q` is read off any type-`P` datum on `T`.  The §13-level producer
      -- `typePData_of_isTypeNonI T_nonI` supplies one (no `T_typeII`/(14.9) needed, keeping this a
      -- clean §13 obligation): its `H_noncyclic` is `¬ IsCyclic` of the same subgroup `Q`.
      obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
      have hHeq : tpd0.H = hyp.Q := by rw [tpd0.H_eq, hyp.Q_eq_TF]
      exact hHeq ▸ tpd0.H_noncyclic
    -- `T`-side (8.5.a) Fitting containment/identity, transported from *any* type-`P` datum on `T`
    -- whose complement is `V` and whose kernel is `Q` (`exists_typePData_U_eq_V`, honest whole-datum
    -- conjugation via `TypePData.conj`).  No longer gated: these are genuine consequences of `T_nonI`.
    secondDerived_le_fitting := by
      obtain ⟨d, hU, hH⟩ := hyp.exists_typePData_U_eq_V hG
      have := d.secondDerived_le_fitting; rwa [hH, hU] at this
    fitting_eq := by
      obtain ⟨d, hU, hH⟩ := hyp.exists_typePData_U_eq_V hG
      have := d.fitting_eq; rwa [hH, hU] at this
    -- **Precise residual (`centralizer_W1`, goal after instantiation `W1 := hyp.W2`, `W2 := hyp.W1`,
    -- `M := hyp.T`): `∀ x ∈ hyp.W2, x ≠ 1 → derivedInG hyp.T ⊓ Subgroup.centralizer ({x}) = hyp.W1`.**
    -- This is the dual cyclic-factor law `C_{T'}(W₂#) = W₁` (Coq (8.4.d) `{in W1^#, C_M'[·] = W2}`
    -- with the swapped `xdefW`).  It is the T-side reflection of the *carried* S-side field
    -- `Sdata.centralizer_W1` (`∀ x ∈ W₁#, S' ⊓ C(x) = W₂`; see its use in
    -- `normalizer_U_inf_W2_eq_bot_of_data`, which crucially also cites the carried `Sdata_W2_eq`).
    -- The ungated general-type-`P` centralizer law `typeP_centralizer_kappaElement_eq`
    -- (`M ⊓ C_G(k) = K ⊔ K*` for `k ∈ K#`, only `IsTypeP M`) would apply to `T` with `K := W₂`,
    -- but ONLY once `W₂` is known to be a κ-Hall of `T` and `K* = M_σ(T) ⊓ C(W₂) = W₁` — precisely
    -- the `typeP_pair` reconciliation (≡ `IsTypeP2 hyp.T`), which the abstract `Hypothesis` does not
    -- carry (no `Tdata`).  Discharged from `hFactA`/`hFactB` via the verified reduction
    -- `reconciled_residuals_of_pairing_facts` (`typeP_derivedInG_inf_centralizer_kappaElement_eq`).
    centralizer_W1 := hCentW1_pf
    normalizer_V := by
      -- The `W`-exceptional-set normalizer `N_G(X) = W` is symmetric in `W₁`/`W₂`, so it is read off
      -- the S-side carrier `Sdata.normalizer_V` (same fact as `base_W_normalizer_V`, inlined since S15
      -- is upstream of S16).  The exceptional set `W − (W₂ ∪ W₁) = W − (W₁ ∪ W₂)` is `union_comm`.
      have hWeq : hyp.Sdata.W = hyp.W := by
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hyp.W_eq_join.symm
      intro X hX hXsub
      rw [← hWeq]
      refine hyp.Sdata.normalizer_V X hX ?_
      rw [hWeq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, Set.union_comm]
      exact hXsub
  }, rfl, rfl, rfl⟩

/-- **`Q^#` is a TI-subset of `G` with normalizer `T`** — the `T`-side mirror of
`H_sharp_isTISubset`, feeding the (13.10.2)/(13.10.3) `Q`-orbit counting.  For `T` of type
II/III/IV the TI property is the `TypePNontrivialCore` field of the type datum (Peterfalvi
(8.6.a)), with the bound pinned to `T` by `normalizer_Q_eq_T`; type V is excluded by `|V| ≠ 1`
(a type-V witness has `U = ⊥`, and `|V| = |tpd.U|` for the reconciled datum by the
witness-independence `card_U_eq_index`). -/
theorem Q_sharp_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    IsTISubset (sharpSubgroup hyp.Q) hyp.T := by
  classical
  have hQnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
  have hcore : ∀ tpd : TypePData hyp.T, TypePNontrivialCore hyp.T tpd →
      IsTISubset (sharpSubgroup hyp.Q) hyp.T := by
    intro tpd hcore
    have hTI := hcore.2.2
    rw [← hyp.Q_eq_TF] at hTI
    rwa [hQnorm] at hTI
  rcases hyp.T_nonI with h | h | h | h
  · exact hcore h.some.typeP h.some.common
  · exact hcore h.some.typeP h.some.common
  · exact hcore h.some.typeP h.some.common
  · -- Type V: excluded by `v·d = |V| ≠ 1`.
    exfalso
    obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
    have vdata := h.some
    have hcardU : Nat.card ↥tpd.U = Nat.card ↥vdata.typeP.U := by
      rw [tpd.card_U_eq_index, vdata.typeP.card_U_eq_index]
    rw [hU, vdata.U_eq_bot, Subgroup.card_bot, hyp.card_V_eq_vd] at hcardU
    exact hvd hcardU

/-- **(13.2.a)-on-`T`, router form**: `T` is of type II, III or IV — the `T_nonI` classification
minus type V, which is excluded by `|V| = v·d ≠ 1` (a type-V witness has `U = ⊥`, and `|V| =
|tpd.U|` for the reconciled datum by the witness-independence `card_U_eq_index`; the same
exclusion as `Q_sharp_isTISubset`).  This is what the §9 machinery's `TypesIIIIIIVSetup.type_alt`
consumes — the finer (13.2.a) "II or III" (type-IV exclusion, Pf (11.9.b,c) on `T`) is not needed
for the router. -/
theorem Hypothesis.T_typeII_or_III_or_IV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    IsTypeII hyp.T ∨ IsTypeIII hyp.T ∨ IsTypeIV hyp.T := by
  rcases hyp.T_nonI with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    obtain ⟨tpd, hU', -, -⟩ := reconciled_typePData_T hG hyp
    have vdata := h.some
    have hcardU : Nat.card ↥tpd.U = Nat.card ↥vdata.typeP.U := by
      rw [tpd.card_U_eq_index, vdata.typeP.card_U_eq_index]
    rw [hU', vdata.U_eq_bot, Subgroup.card_bot, hyp.card_V_eq_vd] at hcardU
    exact hvd hcardU

open scoped Classical in
/-- **The §9 setup on `T`** (the (13.4) gate-3 router, issue 9013): the `TypesIIIIIIVSetup T`
carrier assembled from the **reconciled** type-`P` datum (`reconciled_typePData_T`), so its
`U`/`W1`/`W2` are the hypothesis's `V`/`W₂`/`W₁` (companions `toTypesIIIIIIVSetupT_U_eq` etc.)
and its kernel is `H = T_F = Q` (`toTypesIIIIIIVSetupT_H_eq`).  Nontriviality: `U = V ≠ ⊥` from
`|V| = v·d ≠ 1`; `|W1| = |W₂| = p` prime; the `M_F`-TI component of `TypePNontrivialCore` is
datum-independent, read off any non-V type witness (`T_typeII_or_III_or_IV`).  Opens the §9
machinery ((9.7)–(9.9), `typeII_III_IV_order_relations`, the `hcPsi` degree analysis) on `T` —
the (13.3.b)-on-`T` route of the (13.4) θ-package.  Mirrors `toTypesIIIIIIVSetupS`; extracts the
inline construction of `Q_elementaryAbelian_T` (`S15_SAndT`) without its `IsTypeII` hypothesis. -/
noncomputable def Hypothesis.toTypesIIIIIIVSetupT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup hyp.T where
  maximal := hyp.T_maximal
  typeP := (reconciled_typePData_T hG hyp).choose
  nontrivial := by
    obtain ⟨hU, hW1, -⟩ := (reconciled_typePData_T hG hyp).choose_spec
    refine ⟨?_, ?_, ?_⟩
    · rw [hU]
      intro hbot
      apply hvd
      rw [← hyp.card_V_eq_vd, hbot, Subgroup.card_bot]
    · rw [hW1, ← hyp.p_eq_card_W2]
      exact hyp.p_prime
    · rcases hyp.T_typeII_or_III_or_IV hG hvd with h | h | h
      · exact h.some.common.2.2
      · exact h.some.common.2.2
      · exact h.some.common.2.2
  type_alt := hyp.T_typeII_or_III_or_IV hG hvd

theorem Hypothesis.toTypesIIIIIIVSetupT_U_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).U = hyp.V :=
  (reconciled_typePData_T hG hyp).choose_spec.1

theorem Hypothesis.toTypesIIIIIIVSetupT_W1_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).W1 = hyp.W2 :=
  (reconciled_typePData_T hG hyp).choose_spec.2.1

theorem Hypothesis.toTypesIIIIIIVSetupT_W2_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).W2 = hyp.W1 :=
  (reconciled_typePData_T hG hyp).choose_spec.2.2

theorem Hypothesis.toTypesIIIIIIVSetupT_H_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q := by
  show (reconciled_typePData_T hG hyp).choose.H = hyp.Q
  rw [(reconciled_typePData_T hG hyp).choose.H_eq, hyp.Q_eq_TF]

open OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **§9 character data on `T`** (the T-mirror of `mkSection11CharacterDataS`, over the
`toTypesIIIIIIVSetupT` router; issue 9013 gate 3): `u = |V̄|` is rfl-pinned to the `V`-action
image on the chief factor of `Q`; `tau := hyp.tauT`; `H0CprimeSupport := ∅` and
`quotientSemidirectFrobenius := True` are the same documented count/degree-only placeholders as
the `S`-instance (NOT for coherence consumption).  Opens the §9 (9.8)/(9.9) counts — in
particular the (13.3.b) dichotomy glue `caseB_of_no_irreducible_sOf_H0Cprime` — on `T`. -/
noncomputable def Hypothesis.mkSection11CharacterDataT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      (((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1)).subtype)).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := ∅
  tau := hyp.tauT
  quotientSemidirectFrobenius := True

/-- **Peterfalvi (13.3.b), dichotomy glue** (§9-generic, issue 9013 gate 3): if the §9 family
`𝒮(H₀C')` contains **no** irreducible character, then case (9.7.b) holds
(a `CliffordCaseBData` — carrying the Singer facts `Ū` cyclic, `u ∣ (p^q−1)/(p−1)`, irreducible
action), with `C = ⊥` and the full value `u = (p^q − 1)/(p − 1)`.

Assembly of the sorry-free §9 endpoints: `clifford_dichotomy` splits into the two Clifford cases;
in case (a) the (9.8.c) witness (`caseA_character_counts` conjunct (c)) is an irreducible member
of `𝒮(H₀C) ⊆ 𝒮(H₀C')` (`sOf_antitone`, `C' ≤ C`) — contradicting the hypothesis; in case (b) the
(9.9.c) conjunct (d) of `caseB_character_counts` delivers both values.  This is the C=1/u-full
half of (13.3.b); the "case (9.7.b) holds"半 is the returned `CliffordCaseBData` itself.  Stated
generically over `M` so both the `S`- and `T`-instances (via `toTypesIIIIIIVSetupS` /
`toTypesIIIIIIVSetupT`) can cite it — the T-instance is the (13.4) θ-package's (13.3.b)-on-`T`
input (contrapositive form). -/
theorem caseB_of_no_irreducible_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    (chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ) :
    ∃ _caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData chars,
      chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) := by
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG chars with hA | hB
  · exfalso
    obtain ⟨caseA⟩ := hA
    obtain ⟨-, -, ⟨χ, hχmem, hχirr, -⟩, -⟩ :=
      OddOrder.Peterfalvi.S11.caseA_character_counts hG chars caseA
    exact hno ⟨χ,
      OddOrder.Peterfalvi.S11.sOf_antitone data
        (sup_le_sup_left chars.Cprime_le_C chief.H0) hχmem, hχirr⟩
  · obtain ⟨caseB⟩ := hB
    exact ⟨caseB,
      (OddOrder.Peterfalvi.S11.caseB_character_counts hG chars caseB).2.2.2 hno⟩

/-- **`q ∤ |H|`** — the order-theoretic core of the `(H^#)^G ∩ (Q^#)^G = ∅` disjointness:
`H = PC ≤ S' = PU` has order dividing `|P|·|U|` (`derived_complement`), `q ∤ |P| = p^q`
(`p ≠ q`), and `q ∤ |U|` (the `U W₁` Frobenius structure has coprime kernel and complement,
`|W₁| = q`). -/
theorem Hypothesis.q_not_dvd_card_H [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : ¬ hyp.q ∣ Nat.card ↥hyp.H := by
  intro hdvd
  -- `|H| ∣ |S'| = |P|·|U|`.
  have hHle : hyp.H ≤ derivedInG hyp.S := by
    show hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hcard_deriv : Nat.card ↥hyp.P * Nat.card ↥hyp.U = Nat.card ↥(derivedInG hyp.S) := by
    have h := hyp.Sdata.derived_complement.card_mul
    have hPeq : hyp.Sdata.H = hyp.P := by rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPeq ▸ hyp.Sdata.H_le)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv, hPeq,
      hyp.Sdata_U_eq] at h
  have hdvd' : hyp.q ∣ Nat.card ↥hyp.P * Nat.card ↥hyp.U := by
    rw [hcard_deriv]
    exact hdvd.trans (Subgroup.card_dvd_of_le hHle)
  rcases (Nat.Prime.dvd_mul hyp.q_prime).mp hdvd' with hq | hq
  · -- `q ∤ |P| = p^q` since `p ≠ q`.
    rw [hyp.card_P_eq hG hyp.Sdata_W2_eq] at hq
    have hqp : hyp.q ∣ hyp.p := Nat.Prime.dvd_of_dvd_pow hyp.q_prime hq
    exact hyp.p_ne_q ((Nat.prime_dvd_prime_iff_eq hyp.q_prime hyp.p_prime).mp hqp).symm
  · -- `q ∤ |U|`: `U W₁` Frobenius has coprime kernel/complement.
    -- `U ≠ ⊥` via the type-II witness on `S` (as in `basic_structure`).
    have hSII : IsTypeII hyp.S :=
      OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
    have tdata : TypeIIData hyp.S := hSII.some
    have hSdataUne : hyp.Sdata.U ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
        rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
      rw [hbot, Subgroup.card_bot] at h1
      exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
    have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    have hcop := hfrob.coprime_card_kernel_complement
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hyp.Sdata.U ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        hyp.Sdata.W1 ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv,
      hyp.Sdata_U_eq, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at hcop
    exact hyp.q_prime.ne_one (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hq dvd_rfl))

/-- **`(H^#)^G` and `(Q^#)^G` are disjoint**: a common element would be conjugate both to a
nonidentity element of `H` (order dividing `|H|`, so prime to `q` by `q_not_dvd_card_H`) and to
a nonidentity element of `Q` (order a positive power of `q`, `|Q| = q^p`). -/
theorem disjoint_conjClassSet_sharp_H_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) :
    ∀ x : G, x ∈ conjClassSet (sharpSubgroup hyp.H) →
      x ∈ conjClassSet (sharpSubgroup hyp.Q) → False := by
  intro x hxH hxQ
  obtain ⟨a, ⟨haH, ha1⟩, g, rfl⟩ := mem_conjClassSet.mp hxH
  obtain ⟨b, ⟨hbQ, hb1⟩, h, hab⟩ := mem_conjClassSet.mp hxQ
  -- Conjugation preserves orders: `orderOf a = orderOf b`.
  have horder : orderOf a = orderOf b := by
    have h1 : orderOf (g * a * g⁻¹) = orderOf a := by
      rw [show g * a * g⁻¹ = (MulAut.conj g) a from rfl]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
    have h2 : orderOf (h * b * h⁻¹) = orderOf b := by
      rw [show h * b * h⁻¹ = (MulAut.conj h) b from rfl]
      exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective b
    rw [← h1, ← hab, h2]
  -- `orderOf b` is a positive power of `q`, so `q ∣ orderOf a ∣ |H|`.
  have hbdvd : orderOf b ∣ hyp.q ^ hyp.p := by
    have h1 : orderOf (⟨b, hbQ⟩ : ↥hyp.Q) ∣ Nat.card ↥hyp.Q := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk b hbQ, hcardQ] at h1
  obtain ⟨i, hip, hbord⟩ := (Nat.dvd_prime_pow hyp.q_prime).mp hbdvd
  have hi0 : i ≠ 0 := by
    intro hi0
    rw [hi0, pow_zero] at hbord
    exact hb1 (orderOf_eq_one_iff.mp hbord)
  have hqdvd_a : hyp.q ∣ orderOf a := by
    rw [horder, hbord]
    exact dvd_pow_self hyp.q hi0
  have hadvd : orderOf a ∣ Nat.card ↥hyp.H := by
    have h1 : orderOf (⟨a, SetLike.mem_coe.mp haH⟩ : ↥hyp.H) ∣ Nat.card ↥hyp.H :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk a (SetLike.mem_coe.mp haH)] at h1
  exact hyp.q_not_dvd_card_H hG (hqdvd_a.trans hadvd)

/-- Membership in the generic set `G₀`, unfolded: nonidentity and in neither saturation. -/
theorem Hypothesis.mem_G0_iff (hyp : Hypothesis (G := G)) (x : G) :
    x ∈ hyp.G0 ↔ x ≠ 1 ∧ x ∉ conjClassSet (sharpSubgroup hyp.H)
      ∧ x ∉ conjClassSet (sharpSubgroup hyp.Q) := by
  show x ∈ sharpSubgroup (⊤ : Subgroup G) \ _ ↔ _
  simp only [sharpSubgroup, Set.mem_diff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_union, not_or]

open scoped Classical in
/-- **The four-piece split of a conjugation-invariant sum** (the (13.10) counting skeleton):
for a conjugation-invariant `f`,

  `∑_G f = f(1) + ∑_{G₀} f + [G:S]·∑_{H^#} f + [G:T]·∑_{Q^#} f`.

`G` is the disjoint union of `{1}`, `G₀`, `(H^#)^G`, and `(Q^#)^G` (the saturations are disjoint
by `disjoint_conjClassSet_sharp_H_Q` and miss `1`; `G₀` is *defined* as the complement), and each
saturation sum collapses by `IsTISubset.sum_conjClassSet` (issue 9011) via the proven TI
structure (`H_sharp_isTISubset` / `Q_sharp_isTISubset`).  Instantiations: `f = ‖χ(·)‖²` gives the
Parseval splits (13.10.1)/(13.10.2); `f = 1` the cover count (13.10.3). -/
theorem Hypothesis.sum_univ_split [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    ∑ x : G, f x
      = f 1 + (∑ x ∈ hyp.G0Finset, f x)
        + hyp.S.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, f x
        + hyp.T.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, f x := by
  classical
  -- TI structure and stabilization on both sides.
  have hTIH : OddOrder.GroupTheory.IsTISubset (sharpSubgroup hyp.H) hyp.S :=
    H_sharp_isTISubset hG hyp
  have hTIQ : OddOrder.GroupTheory.IsTISubset (sharpSubgroup hyp.Q) hyp.T :=
    Q_sharp_isTISubset hG hyp hvd
  have hstabH : ∀ l ∈ hyp.S, MulAut.conj l • sharpSubgroup hyp.H = sharpSubgroup hyp.H :=
    fun l hl => conj_smul_sharpSubgroup_eq (normalizer_H_eq_S hG hyp) hl
  have hstabQ : ∀ l ∈ hyp.T, MulAut.conj l • sharpSubgroup hyp.Q = sharpSubgroup hyp.Q :=
    fun l hl => conj_smul_sharpSubgroup_eq (normalizer_Q_eq_T hG hyp) hl
  -- The four Finset pieces.
  set CH : Finset G := (Set.toFinite (conjClassSet (sharpSubgroup hyp.H))).toFinset with hCHdef
  set CQ : Finset G := (Set.toFinite (conjClassSet (sharpSubgroup hyp.Q))).toFinset with hCQdef
  have hmemCH : ∀ x : G, x ∈ CH ↔ x ∈ conjClassSet (sharpSubgroup hyp.H) := fun x =>
    (Set.toFinite _).mem_toFinset
  have hmemCQ : ∀ x : G, x ∈ CQ ↔ x ∈ conjClassSet (sharpSubgroup hyp.Q) := fun x =>
    (Set.toFinite _).mem_toFinset
  have hmemG0 : ∀ x : G, x ∈ hyp.G0Finset ↔ x ∈ hyp.G0 := fun x =>
    (Set.toFinite _).mem_toFinset
  -- Nonidentity: conjugates of nonidentity elements are nonidentity.
  have hne1 : ∀ (K : Subgroup G) (x : G), x ∈ conjClassSet (sharpSubgroup K) → x ≠ 1 := by
    rintro K x hx rfl
    obtain ⟨a, ⟨-, ha1⟩, g, hg⟩ := mem_conjClassSet.mp hx
    refine ha1 ?_
    show a = 1
    have ha : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [ha, hg]
    group
  have hne1H : ∀ x ∈ CH, x ≠ 1 := fun x hx => hne1 hyp.H x ((hmemCH x).mp hx)
  have hne1Q : ∀ x ∈ CQ, x ≠ 1 := fun x hx => hne1 hyp.Q x ((hmemCQ x).mp hx)
  -- `G₀` misses `1` and both saturations (definitional).
  have hG0iff := hyp.mem_G0_iff
  -- The partition: `univ = {1} ∪ G₀ ∪ CH ∪ CQ`, pairwise disjoint.
  have hcover : (Finset.univ : Finset G) = insert 1 (hyp.G0Finset ∪ CH ∪ CQ) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      by_cases hxH : x ∈ conjClassSet (sharpSubgroup hyp.H)
      · exact Or.inl (Or.inr ((hmemCH x).mpr hxH))
      · by_cases hxQ : x ∈ conjClassSet (sharpSubgroup hyp.Q)
        · exact Or.inr ((hmemCQ x).mpr hxQ)
        · exact Or.inl (Or.inl ((hmemG0 x).mpr ((hG0iff x).mpr ⟨hx1, hxH, hxQ⟩)))
  have hdisjHQ : Disjoint CH CQ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact disjoint_conjClassSet_sharp_H_Q hG hyp hcardQ x ((hmemCH x).mp hx) ((hmemCQ x).mp hx')
  have hdisjG0 : Disjoint hyp.G0Finset (CH ∪ CQ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨-, hxH, hxQ⟩ := (hG0iff x).mp ((hmemG0 x).mp hx)
    rcases Finset.mem_union.mp hx' with h | h
    · exact hxH ((hmemCH x).mp h)
    · exact hxQ ((hmemCQ x).mp h)
  have hone_notin : (1 : G) ∉ hyp.G0Finset ∪ CH ∪ CQ := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact ((hG0iff 1).mp ((hmemG0 1).mp h')).1 rfl
      · exact hne1H 1 h' rfl
    · exact hne1Q 1 h rfl
  -- Assemble the split.
  rw [hcover, Finset.sum_insert hone_notin, Finset.union_assoc, Finset.sum_union hdisjG0,
    Finset.sum_union hdisjHQ, hCHdef, hCQdef,
    OddOrder.GroupTheory.IsTISubset.sum_conjClassSet f hTIH hstabH hf,
    OddOrder.GroupTheory.IsTISubset.sum_conjClassSet f hTIQ hstabQ hf]
  abel

/-- `|S'| = |P|·|U|` — the (13.1.b) `S' = P ⋊ U` order decomposition
(`Sdata.derived_complement`). -/
theorem Hypothesis.card_deriv_S_eq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥(derivedInG hyp.S) = Nat.card ↥hyp.P * Nat.card ↥hyp.U := by
  have h := hyp.Sdata.derived_complement.card_mul
  have hPeq : hyp.Sdata.H = hyp.P := by rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv, hPeq,
    hyp.Sdata_U_eq] at h
  exact h.symm

/-- `|S| = |S'|·q` — the (13.1.b) `S = S' ⋊ W₁` order decomposition (`Sdata.M_complement`). -/
theorem Hypothesis.card_S_eq_deriv_mul_q [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.S = Nat.card ↥(derivedInG hyp.S) * hyp.q := by
  have hle : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have h := hyp.Sdata.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.W1_le).toEquiv,
    hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at h
  exact h.symm

/-- **`|S| = p^q·(uc)·q`** — the (13.2)-level order value of `S`, assembling
`card_S_eq_deriv_mul_q`, `card_deriv_S_eq`, `card_P_eq` (`|P| = p^q`), and `|U| = uc`. -/
theorem Hypothesis.card_S_val [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.S = hyp.p ^ hyp.q * (hyp.u * hyp.c) * hyp.q := by
  rw [hyp.card_S_eq_deriv_mul_q, hyp.card_deriv_S_eq, hyp.card_P_eq hG hyp.Sdata_W2_eq,
    hyp.card_U_eq_uc]

/-- **`|H| = p^q · c`** (Peterfalvi (13.2)): `H = PC` with `P = S_F` elementary abelian of order
`p^q` and `C = C_U(P)` of order `c`, and `P ⊓ C = ⊥` (`P` a `p`-group, `C ≤ U` with `|U| = uc`
coprime to `p` by the Hall property of `P` in `S`).  So `|PC| = |P|·|C| = p^q·c` (the complement
`card_mul_card_of_complement_normal`, `P ◁ H`).  Feeds `[S:H] = uq` (`mu_j_isIndPC` degree) and the
(13.5) counting value `|H^#|/|S| = uq/(cp^q)`. -/
theorem Hypothesis.card_H_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.H = hyp.p ^ hyp.q * hyp.c := by
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hC_le_S : hyp.C ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    exact le_trans (hyp.C_eq ▸ inf_le_left) hUS
  have hPH : hyp.P ≤ hyp.H := le_sup_left
  have hCH : hyp.C ≤ hyp.H := le_sup_right
  have hPcard : Nat.card ↥hyp.P = hyp.p ^ hyp.q := hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- `p ∤ c`: `P` Hall in `S`, `[S:P] = ucq`
  have hPScard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
  have hcop : Nat.Coprime (hyp.p ^ hyp.q) ((hyp.P.subgroupOf hyp.S).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
    rw [← hyp.P_eq_SF] at hHall
    have h0 := Ch03.IsHallSubgroup.coprime_index hHall
    rw [hPScard, hPcard] at h0
    exact h0
  have hSPidx : (hyp.P.subgroupOf hyp.S).index = hyp.u * hyp.c * hyp.q := by
    have hm := Subgroup.card_mul_index (hyp.P.subgroupOf hyp.S)
    rw [hPScard, hPcard, hyp.card_S_val hG] at hm
    have hpq : (0 : ℕ) < hyp.p ^ hyp.q := pow_pos hyp.p_prime.pos hyp.q
    have hmm : hyp.p ^ hyp.q * (hyp.P.subgroupOf hyp.S).index
        = hyp.p ^ hyp.q * (hyp.u * hyp.c * hyp.q) := by rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hpq hmm
  have hpc : Nat.Coprime (hyp.p ^ hyp.q) hyp.c := by
    have hcdvd : hyp.c ∣ (hyp.P.subgroupOf hyp.S).index := by
      rw [hSPidx]; exact ⟨hyp.u * hyp.q, by ring⟩
    exact Nat.Coprime.coprime_dvd_right hcdvd hcop
  have hpc' : Nat.gcd (hyp.p ^ hyp.q) hyp.c = 1 := hpc
  -- `P ⊓ C = ⊥` from coprime orders
  have hdisj : hyp.P ⊓ hyp.C = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have hd1 : Nat.card ↥(hyp.P ⊓ hyp.C) ∣ hyp.p ^ hyp.q :=
      hPcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(hyp.P ⊓ hyp.C) ∣ hyp.c :=
      hyp.c_eq_card_C ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Nat.dvd_one.mp (hpc' ▸ Nat.dvd_gcd hd1 hd2)
  -- `|H| = |P|·|C|` (complement `P ◁ H`)
  haveI hPnormalH : (hyp.P.subgroupOf hyp.H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr ?_
    have hSnorm : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    exact le_trans (hyp.H_le_S) hSnorm
  have hinf : hyp.P.subgroupOf hyp.H ⊓ hyp.C.subgroupOf hyp.H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hmem : ((x : ↥hyp.H) : G) ∈ hyp.P ⊓ hyp.C :=
      ⟨Subgroup.mem_subgroupOf.mp hxP, Subgroup.mem_subgroupOf.mp hxC⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; exact Subtype.ext hmem
  have hsup : hyp.P.subgroupOf hyp.H ⊔ hyp.C.subgroupOf hyp.H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPH hCH]
    exact Subgroup.subgroupOf_self hyp.H
  have hcompl : Subgroup.IsComplement' (hyp.P.subgroupOf hyp.H) (hyp.C.subgroupOf hyp.H) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
  have hmul := hcompl.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv, hPcard,
    ← hyp.c_eq_card_C] at hmul
  exact hmul.symm

/-- **`[S : H] = uq`** (Peterfalvi (13.2)): the index of `H = PC` in `S`.  From
`|S| = p^q·(uc)·q` (`card_S_val`) and `|H| = p^q·c` (`card_H_eq`), `[S:H] = |S|/|H| = uq`.  The
degree index of `mu_j_isIndPC` (`μ_j(1) = [S:H]·θ(1) = uq`). -/
theorem Hypothesis.H_index_eq_uq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (hyp.H.subgroupOf hyp.S).index = hyp.u * hyp.q := by
  have hm := Subgroup.card_mul_index (hyp.H.subgroupOf hyp.S)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hyp.H_le_S)).toEquiv, hyp.card_H_eq hG,
    hyp.card_S_val hG] at hm
  have hpos : (0 : ℕ) < hyp.p ^ hyp.q * hyp.c :=
    Nat.mul_pos (pow_pos hyp.p_prime.pos hyp.q) (hyp.c_eq_card_C ▸ Nat.card_pos)
  have hmm : hyp.p ^ hyp.q * hyp.c * (hyp.H.subgroupOf hyp.S).index
      = hyp.p ^ hyp.q * hyp.c * (hyp.u * hyp.q) := by rw [hm]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos hmm

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), degree**: each nonzero `μ`-column sum has degree `uq`.  Immediate from
`mu_j_isIndPC` (`μ_j = Ind_{PC} θ`, `θ` linear) and `H_index_eq_uq` (`[S:H] = uq`):
`μ_j(1) = [S:H]·θ(1) = uq·1 = uq`. -/
theorem Hypothesis.mu_j_degree [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    (∑ i : Fin hyp.q, hyp.mu i j) (1 : ↥hyp.S) = ((hyp.u * hyp.q : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG j hj
  rw [hθeq, ClassFunction.induce_apply_one, hθ1, mul_one, hyp.H_index_eq_uq hG]

open scoped FiniteInduce in
/-- **Column-constant degree** (Peterfalvi (13.1.e)/(4.3.c)): within a column `j`, all
`μ_{ij}(1)` are equal.  From `mu_definition` at `1`: the LHS `Ind_W^S(ω_{ij} − ω_{0j})(1)` is
`[S:W]·(ω_{ij}(1) − ω_{0j}(1)) = 0` (`omega_apply_one`: `ω`-grid linear), so the RHS
`δ_j·(μ_{ij}(1) − μ_{0j}(1)) = 0`, and `δ_j = ±1 ≠ 0` (`delta_pm_one`) gives the equality. -/
theorem Hypothesis.mu_apply_one_column_const [Finite G] (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) (j : Fin hyp.p) :
    hyp.mu i j (1 : ↥hyp.S) = hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) := by
  haveI := hyp.finiteG
  have hdef := hyp.mu_definition i j
  have h1 := congrArg (fun f : ClassFunction ↥hyp.S ℂ => f (1 : ↥hyp.S)) hdef
  simp only at h1
  -- LHS(1) = 0
  rw [ClassFunction.induce_apply_one] at h1
  have homega0 : (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe ((le_of_eq hyp.W_eq_inter).trans inf_le_left)).toMonoidHom
        (hyp.omega i j - hyp.omega ⟨0, hyp.q_prime.pos⟩ j))
      (1 : ↥(hyp.W.subgroupOf hyp.S)) = 0 := by
    rw [ClassFunction.compHom_apply, map_one, ClassFunction.sub_apply,
      hyp.omega_apply_one, hyp.omega_apply_one, sub_self]
  rw [homega0, mul_zero] at h1
  -- RHS(1) = δ_j·(μ_{ij}(1) − μ_{0j}(1)) = 0, with δ_j ≠ 0
  have hδ : (hyp.delta j : ℂ) ≠ 0 := by
    rcases (hyp.delta_pm_one.1 j) with h | h <;> rw [h] <;> norm_num
  have hsub : hyp.mu i j (1 : ↥hyp.S) - hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) = 0 :=
    (mul_eq_zero.mp h1.symm).resolve_left hδ
  exact sub_eq_zero.mp hsub

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), per-entry degree**: `μ_{ij}(1) = u` for `j ≥ 1`.  The column is
degree-constant (`mu_apply_one_column_const`), so the column sum `μ_j(1) = q·μ_{0j}(1)`; with
`μ_j(1) = uq` (`mu_j_degree`) and `q ≠ 0`, `μ_{0j}(1) = u`.  The `μ_{ij}(1) = u` that Peterfalvi
(13.3.c) feeds into the `(4.3.d)` congruence `u ≡ δ_j (mod q)` for `δ_j = 1`. -/
theorem Hypothesis.mu_apply_one_eq_u [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (i : Fin hyp.q) (j : Fin hyp.p)
    (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.mu i j (1 : ↥hyp.S) = ((hyp.u : ℕ) : ℂ) := by
  haveI := hyp.finiteG
  -- `∑ᵢ μ_{ij}(1) = q·μ_{0j}(1)` and `= uq`
  have hsum := hyp.mu_j_degree hG j hj
  rw [ClassFunction.finset_sum_apply] at hsum
  have hconst : ∑ k : Fin hyp.q, hyp.mu k j (1 : ↥hyp.S)
      = (hyp.q : ℂ) * hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) := by
    rw [Finset.sum_congr rfl (fun k _ => hyp.mu_apply_one_column_const k j),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at hsum
  have hq0 : (hyp.q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hyp.q_prime.pos.ne'
  have h0j : hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) = ((hyp.u : ℕ) : ℂ) := by
    have : (hyp.q : ℂ) * hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S)
        = (hyp.q : ℂ) * ((hyp.u : ℕ) : ℂ) := by rw [hsum]; push_cast; ring
    exact mul_left_cancel₀ hq0 this
  rw [hyp.mu_apply_one_column_const i j, h0j]

/-- **Peterfalvi `u ≡ 1 (mod q)`** (the (13.3.c) crux, (11.8.1) `|Ū| ≡ 1 mod q`).  The `S`-side
`U W₁` is a Frobenius group (`typeP_uW1_frobenius`), so for the conjugation homomorphism
`φ : U W₁ →* Aut(P)` the kernel-image `φ(U) = U/C_U(P) = Ū` satisfies `|Ū| ≡ 1 (mod |W₁|)`
(`IsFrobeniusGroup.card_range_comp_subtype_modEq_one`, Isaacs Lemma 6.1); with `|Ū| = u`
(`card_U_eq_uc`, `C = U ⊓ C_G(P)`) and `|W₁| = q` this is `u ≡ 1 (mod q)`.  Crucially **ungated**:
uses only the (proven) `U W₁` Frobenius structure, not the case-(b) Singer field model. -/
theorem Hypothesis.u_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.u ≡ 1 [MOD hyp.q] := by
  haveI := hyp.finiteG
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  have tdata : TypeIIData hyp.S := hSII.some
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
  have hUW1leS : hyp.Sdata.U ⊔ hyp.Sdata.W1 ≤ hyp.S :=
    sup_le (hyp.Sdata.U_le.trans (Subgroup.map_subtype_le _)) hyp.Sdata.W1_le
  have hSnormP : hyp.S ≤ Subgroup.normalizer hyp.P := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hUW1normP : hyp.Sdata.U ⊔ hyp.Sdata.W1 ≤ Subgroup.normalizer hyp.P :=
    le_trans hUW1leS hSnormP
  letI : MulDistribMulAction ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) ↥hyp.P :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer hyp.P)) ↥hyp.P
      (Subgroup.inclusion hUW1normP)
  set φ : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) →* MulAut ↥hyp.P :=
    MulDistribMulAction.toMulAut ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) ↥hyp.P with hφ
  have hmod := hfrob.card_range_comp_subtype_modEq_one φ
  have hAcard : Nat.card ↥(hyp.Sdata.W1.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1)) = hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
      hyp.Sdata.W1 ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hφapply : ∀ (a : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1)) (p : ↥hyp.P),
      ((φ a p : ↥hyp.P) : G) = (a : G) * (p : G) * (a : G)⁻¹ := fun a p => rfl
  have hker_iff : ∀ a : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1),
      φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (hyp.P : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h1 p hp
      have hcg := congrArg (fun e : MulAut ↥hyp.P => ((e ⟨p, hp⟩ : ↥hyp.P) : G)) h1
      simp only [hφapply, MulAut.one_apply] at hcg
      exact (mul_inv_eq_iff_eq_mul.mp hcg).symm
    · intro hc
      ext p
      simp only [hφapply, MulAut.one_apply]
      have hpc := hc (p : G) p.2
      rw [← hpc]; group
  set N := hyp.Sdata.U.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1) with hN
  set ψ : ↥N →* MulAut ↥hyp.P := φ.comp N.subtype with hψ
  set ρ : ↥N →* G := (hyp.Sdata.U ⊔ hyp.Sdata.W1).subtype.comp N.subtype with hρ
  have hρinj : Function.Injective ρ :=
    (hyp.Sdata.U ⊔ hyp.Sdata.W1).subtype_injective.comp N.subtype_injective
  have hkermap : (ψ.ker).map ρ = hyp.C := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply] at hn
      have hgC : (ρ n : G) ∈ Subgroup.centralizer (hyp.P : Set G) := (hker_iff _).mp hn
      have hgU : (ρ n : G) ∈ hyp.Sdata.U := Subgroup.mem_subgroupOf.mp n.2
      have hgU' : (ρ n : G) ∈ hyp.U := by rw [← hyp.Sdata_U_eq]; exact hgU
      rw [hyp.C_eq]
      exact ⟨hgU', hgC⟩
    · intro hgC
      rw [hyp.C_eq, Subgroup.mem_inf] at hgC
      obtain ⟨hgU, hgc⟩ := hgC
      have hgUS : g ∈ hyp.Sdata.U := by rw [hyp.Sdata_U_eq]; exact hgU
      have hgUW1 : g ∈ hyp.Sdata.U ⊔ hyp.Sdata.W1 :=
        (le_sup_left : hyp.Sdata.U ≤ _) hgUS
      have hgN : (⟨g, hgUW1⟩ : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1)) ∈ N :=
        Subgroup.mem_subgroupOf.mpr hgUS
      refine ⟨⟨⟨g, hgUW1⟩, hgN⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
      exact (hker_iff _).mpr hgc
  have hkercard : Nat.card ↥(ψ.ker) = hyp.c := by
    rw [hyp.c_eq_card_C, ← hkermap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ ρ hρinj).toEquiv
  have hNcard : Nat.card ↥N = hyp.u * hyp.c := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
      hyp.Sdata.U ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv, hyp.Sdata_U_eq, hyp.card_U_eq_uc]
  have hrangecard : Nat.card ↥(ψ.range) = hyp.u := by
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkercard, hNcard] at hsplit
    have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hc0 hsplit).symm
  have hru : Nat.card ↥((φ.comp N.subtype).range) = hyp.u := hrangecard
  rw [hru, hAcard] at hmod
  exact hmod

/-- **Peterfalvi (13.3.c), the `S`-side signs are `1`**: `δ_j = 1` for `j ≥ 1`.  The (4.3.d)
congruence `μ_{0j}(1) = δ_j + q·a` (`mu_degree_modEq_delta`) with `μ_{0j}(1) = u`
(`mu_apply_one_eq_u`) and `u ≡ 1 (mod q)` (`u_modEq_one`) gives `q ∣ δ_j − 1`; since `δ_j = ±1`
(`delta_pm_one`) and `q ≥ 3`, `δ_j = -1` would force `q ∣ 2`, so `δ_j = 1`. -/
theorem Hypothesis.delta_eq_one_of_ne_zero [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.delta j = 1 := by
  obtain ⟨a, ha⟩ := hyp.mu_degree_modEq_delta ⟨0, hyp.q_prime.pos⟩ j
  rw [hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j hj] at ha
  have haZ : (hyp.u : ℤ) = hyp.delta j + (hyp.q : ℤ) * a := by exact_mod_cast ha
  have hqu : (hyp.q : ℤ) ∣ (hyp.u : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd.mp (hyp.u_modEq_one hG))
    simpa using (dvd_neg.mpr h)
  have hqδ : (hyp.q : ℤ) ∣ hyp.delta j - 1 := by
    have hsub : hyp.delta j - 1 = ((hyp.u : ℤ) - 1) - (hyp.q : ℤ) * a := by
      rw [haZ]; ring
    rw [hsub]
    exact dvd_sub hqu (Dvd.intro a rfl)
  rcases hyp.delta_pm_one.1 j with h1 | hm1
  · exact h1
  · exfalso
    rw [hm1] at hqδ
    have hq2 : (hyp.q : ℤ) ∣ 2 := dvd_neg.mp (by simpa using hqδ)
    have hqle : hyp.q ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast hq2)
    have h2le := hyp.q_prime.two_le
    have hodd := Nat.odd_iff.mp hyp.q_odd
    omega

/-- **Peterfalvi (13.3.c), the `S`-side signs are all `1`**: `δ_j = 1` for every `j`.  The
base `δ_0 = 1` is the (4.4) trivial-column anchor (`delta_zero_eq_one`); for `j ≥ 1` it is
`delta_eq_one_of_ne_zero` (the `u ≡ 1 (mod q)` route).  This is the `S`-half of the
`CharacterDegreeData.delta_eq_one` field. -/
theorem Hypothesis.delta_eq_one_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) : hyp.delta j = 1 := by
  by_cases hj : j = ⟨0, hyp.p_prime.pos⟩
  · rw [hj]; exact hyp.delta_zero_eq_one
  · exact hyp.delta_eq_one_of_ne_zero hG j hj

/-- `|T| = |Q|·(vd)·p` — the `T`-side order decomposition, read off the reconciled type-`P`
datum (`M_complement`/`derived_complement` of `reconciled_typePData_T`) with `|V| = vd` and
`|W₂| = p`. -/
theorem Hypothesis.card_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥hyp.Q * (hyp.v * hyp.d) * hyp.p := by
  obtain ⟨tpd, hU, hW1, -⟩ := reconciled_typePData_T hG hyp
  -- `|T| = |T'|·p`.
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h1 := tpd.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h1
  -- `|T'| = |Q|·|V| = |Q|·(vd)`.
  have h2 := tpd.derived_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  rw [← h1, ← h2]

/-- `|T| = |T'|·p` — the `T`-side mirror of `card_S_eq_deriv_mul_q`
(`M_complement` of the reconciled type-`P` datum + `|W₂| = p`). -/
theorem Hypothesis.card_T_eq_deriv_mul_p [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥(derivedInG hyp.T) * hyp.p := by
  obtain ⟨tpd, -, hW1, -⟩ := reconciled_typePData_T hG hyp
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h := tpd.M_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h
  exact h.symm

/-- **(13.2.e)-for-`T`, `K^# = (QD)^#` TI-centralizer gate** ((13.4) structural gate, issue 9013
追記⁶ (c)): every nonidentity element of `K = QD ⊆ A₀(T)` has its `G`-centralizer inside `T` —
the `A₀(T)` TI-subset property of (13.2.e) applied to the `K^#`-points.  The proven
`Q_sharp_isTISubset` is the `D = ⊥` special case; the general form (live in the (13.4)
contradiction branch, where `D` may be nontrivial) needs the `A₀(T)`-TI materialization. -/
theorem QD_sharp_centralizer_le_T [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ z : ↥hyp.T, (z : G) ∈ hyp.Q ⊔ hyp.D → z ≠ 1 →
      Subgroup.centralizer ({(z : G)} : Set G) ≤ hyp.T := by
  sorry

/-- **No conjugate of `P` fits inside `T`** ((13.4) structural gate, issue 9013 追記⁶ (c),
discharged type-free post-9073): `|P| = p^q` (13.2.b) exceeds the `p`-part `p = |W₂|` of
`|T| = |Q|·(v·d)·p` (`card_T_eq`): `p ∤ |Q|` because `Q = T_F` is a Hall subgroup of `T` whose
index `(v·d)·p` is divisible by `p`, and `p ∤ v·d = |V|` because `V ⋊ W₂` is a Frobenius group
(`|V| ≡ 1 (mod p)`; trivially if `V = ⊥`).  So `v_p(|T|) = 1 < q`, and a conjugate `P^w ≤ T`
would give `p^q ∣ |T|` by Lagrange — impossible. -/
theorem P_conj_forall_not_le_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ w : G, ¬ ∀ r ∈ hyp.P, w⁻¹ * r * w ∈ hyp.T := by
  intro w hall
  haveI := hyp.finiteG
  -- `|P| = p^q` (13.2.b).
  obtain ⟨-, -, -, hPcard, -, -⟩ := basic_structure hG hyp
  -- The conjugate `P^w = (conj w⁻¹)(P)` lies in `T` and has order `p^q`; Lagrange.
  set f : G →* G := (MulAut.conj w⁻¹).toMonoidHom with hf
  have hle : hyp.P.map f ≤ hyp.T := by
    rintro - ⟨r, hr, rfl⟩
    simpa [hf, MulAut.conj_apply] using hall r hr
  have hcardmap : Nat.card ↥(hyp.P.map f) = hyp.p ^ hyp.q := by
    rw [← hPcard]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective hyp.P f (MulAut.conj w⁻¹).injective).toEquiv).symm
  have hdvd : hyp.p ^ hyp.q ∣ Nat.card ↥hyp.T := by
    rw [← hcardmap]
    exact Subgroup.card_dvd_of_le hle
  rw [hyp.card_T_eq hG] at hdvd
  -- `p ∤ v·d = |V|`: Frobenius `V ⋊ W₂` gives `|V| ≡ 1 (mod p)` (trivial if `V = ⊥`).
  have hpV : ¬ hyp.p ∣ hyp.v * hyp.d := by
    rw [← hyp.card_V_eq_vd]
    by_cases hVbot : hyp.V = ⊥
    · rw [hVbot, Subgroup.card_bot]
      intro h
      exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp h)
    · obtain ⟨tpd, htpdU, htpdW1, -⟩ := reconciled_typePData_T hG hyp
      have hUne : tpd.U ≠ ⊥ := by rw [htpdU]; exact hVbot
      have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd hUne
      rw [htpdU, htpdW1] at hfrob
      have hmod := hfrob.card_kernel_modEq_one
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (le_sup_left : hyp.V ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (le_sup_right : hyp.W2 ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          ← hyp.p_eq_card_W2] at hmod
      intro hpdvd
      have hV1 : 1 ≤ Nat.card ↥hyp.V := Nat.card_pos
      have hsub : hyp.p ∣ Nat.card ↥hyp.V - 1 := (Nat.modEq_iff_dvd' hV1).mp hmod.symm
      have hone : hyp.p ∣ 1 := by
        have := Nat.dvd_sub hpdvd hsub
        rwa [Nat.sub_sub_self hV1] at this
      exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp hone)
  -- `p ∤ |Q|`: `Q = T_F` is Hall in `T` and `p` divides its index `(v·d)·p`.
  have hpQ : ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
    have hQ_le_T : hyp.Q ≤ hyp.T := hyp.Q_eq_TF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have hcard_eq : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv
    have hcopIdx : Nat.Coprime (Nat.card ↥hyp.Q) (hyp.Q.subgroupOf hyp.T).index :=
      hcard_eq ▸ OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    -- `index · |Q| = |T| = |Q|·(v·d)·p ⟹ index = (v·d)·p`, so `p ∣ index`.
    have hidx : (hyp.Q.subgroupOf hyp.T).index * Nat.card ↥hyp.Q
        = Nat.card ↥hyp.Q * (hyp.v * hyp.d) * hyp.p := by
      rw [← hyp.card_T_eq hG, ← hcard_eq]
      exact Subgroup.index_mul_card _
    have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
    have hidx' : (hyp.Q.subgroupOf hyp.T).index = hyp.v * hyp.d * hyp.p := by
      have h : (hyp.Q.subgroupOf hyp.T).index * Nat.card ↥hyp.Q
          = hyp.v * hyp.d * hyp.p * Nat.card ↥hyp.Q := by
        rw [hidx]; ring
      exact Nat.eq_of_mul_eq_mul_right hQpos h
    intro hpdvd
    have hpidx : hyp.p ∣ (hyp.Q.subgroupOf hyp.T).index := by
      rw [hidx']; exact dvd_mul_left hyp.p (hyp.v * hyp.d)
    have hp1 := Nat.dvd_gcd hpdvd hpidx
    rw [Nat.Coprime.gcd_eq_one hcopIdx] at hp1
    exact hyp.p_prime.one_lt.ne' (Nat.dvd_one.mp hp1)
  -- `p^q ∣ (|Q|·(v·d))·p` with `p` prime to `|Q|·(v·d)` forces `p ∣ |Q|·(v·d)` (`q ≥ 2`) — absurd.
  have hK : ¬ hyp.p ∣ Nat.card ↥hyp.Q * (hyp.v * hyp.d) := by
    intro h
    rcases (Nat.Prime.dvd_mul hyp.p_prime).mp h with h' | h'
    exacts [hpQ h', hpV h']
  have hpow : hyp.p ^ hyp.q = hyp.p ^ (hyp.q - 1) * hyp.p := by
    rw [← pow_succ]
    congr 1
    have := hyp.q_prime.two_le
    omega
  rw [hpow] at hdvd
  have hcancel : hyp.p ^ (hyp.q - 1) ∣ Nat.card ↥hyp.Q * (hyp.v * hyp.d) :=
    (Nat.mul_dvd_mul_iff_right hyp.p_prime.pos).mp hdvd
  have hq1 : hyp.q - 1 ≠ 0 := by
    have := hyp.q_prime.two_le
    omega
  exact hK (dvd_trans (dvd_pow_self hyp.p hq1) hcancel)

open scoped FiniteInduce in
/-- **(13.3.b,c)-for-`T` θ-package** ((13.4) character gate, issue 9013 追記⁶ (a)+(b)): if the
(13.4) conclusion fails, then by (13.3.b) applied to `T` the family `𝒯` contains an irreducible
character `θ` induced from a linear character of `K = QD`, and (13.3.c) for `T` writes the
`τ₁`-image of the distinguished `ν`-row sum as a signed `η`-row.  Packaged in the exact form the
(13.4) contradiction consumes:

* `θT − ν_r` is `K^#`-supported ((13.3.a) for `T`: both are `K`-induced of equal degree `vp`);
* its Dade image (`τ = Ind_T^G` by (13.2.e) for `T`) is `θ° − δ'·∑ⱼ η_{rj}` ((13.3.c) for `T`,
  `τ₁`-additivity);
* `θ° = θ^{τ₁}` is orthogonal to the `η`-grid and to `λ^{τ₁}` ((4.1) + (5.3.b) pairwise
  orthogonality of `η_{ij}`, `λ^{τ₁}`, `θ^{τ₁}`). -/
theorem tSide_theta_package_of_not_caseB [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    (_hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) :
    ∃ (θT : ClassFunction ↥hyp.T ℂ) (r : Fin hyp.q) (δ' : ℤ) (θG : ClassFunction G ℂ),
      (δ' = 1 ∨ δ' = -1) ∧
      ((θT - ∑ j : Fin hyp.p, hyp.nu r j).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) ∧
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)
        = θG - (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r j) ∧
      (∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) θG = 0) ∧
      ClassFunction.inner (chars.tau1S chars.lambda) θG = 0 := by
  sorry

open scoped FiniteInduce in
/-- **Peterfalvi (13.4)**: if `S` contains a degree-`u q` character induced
from a linear character of `P C`, then case (9.7.b) holds for `T`, with
`D = 1` and `v = (q^p - 1) / (q - 1)`.

The third conjunct `|Q| = q^p` is the kernel-order component of "case (9.7.b) holds for `T`"
(the (9.7.b) field model identifies `Q̄` with a field of cardinality `q^p`); it is what the
(13.10) counting reads off ((13.10.3) computes `|Q^#|/|T| = (q^p−1)/(pq^p v)`).

**Proof structure** (issue 9013 追記⁶, textbook 04.15 mmd:49-58): by contradiction.  The T-side
θ-package (`tSide_theta_package_of_not_caseB`, (13.3.b,c)-for-`T`) supplies `β = θ − ν_r` with
`K^#`-support and Dade image `θ° − δ'·∑ⱼ η_{rj}`; the carried S-side (13.3) data give
`α = λ − μ_{j₀}` with `H^#`-support (`H ⊴ S`, equal degrees) and Dade image `λ° − δ·∑ᵢ η_{i1}`.
`(H^#)^G ∩ (K^#)^G = ∅` (`P` centralizes `H`-points, the `K^#`-centralizers lie in `T`, and no
conjugate of `P` fits in `T`), so `(α^τ, β^τ) = 0` — but the bilinear expansion leaves the shared
grid entry `δδ'·⟨η_{r1}, η_{r1}⟩ = ±1`.  Contradiction (`eta_cross_expansion_ne_zero`). -/
theorem lambda_forces_T_caseB [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  haveI := hyp.finiteG
  by_contra hne
  -- T-side θ-package from the (13.3.b,c)-for-`T` gate.
  obtain ⟨θT, r, δ', θG, hδ', hβsupp, hβform, hηθ, hLamTheta⟩ :=
    tSide_theta_package_of_not_caseB hG chars hne
  -- S-side (13.3) data: `λ = Ind thetaL` and the distinguished `μ`-column `μ_{j₀} = Ind θlin` with
  -- `τ₁`-image `δ·∑ᵢ η_{i1}`.
  obtain ⟨thetaL, hthetaLirr, hthetaL1, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  obtain ⟨j₀, δ, θlin, hδ, hθlinirr, hθlin1, hμeq, hμtau⟩ := chars.mu_col_tau1_eta_col_one
  -- `α = λ − μ_{j₀}` is supported on `H^#` (`H ⊴ S`; both terms `H`-induced of equal degree).
  have hαsupp : (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀).support ⊆
      {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1} := by
    intro s hs
    have hs0 : (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀) s ≠ 0 := hs
    refine ⟨?_, ?_⟩
    · by_contra hsH
      apply hs0
      have hsH' : s ∉ hyp.H.subgroupOf hyp.S := fun h => hsH (Subgroup.mem_subgroupOf.mp h)
      rw [ClassFunction.sub_apply, hlamEq, hμeq,
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH',
        ClassFunction.induce_eq_zero_of_not_mem_normal _ hsH', sub_zero]
    · rintro rfl
      apply hs0
      rw [ClassFunction.sub_apply, hlamEq, hμeq, ClassFunction.induce_apply_one,
        ClassFunction.induce_apply_one, hthetaL1, hθlin1, sub_self]
  -- The conjugate closures of `H^#` and `K^#` are disjoint.
  have hdisj := disjoint_conjugatesIntoSet_of_centralizer
    (A_M := {y : ↥hyp.S | (y : G) ∈ hyp.H ∧ y ≠ 1})
    (A_N := {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1})
    (fun _y hy => hyp.P_le_centralizer_of_mem_H hG hy.1)
    (fun z hz => QD_sharp_centralizer_le_T hG hyp z hz.1 hz.2)
    (P_conj_forall_not_le_T hG hyp)
  -- Hence `(α^τ, β^τ) = 0`.
  have h0 : ClassFunction.inner
      (ClassFunction.induce hyp.S (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀))
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)) = 0 :=
    inner_induce_induce_eq_zero_of_disjoint hαsupp hβsupp hdisj
  -- Rewrite `α^τ = λ° − δ·∑ᵢ η_{i1}` ((13.2.e)+τ₁-additivity + the (13.3.c) column formula).
  have hαform : ClassFunction.induce hyp.S (chars.lambda - ∑ i : Fin hyp.q, hyp.mu i j₀)
      = chars.tau1S chars.lambda
        - (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by
    conv_lhs => rw [hlamEq, hμeq]
    rw [← chars.tau1S_apply_induce_sub thetaL θlin hthetaLirr hθlinirr, map_sub, ← hlamEq, ← hμeq, hμtau]
  -- The `λ°`-side grid orthogonality, flipped to the expansion brick's slot order.
  have hLamEta : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (chars.tau1S chars.lambda) (hyp.eta i j) = 0 := by
    intro i j
    have h := chars.tau1S_induce_inner_eta i j thetaL hthetaLirr
    rw [← hlamEq] at h
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  -- The bilinear expansion is `δ·δ' ≠ 0` — contradiction.
  rw [hαform, hβform] at h0
  exact eta_cross_expansion_ne_zero hyp.eta (fun i k j l => hyp.eta_orthonormal i k j l)
    (chars.tau1S chars.lambda) θG r ⟨1, hyp.p_prime.one_lt⟩ hLamEta hηθ hLamTheta hδ hδ' h0

open scoped Classical in
/-- `|K^#| = |K| − 1`, `Finset` form. -/
theorem card_sharp_toFinset [Fintype G] (K : Subgroup G) :
    (Set.toFinite (sharpSubgroup K)).toFinset.card = Nat.card ↥K - 1 := by
  classical
  have h : (Set.toFinite (sharpSubgroup K)).toFinset
      = (Finset.univ.filter (· ∈ K)).erase 1 := by
    ext x
    rw [Set.Finite.mem_toFinset, Finset.mem_erase, Finset.mem_filter]
    show x ∈ (K : Set G) \ {1} ↔ _
    rw [Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [h, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.one_mem⟩)]
  congr 1
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]

/-- **Peterfalvi (13.10.3), ℕ form**: `|G| = 1 + |G₀| + [G:S]·|H^#| + [G:T]·|Q^#|` — the
`f = 1` instance of the four-piece split. -/
theorem Hypothesis.card_univ_split [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    Nat.card G = 1 + hyp.G0Finset.card
      + hyp.S.index * (Nat.card ↥hyp.H - 1) + hyp.T.index * (Nat.card ↥hyp.Q - 1) := by
  have h := hyp.sum_univ_split hG (fun _ => (1 : ℕ)) (fun _ _ => rfl) hcardQ hvd
  simp only [← Finset.card_eq_sum_ones, Finset.card_univ, smul_eq_mul,
    card_sharp_toFinset] at h
  rw [Nat.card_eq_fintype_card]
  exact h

/-- **`T` normalizes `Q^#`** — the `T`-side mirror of `S_normalizes_H_sharp`, via
`normalizer_Q_eq_T`. -/
theorem T_normalizes_Q_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ (l : hyp.T) ⦃a : G⦄, a ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) →
      (l : G) * a * (l : G)⁻¹ ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
  have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
  intro l a ha
  rw [OddOrder.Peterfalvi.S04.mem_sharp] at ha ⊢
  obtain ⟨haQ, ha1⟩ := ha
  have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hnorm]; exact l.2
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hlnorm a).mp haQ, ?_⟩
  intro heq
  refine ha1 ?_
  calc a = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * (l : G) := by group
    _ = 1 := by rw [heq]; group

/-- **The (13.8)-for-`T` Dade hypothesis for the TI-subset `(T, Q^#)`** — the `T`-side mirror of
`H_sharp_dadeHypothesis`, from the proven `Q_sharp_isTISubset` (type V excluded by `vd ≠ 1`).
The foundation of the `T`-side (13.5) ρ-machinery consumed by `exists_caseB_data_eta10_T`. -/
noncomputable def Q_sharp_dadeHypothesis [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S04.Hypothesis G (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  refine OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset ?_ ?_ (T_normalizes_Q_sharp hG hyp)
    (Q_sharp_isTISubset hG hyp hvd)
  · intro x hx
    exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩
  · intro x hx
    exact hQT (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1

/-- The `(T, Q^#)` Dade datum is conjugation-invariant (`H(a) = ⊥` for the TI construction). -/
theorem Q_sharp_hconj [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    (Q_sharp_dadeHypothesis hG hyp hvd).HConjInvariant :=
  OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot _ (fun _ => rfl)

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (7.1) ρ-hypothesis for `(T, Q^#)` — mirror of `H_sharp_hypothesis71`. -/
noncomputable def Q_sharp_hypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T :=
  { hyp := Q_sharp_dadeHypothesis hG hyp hvd
    τ := ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.toDadeMap
    isDadeMap := ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.isDadeMap
    hConjInvariant := Q_sharp_hconj hG hyp hvd }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (7.6) coherent-family datum for `(T, Q^#)` — mirror of `H_sharp_hypothesis76`; the
datum on which the `T`-side (13.5.a) point formula is read off. -/
noncomputable def Q_sharp_hypothesis76 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G
      (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDade (Q_sharp_hypothesis71 hG hyp hvd)
    (((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData
      (Q_sharp_hconj hG hyp hvd)).toDadeIsometryData.isDadeIsometry) hyp.Q ?_ ?_ rfl
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  · intro l h hh
    have := T_normalizes_Q_sharp hG hyp
    -- `T` normalizes `Q` itself (not just `Q^#`): via the normalizer identity.
    have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
    have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
      rw [hnorm]; exact l.2
    exact (Subgroup.mem_set_normalizer_iff.mp hlnorm h).mp hh

/-- **`G₀` is cyclic-closed**: closed under `x ↦ x^k` for `k` coprime to `|G|` — the hypothesis
shape of the Galois integrality `exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed` (and of
[Is] Lemma 3.14) that makes the (13.10) atoms `slam`/`seta` rational.  The coprime power is
undone by a further coprime power (Euler), so `x^k = 1` forces `x = 1`, and a conjugate of
`H^#`/`Q^#` hitting `x^k` pulls back to one hitting `x` (subgroups are power-closed). -/
theorem Hypothesis.G0Finset_cyclicClosed [Finite G] (hyp : Hypothesis (G := G)) :
    ∀ x ∈ hyp.G0Finset, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ hyp.G0Finset := by
  intro x hx k hk
  rw [Hypothesis.G0Finset, Set.Finite.mem_toFinset] at hx ⊢
  obtain ⟨hx1, hxH, hxQ⟩ := (hyp.mem_G0_iff x).mp hx
  -- Euler round-trip: `(x^k)^(k^(φ(|G|)−1)) = x`.
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  set t := (Nat.card G).totient with htdef
  have ht1 : 1 ≤ t := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)
  set m : ℕ := k ^ (t - 1) with hmdef
  have hround : (x ^ k) ^ m = x := by
    rw [hmdef, ← pow_mul]
    have hkt : k * k ^ (t - 1) = k ^ t := by rw [← pow_succ']; congr 1; omega
    rw [hkt]
    have hord : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
    have hmod : k ^ t ≡ 1 [MOD orderOf x] := (Nat.ModEq.pow_totient hk).of_dvd hord
    rw [pow_eq_pow_iff_modEq.mpr hmod, pow_one]
  -- Conjugates of `K^#` hitting `x^k` pull back to `x`.
  have hpull : ∀ K : Subgroup G, x ^ k ∈ conjClassSet (sharpSubgroup K) →
      x ∈ conjClassSet (sharpSubgroup K) := by
    intro K hmem
    obtain ⟨a, ⟨haK, ha1⟩, g, hg⟩ := mem_conjClassSet.mp hmem
    refine mem_conjClassSet.mpr ⟨a ^ m, ⟨?_, ?_⟩, g, ?_⟩
    · exact SetLike.mem_coe.mpr (pow_mem (SetLike.mem_coe.mp haK) m)
    · intro h1
      rw [Set.mem_singleton_iff] at h1
      refine hx1 ?_
      rw [← hround, ← hg, conj_pow, h1, mul_one, mul_inv_cancel]
    · rw [← conj_pow, hg, hround]
  refine (hyp.mem_G0_iff _).mpr ⟨?_, fun h => hxH (hpull _ h), fun h => hxQ (hpull _ h)⟩
  intro h1
  refine hx1 ?_
  rw [← hround, h1, one_pow]

/-- `|T'| = |Q|·(vd)` — the `T`-side derived-subgroup order decomposition
(`derived_complement` of the reconciled type-`P` datum). -/
theorem Hypothesis.card_deriv_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥(derivedInG hyp.T) = Nat.card ↥hyp.Q * (hyp.v * hyp.d) := by
  obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
  have h2 := tpd.derived_complement.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  exact h2.symm

open scoped FiniteInduce in
/-- **Global Parseval four-piece split** for a norm-`1` class function (the shared spine of the
Peterfalvi (13.10.1)/(13.10.2) estimates):

  `|G| = ‖φ(1)‖² + ∑_{G₀}‖φ‖² + [G:S]·∑_{H^#}‖φ‖² + [G:T]·∑_{Q^#}‖φ‖²`.

The total `∑_G ‖φ‖² = |G|·⟨φ,φ⟩ = |G|` (Parseval, `sum_normSq_eq_card_mul_inner`), split by the
four-piece decomposition `sum_univ_split` (the summand `‖φ(·)‖²` is conjugation-invariant since
`φ` is a class function). -/
theorem Hypothesis.global_normSq_split [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (φ : ClassFunction G ℂ)
    (hn : ClassFunction.inner φ φ = 1)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    (Nat.card G : ℝ)
      = ‖φ 1‖ ^ 2 + (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2)
        + hyp.S.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖φ x‖ ^ 2)
        + hyp.T.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2) := by
  have hsplit := hyp.sum_univ_split hG (fun x => ‖φ x‖ ^ 2)
    (fun g x => by
      show ‖φ (g * x * g⁻¹)‖ ^ 2 = ‖φ x‖ ^ 2
      rw [ClassFunction.conj_eq φ x g]) hcardQ hvd
  have htotal : ((∑ x : G, ‖φ x‖ ^ 2 : ℝ) : ℂ) = (Nat.card G : ℂ) := by
    rw [sum_normSq_eq_card_mul_inner, hn, mul_one]
  have htotalR : ∑ x : G, ‖φ x‖ ^ 2 = (Nat.card G : ℝ) := by exact_mod_cast htotal
  rw [← htotalR, hsplit]

end CountingLayer

/-! ### The four (13.6)–(13.9) estimate producers

Each is a *faithful* statement of one textbook estimate in terms of the shared atoms; together
they assemble into `analyticInequalityEstimates` `sorry`-free.  Remaining gates, per producer:

* `analyticEstimate_lambda` (13.6): the (13.3) character `λ` (the `chars` fields are bare —
  `character_degree_analysis` is the upstream `sorry`) + the (13.5) ρ-machinery
  (`H_sharp_hypothesis76`, proven) + the `u`-bound `2u ≤ |P|−1` (issue 9000);
* `analyticEstimate_eta` (13.7)+(13.8): the T-side (13.5) machinery + the carried grid
  properties (`tau3_isometry`/`omega_orthonormal`, issue 3002 — now threaded);
* `analyticCounting_disjointCover` (13.9.a): pure group-theoretic counting of the disjoint
  cover `G = {1} ⊔ G₀ ⊔ (H#)^G ⊔ (Q#)^G` (TI-sets with normalizers `S`/`T`) + the (13.4)
  counting values;
* `analyticEstimate_galois` (13.9.b): the per-cyclic-class Galois bound
  (`sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed`) + the (13.9) nonvanishing dichotomy
  (`λ^{τ₁}`, `η₁₀` do not vanish simultaneously on `G₀`). -/

/-- The (13.4) case-(b) parameters, unpacked: `d = 1`, `v ≥ 2`, and (for the type-V exclusion
of the counting layer) `vd ≠ 1`. -/
theorem Hypothesis.caseB_vd_facts (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    hyp.d = 1 ∧ 2 ≤ hyp.v ∧ hyp.v * hyp.d ≠ 1 := by
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega)
        (by have := hyp.three_le_p; omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  exact ⟨hd1, hv2, by rw [hd1, mul_one]; omega⟩

/- `Hypothesis.eta10_mem_ZIrr` moved up next to the `eta10` definition (issue 2033:
the (1.10) congruence helper cites it). -/

open scoped FiniteInduce in
/-- **`‖η₁₀‖² = 1`** — real content of the 3002-threaded grid: `τ₃` is an isometry
(`tau3_isometry`) and the `ω`-grid is orthonormal (`omega_orthonormal`). -/
theorem Hypothesis.eta10_inner_self_one [Finite G] (hyp : Hypothesis (G := G)) :
    ClassFunction.inner hyp.eta10 hyp.eta10 = 1 := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega, hyp.tau3_isometry.inner_eq,
    hyp.omega_orthonormal]
  simp

open scoped FiniteInduce in
/-- **`λ^{τ₁}` is a norm-one virtual character** — the (13.2.d)/(13.3) coherence-isometry facts
for the distinguished `λ`: `τ₁` extends the Dade isometry isometrically on `ℤ[S] ∋ λ`, and `λ`
is irreducible.  Faithful producer; gated on the (13.3) analysis (`character_degree_analysis`)
pinning `tau1S` to the coherence extension of (13.2.d). -/
theorem lambda_tau1_norm_one [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    chars.tau1S chars.lambda ∈ ZIrr G ∧
      ClassFunction.inner (chars.tau1S chars.lambda) (chars.tau1S chars.lambda) = 1 ∧
      ClassFunction.inner chars.lambda chars.lambda = 1 := by
  obtain ⟨θ, hθirr, -, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  have hnorm : ClassFunction.inner chars.lambda chars.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨chars.lambda, chars.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨chars.lambda, chars.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_, hnorm⟩
  · rw [hlamEq]
    exact chars.tau1S_induce_mem_ZIrr θ hθirr
  · rw [hlamEq, chars.tau1S_inner_induce θ θ hθirr hθirr, ← hlamEq]
    exact hnorm

open scoped Classical in
/-- **Sharp-set sum transport** (subgroup-of form ↔ ambient form): for `K ≤ L`, a sum over the
nonidentity `K`-members *inside `↥L`* equals the sum over the ambient sharp `K^# ⊂ G`.  The
bridge between the (13.5)/(13.6) engines (stated inside the abstract ambient `↥S` with
`H.subgroupOf S`) and the (13.10) counting layer (stated over `sharpSubgroup K ⊂ G`). -/
theorem sum_apply_erase_one_filter_subgroupOf [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Fintype ↥L] (hKL : K ≤ L) (f : G → M) :
    ∑ x ∈ (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1, f ↑x
      = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  refine Finset.sum_bij' (fun x _ => (↑x : G))
    (fun y hy => (⟨y, hKL ((Set.Finite.mem_toFinset _).mp hy).1⟩ : ↥L)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hxK⟩ := Finset.mem_erase.mp hx
    rw [Set.Finite.mem_toFinset]
    refine ⟨Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxK).2, ?_⟩
    intro h1
    rw [Set.mem_singleton_iff] at h1
    exact hx1 (Subtype.ext h1)
  · intro y hy
    obtain ⟨hyK, hy1⟩ := (Set.Finite.mem_toFinset _).mp hy
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr hyK⟩⟩
    intro h1
    exact hy1 (by simpa using congrArg (Subtype.val) h1)
  · intro x hx
    rfl
  · intro y hy
    rfl
  · intro x hx
    rfl

/-- **`2u ≤ |P| − 1`** (Peterfalvi (13.2.c) consequence): from the (13.2.e) bound
`u ≤ (p^q − 1)/(p − 1)` (`basic_structure`) and `p ≥ 3`, so `u ≤ (p^q−1)/2`. -/
theorem Hypothesis.two_mul_u_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : 2 * hyp.u ≤ hyp.p ^ hyp.q - 1 := by
  obtain ⟨-, -, -, -, hub, -⟩ := basic_structure hG hyp
  have hp3 := hyp.three_le_p
  have h1 : (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ≤ (hyp.p ^ hyp.q - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : (hyp.p ^ hyp.q - 1) / 2 * 2 ≤ hyp.p ^ hyp.q - 1 := Nat.div_mul_le_self _ _
  omega

open scoped Classical in
open scoped FiniteInduce in
/-- **The distinguished `λ`-index in the (7.6) family, membership half** (real): `λ = Ind_H^S θ`
(the materialized (13.3.b) field) appears at a family index (`zeta_family_cover`), at a
*positive* one (the base is pinned to `ζ₀ = Ind 1_H`, `H_sharp_zeta_zero`, which is `P`-kernel
while `λ` is not), and `P ⊄ Ker ζ_{i₁}` (kernel descent,
`mem_characterKernel_of_mem_characterKernel_induce`). -/
theorem exists_lambda_family_index [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i₁)) ∧
      (H_sharp_hypothesis76 hG hyp).zeta i₁ = chars.lambda := by
  classical
  obtain ⟨θ, hθirr, hθ1, hlamEq, x₀, hx₀P, hx₀ker⟩ := chars.lambda_induced_from_PC_linear
  obtain ⟨i₁, hi₁⟩ := (H_sharp_hypothesis76 hG hyp).zeta_family_cover ⟨θ, hθirr⟩
  -- `ζ_{i₁} = Ind θ = λ` (instance bridge between the canonical and scoped `induce`s)
  have heq : (H_sharp_hypothesis76 hG hyp).zeta i₁ = chars.lambda := by
    rw [hi₁, hlamEq]
    congr! <;> exact Subsingleton.elim _ _
  -- `P ⊄ Ker ζ_{i₁}`: the witness `x₀ ∈ P ∖ Ker θ` survives kernel descent
  have hker : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i₁)) := by
    intro hsub
    refine hx₀ker ?_
    have hx₀S : ((x₀ : ↥hyp.S)) ∈ hyp.P.subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr hx₀P
    have hmem : ((x₀ : ↥hyp.S)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) := by
      have h1 := hsub hx₀S
      rw [heq, hlamEq] at h1
      exact h1
    have hbridge := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (L := ↥hyp.S) (H := hyp.H.subgroupOf hyp.S) hθirr x₀.2 hmem
    rwa [show (⟨((x₀ : ↥hyp.S)), x₀.2⟩ : ↥(hyp.H.subgroupOf hyp.S)) = x₀ from rfl] at hbridge
  -- positivity: `ζ₀ = Ind 1_H` is `P`-kernel, so `i₁ ≠ 0`
  refine ⟨i₁, ?_, hker, heq⟩
  rw [Fin.pos_iff_ne_zero]
  intro h0
  refine hker ?_
  rw [h0, H_sharp_zeta_zero hG hyp]
  intro y hyP
  have hyH : (y : ↥hyp.S) ∈ hyp.H.subgroupOf hyp.S := by
    have hPH : hyp.P ≤ hyp.H := le_sup_left
    exact Subgroup.mem_subgroupOf.mpr (hPH (Subgroup.mem_subgroupOf.mp hyP))
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def,
    show ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter
        ↥(hyp.H.subgroupOf hyp.S)) : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
      = trivialClassFunction ↥(hyp.H.subgroupOf hyp.S) from rfl]
  rw [OddOrder.Peterfalvi.S09.Cert.induce_trivialChar_apply_eq_index _ hyH,
    OddOrder.Peterfalvi.S09.Cert.induce_trivialChar_apply_eq_index _
      (Subgroup.one_mem (hyp.H.subgroupOf hyp.S))]

open scoped Classical in
open scoped FiniteInduce in
/-- **The (7.7.a) coefficients of `λ^{τ₁}` at the distinguished index** (Peterfalvi (13.5),
"the hypothesis of (13.5) holds with `ζ₁ = λ`, `χ = λ^{τ₁}`, `a = 1` — since `𝒮` is coherent
and `𝒮₁ ⊂ ℤ[𝒮]`"): `c_{i₁} = ⟨τψ_{i₁}, λ^{τ₁}⟩ = 1` and every other `P`-non-kernel
coefficient vanishes.  The content is the τ₁-coherence semantics (τ₁ extends τ on family
differences + τ₁-isometry + distinct-induced orthogonality); faithful producer, gated on the
(13.3)/τ₁ fields (issue 2034 設計). -/
theorem lambda_tau1_cCoeff [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    (i₁ : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)) (hi₁pos : 0 < i₁)
    (hi₁eq : (H_sharp_hypothesis76 hG hyp).zeta i₁ = chars.lambda) :
    (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
        (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) i = 0) := by
  classical
  obtain ⟨θl, hθlirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ := chars.lambda_induced_from_PC_linear
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  -- the one-time spelling bridge (`(H76).H = hyp.H` definitionally)
  have hKJ : K = hyp.H.subgroupOf hyp.S := rfl
  haveI hKnorm : K.Normal := by rw [hKJ]; exact H_sharp_subgroupOf_normal hyp
  -- `K ≅ H` abelian ⟹ all family degrees are `[S:K]` ⟹ `d ≡ 1`
  haveI hKcomm : IsMulCommutative ↥K := by
    rw [hKJ]
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).d j = 1 := by
    intro j
    have h := (H_sharp_hypothesis76 hG hyp).zeta_one_eq_d_mul j
    rw [hzeta_one j, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- distinct induced characters of `K` are orthogonal
  have hInd0 : ∀ θ ψ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          ≠ ClassFunction.induce K (ψ : ClassFunction ↥K ℂ) →
      ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (ψ : ClassFunction ↥K ℂ)) = 0 := by
    intro θ ψ hne
    refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ ψ
      (fun g heq => hne ?_)
    have h1 : ClassFunction.induce K
        ((OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy g θ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) := by
      rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy]
      exact OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq
        (G := ↥hyp.S) (H := K) g _
    rw [← h1, heq]
  -- the field-side data, transported into the `K`-spelling (syntactic via `hKJ`)
  have hθlK : ∃ θK : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      chars.lambda = ClassFunction.induce K (θK : ClassFunction ↥K ℂ) := by
    rw [hKJ]
    exact ⟨⟨θl, hθlirr⟩, hlamEq⟩
  obtain ⟨θlK, hlamK⟩ := hθlK
  have hζ0K : (H_sharp_hypothesis76 hG hyp).zeta 0
      = ClassFunction.induce K
          ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
            OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
              ClassFunction ↥K ℂ) := by
    rw [hKJ]
    exact H_sharp_zeta_zero hG hyp
  have hfield1 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      chars.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ))
        = ClassFunction.induce hyp.S
            (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
              - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ'
    have h := chars.tau1S_apply_induce_sub _ _ θ.2 θ'.2
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  have hfield2 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.inner (chars.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)))
          (chars.tau1S (ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)))
        = ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ'
    have h := chars.tau1S_inner_induce _ _ θ.2 θ'.2
    convert h using 1 <;> congr! <;> exact Subsingleton.elim _ _
  -- `λ ≠ ζ₀` (positivity of `i₁` + injectivity), so `⟨ζ₀, λ⟩ = 0`
  have hζi₁K : (H_sharp_hypothesis76 hG hyp).zeta i₁
      = ClassFunction.induce K (θlK : ClassFunction ↥K ℂ) := by
    rw [hi₁eq]
    exact hlamK
  have hθl_ne_triv : ClassFunction.induce K (θlK : ClassFunction ↥K ℂ)
      ≠ ClassFunction.induce K
          ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
            OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
              ClassFunction ↥K ℂ) := by
    intro heq
    have hzz : (H_sharp_hypothesis76 hG hyp).zeta i₁ = (H_sharp_hypothesis76 hG hyp).zeta 0 := by
      rw [hζi₁K, hζ0K, heq]
    exact (Fin.pos_iff_ne_zero.mp hi₁pos) ((H_sharp_hypothesis76 hG hyp).zeta_injective hzz)
  have hz0lam : ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta 0) chars.lambda = 0 := by
    rw [hζ0K, hlamK]
    exact hInd0 _ _ (Ne.symm hθl_ne_triv)
  -- the generic coefficient computation for a family index with known inducing character
  have hcoeff : ∀ (j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))
      (θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K),
      (H_sharp_hypothesis76 hG hyp).zeta j = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) →
      (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) j
        = ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta j) chars.lambda
          - ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta 0) chars.lambda := by
    intro j θ hζj
    rw [show (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) j
        = ClassFunction.inner
            ((H_sharp_hypothesis76 hG hyp).hyp71.τ ((H_sharp_hypothesis76 hG hyp).psiSupp j))
            (chars.tau1S chars.lambda) from rfl]
    rw [show (H_sharp_hypothesis76 hG hyp).hyp71.τ = (H_sharp_hypothesis71 hG hyp).τ from rfl,
      H_sharp_tau_eq_induce hG hyp]
    have hψ : ((H_sharp_hypothesis76 hG hyp).psiSupp j : ClassFunction ↥hyp.S ℂ)
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K
              ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
                OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
                  ClassFunction ↥K ℂ) := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1 j, one_smul, hζj, hζ0K]
    rw [hψ, ← hfield1 θ _, map_sub, ClassFunction.inner_sub_left, hlamK,
      hfield2 θ θlK, hfield2 _ θlK, ← hlamK, ← hζj, ← hζ0K]
  -- conjunct 1: `c_{i₁} = ⟨λ,λ⟩ − ⟨ζ₀,λ⟩ = 1 − 0`
  have hlamIrr : ClassFunction.inner chars.lambda chars.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨chars.lambda, chars.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨chars.lambda, chars.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_⟩
  · rw [hcoeff i₁ θlK hζi₁K, hi₁eq, hlamIrr, hz0lam, sub_zero]
  · intro i hipos hine _
    obtain ⟨θi0, hθi0⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced i
    have hθi : (H_sharp_hypothesis76 hG hyp).zeta i
        = ClassFunction.induce K (θi0 : ClassFunction ↥K ℂ) := by
      rw [hθi0]
    rw [hcoeff i θi0 hθi, hz0lam, sub_zero]
    have hne : ClassFunction.induce K (θi0 : ClassFunction ↥K ℂ)
        ≠ ClassFunction.induce K (θlK : ClassFunction ↥K ℂ) := by
      intro heq
      refine hine ((H_sharp_hypothesis76 hG hyp).zeta_injective ?_)
      rw [hθi, hζi₁K]
      exact heq
    rw [hθi, hlamK]
    exact hInd0 θi0 θlK hne

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3)/(13.5), the distinguished index of `λ`** — real assembly: the
membership half is `exists_lambda_family_index` (family cover + trivial base + kernel
descent, all proven); the coefficient half is the τ₁-coherence producer
`lambda_tau1_cCoeff`. -/
theorem exists_lambda_index [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i₁)) ∧
      (H_sharp_hypothesis76 hG hyp).zeta i₁ = chars.lambda ∧
      (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
        (H_sharp_hypothesis76 hG hyp).cCoeff (chars.tau1S chars.lambda) i = 0) := by
  obtain ⟨i₁, hpos, hker, heq⟩ := exists_lambda_family_index hG chars
  obtain ⟨hc1, hmid⟩ := lambda_tau1_cCoeff hG chars i₁ hpos heq
  exact ⟨i₁, hpos, hker, heq, hc1, hmid⟩

open scoped Classical in
open scoped FiniteInduce in
/-- **`⟨Res_H λ, α⟩ = 0`** — the (13.5.a) `P`-kernel orthogonality for the `λ`-package: `λ`'s
`H`-restriction is the orbit character of the `P`-non-kernel `θ_{i₁}`, while `α` is supported
on `P`-kernel orbit characters; distinct orbits are orthogonal.  Real-provable from the orbit
machinery (distinct induced ⟹ disjoint orbits ⟹ orthogonal restrictions); kept as a named
producer pending the orbit-orthogonality lemma. -/
theorem lambda_alphaFun_inner_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
      chars.lambda x * (starRingEnd ℂ)
        (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x)) = 0 := by
  classical
  obtain ⟨i₁, -, hi₁ker, hi₁eq, -, -⟩ := exists_lambda_index hG chars
  -- `λ = ζ_{i₁}` vanishes off `H`, so the filtered sum extends to the full `↥S`-sum.
  have hvanish : ∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → chars.lambda x = 0 := by
    intro x hx
    rw [← hi₁eq]
    exact (H_sharp_hypothesis76 hG hyp).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  have hext : (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
      chars.lambda x * (starRingEnd ℂ)
        (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x))
      = ∑ x : ↥hyp.S, chars.lambda x * (starRingEnd ℂ)
          (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ hyp.H.subgroupOf hyp.S)
      (fun x => chars.lambda x * (starRingEnd ℂ)
        (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x))]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.H.subgroupOf hyp.S),
        chars.lambda x * (starRingEnd ℂ)
          (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hvanish x (Finset.mem_filter.mp hx).2, zero_mul]
    rw [h0, add_zero]
  rw [hext]
  -- The full sum is `|S|·⟨λ, α⟩`, and `⟨λ, α⟩ = 0` term by term.
  have hsum : ∑ x : ↥hyp.S, chars.lambda x * (starRingEnd ℂ)
      (H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) x)
      = ClassFunction.innerSum chars.lambda (H_sharp_alphaCF hG hyp (chars.tau1S chars.lambda)) := by
    rw [ClassFunction.innerSum]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [H_sharp_alphaCF_apply, starRingEnd_apply])
  rw [hsum, ← ClassFunction.card_mul_inner]
  -- `⟨λ, α⟩ = Σ_j coeff·⟨ζ_{i₁}, ζ_j⟩ = 0` (distinct-fibre induced are orthogonal).
  have hinner0 : ClassFunction.inner chars.lambda
      (H_sharp_alphaCF hG hyp (chars.tau1S chars.lambda)) = 0 := by
    rw [H_sharp_alphaCF, inner_sum_right]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [OddOrder.RepresentationTheory.inner_smul_right]
    have hjker := (Finset.mem_filter.mp hj).2
    -- `ζ_{i₁} ≠ ζ_j` (`P`-kernel property differs), both induced ⟹ orthogonal.
    have hzne : (H_sharp_hypothesis76 hG hyp).zeta i₁ ≠ (H_sharp_hypothesis76 hG hyp).zeta j :=
      fun heq => hi₁ker (heq ▸ hjker)
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced i₁
    obtain ⟨θ', hθ'⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    haveI : ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S).Normal :=
      H_sharp_subgroupOf_normal hyp
    have hz0 : ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta i₁)
        ((H_sharp_hypothesis76 hG hyp).zeta j) = 0 := by
      rw [hθ, hθ']
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ θ'
        (fun g hconj => ?_)
      refine hzne ?_
      rw [hθ, hθ', ← hconj, OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy,
        OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq]
    rw [← hi₁eq, hz0, mul_zero]
  rw [hinner0, mul_zero]

open scoped Classical in
open scoped FiniteInduce in
/-- **`λ` vanishes on the mixed products `W₂·W₁^#`** (Peterfalvi (13.6) proof, "`λ(xy) = 0`"):
`λ = ζ_{i₁}` is a member of the (7.6) family induced from `H` (`exists_lambda_index`), the
family vanishes off `H` (`zeta_eq_zero_of_not_mem_H`), and `x·y ∉ H` — `q` divides
`orderOf (x·y) = orderOf x · q` (commuting factors of coprime prime orders) while `q ∤ |H|`
(`q_not_dvd_card_H`). -/
theorem lambda_apply_mul_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    {x y : G} (hx : x ∈ hyp.W2) (hy : y ∈ hyp.W1) (hy1 : y ≠ 1)
    (hxyS : x * y ∈ hyp.S) :
    chars.lambda ⟨x * y, hxyS⟩ = 0 := by
  obtain ⟨i₁, -, -, hi₁eq, -, -⟩ := exists_lambda_index hG chars
  rw [← hi₁eq]
  refine (H_sharp_hypothesis76 hG hyp).zeta_eq_zero_of_not_mem_H i₁ _ (fun hmem => ?_)
  have hmem' : x * y ∈ hyp.H := by
    rwa [show (H_sharp_hypothesis76 hG hyp).H = hyp.H from rfl] at hmem
  -- `orderOf y = q`
  have hyq : orderOf y = hyp.q := by
    have h2 : orderOf y = orderOf (⟨y, hy⟩ : ↥hyp.W1) :=
      orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨y, hy⟩
    have h1 : orderOf (⟨y, hy⟩ : ↥hyp.W1) ∣ hyp.q := by
      rw [hyp.q_eq_card_W1]; exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hyp.q_prime).mp h1 with h | h
    · exact absurd (congrArg Subtype.val (orderOf_eq_one_iff.mp h)) hy1
    · rw [h2, h]
  -- `orderOf x ∣ p`
  have hxord : orderOf x ∣ hyp.p := by
    have h2 : orderOf x = orderOf (⟨x, hx⟩ : ↥hyp.W2) :=
      orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨x, hx⟩
    rw [h2, hyp.p_eq_card_W2]
    exact orderOf_dvd_natCard _
  -- `q ∣ orderOf (x·y)`
  have hcomm : Commute y x := hyp.W1_commutes_W2 y hy x hx
  have hcop : Nat.Coprime (orderOf y) (orderOf x) := by
    rw [hyq]
    exact Nat.Coprime.coprime_dvd_right hxord
      ((Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm (hyp.p_ne_q)))
  have hqdvd : hyp.q ∣ orderOf (x * y) := by
    rw [show x * y = y * x from hcomm.eq.symm,
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hyq]
    exact dvd_mul_right _ _
  -- ... but every `H`-element has order prime to `q`
  have hdvdH : orderOf (x * y) ∣ Nat.card ↥hyp.H := by
    have h2 : orderOf (x * y) = orderOf (⟨x * y, hmem'⟩ : ↥hyp.H) :=
      orderOf_injective hyp.H.subtype Subtype.coe_injective ⟨x * y, hmem'⟩
    rw [h2]; exact orderOf_dvd_natCard _
  exact hyp.q_not_dvd_card_H hG (hqdvd.trans hdvdH)

open scoped FiniteInduce in
/-- **Peterfalvi (3.2.d)** (hypothesis-level): a class function of `G` orthogonal to the whole
`η`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — every irreducible of `G` off the
`σ`-image vanishes on `Ŵ`, and the `η_{ij} = ω_{ij}^{τ₃}` enumerate the image.  Faithful
producer; the honest supply is `S05.eq_zero_of_mem_V_of_inner_chiFam_eq_zero` (proven) through
the spine's `ω`-grid ↔ character-pair identification (`gridEquivE`/`omegaProdChar` — the
issue-2033 threading pattern; the grid here is `Fin q × Fin p`-indexed while the S05 family is
hom-pair-indexed, and the enumerations correspond along `w1CharEquiv`/`chi2enum`). -/
theorem Hypothesis.vanish_of_inner_eta_eq_zero [Finite G] (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ)
    (horth : ∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) χ = 0)
    {w : G} (hwW : w ∈ hyp.W) (hnot : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G)) :
    χ w = 0 := by
  refine hyp.eta_complete_vanish χ (fun i j => ?_) w hwW hnot
  rw [← hyp.eta_eq_tau_omega]
  exact horth i j

open scoped Classical in
open scoped FiniteInduce in
/-- **`λ^{τ₁}` vanishes on the mixed products `W₂^#·W₁^#`** (Peterfalvi (13.6) proof, "by
(3.2.d), (5.3.b) and (5.5), `λ^{τ₁}(xy) = 0`"): the coherence extension `τ₁` sends `ℤ[𝒮]`
to class functions whose values on the regular section `xy ∈ Ŵ` are controlled by the
`η`-grid, and `λ^{τ₁}` has no `η`-component there.  Faithful producer; gated on the
(13.2.d)/(5.3.b)/(5.5) coherence-support analysis (the same (13.3)-cluster gate as
`exists_lambda_index`). -/
theorem lambda_tau1_apply_mul_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    {x y : G} (hx : x ∈ hyp.W2) (hy : y ∈ hyp.W1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    chars.tau1S chars.lambda (x * y) = 0 := by
  obtain ⟨θl, hθlirr, -, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  have hcomm : Commute y x := hyp.W1_commutes_W2 y hy x hx
  have hnot : x * y ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := by
    rw [show x * y = y * x from hcomm.eq.symm]
    exact hyp.mul_notMem_W1_union_W2 hy hx hy1 hx1
  refine hyp.vanish_of_inner_eta_eq_zero (chars.tau1S chars.lambda) (fun i j => ?_)
    (mul_mem (hW2W hx) (hW1W hy)) hnot
  rw [hlamEq]
  exact chars.tau1S_induce_inner_eta i j θl hθlirr

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (7.7.a) coefficients of any virtual character are integers** (general form; cf.
Peterfalvi (13.5) "`α(1) = qb` with `b` an integer"): `c_i = ⟨τψ_i, χ⟩` with both arguments
virtual characters — `ψ_i = ζ_i − d_i ζ_0` has `d_i = 1` (all degrees are `[S:K]` since
`K ≅ H` is abelian) and the Dade image `τψ_i ∈ ℤ[Irr G]` ((2.10)
`preserves_virtualCharacters`). -/
theorem H_sharp_cCoeff_int [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) :
    ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      ∃ z : ℤ, (H_sharp_hypothesis76 hG hyp).cCoeff χ i = (z : ℂ) := by
  classical
  intro i
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  -- `K ≅ H` is abelian, so every `θ_j` is linear and all `ζ_j` have degree `[S:K]`.
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  haveI hKcomm : IsMulCommutative ↥K := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76 hG hyp).H ≤ hyp.S from hHS)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  -- Degrees: `ζ_j(1) = [S:K]` for every `j`, so the degree ratio is `1`.
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (H_sharp_hypothesis76 hG hyp).d i = 1 := by
    have h := (H_sharp_hypothesis76 hG hyp).zeta_one_eq_d_mul i
    rw [hzeta_one i, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- `ψ_i = ζ_i − ζ_0 ∈ ℤ[Irr S]`.
  have hzetaZ : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j ∈ ZIrr ↥hyp.S := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr K (θ.2.mem_ZIrr)
  have hψZ : ((H_sharp_hypothesis76 hG hyp).psiSupp i : ClassFunction ↥hyp.S ℂ)
      ∈ ZIrr ↥hyp.S := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul]
    exact Submodule.sub_mem _ (hzetaZ i) (hzetaZ 0)
  -- The Dade image is a virtual character ((2.10) `preserves_virtualCharacters`).
  have hτeq : (H_sharp_hypothesis76 hG hyp).hyp71.τ
      = ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
          (H_sharp_hconj hG hyp)).toDadeIsometryData.toDadeMap := rfl
  have hpres : (H_sharp_hypothesis76 hG hyp).hyp71.τ
      ((H_sharp_hypothesis76 hG hyp).psiSupp i) ∈ ZIrr G := by
    rw [hτeq]
    exact ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
      (H_sharp_hconj hG hyp)).preserves_virtualCharacters _ hψZ
  -- `c_i = ⟨τψ_i, η₁₀⟩ ∈ ℤ`.
  rw [OddOrder.Peterfalvi.S09.Hypothesis76.cCoeff]
  exact ClassFunction.inner_mem_ZIrr_int hpres hχ


open scoped Classical in
open scoped FiniteInduce in
/-- **`α(1) ∈ ℤ` for the `λ`-package** (the (13.5) framing "`α(1) = qb` with `b` an integer",
integrality half): `α(1) = ∑_{P ⊆ ker ζᵢ} c̄ᵢ·ζᵢ(1)/‖ζᵢ‖²` with `cᵢ = ⟨τψᵢ, λ^{τ₁}⟩ ∈ ℤ`
(both virtual characters — `λ^{τ₁} ∈ ℤ[Irr G]` is `lambda_tau1_norm_one.1`, the `τψᵢ`
via `preserves_virtualCharacters` as in `eta10_cCoeff_int`) and `ζᵢ(1)/‖ζᵢ‖² = [S : I_S(θᵢ)]`
(the inertia-index identity `card_mul_inner_self_induce_eq_card_inertia` /
`card_smul_restrict_induce_eq_inertia_smul_orbitSum`).  Faithful producer; assembly pending
the per-index inertia bookkeeping. -/
theorem lambda_alphaFun_one_int [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    ∃ m : ℤ, H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) 1 = (m : ℂ) := by
  classical
  obtain ⟨hZtau, -, -⟩ := lambda_tau1_norm_one hG chars
  have hcInt := H_sharp_cCoeff_int hG hyp hZtau
  -- `K = H.subgroupOf S` is abelian normal, so `ζ_j(1) = [S:K]` for every `j`
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  haveI hKcomm : IsMulCommutative ↥K := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76 hG hyp).H ≤ hyp.S from hHS)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  -- the degree/norm ratio is the inertia index: `ζ_j(1)/‖ζ_j‖² = [S : I_S(θ_j)]`
  have hratio : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      ∃ N : ℕ, (H_sharp_hypothesis76 hG hyp).zeta j 1
          / (H_sharp_hypothesis76 hG hyp).zetaNormSq j = (N : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    refine ⟨(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)).index, ?_⟩
    have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hI0 : (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    -- inertia: `|K|·‖ζ_j‖² = |I|`
    have hns : (Nat.card ↥K : ℂ) * (H_sharp_hypothesis76 hG hyp).zetaNormSq j
        = (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℂ) := by
      rw [show (H_sharp_hypothesis76 hG hyp).zetaNormSq j
        = ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta j)
          ((H_sharp_hypothesis76 hG hyp).zeta j) from rfl, hθ]
      exact OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia θ
    -- Lagrange twice: `|K|·[S:K] = |S| = |I|·[S:I]`
    have hKS : (Nat.card ↥K : ℂ) * (K.index : ℂ) = (Nat.card ↥hyp.S : ℂ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (Subgroup.card_mul_index K)
    have hIS : (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℂ)
        * ((ClassFunction.inertia (θ : ClassFunction ↥K ℂ)).index : ℂ)
        = (Nat.card ↥hyp.S : ℂ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℂ)
        (Subgroup.card_mul_index (ClassFunction.inertia (θ : ClassFunction ↥K ℂ)))
    have hns0 : (H_sharp_hypothesis76 hG hyp).zetaNormSq j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hns
      exact hI0 hns.symm
    rw [hzeta_one j, div_eq_iff hns0]
    have hmul : (Nat.card ↥K : ℂ) * (K.index : ℂ)
        = (Nat.card ↥K : ℂ)
          * (((ClassFunction.inertia (θ : ClassFunction ↥K ℂ)).index : ℂ)
              * (H_sharp_hypothesis76 hG hyp).zetaNormSq j) := by
      rw [hKS]
      calc (Nat.card ↥hyp.S : ℂ)
          = (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℂ)
            * ((ClassFunction.inertia (θ : ClassFunction ↥K ℂ)).index : ℂ) := hIS.symm
        _ = _ := by rw [← hns]; ring
    exact mul_left_cancel₀ hK0 hmul
  -- assemble: every `P`-kernel tail term is an integer, so the sum is
  have hmem : H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) 1
      ∈ (Int.castRingHom ℂ).range := by
    simp only [H_sharp_alphaFun]
    refine Subring.sum_mem _ (fun i _ => ?_)
    obtain ⟨z, hz⟩ := hcInt i
    obtain ⟨N, hN⟩ := hratio i
    refine ⟨z * N, ?_⟩
    show ((z * N : ℤ) : ℂ) = _
    push_cast
    rw [hz, star_intCast, div_mul_eq_mul_div, mul_div_assoc, hN]
  obtain ⟨m, hm⟩ := hmem
  exact ⟨m, hm.symm⟩

open scoped Classical in
open scoped FiniteInduce in
/-- **`α(1) ≡ 0 (mod q)` for the `λ`-package** (Peterfalvi (13.6) proof, the (1.10) congruence):
`λ(x) ≡ λ^{τ₁}(x) ≡ 0 (mod 1−ε)` on `W₂^#`, so `α(1) = α(x) = λ^{τ₁}(x) − λ(x) ≡ 0 (mod q)`.
Faithful producer; gated on the (1.10)/(3.2) grid congruences. -/
theorem exists_lambda_alphaFun_one_qb [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) :
    ∃ b : ℤ, H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) 1
      = (hyp.q : ℂ) * (b : ℂ) := by
  classical
  -- `α(1) = m ∈ ℤ` (integrality producer)
  obtain ⟨m, hm⟩ := lambda_alphaFun_one_int hG chars
  -- the distinguished index and the norm normalizations
  obtain ⟨i₁, hi₁pos, hi₁ker, hi₁eq, hi₁c, hmiddle⟩ := exists_lambda_index hG chars
  obtain ⟨hZtau, -, hnormLam⟩ := lambda_tau1_norm_one hG chars
  -- pick `x ∈ W₂^#`, `y ∈ W₁^#`
  obtain ⟨x', hx'⟩ : ∃ x' : ↥hyp.W2, x' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W2 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.p_eq_card_W2]; exact hyp.p_prime.one_lt)
    exact exists_ne 1
  obtain ⟨y', hy'⟩ : ∃ y' : ↥hyp.W1, y' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W1 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.q_eq_card_W1]; exact hyp.q_prime.one_lt)
    exact exists_ne 1
  have hxW2 : (x' : G) ∈ hyp.W2 := x'.2
  have hyW1 : (y' : G) ∈ hyp.W1 := y'.2
  have hx1 : (x' : G) ≠ 1 := fun h => hx' (Subtype.ext h)
  have hy1 : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
  -- memberships: `x ∈ P ≤ H ≤ S`, `y ∈ W₁ ≤ W ≤ S`
  have hxP : (x' : G) ∈ hyp.P := W2_le_P hG hyp hxW2
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hxS : (x' : G) ∈ hyp.S := hPS hxP
  have hxH : (x' : G) ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.H) hxP
  have hWS : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hyS : (y' : G) ∈ hyp.S := hWS (hW1W hyW1)
  -- the point formula at `x`: `λ^{τ₁}(x) = λ(x) + α(x)` (with `c₁ = 1`, `‖ζ₁‖² = 1`)
  have hns : (H_sharp_hypothesis76 hG hyp).zetaNormSq i₁ = 1 := by
    rw [show (H_sharp_hypothesis76 hG hyp).zetaNormSq i₁
      = ClassFunction.inner ((H_sharp_hypothesis76 hG hyp).zeta i₁)
        ((H_sharp_hypothesis76 hG hyp).zeta i₁) from rfl, hi₁eq]
    exact hnormLam
  have hpf : chars.tau1S chars.lambda ((x' : G))
      = chars.lambda ⟨(x' : G), hxS⟩
        + H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) ⟨(x' : G), hxS⟩ := by
    have h := H_sharp_point_formula hG hyp (chars.tau1S chars.lambda) i₁ hi₁pos hi₁ker
      hmiddle ⟨(x' : G), hxS⟩
      (by rw [OddOrder.Peterfalvi.S04.mem_sharp]; exact ⟨hxH, hx1⟩)
    rwa [hi₁c, hns, star_one, div_one, one_mul, hi₁eq] at h
  -- `λ = ζ_{i₁} ∈ ℤ[Irr ↥S]` (for the `↥S`-level (1.10.a))
  have hZlam : chars.lambda ∈ ZIrr ↥hyp.S := by
    rw [← hi₁eq]
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced i₁
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _ (θ.2.mem_ZIrr)
  -- the primitive `q`-th root and the two (1.10.a) congruences at `x` vs `yx`
  have hε : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / hyp.q)) hyp.q :=
    Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne'
  set ε : ℂ := Complex.exp (2 * Real.pi * Complex.I / hyp.q) with hεdef
  have hyq : (y' : G) ^ hyp.q = 1 := by
    have h1 : y' ^ hyp.q = 1 := by
      rw [hyp.q_eq_card_W1]; exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  have hcommG : Commute ((y' : G)) ((x' : G)) := hyp.W1_commutes_W2 _ hyW1 _ hxW2
  -- τ₁-side (`G`-level): `λ^{τ₁}(x) = λ^{τ₁}(yx) − (1−ε)z₂ = −(1−ε)z₂`
  obtain ⟨z₂, hz₂int, hz₂⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hZtau hyq hcommG
  have htau0 : chars.tau1S chars.lambda ((y' : G) * (x' : G)) = 0 := by
    rw [hcommG.eq]
    exact lambda_tau1_apply_mul_eq_zero hG chars hxW2 hyW1 hx1 hy1
  -- λ-side (`↥S`-level): `λ(x) = λ(yx) − (1−ε)z₁ = −(1−ε)z₁`
  have hyqS : (⟨(y' : G), hyS⟩ : ↥hyp.S) ^ hyp.q = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hyq
  have hcommS : Commute (⟨(y' : G), hyS⟩ : ↥hyp.S) (⟨(x' : G), hxS⟩ : ↥hyp.S) :=
    Subtype.ext hcommG.eq
  obtain ⟨z₁, hz₁int, hz₁⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hZlam hyqS hcommS
  have hlam0 : chars.lambda ((⟨(y' : G), hyS⟩ : ↥hyp.S) * ⟨(x' : G), hxS⟩) = 0 := by
    have hmulS : ((⟨(y' : G), hyS⟩ : ↥hyp.S) * ⟨(x' : G), hxS⟩ : ↥hyp.S)
        = ⟨(x' : G) * (y' : G), mul_mem hxS hyS⟩ := Subtype.ext hcommG.eq
    rw [hmulS]
    exact lambda_apply_mul_eq_zero hG chars hxW2 hyW1 hy1 _
  -- combine: `α(1) = α(x) = λ^{τ₁}(x) − λ(x) = (1−ε)(z₁ − z₂)`
  have hconst := H_sharp_alphaFun_const_on_P hG hyp (chars.tau1S chars.lambda)
    ⟨(x' : G), hxS⟩ (Subgroup.mem_subgroupOf.mpr hxP)
  have hcast : ((m : ℤ) : ℂ) = (1 - ε) * (z₁ - z₂) := by
    rw [htau0, zero_sub] at hz₂
    rw [hlam0, zero_sub] at hz₁
    have e1 : chars.tau1S chars.lambda ((x' : G)) = -((1 - ε) * z₂) := by
      linear_combination -hz₂
    have e2 : chars.lambda ⟨(x' : G), hxS⟩ = -((1 - ε) * z₁) := by
      linear_combination -hz₁
    have e3 : H_sharp_alphaFun hG hyp (chars.tau1S chars.lambda) ⟨(x' : G), hxS⟩
        = (1 - ε) * (z₁ - z₂) := by
      have e4 := hpf
      rw [e1, e2] at e4
      linear_combination -e4
    rw [← hm, ← hconst, e3]
  -- (1.10.b): `q ∣ m`
  have hdvd : (hyp.q : ℤ) ∣ m :=
    OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hyp.q_prime hε
      (hz₁int.sub hz₂int) hcast
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨b, ?_⟩
  rw [hm, hb]
  push_cast
  ring

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a)+(13.5.c) for `ζ₁ = λ`, `χ = λ^{τ₁}`, `a = 1`** — the correction datum
of the (13.6) estimate.

**Real assembly** from the distinguished-index atom (`exists_lambda_index`): with
`ζ_{i₁} = λ`, `c_{i₁} = 1`, and `‖ζ_{i₁}‖² = ⟨λ,λ⟩ = 1` (`lambda_tau1_norm_one`), the proven
point formula `H_sharp_point_formula` collapses to `λ^{τ₁} = λ + α` on `H^#` with
`α = H_sharp_alphaFun` the `P`-kernel tail; `λ` vanishes off `H` (`zeta_eq_zero_of_not_mem_H`);
the inner-product and congruence facts are the named producers
(`lambda_alphaFun_inner_zero` / `exists_lambda_alphaFun_one_qb`); the (13.5.c) inflation is
`H_sharp_alphaFun_inflation`. -/
theorem exists_caseB_data_lambda [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    ∃ (α : ↥hyp.S → ℂ) (b : ℤ),
      (∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → chars.lambda x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
        chars.lambda x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
        chars.tau1S chars.lambda ↑x = chars.lambda x + α x) ∧
      α 1 = (hyp.q : ℂ) * (b : ℂ) ∧
      ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1, ‖α x‖ ^ 2 := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨i₁, hi₁pos, hi₁ker, hi₁eq, hi₁c, hmiddle⟩ := exists_lambda_index _hG chars
  obtain ⟨-, -, hinnerLam⟩ := lambda_tau1_norm_one _hG chars
  obtain ⟨b, hb⟩ := exists_lambda_alphaFun_one_qb _hG chars
  refine ⟨H_sharp_alphaFun _hG hyp (chars.tau1S chars.lambda), b, ?_, ?_, ?_, hb, ?_⟩
  · -- `λ = ζ_{i₁}` vanishes off `H`.
    intro x hx
    rw [← hi₁eq]
    exact (H_sharp_hypothesis76 _hG hyp).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  · exact lambda_alphaFun_inner_zero _hG chars
  · -- The point formula collapses: `c̄_{i₁}/‖ζ_{i₁}‖² = 1` and `ζ_{i₁} = λ`.
    intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxH : (↑x : G) ∈ hyp.H :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    have hpt := H_sharp_point_formula _hG hyp (chars.tau1S chars.lambda) i₁ hi₁pos hi₁ker
      hmiddle x hxsharp
    rw [hpt, hi₁c]
    have hnorm1 : (H_sharp_hypothesis76 _hG hyp).zetaNormSq i₁ = 1 := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hi₁eq]
      exact hinnerLam
    rw [hnorm1, hi₁eq, star_one, div_one, one_mul]
    rfl
  · -- (13.5.c): the inflation bound for the concrete tail, with `α(1) = qb`.
    have hinfl := H_sharp_alphaFun_inflation _hG hyp (chars.tau1S chars.lambda)
    rw [hb] at hinfl
    have hval : ‖(hyp.q : ℂ) * (b : ℂ)‖ ^ 2 = ((hyp.q : ℝ) * (b : ℝ)) ^ 2 := by
      rw [norm_mul, mul_pow, Complex.norm_natCast, Complex.norm_intCast, sq_abs]
      push_cast
      ring
    rw [hval] at hinfl
    exact hinfl

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.6), textbook form**: `∑_{x∈H^#}|λ^{τ₁}(x)|² ≥ |S| − λ(1)²` (`λ(1) = uq`),
as a sum over the ambient sharp `H^# ⊂ G`.

**Real assembly** through the (13.5) engine `caseB_lambda_norm_bound` (inside `↥S`, with
`H.subgroupOf S`): the character-theoretic inputs are the (13.5)-for-`λ` package
(`exists_caseB_data_lambda`), the norm facts (`lambda_tau1_norm_one`: `‖λ‖² = 1` gives the
`S`-Parseval `∑_S|λ|² = |S|`), the degree `λ(1) = uq` (`lambda_degree`), and the `u`-bound
`2u ≤ |P| − 1 = p^q − 1` (`two_mul_u_le`, real from (13.2.e)); the engine output transports to
the ambient sharp by `sum_apply_erase_one_filter_subgroupOf`. -/
theorem lambda_tau1_sharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
          ‖chars.tau1S chars.lambda x‖ ^ 2 := by
  classical
  obtain ⟨α, b, hvanish, hinner, hχ, hα1, hinfl⟩ := exists_caseB_data_lambda _hG chars
  obtain ⟨-, -, hinnerLam⟩ := lambda_tau1_norm_one _hG chars
  -- `H ≤ S`.
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  have hHS : hyp.H ≤ hyp.S := by
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  -- The `S`-Parseval total: `∑_{x:S}‖λ(x)‖² = |S|`.
  have hT : ∑ x : ↥hyp.S, ‖chars.lambda x‖ ^ 2 = ((Nat.card ↥hyp.S : ℕ) : ℝ) := by
    have h := sum_normSq_eq_card_mul_inner (H := ↥hyp.S) chars.lambda
    rw [hinnerLam, mul_one] at h
    exact_mod_cast h
  -- Degree facts.
  have hlamOne : chars.lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ) := chars.lambda_degree
  have hzetaOne : ‖chars.lambda 1‖ ^ 2 = (((hyp.u * hyp.q : ℕ) : ℝ)) ^ 2 := by
    rw [hlamOne, Complex.norm_natCast]
  have hcross : (chars.lambda 1 * (starRingEnd ℂ) (α 1)).re
      = ((hyp.u * hyp.q : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) := by
    have hval : chars.lambda 1 * (starRingEnd ℂ) (α 1)
        = ((((hyp.u * hyp.q : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) : ℝ) : ℂ) := by
      rw [hlamOne, hα1, map_mul]
      push_cast [map_natCast, map_intCast]
      ring
    rw [hval, Complex.ofReal_re]
  have hlam1 : ((hyp.u * hyp.q : ℕ) : ℝ) = (hyp.u : ℝ) * (hyp.q : ℝ) := by push_cast; ring
  -- The engine.
  have hu := hyp.two_mul_u_le _hG
  -- The engine (bridging the `Classical` decidability instances baked into its statement).
  have hengine : (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖chars.tau1S chars.lambda ↑x‖ ^ 2 := by
    have h := caseB_lambda_norm_bound (S := ↥hyp.S) (hyp.H.subgroupOf hyp.S)
      (fun x => chars.lambda x) α (fun x => chars.tau1S chars.lambda ↑x)
      (Scard := Nat.card ↥hyp.S) (Pm1 := hyp.p ^ hyp.q - 1)
      (u := hyp.u) (q := hyp.q) (lam1 := ((hyp.u * hyp.q : ℕ) : ℝ)) (b := b)
      hvanish (by convert hinner using 2 <;> congr!)
      (fun x hx => hχ x (by convert hx using 2 <;> congr!))
      hT hzetaOne hcross hlam1
      (by convert hinfl using 2 <;> congr!) hu
    convert h using 2 <;> congr!
  -- Transport to the ambient sharp set.
  rwa [sum_apply_erase_one_filter_subgroupOf hHS
    (fun y => ‖chars.tau1S chars.lambda y‖ ^ 2)] at hengine

open scoped Classical in
/-- `F`-parameterized form of `sum_filter_erase_one_normSq_eq` (instance-free interface): any
`Finset` with the sharp-membership characterization works. -/
theorem sum_finset_sharp_normSq_eq {L : Type*} [Group L] [Fintype L]
    {K : Subgroup L} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (F : Finset L) (hF : ∀ x : L, x ∈ F ↔ (x ∈ K ∧ x ≠ 1))
    (f : L → ℂ) (ψ : ClassFunction ↥K ℂ) (hagree : ∀ k : ↥K, f ↑k = ψ k)
    {n : ℕ} (hn : ClassFunction.inner ψ ψ = (n : ℂ)) :
    ∑ x ∈ F, ‖f x‖ ^ 2 = (Nat.card ↥K : ℝ) * (n : ℝ) - ‖f 1‖ ^ 2 := by
  classical
  have hFeq : F = (Finset.univ.filter (· ∈ K)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact sum_filter_erase_one_normSq_eq f ψ hagree hn

open scoped Classical in
/-- `F`-parameterized form of `sum_apply_erase_one_filter_subgroupOf` (instance-free
interface). -/
theorem sum_finset_sharp_transport [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Fintype ↥L] (hKL : K ≤ L)
    (F : Finset ↥L) (hF : ∀ x : ↥L, x ∈ F ↔ ((x : G) ∈ K ∧ x ≠ 1))
    (f : G → M) :
    ∑ x ∈ F, f ↑x = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  have hFeq : F = (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter, Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact sum_apply_erase_one_filter_subgroupOf hKL f

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- `F`-parameterized form of `H_sharp_alphaFun_inflation` (instance-free interface). -/
theorem H_sharp_alphaFun_inflation_finset [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ)
    (F : Finset ↥hyp.S) (hF : ∀ x : ↥hyp.S, x ∈ F ↔ ((x : G) ∈ hyp.H ∧ x ≠ 1)) :
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ‖H_sharp_alphaFun hG hyp χ 1‖ ^ 2
      ≤ ∑ x ∈ F, ‖H_sharp_alphaFun hG hyp χ x‖ ^ 2 := by
  classical
  have hFeq : F = (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter, Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact H_sharp_alphaFun_inflation hG hyp χ

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5) orthogonality hypothesis for `χ = η₁₀`** (Peterfalvi (13.7), first step):
`η₁₀` is orthogonal to `S^{τ₁}` by (5.3.b)+(5.5)+(13.3.c), so *every* `P`-non-kernel (7.7.a)
coefficient vanishes (`a = 0`).  Faithful producer; gated on the (13.3.c)/(5.3.b) grid
orthogonality. -/
theorem eta10_cCoeff_orthogonal [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chars : CharacterDegreeData hyp) :
    ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i →
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
      (H_sharp_hypothesis76 hG hyp).cCoeff hyp.eta10 i = 0 := by
  classical
  intro j _ _
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  have hKJ : K = hyp.H.subgroupOf hyp.S := rfl
  haveI hKnorm : K.Normal := by rw [hKJ]; exact H_sharp_subgroupOf_normal hyp
  haveI hKcomm : IsMulCommutative ↥K := by
    rw [hKJ]
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe (show hyp.H ≤ hyp.S from hyp.H_le_S)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzeta_one : ∀ j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      (H_sharp_hypothesis76 hG hyp).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (H_sharp_hypothesis76 hG hyp).d j = 1 := by
    have h := (H_sharp_hypothesis76 hG hyp).zeta_one_eq_d_mul j
    rw [hzeta_one j, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  have hζ0K : (H_sharp_hypothesis76 hG hyp).zeta 0
      = ClassFunction.induce K
          ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
            OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
              ClassFunction ↥K ℂ) := by
    rw [hKJ]
    exact H_sharp_zeta_zero hG hyp
  have hfield1 : ∀ θ θ' : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      chars.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
          - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ))
        = ClassFunction.induce hyp.S
            (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
              - ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) := by
    rw [hKJ]
    intro θ θ'
    have h := chars.tau1S_apply_induce_sub _ _ θ.2 θ'.2
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  -- the (4.1)/(5.3.b) field, at the `η₁₀`-index
  have hfieldEta : ∀ θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥K,
      ClassFunction.inner hyp.eta10
        (chars.tau1S (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))) = 0 := by
    rw [hKJ]
    intro θ
    have h := chars.tau1S_induce_inner_eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ _ θ.2
    convert h using 1 <;> congr! <;> exact Subsingleton.elim _ _
  obtain ⟨θj, hθj⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
  rw [show (H_sharp_hypothesis76 hG hyp).cCoeff hyp.eta10 j
      = ClassFunction.inner
          ((H_sharp_hypothesis76 hG hyp).hyp71.τ ((H_sharp_hypothesis76 hG hyp).psiSupp j))
          hyp.eta10 from rfl]
  rw [show (H_sharp_hypothesis76 hG hyp).hyp71.τ = (H_sharp_hypothesis71 hG hyp).τ from rfl,
    H_sharp_tau_eq_induce hG hyp]
  have hψ : ((H_sharp_hypothesis76 hG hyp).psiSupp j : ClassFunction ↥hyp.S ℂ)
      = ClassFunction.induce K (θj : ClassFunction ↥K ℂ)
        - ClassFunction.induce K
            ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
              OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
                ClassFunction ↥K ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul, hθj, hζ0K]
  rw [hψ, ← hfield1 θj _, map_sub, ClassFunction.inner_sub_left]
  have h1 : ClassFunction.inner
      (chars.tau1S (ClassFunction.induce K (θj : ClassFunction ↥K ℂ))) hyp.eta10 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm hyp.eta10 _, hfieldEta θj, star_zero]
  have h2 : ClassFunction.inner
      (chars.tau1S (ClassFunction.induce K
        ((OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥K :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥K) :
            ClassFunction ↥K ℂ))) hyp.eta10 = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm hyp.eta10 _, hfieldEta _, star_zero]
  rw [h1, h2, sub_zero]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (7.7.a) coefficients of `η₁₀` are integers**: `c_i = ⟨τ(ψ_i), η₁₀⟩` with
`η₁₀ ∈ ℤ[Irr G]` (real, `eta10_mem_ZIrr`) and `τ(ψ_i) ∈ ℤ[Irr G]` (the Dade image of the
virtual character `ψ_i = ζ_i − d_i ζ_0`, Peterfalvi (2.10)).  Faithful producer; the residual
is the `τ`-image virtuality (the (2.10) inclusion–exclusion is a `ℤ`-combination of
`Ind_{M(B)} α_B ∈ ℤ[Irr G]`, `induce_alphaB_mem_ZIrr`). -/
theorem eta10_cCoeff_int [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1),
      ∃ z : ℤ, (H_sharp_hypothesis76 hG hyp).cCoeff hyp.eta10 i = (z : ℂ) :=
  H_sharp_cCoeff_int hG hyp hyp.eta10_mem_ZIrr

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.7) correction is nonzero at `1`**: `α(1) ≡ 1 (mod q)` by the (1.10) congruence
(`η₁₀(x) ≡ ω₁₀(y) ≡ 1 (mod 1−ε)` on `W₂^#`-cosets), so `α(1) ≠ 0`.  Faithful producer; gated
on the (1.10)/(3.2.c) grid congruences. -/
theorem eta10_alphaCF_one_ne_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chars : CharacterDegreeData hyp) :
    H_sharp_alphaCF hG hyp hyp.eta10 1 ≠ 0 := by
  classical
  intro hzero
  -- pick `y ∈ W₂^#`
  obtain ⟨y', hy'⟩ : ∃ y' : ↥hyp.W2, y' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W2 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.p_eq_card_W2]; exact hyp.p_prime.one_lt)
    exact exists_ne 1
  have hyW2 : (y' : G) ∈ hyp.W2 := y'.2
  have hy1 : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
  -- `y ∈ P ≤ H`, `y ∈ S`
  have hyP : (y' : G) ∈ hyp.P := W2_le_P hG hyp hyW2
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hyS : (y' : G) ∈ hyp.S := hPS hyP
  have hyH : (y' : G) ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.H) hyP
  -- kernel-only point formula (`eta10_cCoeff_orthogonal`): `η₁₀(y) = α(y)`
  have hval : hyp.eta10 ((⟨(y' : G), hyS⟩ : ↥hyp.S) : G)
      = H_sharp_alphaFun hG hyp hyp.eta10 ⟨(y' : G), hyS⟩ :=
    H_sharp_point_formula_kernel_only hG hyp hyp.eta10
      (eta10_cCoeff_orthogonal hG hyp chars) ⟨(y' : G), hyS⟩
      (by rw [OddOrder.Peterfalvi.S04.mem_sharp]; exact ⟨hyH, hy1⟩)
  -- `α(y) = α(1) = 0` (`P`-constancy + the assumption)
  have hconst := H_sharp_alphaFun_const_on_P hG hyp hyp.eta10 ⟨(y' : G), hyS⟩
    (Subgroup.mem_subgroupOf.mpr hyP)
  have halpha0 : H_sharp_alphaFun hG hyp hyp.eta10 1 = 0 := by
    rw [← H_sharp_alphaCF_apply hG hyp hyp.eta10 1]; exact hzero
  have heta0 : hyp.eta10 (y' : G) = 0 := by
    have := hval.trans (hconst.trans halpha0)
    exact this
  -- the (1.10) congruence: `η₁₀(y) ≡ 1 (mod (1 − ε))`, so `η₁₀(y) = 0` forces `q ∣ 1`
  obtain ⟨z, hzint, hz⟩ := hyp.eta10_apply_sub_one_integral
    (Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne') hyW2 hy1
  rw [heta0, zero_sub] at hz
  have hdvd : (hyp.q : ℤ) ∣ (-1 : ℤ) :=
    OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hyp.q_prime
      (Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne') hzint (by exact_mod_cast hz)
  have hle : (hyp.q : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdvd)
  have := hyp.q_prime.one_lt
  omega

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5) for `χ = η₁₀`, `a = 0`** — the correction datum of the (13.7) estimate.

Assembly target (WIP): the concrete correction `α = H_sharp_alphaFun` with the point formula
`η₁₀ = α` on `H^#` (`H_sharp_point_formula_kernel_only` + `eta10_cCoeff_orthogonal`),
`α|_H ∈ ℤ[Irr H]` (`H_sharp_alphaCF_restrict_mem_ZIrr` + `eta10_cCoeff_int`) giving
`n = ‖α‖² ∈ ℕ` (`exists_nat_inner_self_of_mem_ZIrr`) and `d = |α(1)|`
(`exists_int_apply_one_of_mem_ZIrr`), the Parseval bookkeeping
(`sum_filter_erase_one_normSq_eq`), the (13.5.c) inflation (`H_sharp_alphaFun_inflation`),
`α(1) ≠ 0` (`eta10_alphaCF_one_ne_zero`) forcing `n ≥ 1`, and `H` abelian
(`H_mulCommutative` + `apply_one_eq_one_of_isMulCommutative`) forcing `d² = 1` at `n = 1`.
The remaining glue is `Fintype`/`Decidable` instance canonicalization across the sum shapes —
**decided route (07-05 loop it.12)**: parameterize `sum_filter_erase_one_normSq_eq`,
`sum_apply_erase_one_filter_subgroupOf`, and `H_sharp_alphaFun_inflation` over an explicit
`F : Finset ↥S` with a membership characterization `hF : ∀ x, x ∈ F ↔ (↑x ∈ K ∧ x ≠ 1)`
(instance-free interfaces; each proof converts `F` to its local spelling by `Finset.ext hF`
within its own single elaboration context), then instantiate all three with one assembly-side
`F`.  Direct `rw`-joins across the lemmas' baked spellings fail on invisible
`Fintype`/`DecidablePred` instance differences even under shared `open scoped` context. -/
theorem exists_caseB_data_eta10 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (chars : CharacterDegreeData hyp) :
    ∃ (α : G → ℂ) (d n s : ℕ),
      (∀ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, hyp.eta10 x = α x) ∧
      (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖α x‖ ^ 2 = (s : ℝ)) ∧
      1 ≤ n ∧ s + d ^ 2 = Nat.card ↥hyp.H * n ∧
      (hyp.p ^ hyp.q - 1) * d ^ 2 ≤ s ∧ (n = 1 → d ^ 2 = 1) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set αS : ↥hyp.S → ℂ := H_sharp_alphaFun _hG hyp hyp.eta10 with hαSdef
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  refine ⟨fun g => if h : g ∈ hyp.S then αS ⟨g, h⟩ else 0, ?_⟩
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 _hG hyp).H.subgroupOf hyp.S with hKdef
  haveI : Fintype ↥K := FiniteInduce.finiteSubFintype K
  -- The single sharp `Finset` all bookkeeping runs through.
  set F : Finset ↥hyp.S := (Finset.univ.filter (· ∈ K)).erase 1 with hFdef
  have hFK : ∀ x : ↥hyp.S, x ∈ F ↔ (x ∈ K ∧ x ≠ 1) := fun x => by
    rw [hFdef, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, Finset.mem_univ _, h2⟩⟩
  have hFH : ∀ x : ↥hyp.S, x ∈ F ↔ ((x : G) ∈ hyp.H ∧ x ≠ 1) := fun x => by
    rw [hFK]
    exact and_congr_left (fun _ => Subgroup.mem_subgroupOf)
  set ψ : ClassFunction ↥K ℂ :=
    ClassFunction.restrict K (H_sharp_alphaCF _hG hyp hyp.eta10) with hψdef
  have hψZ : ψ ∈ ZIrr ↥K :=
    H_sharp_alphaCF_restrict_mem_ZIrr _hG hyp hyp.eta10 (eta10_cCoeff_int _hG hyp)
  obtain ⟨n, hn⟩ := exists_nat_inner_self_of_mem_ZIrr hψZ
  obtain ⟨z, hz⟩ := OddOrder.Algebra.exists_int_apply_one_of_mem_ZIrr hψZ
  have hψ1 : ψ 1 = αS 1 := by
    rw [hψdef, ClassFunction.restrict_apply, OneMemClass.coe_one, H_sharp_alphaCF_apply]
  have hcardK : Nat.card ↥K = Nat.card ↥hyp.H := by
    rw [hKdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76 _hG hyp).H ≤ hyp.S from hHS)).toEquiv
  set d : ℕ := z.natAbs with hddef
  have hagree : ∀ k : ↥K, αS ↑k = ψ k := fun k => by
    rw [hψdef, ClassFunction.restrict_apply, H_sharp_alphaCF_apply]
  -- Bookkeeping over `F`.
  have hbook := sum_finset_sharp_normSq_eq (K := K) F hFK αS ψ hagree hn
  have hα1 : ‖αS 1‖ ^ 2 = (d : ℝ) ^ 2 := by
    have h2 : ((d : ℕ) : ℝ) ^ 2 = ((z : ℝ)) ^ 2 := by
      rw [hddef]
      have h0 : (((z.natAbs ^ 2 : ℕ) : ℤ) : ℝ) = ((z ^ 2 : ℤ) : ℝ) := by
        exact_mod_cast Int.natAbs_sq z
      push_cast at h0
      rw [Int.cast_natAbs, Int.cast_abs]
      exact h0
    rw [← hψ1, hz, Complex.norm_intCast, sq_abs, ← h2]
  have hsharp_nonneg : (0 : ℝ) ≤ ∑ x ∈ F, ‖αS x‖ ^ 2 :=
    Finset.sum_nonneg (fun x _ => by positivity)
  have hd2n : d ^ 2 ≤ Nat.card ↥hyp.H * n := by
    have h0 := hsharp_nonneg
    rw [hbook] at h0
    have h1 : (d : ℝ) ^ 2 ≤ (Nat.card ↥hyp.H : ℝ) * (n : ℝ) := by
      rw [← hα1, ← hcardK]
      linarith [h0]
    exact_mod_cast h1
  set s : ℕ := Nat.card ↥hyp.H * n - d ^ 2 with hsdef
  have hsval : (s : ℝ) = (Nat.card ↥hyp.H : ℝ) * (n : ℝ) - (d : ℝ) ^ 2 := by
    rw [hsdef, Nat.cast_sub hd2n]
    push_cast
    ring
  have hFsum : ∑ x ∈ F, ‖αS x‖ ^ 2 = (s : ℝ) := by
    rw [hbook, hα1, hsval, hcardK]
  -- Transport to the ambient sharp set.
  have hglue := sum_finset_sharp_transport (K := hyp.H) (L := hyp.S) hHS F hFH
    (fun g : G => ‖if h : g ∈ hyp.S then αS ⟨g, h⟩ else 0‖ ^ 2)
  have hGside : ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
      ‖if h : x ∈ hyp.S then αS ⟨x, h⟩ else 0‖ ^ 2 = (s : ℝ) := by
    rw [← hglue, ← hFsum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxS : ((x : ↥hyp.S) : G) ∈ hyp.S := x.2
    rw [dif_pos hxS]
  refine ⟨d, n, s, ?_, hGside, ?_, ?_, ?_, ?_⟩
  · -- The point formula: `η₁₀ = α` on `H^#`.
    intro x hx
    obtain ⟨hxH, hx1⟩ := (Set.Finite.mem_toFinset _).mp hx
    have hxS : x ∈ hyp.S := hHS hxH
    show hyp.eta10 x = if h : x ∈ hyp.S then αS ⟨x, h⟩ else 0
    rw [dif_pos hxS]
    have hxsharp : ((⟨x, hxS⟩ : ↥hyp.S) : G) ∈
        OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) :=
      OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, hx1⟩
    have hpt := H_sharp_point_formula_kernel_only _hG hyp hyp.eta10
      (eta10_cCoeff_orthogonal _hG hyp chars) ⟨x, hxS⟩ hxsharp
    rw [hpt]
    rfl
  · -- `1 ≤ n`: else `ψ = 0` pointwise, contradicting `α(1) ≠ 0`.
    by_contra hn0
    push_neg at hn0
    have hn00 : n = 0 := by omega
    subst hn00
    have hzero : ∑ k : ↥K, ‖ψ k‖ ^ 2 = 0 := by
      have h := sum_normSq_eq_card_mul_inner (H := ↥K) ψ
      rw [hn] at h
      have h0 : ((∑ k : ↥K, ‖ψ k‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [h]; push_cast; ring
      exact_mod_cast h0
    have hψ10 : ψ 1 = 0 := by
      have h1 : ‖ψ 1‖ ^ 2 = 0 := by
        have hle : ‖ψ 1‖ ^ 2 ≤ ∑ k : ↥K, ‖ψ k‖ ^ 2 :=
          Finset.single_le_sum (f := fun k : ↥K => ‖ψ k‖ ^ 2)
            (fun k _ => by positivity) (Finset.mem_univ 1)
        have hge : (0 : ℝ) ≤ ‖ψ 1‖ ^ 2 := by positivity
        linarith [hzero ▸ hle]
      have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      simpa using h2
    refine eta10_alphaCF_one_ne_zero _hG hyp chars ?_
    rw [hψdef, ClassFunction.restrict_apply, OneMemClass.coe_one,
      H_sharp_alphaCF_apply] at hψ10
    rw [← H_sharp_alphaCF_apply _hG hyp hyp.eta10 1] at hψ10
    exact hψ10
  · -- Parseval: `s + d² = |H|·n`.
    omega
  · -- Inflation: `(p^q − 1)·d² ≤ s`.
    have hinfl := H_sharp_alphaFun_inflation_finset _hG hyp hyp.eta10 F hFH
    have h1 : ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 ≤ (s : ℝ) := by
      rw [← hα1, ← hFsum]
      exact hinfl
    exact_mod_cast h1
  · -- `n = 1 → d² = 1`: `ψ` is `±` an irreducible of the abelian `K`, hence linear.
    intro hn1
    subst hn1
    have hn' : ClassFunction.inner ψ ψ = 1 := by rw [hn]; norm_num
    obtain ⟨ε, ξ, hε, hψeq⟩ :=
      OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one hψZ hn'
    haveI : IsMulCommutative ↥K := by
      have hH := hyp.H_mulCommutative _hG
      have e := Subgroup.subgroupOfEquivOfLe
        (show (H_sharp_hypothesis76 _hG hyp).H ≤ hyp.S from hHS)
      exact ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul]
        exact hH.is_comm.comm (e a) (e b))⟩⟩
    have hξ1 : (ξ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        ξ.2
    have hz2 : (z : ℂ) = (ε : ℂ) := by
      rw [← hz, hψeq,
        show ((ε • (ξ : ClassFunction ↥K ℂ)) 1) = (ε : ℂ) * (ξ : ClassFunction ↥K ℂ) 1 from by
          rw [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.smul_apply],
        hξ1, mul_one]
    have hzε : z = ε := by exact_mod_cast hz2
    rcases hε with h | h <;>
      · rw [hddef, hzε, h]
        rfl

/-- **Peterfalvi (13.7), textbook form**: `∑_{x∈H^#}|η₁₀(x)|² ≥ |H^#|`, as a sum over the
ambient sharp `H^# ⊂ G`.

**Real assembly** through the (13.7) engine `caseB_eta_norm_bound` (stated over an abstract
`Finset`, instantiated with `H^# ⊂ G` directly): the character-theoretic inputs are the
(13.5)-for-`η₁₀` package (`exists_caseB_data_eta10`); `|H| ≥ 1` and `|P| = p^q ≥ 2` are
counting facts. -/
theorem eta10_sharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (chars : CharacterDegreeData hyp) :
    (Nat.card ↥hyp.H : ℝ) - 1
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  obtain ⟨α, d, n, s, hχ, hs, hn, hParseval, hInflation, habelian⟩ :=
    exists_caseB_data_eta10 _hG hyp chars
  have hH1 : 1 ≤ Nat.card ↥hyp.H := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hP2 : 2 ≤ hyp.p ^ hyp.q - 1 + 1 := by
    have hp3 := hyp.three_le_p
    have hq3 := hyp.three_le_q
    have h1 : 3 ≤ hyp.p ^ hyp.q := by
      calc 3 ≤ hyp.p := hp3
        _ ≤ hyp.p ^ hyp.q := Nat.le_self_pow (by omega) _
    omega
  haveI : Fintype G := Fintype.ofFinite G
  have h := caseB_eta_norm_bound (S := G) α (fun x => hyp.eta10 x)
    ((Set.toFinite (sharpSubgroup hyp.H)).toFinset)
    (Hcard := Nat.card ↥hyp.H) (P := hyp.p ^ hyp.q - 1 + 1) (d := d) (n := n) (s := s)
    hH1 (fun x hx => hχ x hx) hs hP2 hn hParseval (by simpa using hInflation) habelian
  exact h

/-- **`2v ≤ |Q| − 1`** — the `T`-side mirror of `two_mul_u_le`: from the (13.4) value
`v = (q^p − 1)/(q − 1)` and `q ≥ 3`, so `v ≤ (q^p−1)/2`. -/
theorem Hypothesis.two_mul_v_le (hyp : Hypothesis (G := G))
    (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    2 * hyp.v ≤ hyp.q ^ hyp.p - 1 := by
  have hq3 := hyp.three_le_q
  have h1 : (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ≤ (hyp.q ^ hyp.p - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : (hyp.q ^ hyp.p - 1) / 2 * 2 ≤ hyp.q ^ hyp.p - 1 := Nat.div_mul_le_self _ _
  omega

open scoped Classical in
open scoped FiniteInduce in
open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side (13.3.c) distinguished index** — the `μ'_j` of the (13.8)-for-`T` estimate,
localized to the `(T, Q^#)` (7.6) family: a `Q`-non-kernel member `ζ_{i₁}` with
`‖ζ_{i₁}‖² = p`, degree `pv`, distinguished coefficient `⟨τψ_{i₁}, η₁₀⟩ = δ = ±1`, and all
other `Q`-non-kernel coefficients vanishing.  Faithful producer; gated on the `T`-side (13.3.c)
grid analysis. -/
theorem exists_muT_index [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp)
    (hvd : hyp.v * hyp.d ≠ 1) :
    ∃ (i₁ : Fin ((Q_sharp_hypothesis76 hG hyp hvd).n + 1)) (δ : ℤ), 0 < i₁ ∧
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((Q_sharp_hypothesis76 hG hyp hvd).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (Q_sharp_hypothesis76 hG hyp hvd).cCoeff hyp.eta10 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((Q_sharp_hypothesis76 hG hyp hvd).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((Q_sharp_hypothesis76 hG hyp hvd).zeta i)) →
        (Q_sharp_hypothesis76 hG hyp hvd).cCoeff hyp.eta10 i = 0) ∧
      (Q_sharp_hypothesis76 hG hyp hvd).zetaNormSq i₁ = (hyp.p : ℂ) ∧
      (Q_sharp_hypothesis76 hG hyp hvd).zeta i₁ 1 = ((hyp.p * hyp.v : ℕ) : ℂ) := by
  sorry

open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side correction has integer value at `1`** — the `T`-side (13.5.a) integrality
(`α|_Q ∈ ℤ[Irr Q]` needs `Q` abelian, the gated (13.2.b)-dual; carried as an atom). -/
theorem exists_etaT_alphaFun_one_int [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (hvd : hyp.v * hyp.d ≠ 1) :
    ∃ α1 : ℤ, hypothesis76AlphaFun (Q_sharp_hypothesis76 hG hyp hvd)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 1 = (α1 : ℂ) := by
  sorry

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5) for the `T`-side, `χ = η₁₀`, `ζ = (1/p)·μ'_j`, `a = δ`** — the
correction datum of the (13.8)-for-`T` estimate.

**Real assembly** over the `T`-side ρ-machinery (`Q_sharp_hypothesis76`) and the generic
(13.5.a) cluster: `ζ := (1/p)·ζ_{i₁}` (`exists_muT_index`: `‖ζ_{i₁}‖² = p`, degree `pv`,
coefficient `δ`), `α` the `Q`-kernel tail (`hypothesis76AlphaFun`); the point formula is the
generic `hypothesis76_point_formula`, the first term is `(1/p²)(|T|·p − (pv)²) = |T'| − v²`
(Parseval + `card_T_eq_deriv_mul_p`), the inner-product vanishes by the distinct-fibre
orthogonality (S-level shortcut), and the inflation is the generic `F`-form with
`|Q| = q^p`. -/
theorem exists_caseB_data_eta10_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    ∃ (ζ α : ↥hyp.T → ℂ) (α1 δ : ℤ),
      (∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T → ζ x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        ζ x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
        hyp.eta10 ↑x = (δ : ℂ) * ζ x + α x) ∧
      ((∑ x : ↥hyp.T, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2
        = (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) ∧
      ((ζ 1 * (starRingEnd ℂ) (α 1)).re = (hyp.v : ℝ) * (α1 : ℝ)) ∧
      δ ^ 2 = 1 ∧
      ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) * ((α1 : ℤ) : ℝ) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1, ‖α x‖ ^ 2 := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨hD, hv, hQcard⟩ := lambda_forces_T_caseB _hG chars
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  obtain ⟨i₁, δ, hi₁pos, hi₁ker, hδ2, hi₁c, hmiddle, hnormP, hdeg⟩ :=
    exists_muT_index _hG chars hvd
  obtain ⟨α1, hα1⟩ := exists_etaT_alphaFun_one_int _hG (hyp := hyp) hvd
  have hp3 := hyp.three_le_p
  have hpC : (hyp.p : ℂ) ≠ 0 := by exact_mod_cast (by omega : hyp.p ≠ 0)
  have hpR : (hyp.p : ℝ) ≠ 0 := by exact_mod_cast (by omega : hyp.p ≠ 0)
  have hvanishZ : ∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T →
      (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x = 0 := fun x hx =>
    (Q_sharp_hypothesis76 _hG hyp hvd).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  refine ⟨fun x => ((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x,
    hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10, α1, δ, ?_, ?_, ?_, ?_, ?_, hδ2, ?_⟩
  · -- `ζ` vanishes off `Q`.
    intro x hx
    show ((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x = 0
    rw [hvanishZ x hx, mul_zero]
  · -- `⟨ζ, α⟩ = 0`: pull the `p⁻¹`, extend to the full sum, cite the generic orthogonality.
    have hfull := hypothesis76_zeta_inner_alphaFun_eq_zero
      (Q_sharp_hypothesis76 _hG hyp hvd) (hyp.Q.subgroupOf hyp.T) hyp.eta10 i₁ hi₁ker
    have hext : (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
            (hyp.Q.subgroupOf hyp.T) hyp.eta10 x))
        = ∑ x : ↥hyp.T, (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
              (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ hyp.Q.subgroupOf hyp.T)
        (fun x => (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
            (hyp.Q.subgroupOf hyp.T) hyp.eta10 x))]
      have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.Q.subgroupOf hyp.T),
          (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
              (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) = 0 := by
        refine Finset.sum_eq_zero (fun x hx => ?_)
        rw [hvanishZ x (Finset.mem_filter.mp hx).2, zero_mul]
      rw [h0, add_zero]
    calc ∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        ((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
            (hyp.Q.subgroupOf hyp.T) hyp.eta10 x)
        = ((hyp.p : ℂ))⁻¹ * ∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
            (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x * (starRingEnd ℂ)
              (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
                (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = 0 := by rw [hext, hfull, mul_zero]
  · -- The point formula, with `c̄_{i₁}/‖ζ_{i₁}‖² = δ/p`.
    intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxQ : (↑x : G) ∈ hyp.Q :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxQ, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    show hyp.eta10 ↑x = (δ : ℂ)
        * (((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x)
      + hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
          (hyp.Q.subgroupOf hyp.T) hyp.eta10 x
    have hpt := hypothesis76_point_formula (Q_sharp_hypothesis76 _hG hyp hvd)
      (fun _ => rfl) (hyp.Q.subgroupOf hyp.T) hyp.eta10 i₁ hi₁pos hi₁ker hmiddle x hxsharp
    have htail : (∑ i ∈ (Finset.Ioi (0 : Fin ((Q_sharp_hypothesis76 _hG hyp hvd).n + 1))).filter
          (fun i => (hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
            OddOrder.Peterfalvi.S03.characterKernel
              ((Q_sharp_hypothesis76 _hG hyp hvd).zeta i)),
        (star ((Q_sharp_hypothesis76 _hG hyp hvd).cCoeff hyp.eta10 i) /
          (Q_sharp_hypothesis76 _hG hyp hvd).zetaNormSq i)
          * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i x)
        = hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
            (hyp.Q.subgroupOf hyp.T) hyp.eta10 x := rfl
    rw [hpt, htail, hi₁c, star_intCast, hnormP]
    ring
  · -- The first term: `(1/p²)(|T|·p − (pv)²) = |T'| − v²`.
    have hpars : ((∑ x : ↥hyp.T, ‖(Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x‖ ^ 2 : ℝ) : ℂ)
        = (Nat.card ↥hyp.T : ℂ) * (hyp.p : ℂ) := by
      rw [sum_normSq_eq_card_mul_inner, ← OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq,
        hnormP]
    have hparsR : ∑ x : ↥hyp.T, ‖(Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x‖ ^ 2
        = (Nat.card ↥hyp.T : ℝ) * (hyp.p : ℝ) := by exact_mod_cast hpars
    have hscale : ∀ x : ↥hyp.T,
        ‖((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x‖ ^ 2
        = ((hyp.p : ℝ))⁻¹ ^ 2 * ‖(Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ x‖ ^ 2 := by
      intro x
      rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    have hζ1 : ‖((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ 1‖ ^ 2
        = (hyp.v : ℝ) ^ 2 := by
      rw [hdeg, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
      rw [show ((hyp.p * hyp.v : ℕ) : ℝ) = (hyp.p : ℝ) * (hyp.v : ℝ) from by push_cast; ring]
      field_simp
    have hTp : (Nat.card ↥hyp.T : ℝ) = (Nat.card ↥(derivedInG hyp.T) : ℝ) * (hyp.p : ℝ) := by
      exact_mod_cast hyp.card_T_eq_deriv_mul_p _hG
    rw [Finset.sum_congr rfl (fun x _ => hscale x), ← Finset.mul_sum, hparsR, hζ1, hTp]
    field_simp
  · -- The cross term: `ζ(1) = v` real, `α(1) = α1 ∈ ℤ`.
    have hζ1v : ((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ 1
        = ((hyp.v : ℕ) : ℂ) := by
      rw [hdeg, show ((hyp.p * hyp.v : ℕ) : ℂ) = (hyp.p : ℂ) * (hyp.v : ℂ) from by
        push_cast; ring]
      field_simp
    show ((((hyp.p : ℂ))⁻¹ * (Q_sharp_hypothesis76 _hG hyp hvd).zeta i₁ 1)
        * (starRingEnd ℂ) (hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
          (hyp.Q.subgroupOf hyp.T) hyp.eta10 1)).re = (hyp.v : ℝ) * (α1 : ℝ)
    rw [hζ1v, hα1]
    rw [show ((hyp.v : ℕ) : ℂ) = (((hyp.v : ℕ) : ℝ) : ℂ) from by push_cast; ring,
      show ((α1 : ℤ) : ℂ) = (((α1 : ℤ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  · -- The inflation: generic `F`-form with `|Q| = q^p`.
    have hF : ∀ x : ↥hyp.T, x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1
        ↔ ((x : G) ∈ (Q_sharp_hypothesis76 _hG hyp hvd).H ∧ x ≠ 1) := by
      intro x
      rw [Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨Subgroup.mem_subgroupOf.mp h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr h2⟩
    have hP'H : ∀ x : ↥hyp.T, x ∈ hyp.Q.subgroupOf hyp.T →
        (x : G) ∈ (Q_sharp_hypothesis76 _hG hyp hvd).H := fun x hx =>
      Subgroup.mem_subgroupOf.mp hx
    have hinfl := hypothesis76AlphaFun_inflation (Q_sharp_hypothesis76 _hG hyp hvd)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 _ hF hP'H
    have hcardQT : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = hyp.q ^ hyp.p := by
      have hQT : hyp.Q ≤ hyp.T := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv]
      exact hQcard
    have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p :=
      Nat.one_le_pow _ _ (by have := hyp.three_le_q; omega)
    have hcoeff : ((Nat.card ↥(hyp.Q.subgroupOf hyp.T) : ℝ)) - 1
        = ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) := by
      rw [hcardQT, Nat.cast_sub hqp1]
      norm_num
    have hval : ‖hypothesis76AlphaFun (Q_sharp_hypothesis76 _hG hyp hvd)
        (hyp.Q.subgroupOf hyp.T) hyp.eta10 1‖ ^ 2 = ((α1 : ℤ) : ℝ) ^ 2 := by
      rw [hα1, Complex.norm_intCast, sq_abs]
    rw [← hval, ← hcoeff]
    exact hinfl


open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8) applied to `T`**: `∑_{x∈Q^#}|η₁₀(x)|² ≥ |T'| − v²`, as a sum over the
ambient sharp `Q^# ⊂ G`.

**Real assembly** through the (13.8) engine `caseB_eta01_norm_bound` (inside `↥T`, with
`Q.subgroupOf T`): the character-theoretic inputs are the `T`-side (13.5) package
(`exists_caseB_data_eta10_T`, normalized `ζ` with first term `|T'| − v²`), and the `v`-bound
`2v ≤ |Q| − 1 = q^p − 1` (`two_mul_v_le`, real from the (13.4) value); the engine output
transports to the ambient sharp by `sum_apply_erase_one_filter_subgroupOf`. -/
theorem eta10_Qsharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  classical
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  obtain ⟨-, hv, -⟩ := lambda_forces_T_caseB _hG chars
  obtain ⟨ζ, α, α1, δ, hvanish, hinner, hχ, hfirstTerm, hcross, hδ, hinfl⟩ :=
    exists_caseB_data_eta10_T _hG chars
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hu := hyp.two_mul_v_le hv
  -- The engine (bridging the `Classical` decidability instances baked into its statement).
  have hengine : (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
          ‖hyp.eta10 ↑x‖ ^ 2 := by
    have h := caseB_eta01_norm_bound (S := ↥hyp.T) (hyp.Q.subgroupOf hyp.T)
      ζ α (fun x => hyp.eta10 ↑x)
      (Pm1 := hyp.q ^ hyp.p - 1) (u := hyp.v)
      (firstTerm := (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      (α1 := α1) (δ := δ)
      hvanish (by convert hinner using 2 <;> congr!)
      (fun x hx => hχ x (by convert hx using 2 <;> congr!))
      hfirstTerm hcross hδ
      (by convert hinfl using 2 <;> congr!) hu
    convert h using 2 <;> congr!
  rwa [sum_apply_erase_one_filter_subgroupOf hQT
    (fun y => ‖hyp.eta10 y‖ ^ 2)] at hengine

open scoped FiniteInduce in
/-- **Peterfalvi (13.6) + Parseval, atom form**: `1 ≥ 1/|G| + slam + 1 − uq/(cp^q)`.

The (13.10.1) estimate: global Parseval for `λ^{τ₁}` (`global_normSq_split`, real), the
`‖λ^{τ₁}(1)‖² ≥ 1` term (`one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one`, real from
`lambda_tau1_norm_one`), the `G₀`-sum read as the rational atom (`normSqSumQ_spec` +
`G0Finset_cyclicClosed` + Galois integrality, real), the `H^#`-sum bounded by (13.6)
(`lambda_tau1_sharp_norm_lower`), the `Q^#`-sum dropped, and `|S| = p^q(uc)q` (`card_S_val`). -/
theorem analyticEstimate_lambda [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (chars : CharacterDegreeData hyp) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset (chars.tau1S chars.lambda) / (Nat.card G : ℚ) + 1
        - (hyp.u : ℚ) * (hyp.q : ℚ) / ((hyp.c : ℚ) * (hyp.p : ℚ) ^ hyp.q) := by
  classical
  obtain ⟨hZ, hn, -⟩ := lambda_tau1_norm_one _hG chars
  obtain ⟨hD, hv, hQ⟩ := lambda_forces_T_caseB _hG chars
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  set φ : ClassFunction G ℂ := chars.tau1S chars.lambda with hφdef
  -- Global Parseval split and the term bounds.
  have hsplit := hyp.global_normSq_split _hG φ hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖φ 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharp := lambda_tau1_sharp_norm_lower _hG chars
  rw [← hφdef] at hsharp
  have hQnonneg : (0 : ℝ) ≤ (hyp.T.index : ℝ)
      * ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2 := by
    have h1 : (0 : ℝ) ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2 :=
      Finset.sum_nonneg fun x _ => by positivity
    positivity
  -- The rational atom is the `G₀`-sum.
  have hGal := OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZ
    hyp.G0Finset_cyclicClosed
  have hspec := normSqSumQ_spec hGal
  -- Cardinalities.
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hGeq : (Nat.card G : ℝ)
      = (hyp.p : ℝ) ^ hyp.q * ((hyp.u : ℝ) * (hyp.c : ℝ)) * (hyp.q : ℝ)
        * (hyp.S.index : ℝ) := by
    have h := hyp.S.card_mul_index
    rw [hyp.card_S_val _hG] at h
    exact_mod_cast h.symm
  have hc0 : (0 : ℝ) < (hyp.c : ℝ) := by
    have : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
    exact_mod_cast this
  have hp0 : (0 : ℝ) < (hyp.p : ℝ) := by
    have := hyp.three_le_p; exact_mod_cast (by omega : 0 < hyp.p)
  -- Assemble in ℝ, then cast.
  rw [ge_iff_le, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspec]
  set s : ℝ := ∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2 with hsdef
  set w : ℝ := (hyp.u : ℝ) * (hyp.q : ℝ) / ((hyp.c : ℝ) * (hyp.p : ℝ) ^ hyp.q) with hwdef
  -- `w·|G| = [G:S]·(uq)²`.
  have hwg : w * (Nat.card G : ℝ) = (hyp.S.index : ℝ) * ((hyp.u : ℝ) * (hyp.q : ℝ)) ^ 2 := by
    rw [hwdef, hGeq]
    field_simp
  -- `1 + s ≤ w·|G|` from the split.
  have hSidx0 : (0 : ℝ) ≤ (hyp.S.index : ℝ) := by positivity
  have hkey : 1 + s ≤ w * (Nat.card G : ℝ) := by
    rw [hwg]
    have hSGeq : (hyp.S.index : ℝ) * (Nat.card ↥hyp.S : ℝ) = (Nat.card G : ℝ) := by
      exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
    have huq : ((hyp.u * hyp.q : ℕ) : ℝ) = (hyp.u : ℝ) * (hyp.q : ℝ) := by push_cast; ring
    rw [huq] at hsharp
    have hHbound := mul_le_mul_of_nonneg_left hsharp hSidx0
    rw [nsmul_eq_mul, nsmul_eq_mul] at hsplit
    linarith [hsplit, hone, hHbound, hQnonneg, hSGeq]
  -- Final division.
  have hdiv : (1 + s) / (Nat.card G : ℝ) ≤ w :=
    (div_le_iff₀ hg0).mpr (by linarith [hkey])
  calc 1 / (Nat.card G : ℝ) + s / (Nat.card G : ℝ) + 1 - w
      = (1 + s) / (Nat.card G : ℝ) + 1 - w := by rw [add_div]
    _ ≤ w + 1 - w := by linarith [hdiv]
    _ = 1 := by ring

open scoped FiniteInduce in
/-- **Peterfalvi (13.7)+(13.8) for `T` (`D = 1`), atom form**:
`1 ≥ 1/|G| + seta + HS + TT` with `TT` the (13.4) counting value.

The (13.10.2) estimate: global Parseval for `η₁₀` (`global_normSq_split`; the norm-one facts
are *real*, from the 3002-threaded grid: `eta10_mem_ZIrr`/`eta10_inner_self_one`), the
`G₀`-sum read as the rational atom, the `H^#`-sum bounded by (13.7) (`eta10_sharp_norm_lower`),
the `Q^#`-sum bounded by (13.8)-for-`T` (`eta10_Qsharp_norm_lower`), and the (13.4) values
collapsing `(|T'|−v²)/|T|` to the stated `TT`. -/
theorem analyticEstimate_eta [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
          + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) := by
  classical
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  obtain ⟨hD, hv, hQ⟩ := lambda_forces_T_caseB _hG chars
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  have hZ := hyp.eta10_mem_ZIrr
  have hn := hyp.eta10_inner_self_one
  -- Global Parseval split and the term bounds.
  have hsplit := hyp.global_normSq_split _hG hyp.eta10 hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖hyp.eta10 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharpH := eta10_sharp_norm_lower _hG hyp chars
  have hsharpQ := eta10_Qsharp_norm_lower _hG hyp
  -- The rational atom is the `G₀`-sum.
  have hGal := OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZ
    hyp.G0Finset_cyclicClosed
  have hspec := normSqSumQ_spec hGal
  -- Cardinalities and casts.
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p := Nat.one_le_pow _ _ (by omega)
  have hdvd : (hyp.q - 1) ∣ (hyp.q ^ hyp.p - 1) := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.q 1 hyp.p
  have hvq : (hyp.v : ℝ) * ((hyp.q : ℝ) - 1) = (hyp.q : ℝ) ^ hyp.p - 1 := by
    have h := Nat.div_mul_cancel hdvd
    rw [← hv] at h
    have := congrArg (Nat.cast (R := ℝ)) h
    push_cast [Nat.cast_sub (by omega : (1:ℕ) ≤ hyp.q), Nat.cast_sub hqp1] at this
    convert this using 2 <;> push_cast <;> ring
  have hderivT : (Nat.card ↥(derivedInG hyp.T) : ℝ) = (hyp.q : ℝ) ^ hyp.p * (hyp.v : ℝ) := by
    have h := hyp.card_deriv_T_eq _hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hTval : (Nat.card ↥hyp.T : ℝ) = (hyp.q : ℝ) ^ hyp.p * (hyp.v : ℝ) * (hyp.p : ℝ) := by
    have h := hyp.card_T_eq _hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hSGeq : (hyp.S.index : ℝ) * (Nat.card ↥hyp.S : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
  have hTGeq : (hyp.T.index : ℝ) * (Nat.card ↥hyp.T : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.T) hyp.T.index ▸ hyp.T.card_mul_index
  have hS0 : (0 : ℝ) < (Nat.card ↥hyp.S : ℝ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.S)
  have hT0 : (0 : ℝ) < (Nat.card ↥hyp.T : ℝ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.T)
  have hSidx0 : (0 : ℝ) < (hyp.S.index : ℝ) := by
    rcases (Nat.cast_pos (α := ℝ)).mpr (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := hyp.S))) with h
    exact h
  have hTidx0 : (0 : ℝ) < (hyp.T.index : ℝ) := by
    rcases (Nat.cast_pos (α := ℝ)).mpr (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := hyp.T))) with h
    exact h
  have hp0 : (0 : ℝ) < (hyp.p : ℝ) := by exact_mod_cast (by omega : 0 < hyp.p)
  have hq10 : (0 : ℝ) < (hyp.q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (hyp.q : ℝ) := by exact_mod_cast hq3
    linarith
  have hqp0 : (0 : ℝ) < (hyp.q : ℝ) ^ hyp.p := by
    have : (0 : ℝ) < (hyp.q : ℝ) := by exact_mod_cast (by omega : 0 < hyp.q)
    positivity
  have hv0 : (0 : ℝ) < (hyp.v : ℝ) := by exact_mod_cast (by omega : 0 < hyp.v)
  -- Cast the goal to ℝ.
  rw [ge_iff_le, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspec]
  set s : ℝ := ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 with hsdef
  set sH : ℝ := ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖hyp.eta10 x‖ ^ 2
    with hsHdef
  set sQ : ℝ := ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖hyp.eta10 x‖ ^ 2
    with hsQdef
  rw [nsmul_eq_mul, nsmul_eq_mul] at hsplit
  -- The `TT` value equals `(|T'| − v²)/|T|`.
  set TT : ℝ := 1 / (hyp.p : ℝ) - 1 / ((hyp.p : ℝ) * ((hyp.q : ℝ) - 1))
      + 1 / ((hyp.p : ℝ) * ((hyp.q : ℝ) - 1) * (hyp.q : ℝ) ^ hyp.p) with hTTdef
  have hveq : (hyp.v : ℝ) = ((hyp.q : ℝ) ^ hyp.p - 1) / ((hyp.q : ℝ) - 1) := by
    rw [eq_div_iff hq10.ne']
    exact hvq
  have hTT : TT = ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      / (Nat.card ↥hyp.T : ℝ) := by
    rw [hTTdef, hderivT, hTval, hveq]
    have hqp1' : (1 : ℝ) < (hyp.q : ℝ) ^ hyp.p := by
      have h1 : (1:ℕ) < hyp.q ^ hyp.p := by
        calc 1 < hyp.q := by omega
          _ ≤ hyp.q ^ hyp.p := Nat.le_self_pow (by omega) _
      exact_mod_cast h1
    have hnum0 : (hyp.q : ℝ) ^ hyp.p - 1 ≠ 0 := by linarith
    field_simp
    ring
  -- The `HS` term transported to `/|G|`.
  have hH1 : (1 : ℕ) ≤ Nat.card ↥hyp.H := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hterm3 : ((Nat.card ↥hyp.H - 1 : ℕ) : ℝ) / (Nat.card ↥hyp.S : ℝ)
      = (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1) / (Nat.card G : ℝ) := by
    rw [← hSGeq, Nat.cast_sub hH1, Nat.cast_one,
      mul_div_mul_left _ _ hSidx0.ne']
  have hterm4 : TT = (hyp.T.index : ℝ)
      * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) / (Nat.card G : ℝ) := by
    rw [hTT, ← hTGeq, mul_div_mul_left _ _ hTidx0.ne']
  -- Assemble.
  have hbound : 1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
      + (hyp.T.index : ℝ) * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      ≤ (Nat.card G : ℝ) := by
    have hHb := mul_le_mul_of_nonneg_left hsharpH hSidx0.le
    have hQb := mul_le_mul_of_nonneg_left hsharpQ hTidx0.le
    nlinarith [hsplit, hone, hHb, hQb]
  rw [hterm3, hterm4]
  have hfinal : (1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
      + (hyp.T.index : ℝ) * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2))
      / (Nat.card G : ℝ) ≤ 1 := by
    rw [div_le_one hg0]
    exact hbound
  calc 1 / (Nat.card G : ℝ) + s / (Nat.card G : ℝ)
        + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1) / (Nat.card G : ℝ)
        + (hyp.T.index : ℝ) * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
          / (Nat.card G : ℝ)
      = (1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
          + (hyp.T.index : ℝ) * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2))
          / (Nat.card G : ℝ) := by
        rw [add_div, add_div, add_div]
    _ ≤ 1 := hfinal

/-- **Peterfalvi (13.9.a), atom form**: the disjoint-cover counting
`1 = 1/|G| + |G₀|/|G| + |H#|/|S| + |Q#|/|T|` with `|Q#|/|T|` collapsed to its (13.4) value
`(q−1)/(pq^p)`.

Assembled from the ℕ-count `card_univ_split` (the `f = 1` four-piece split over the TI
saturations), Lagrange (`card_mul_index` on `S` and `T`), the `|T|`-decomposition `card_T_eq`,
and the (13.4) values (`lambda_forces_T_caseB`: `D = 1`, `v = (q^p−1)/(q−1)`, `|Q| = q^p`). -/
theorem analyticCounting_disjointCover [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (1 : ℚ) = 1 / (Nat.card G : ℚ) + (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- (13.4) values.
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  obtain ⟨hD, hv, hQ⟩ :=
    lambda_forces_T_caseB _hG chars
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  -- `v ≥ 2` (so `vd ≠ 1`, excluding type V in the counting layer).
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega) (by omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  have hvd : hyp.v * hyp.d ≠ 1 := by rw [hd1, mul_one]; omega
  -- The ℕ-count, cast to ℚ.
  have hsplit := hyp.card_univ_split _hG hQ hvd
  have key : (Nat.card G : ℚ) = 1 + (hyp.G0Finset.card : ℚ)
      + (hyp.S.index : ℚ) * ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ)
      + (hyp.T.index : ℚ) * ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) := by
    exact_mod_cast hsplit
  -- Nonvanishing.
  have hG0 : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos (α := G)
  have hS0 : (0 : ℚ) < (Nat.card ↥hyp.S : ℚ) := by exact_mod_cast Nat.card_pos (α := ↥hyp.S)
  have hT0 : (0 : ℚ) < (Nat.card ↥hyp.T : ℚ) := by exact_mod_cast Nat.card_pos (α := ↥hyp.T)
  have hSidx : (hyp.S.index : ℚ) * (Nat.card ↥hyp.S : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
  have hTidx : (hyp.T.index : ℚ) * (Nat.card ↥hyp.T : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.T) hyp.T.index ▸ hyp.T.card_mul_index
  have hSidx0 : (hyp.S.index : ℚ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hSidx; exact hG0.ne' hSidx.symm
  have hTidx0 : (hyp.T.index : ℚ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hTidx; exact hG0.ne' hTidx.symm
  -- `v(q−1) = q^p − 1` in ℚ (exact ℕ-division).
  have hq1 : (1 : ℕ) ≤ hyp.q := by omega
  have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p := Nat.one_le_pow _ _ (by omega)
  have hdvd : (hyp.q - 1) ∣ (hyp.q ^ hyp.p - 1) := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.q 1 hyp.p
  have hvq : (hyp.v : ℚ) * ((hyp.q : ℚ) - 1) = (hyp.q : ℚ) ^ hyp.p - 1 := by
    have h := Nat.div_mul_cancel hdvd
    rw [← hv] at h
    have := congrArg (Nat.cast (R := ℚ)) h
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hqp1] at this
    convert this using 2 <;> push_cast <;> ring
  -- `|T| = q^p·v·p` in ℚ.
  have hTval : (Nat.card ↥hyp.T : ℚ)
      = (hyp.q : ℚ) ^ hyp.p * (hyp.v : ℚ) * (hyp.p : ℚ) := by
    have h := hyp.card_T_eq _hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  -- `|Q^#|` in ℚ.
  have hQ1 : ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) = (hyp.q : ℚ) ^ hyp.p - 1 := by
    rw [hQ, Nat.cast_sub hqp1]
    push_cast
    ring
  -- Term conversions: `S.index·(|H|−1)/|G| = (|H|−1)/|S|`, and the `Q`-term collapses to the
  -- (13.4) value.
  have hterm3 : ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ) / (Nat.card ↥hyp.S : ℚ)
      = (hyp.S.index : ℚ) * ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ) / (Nat.card G : ℚ) := by
    rw [← hSidx, mul_div_mul_left _ _ hSidx0]
  have hv0 : (hyp.v : ℚ) ≠ 0 := by
    have : (2 : ℚ) ≤ (hyp.v : ℚ) := by exact_mod_cast hv2
    linarith
  have hq10 : (hyp.q : ℚ) - 1 ≠ 0 := by
    have : (3 : ℚ) ≤ (hyp.q : ℚ) := by exact_mod_cast hq3
    linarith
  have hp0 : (hyp.p : ℚ) ≠ 0 := by
    have : (3 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hp3
    linarith
  have hqp0 : (hyp.q : ℚ) ^ hyp.p ≠ 0 := by
    have : (1 : ℚ) ≤ (hyp.q : ℚ) ^ hyp.p := by exact_mod_cast hqp1
    linarith
  have hterm4 : ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p)
      = (hyp.T.index : ℚ) * ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) / (Nat.card G : ℚ) := by
    rw [hQ1, ← hvq, ← hTidx, hTval]
    field_simp
  -- Assemble.
  rw [hterm3, hterm4, ← add_div, ← add_div, ← add_div, ← key, div_self hG0.ne']

open scoped FiniteInduce in
/-- **The `λ^{τ₁}`-value off the `H^#`-saturation is `±` an `η`-column sum** (Peterfalvi
(13.9.a), first step): `(μ_j − λ)^{τ₁} = Ind_S^G(μ_j − λ)` vanishes off `(H^#)^G` — both are
induced from linear characters of `H = PC` ((13.3.a) via `mu_col_tau1_eta_col_one`), so the
difference is `H^#`-supported — whence `λ^{τ₁}(x) = δ ∑_i η_{i1}(x)` there by the (13.3.c)
column formula. -/
theorem lambda_tau1_apply_eq_of_not_mem_H_sat [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) {x : G}
    (hx : x ∉ OddOrder.GroupTheory.conjClassSet (sharpSubgroup hyp.H)) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      chars.tau1S chars.lambda x
        = (δ : ℂ) * ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x := by
  classical
  obtain ⟨j, δ, θμ, hδ, hθμirr, hθμ1, hμInd, hμτ⟩ := chars.mu_col_tau1_eta_col_one
  obtain ⟨θl, hθlirr, hθl1, hlamEq, -⟩ := chars.lambda_induced_from_PC_linear
  haveI hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  have hdiff : chars.tau1S (∑ i : Fin hyp.q, hyp.mu i j) - chars.tau1S chars.lambda
      = ClassFunction.induce hyp.S
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
            - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) := by
    rw [← map_sub, hμInd, hlamEq]
    have h := chars.tau1S_apply_induce_sub θμ θl hθμirr hθlirr
    exact h.trans (by congr! <;> exact Subsingleton.elim _ _)
  have hsupp : ∀ w : ↥hyp.S, (w : G) ∉ sharpSubgroup hyp.H →
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) w = 0 := by
    intro w hw
    rw [ClassFunction.sub_apply]
    by_cases hwH : (w : G) ∈ hyp.H
    · have hw1 : (w : G) = 1 := by
        by_contra hne
        exact hw ⟨hwH, fun h1 => hne (Set.mem_singleton_iff.mp h1)⟩
      have hw1' : w = 1 := Subtype.ext hw1
      subst hw1'
      rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθμ1, hθl1, sub_self]
    · rw [OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal _
          (fun h => hwH (Subgroup.mem_subgroupOf.mp h)),
        OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal _
          (fun h => hwH (Subgroup.mem_subgroupOf.mp h)), sub_self]
  have hvan : ClassFunction.induce hyp.S
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) x = 0 :=
    OddOrder.GroupTheory.IsTISubset.induce_apply_of_not_mem_conjClassSet _ hsupp hx
  refine ⟨δ, hδ, ?_⟩
  have hdv := congrArg (fun f : ClassFunction G ℂ => f x) hdiff
  simp only [ClassFunction.sub_apply] at hdv
  rw [hvan] at hdv
  have hμv := congrArg (fun f : ClassFunction G ℂ => f x) hμτ
  simp only [ClassFunction.smul_apply, smul_eq_mul,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply] at hμv
  have hlamv : chars.tau1S chars.lambda x = chars.tau1S (∑ i : Fin hyp.q, hyp.mu i j) x :=
    (sub_eq_zero.mp hdv).symm
  exact hlamv.trans hμv

/-- **Peterfalvi (13.9.a), nonvanishing dichotomy**: on the generic set `G₀`, the characters
`λ^{τ₁}` and `η₁₀` do not vanish simultaneously.  Faithful producer of the textbook (13.9.a) —
the character content bottoms out at the (13.3.c) `μ_j^{τ₁} = δ·Σηᵢ₁` formula, the (13.2.e)
support fact for `(μ_j − λ)^τ`, the (3.2.c) regular-value formula, and the (3.9.b)/(3.4) grid
relations forcing `q·η₁₁(x) + 1 = 0` (impossible for an algebraic integer) in the doubly-vanishing
case. -/
theorem G0_nonvanishing_dichotomy [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp) :
    ∀ x ∈ hyp.G0Finset, chars.tau1S chars.lambda x ≠ 0 ∨ hyp.eta10 x ≠ 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro x hxF
  have hxG0 : x ∈ hyp.G0 := (Set.Finite.mem_toFinset _).mp hxF
  obtain ⟨hx1, hxH, hxQ⟩ := (hyp.mem_G0_iff x).mp hxG0
  by_cases hreg : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))
  · -- regular-conjugate branch: `η₁₀(x) = ω₁₀(w) ≠ 0`
    right
    obtain ⟨w, hwmem, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hreg
    obtain ⟨hwW, hwnot⟩ := hwmem
    have hconjval : hyp.eta10 x = hyp.eta10 w := by
      rw [← hg]
      exact (OddOrder.RepresentationTheory.ClassFunction.of_isConj hyp.eta10
        (isConj_iff.mpr ⟨g, rfl⟩)).symm
    have hval : hyp.eta10 w
        = hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨w, hwW⟩ := by
      rw [show hyp.eta10 = hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ from rfl,
        hyp.eta_eq_tau_omega]
      exact hyp.tau3_apply_of_regular _ _ hwW hwnot
    rw [hconjval, hval]
    intro h0
    have hmul := hyp.omega_mul ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩
      ⟨w, hwW⟩ ⟨w, hwW⟩⁻¹
    rw [mul_inv_cancel, hyp.omega_apply_one, h0, zero_mul] at hmul
    exact one_ne_zero hmul
  · -- doubly-vanishing branch: contradiction via `q·η₀₁(x) = q − 1`
    by_contra hboth
    push_neg at hboth
    obtain ⟨hl0, he0⟩ := hboth
    obtain ⟨δ, hδ, hlam⟩ := lambda_tau1_apply_eq_of_not_mem_H_sat _hG chars hxH
    have hδ0 : (δ : ℂ) ≠ 0 := by
      rcases hδ with rfl | rfl <;> norm_num
    have hsum0 : ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x = 0 := by
      have h := hlam.symm.trans hl0
      exact (mul_eq_zero.mp h).resolve_left hδ0
    have he10 : hyp.tau3 (hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩) x = 0 := by
      rw [← hyp.eta_eq_tau_omega]
      exact he0
    have hrow := hyp.eta_row_vanish_of_one_zero x he10
    have hcol1ne : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) one_ne_zero
    have hfc : ∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
        hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x
          = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1 := by
      intro i hi
      have h4 := hyp.eta_fourcorner_vanish i ⟨1, hyp.p_prime.one_lt⟩ hi hcol1ne x hreg
      rw [hrow i hi] at h4
      rw [hyp.eta_eq_tau_omega, hyp.eta_eq_tau_omega]
      linear_combination h4
    -- split the sum at the `0`-row: `0 = q·η₀₁(x) − (q − 1)`
    have hsplit : (0 : ℂ)
        = (hyp.q : ℂ) * hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
          - ((hyp.q : ℂ) - 1) := by
      have hqpos : 0 < hyp.q := hyp.q_prime.pos
      have hcard : (Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q)).card = hyp.q - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      calc (0 : ℂ) = ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x := hsum0.symm
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ∑ i ∈ Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q),
                hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ∑ _i ∈ Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q),
                (hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1) := by
          congr 1
          exact Finset.sum_congr rfl (fun i hi =>
            hfc i (Finset.ne_of_mem_erase hi))
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ((hyp.q - 1 : ℕ) : ℂ)
              * (hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ = (hyp.q : ℂ) * hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            - ((hyp.q : ℂ) - 1) := by
          have h1 : ((hyp.q - 1 : ℕ) : ℂ) = (hyp.q : ℂ) - 1 := by
            rw [Nat.cast_sub hyp.q_prime.one_lt.le, Nat.cast_one]
          rw [h1]
          ring
    -- `η₀₁(x)` is an algebraic integer, so `q ∣ q − 1` — impossible
    have hZ : hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ ∈ ZIrr G := by
      rw [hyp.eta_eq_tau_omega]
      exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)
    have hint := OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr hZ x
    have hcast : (((hyp.q : ℤ) - 1 : ℤ) : ℂ)
        = ((hyp.q : ℤ) : ℂ)
          * hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x := by
      push_cast
      linear_combination hsplit
    have hdvd := OddOrder.RepresentationTheory.int_dvd_of_intCast_eq_mul_isIntegral
      (by exact_mod_cast hyp.q_prime.pos.ne' : (hyp.q : ℤ) ≠ 0) hint hcast
    have hone : (hyp.q : ℤ) ∣ 1 := by
      have h2 : (hyp.q : ℤ) ∣ (hyp.q : ℤ) - ((hyp.q : ℤ) - 1) := dvd_sub dvd_rfl hdvd
      simpa using h2
    have := Int.le_of_dvd one_pos hone
    have := hyp.q_prime.one_lt
    omega

/-- **AM–GM via `log`** (analytic core of [Is] Lemma 3.14): for positive reals whose product is
`≥ 1`, the sum is at least the count.  This powers Peterfalvi (13.9.b): for a cyclic-equivalence
class `[a] = {a^k : gcd(k, |⟨a⟩|) = 1}`, the values `χ(a^k)` are the Galois conjugates of `χ(a)`,
so `∏_k |χ(a^k)|² = |N(χ(a))|² ≥ 1` whenever `χ(a) ≠ 0` (the field norm of a nonzero algebraic
integer is a nonzero rational integer), whence `∑_k |χ(a^k)|² ≥ φ(|⟨a⟩|) = |[a]|`; summing over the
cyclic classes gives `∑_{x∈A}|χ(x)|² ≥ |A|` for any cyclic-closed `A` with `χ ≠ 0` on `A`.
Proof: `log x ≤ x − 1` summed gives `0 ≤ log (∏ f) ≤ ∑ (f − 1) = ∑ f − |s|`. -/
theorem sum_ge_card_of_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < f i) (hprod : 1 ≤ ∏ i ∈ s, f i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, f i := by
  have hlog : ∑ i ∈ s, Real.log (f i) ≤ ∑ i ∈ s, (f i - 1) :=
    Finset.sum_le_sum (fun i hi => Real.log_le_sub_one_of_pos (hpos i hi))
  have hprodlog : (0 : ℝ) ≤ ∑ i ∈ s, Real.log (f i) := by
    rw [← Real.log_prod (fun i hi => (hpos i hi).ne')]
    exact Real.log_nonneg hprod
  have hsum : (0 : ℝ) ≤ ∑ i ∈ s, (f i - 1) := le_trans hprodlog hlog
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  linarith

/-- **[Isaacs] Lemma 3.14 (sum form, virtual characters)**: a virtual character nowhere zero on
a cyclic-closed `Finset A` has `∑_{x∈A}‖φ(x)‖² ≥ |A|` — the `ℤ[Irr]` extension of
`sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed`, combining the Galois product bound
`one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed` with the AM–GM `sum_ge_card_of_one_le_prod`
(declared below; the two are independent). -/
theorem sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed {H : Type*} [Group H] [Finite H]
    {φ : ClassFunction H ℂ} (hφ : φ ∈ ZIrr H) {A : Finset H}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card H) → x ^ k ∈ A)
    (hne : ∀ x ∈ A, φ x ≠ 0) :
    (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
  sum_ge_card_of_one_le_prod A (fun x => ‖φ x‖ ^ 2)
    (fun x hx => pow_pos (norm_pos_iff.mpr (hne x hx)) 2)
    (OddOrder.Algebra.one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed hφ hclosed hne)

/-- **The nonvanishing locus of a virtual character inside a cyclic-closed set is cyclic-closed**
(Peterfalvi (1.9.b)): for `k` coprime to `|G|` there is `σ : ℂ ≃+* ℂ` with `σ(φ(x)) = φ(x^k)`
(`exists_complexRingEquiv_mapRingEquiv_eq_pow` with `a = |G|`, `b = 1`), and ring automorphisms
preserve nonvanishing. -/
theorem filter_ne_zero_cyclicClosed [Finite G] {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {A : Finset G} (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A) :
    ∀ x ∈ A.filter (fun y => φ y ≠ 0), ∀ k : ℕ, k.Coprime (Nat.card G) →
      x ^ k ∈ A.filter (fun y => φ y ≠ 0) := by
  classical
  intro x hx k hk
  obtain ⟨hxA, hxne⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hclosed x hxA k hk, ?_⟩
  obtain ⟨σ, hσ⟩ := OddOrder.RepresentationTheory.exists_complexRingEquiv_mapRingEquiv_eq_pow G
    (a := Nat.card G) (b := 1) (mul_one _).symm (Nat.coprime_one_right _) hk
  have hval : ClassFunction.mapRingEquiv σ φ x = φ (x ^ k) :=
    (hσ hφ x).1 (orderOf_dvd_natCard x)
  rw [ClassFunction.mapRingEquiv_apply] at hval
  rw [← hval]
  simpa using hxne

open scoped FiniteInduce in
/-- **Peterfalvi (13.9.b), atom form**: `|G₀|/|G| ≤ slam + seta`.

`G₀ = A ∪ B` with `A`/`B` the nonvanishing loci of `λ^{τ₁}`/`η₁₀`
(`G0_nonvanishing_dichotomy` = (13.9.a)); each locus is cyclic-closed
(`filter_ne_zero_cyclicClosed`, Pf (1.9.b)), so [Is] Lemma 3.14
(`sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed`) bounds its cardinality by the norm sum. -/
theorem analyticEstimate_galois [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (chars : CharacterDegreeData hyp) :
    (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ)
      ≤ normSqSumQ hyp.G0Finset (chars.tau1S chars.lambda) / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ) := by
  classical
  obtain ⟨hZlam, -, -⟩ := lambda_tau1_norm_one _hG chars
  have hZeta := hyp.eta10_mem_ZIrr
  set φ : ClassFunction G ℂ := chars.tau1S chars.lambda with hφdef
  set A : Finset G := hyp.G0Finset.filter (fun y => φ y ≠ 0) with hA
  set B : Finset G := hyp.G0Finset.filter (fun y => hyp.eta10 y ≠ 0) with hB
  -- The dichotomy: `G₀ ⊆ A ∪ B`.
  have hdich := G0_nonvanishing_dichotomy _hG chars
  have hcover : hyp.G0Finset ⊆ A ∪ B := by
    intro x hx
    rcases hdich x hx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, by rw [← hφdef] at h; exact h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hcard : hyp.G0Finset.card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  -- Per-locus Galois bounds.
  have hgeA : (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
    sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed hZlam
      (filter_ne_zero_cyclicClosed hZlam hyp.G0Finset_cyclicClosed)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  have hgeB : (B.card : ℝ) ≤ ∑ x ∈ B, ‖hyp.eta10 x‖ ^ 2 :=
    sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed hZeta
      (filter_ne_zero_cyclicClosed hZeta hyp.G0Finset_cyclicClosed)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  -- Locus sums are bounded by the `G₀` sums.
  have hsubA : ∑ x ∈ A, ‖φ x‖ ^ 2 ≤ ∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  have hsubB : ∑ x ∈ B, ‖hyp.eta10 x‖ ^ 2 ≤ ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  -- The rational atoms.
  have hspecLam := normSqSumQ_spec
    (OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZlam
      hyp.G0Finset_cyclicClosed)
  have hspecEta := normSqSumQ_spec
    (OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZeta
      hyp.G0Finset_cyclicClosed)
  -- Assemble over ℝ.
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspecLam, hspecEta, ← add_div]
  have hnum : (hyp.G0Finset.card : ℝ)
      ≤ (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2) + ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 := by
    have hcard' : (hyp.G0Finset.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
      exact_mod_cast hcard
    linarith [hgeA, hgeB, hsubA, hsubB]
  gcongr


/-- **Faithful (13.6)–(13.9) norm-estimate inputs to Peterfalvi (13.10)**.

The four estimates are the genuine character-theoretic / counting outputs of the norm cascade,
stated for the real atoms `slam = (1/|G|)·Σ_{G₀}‖λ^{τ₁}‖²`, `seta = (1/|G|)·Σ_{G₀}‖η₁₀‖²`,
`g0 = |G₀|/|G|`, `HS = |H#|/|S|` (with the (13.4) counting values `LS = uq/(cp^q)`,
`TT = 1/p − 1/(p(q−1)) + 1/(p(q−1)q^p)`, `QT = (q−1)/(pq^p)` substituted):

* `h1` — **(13.6)**: Parseval for `λ^{τ₁}` (`‖λ^{τ₁}‖² = 1`) with the norm bound
  `Σ_{H#}‖λ^{τ₁}‖² ≥ |S| − λ(1)²` (`caseB_lambda_norm_bound`);
* `h2` — **(13.7)+(13.8)** for `T` with `D = 1` (`caseB_eta_norm_bound`, `caseB_eta01_norm_core`);
* `h3` — **(13.9.a)**: the disjoint-union cover `G = {1} ⊔ G₀ ⊔ (H#)^G ⊔ (Q#)^G`;
* `h139b` — **(13.9.b)**: the Galois-integrality bound `|G₀|/|G| ≤ slam + seta`
  (`sum_ge_card_of_one_le_prod`).

Assembled `sorry`-free from the four named producers above (which carry the residual gates —
see their header).  The pure arithmetic that turns the four estimates into the `u/c` bound is
the `sorry`-free `analytic_inequality_arith`. -/
theorem analyticInequalityEstimates [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ slam seta g0 HS : ℚ,
      (1 : ℚ) ≥ 1 / (Nat.card G : ℚ) + slam + 1
          - (hyp.u : ℚ) * (hyp.q : ℚ) / ((hyp.c : ℚ) * (hyp.p : ℚ) ^ hyp.q) ∧
        (1 : ℚ) ≥ 1 / (Nat.card G : ℚ) + seta + HS
          + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
            + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) ∧
        (1 : ℚ) = 1 / (Nat.card G : ℚ) + g0 + HS
          + ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p) ∧
        g0 ≤ slam + seta := by
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  exact ⟨normSqSumQ hyp.G0Finset (chars.tau1S chars.lambda) / (Nat.card G : ℚ),
    normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ),
    (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ),
    ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ),
    analyticEstimate_lambda _hG hyp chars,
    analyticEstimate_eta _hG hyp,
    analyticCounting_disjointCover _hG hyp,
    analyticEstimate_galois _hG hyp chars⟩


/-- **Peterfalvi (13.9.b) core** ([Is] Lemma 3.14, sum form): for a character `φ` that is nowhere
zero on a cyclic-closed `Finset A` (closed under `x ↦ x ^ k`, `k` coprime `|G|`), the squared-norm
sum over `A` is at least `|A|`.  Combines the Galois-integrality product bound
`one_le_prod_normSq_character_of_cyclicClosed` (`∏_{x∈A} ‖φ(x)‖² ≥ 1`, since the product of the
Galois conjugates is a nonzero rational integer) with the AM–GM `sum_ge_card_of_one_le_prod`.
This is the per-cyclic-class building block for the (13.9.b) bound `|G₀|/|G| ≤ slam + seta` in the
(13.10) analytic inequality (applied on each class to whichever of `λ^{τ₁}`, `η₁₀` is nonzero). -/
theorem sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed {H : Type*} [Group H] [Finite H]
    {φ : ClassFunction H ℂ} (hφ : OddOrder.RepresentationTheory.IsCharacter φ) {A : Finset H}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card H) → x ^ k ∈ A)
    (hne : ∀ x ∈ A, φ x ≠ 0) :
    (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
  sum_ge_card_of_one_le_prod A (fun x => ‖φ x‖ ^ 2)
    (fun x hx => pow_pos (norm_pos_iff.mpr (hne x hx)) 2)
    (OddOrder.Algebra.one_le_prod_normSq_character_of_cyclicClosed hφ hclosed hne)

/-- **Peterfalvi (13.10), arithmetic core** (04.15 pp.85–86): the (13.6)–(13.9) norm estimates
together with the disjoint-union counting `G = {1} ⊔ G₀ ⊔ (H#)^G ⊔ (Q#)^G` and the (13.4) counting
identities force `u / c > m p^(q-1) / q`.

This is the faithful Lean encoding of Peterfalvi (13.10)'s derivation, with the **grid-dependent
character content fully isolated** into the concrete norm-sum hypotheses (the (13.6)/(13.7)/(13.8)
outputs and the (13.9.b) cover, to be supplied by the cascade producers once the grid τ-isometry /
orthogonality is carried) and the **group-counting identities** `hLS`/`hTT`/`hQT`.  No grid carrier
is needed here: this is a `sorry`-free reusable arithmetic lemma.  The abstract real atoms are
`gi = 1/|G|`, `slam = (1/|G|)·Σ_{G₀}|λ^{τ₁}(x)|²`, `seta = (1/|G|)·Σ_{G₀}|η₁₀(x)|²`,
`g0 = |G₀|/|G|`, `LS = λ(1)²/|S|`, `HS = |H#|/|S|`, `TT = (|T'|−v²)/|T|`, `QT = |Q#|/|T|`.

* `h1` — (13.10.1): `1 ≥ 1/|G| + (1/|G|)Σ_{G₀}|λ^{τ₁}|² + 1 − λ(1)²/|S|` (Parseval + (13.6));
* `h2` — (13.10.2): `1 ≥ 1/|G| + (1/|G|)Σ_{G₀}|η₁₀|² + |H#|/|S| + (|T'|−v²)/|T|`
  (Parseval + (13.7) + (13.8) for `T`, `D = 1`);
* `h3` — (13.10.3): the disjoint-union counting `1 = 1/|G| + |G₀|/|G| + |H#|/|S| + |Q#|/|T|`;
* `h139b` — (13.9.b): `|G₀|/|G| ≤ (1/|G|)(Σ_{G₀}|λ^{τ₁}|² + Σ_{G₀}|η₁₀|²)`.

**Stage A** (`linarith`): combining `h1 + h2 − h3` with `h139b` and `gi > 0` gives `LS > TT − QT`.
**Stage B**: the counting identities collapse `TT − QT` to `m/p`, and factoring out `q/p^q > 0`
turns `uq/(cp^q) > m/p` into `u/c > m p^(q-1)/q`. -/
theorem analytic_inequality_arith {p q u c : ℕ} {m gi slam seta g0 LS HS TT QT : ℚ}
    (hp2 : 2 ≤ p) (hq2 : 2 ≤ q) (hc0 : 0 < c)
    (h1 : 1 ≥ gi + slam + 1 - LS)
    (h2 : 1 ≥ gi + seta + HS + TT)
    (h3 : 1 = gi + g0 + HS + QT)
    (h139b : g0 ≤ slam + seta)
    (hgi : 0 < gi)
    (hLS : LS = ((u : ℚ) * (q : ℚ)) / ((c : ℚ) * (p : ℚ) ^ q))
    (hTT : TT = 1 / (p : ℚ) - 1 / ((p : ℚ) * ((q : ℚ) - 1))
      + 1 / ((p : ℚ) * ((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hQT : QT = ((q : ℚ) - 1) / ((p : ℚ) * (q : ℚ) ^ p))
    (hm : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)) :
    (u : ℚ) / (c : ℚ) > m * ((p : ℚ) ^ (q - 1)) / (q : ℚ) := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show 0 < q by omega)
  have hcQ : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc0
  have hq1 : (0 : ℚ) < (q : ℚ) - 1 := by
    have h2q : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq2
    linarith
  have hqpowp : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hppow1 : (0 : ℚ) < (p : ℚ) ^ (q - 1) := by positivity
  have hppowq : (0 : ℚ) < (p : ℚ) ^ q := by positivity
  -- Stage A: the (13.10.1)+(13.10.2)−(13.10.3)+(13.9.b) combination gives `LS > TT − QT`.
  have hStageA : LS > TT - QT := by linarith
  -- Stage B: the counting identities collapse `TT − QT` to `m / p`.
  have hTTQT : TT - QT = m / (p : ℚ) := by
    rw [hTT, hQT, hm]
    field_simp
    ring
  rw [hTTQT, hLS] at hStageA
  -- `hStageA : u q / (c p^q) > m / p`.  Factor out the positive `q / p^q`.
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hfac : (0 : ℚ) < (q : ℚ) / (p : ℚ) ^ q := by positivity
  have e1 : ((u : ℚ) * (q : ℚ)) / ((c : ℚ) * (p : ℚ) ^ q)
      = ((u : ℚ) / (c : ℚ)) * ((q : ℚ) / (p : ℚ) ^ q) := by
    field_simp
  have e2 : m / (p : ℚ)
      = (m * ((p : ℚ) ^ (q - 1)) / (q : ℚ)) * ((q : ℚ) / (p : ℚ) ^ q) := by
    rw [hpexp]
    field_simp
  rw [e1, e2] at hStageA
  exact lt_of_mul_lt_mul_right hStageA (le_of_lt hfac)

/-- **Peterfalvi (13.10)**: the norm estimates imply `u / c > m p^(q-1) / q`.

The real inequality conclusion is discharged `sorry`-free from `analytic_inequality_arith` fed by
the faithful (13.6)–(13.9) estimates `analyticInequalityEstimates`; the opaque `NormCascadeData`
scaffold flags carry `True`. -/
theorem analytic_inequality [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp,
      data.analytic_inequality ∧
        (hyp.u : ℚ) / (hyp.c : ℚ) >
          hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ) := by
  obtain ⟨chars⟩ := character_degree_analysis _hG hyp
  obtain ⟨slam, seta, g0, HS, h1, h2, h3, h139b⟩ := analyticInequalityEstimates _hG hyp
  have hc0 : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hgi : (0 : ℚ) < 1 / (Nat.card G : ℚ) := by
    have : 0 < Nat.card G := Nat.card_pos
    positivity
  have hpq : ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) = (hyp.p : ℚ) ^ (hyp.q - 1) := by push_cast; ring
  refine ⟨{ chars := chars
            lambda_norm_lower := True
            eta10_norm_lower := True
            eta01_norm_lower := True
            global_cover := True
            global_norm_lower := True
            analytic_inequality := True }, trivial, ?_⟩
  rw [hpq]
  exact analytic_inequality_arith hyp.p_prime.two_le hyp.q_prime.two_le hc0
    h1 h2 h3 h139b hgi rfl rfl rfl hyp.m_eq

/-! ## (13.11)--(13.15): order and divisor determination -/

/-- Lower estimate for the analytic parameter `m` of **Peterfalvi (13.10)**.
Dropping the (positive) last summand and bounding `(q-1)/q^p ≤ 1/q^2` (valid once
`p ≥ 3`) gives `m ≥ 1 - 1/(q-1) - 1/q^2`. -/
theorem m_value_ge_aux {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (1 : ℚ) - 1 / ((q : ℚ) - 1) - 1 / (q : ℚ) ^ 2 ≤
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hXpos : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hX3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hfrac : ((q : ℚ) - 1) / (q : ℚ) ^ p ≤ 1 / (q : ℚ) ^ 2 := by
    rw [div_le_div_iff₀ hXpos (by positivity)]
    have e : (q : ℚ) ^ 3 = ((q : ℚ) - 1) * (q : ℚ) ^ 2 + (q : ℚ) ^ 2 := by ring
    have hsq : (0 : ℚ) ≤ (q : ℚ) ^ 2 := sq_nonneg _
    linarith [hX3, e, hsq]
  have hpos : (0 : ℚ) ≤ 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by positivity
  linarith [hfrac, hpos]

/-- **Peterfalvi (13.11.b)** numeric bound: `q ≥ 5 ⇒ m > 7/10`. -/
theorem m_value_gt_seven_tenths {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (7 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have haux := m_value_ge_aux hq hp
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq5]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11.a)** numeric bound: `q ≥ 7 ⇒ m > 8/10`. -/
theorem m_value_gt_four_fifths {q p : ℕ} (hq : 7 ≤ q) (hp : 3 ≤ p) :
    (8 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : 5 ≤ q := by omega
  have haux := m_value_ge_aux hq5 hp
  have hq7 : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 49 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq7]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11)** numeric core of the `q = 3` branch: once the
Section 16 hypothesis gives `p ≥ 5`, the concrete value of `m` is already
strictly larger than `49/100`. -/
theorem m_value_q_three_gt_49_hundredths {p : ℕ} (hp : 5 ≤ p) :
    (49 : ℚ) / 100 <
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
        1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p) := by
  have h4 : 4 ≤ p - 1 := by omega
  have hpow4 : (3 : ℚ) ^ 4 ≤ (3 : ℚ) ^ (p - 1) :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 3) h4
  norm_num at hpow4
  have hden_gt : (100 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hden_pos : (0 : ℚ) < 2 * (3 : ℚ) ^ (p - 1) := by nlinarith
  have hsmall : 1 / (2 * (3 : ℚ) ^ (p - 1)) < (1 : ℚ) / 100 := by
    rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℚ) < 100)]
    nlinarith
  have hpow : (3 : ℚ) ^ p = 3 * (3 : ℚ) ^ (p - 1) := by
    have hp_eq : p = (p - 1) + 1 := by omega
    rw [hp_eq, pow_succ]
    rw [show p - 1 + 1 - 1 = p - 1 by omega]
    ring
  have hexpr :
      1 - 1 / ((3 : ℚ) - 1) - ((3 : ℚ) - 1) / (3 : ℚ) ^ p +
          1 / (((3 : ℚ) - 1) * (3 : ℚ) ^ p)
        = (1 : ℚ) / 2 - 1 / (2 * (3 : ℚ) ^ (p - 1)) := by
    rw [hpow]
    field_simp [hden_pos.ne']
    ring
  rw [hexpr]
  linarith [hsmall]

/-- **Numerical core shared by Peterfalvi (13.12) and (13.15)**: the upper estimate
`m < q·p / ((2q+1)(p-1))` — obtained from `c ≥ 2q+1` (13.12) resp. the divisor `x ≥ 2q+1`
(13.15) together with the analytic inequality (13.10) and `u ≤ (p^q-1)/(p-1)` (13.2.c) — combined
with the (13.11) lower bounds on `m` forces `q = 3`.

Self-contained `ℚ`-arithmetic over an abstract `m` satisfying the (13.11.a,b) lower bounds; `p`, `q`
are odd primes so `p = 3 ∨ p ≥ 5` and `q = 3 ∨ q ≥ 5`, as supplied by the callers.

* `p ≥ 5`: `m < q·p/((2q+1)(p-1)) < (1/2)(5/4) = 5/8 < 7/10`, against `m > 7/10` (13.11.b).
* `p = 3`, `q ≥ 7`: `m < 3q/(2(2q+1)) < 3/4 < 8/10`, against `m > 8/10` (13.11.a).
* `p = 3`, `5 ≤ q < 7`: `m < 3q/(2(2q+1)) < 7/10`, against `m > 7/10` (13.11.b). -/
theorem caseB_numeric_forces_q_three {p q : ℕ} {m : ℚ}
    (hp : p = 3 ∨ 5 ≤ p) (hq : q = 3 ∨ 5 ≤ q)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hbound : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1))) :
    q = 3 := by
  rcases hq with hq3 | hq5
  · exact hq3
  exfalso
  have hqR : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq5
  have hm7over : (7 : ℚ) / 10 < m := hm5 hq5
  rcases hp with rfl | hp5
  · -- `p = 3`
    have hden : (0 : ℚ) < (2 * (q : ℚ) + 1) * (((3 : ℕ) : ℚ) - 1) := by
      rw [show (((3 : ℕ) : ℚ)) = 3 by norm_num]; nlinarith [hqR]
    have hb := (lt_div_iff₀ hden).mp hbound
    rw [show (((3 : ℕ) : ℚ)) = 3 by norm_num] at hb
    by_cases hq7 : 7 ≤ q
    · have h87 : (8 : ℚ) / 10 < m := hm7 hq7
      nlinarith [hb, h87, hqR]
    · have hqlt7 : (q : ℚ) < 7 := by exact_mod_cast (show q < 7 by omega)
      nlinarith [hb, hm7over, hqR, hqlt7]
  · -- `p ≥ 5`
    have hpR5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp5
    have hden : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by nlinarith [hqR, hpR5]
    have hb := (lt_div_iff₀ hden).mp hbound
    nlinarith [hb, hm7over, hqR, hpR5]

namespace Hypothesis

/-- **Peterfalvi (13.11.a)** at the Section 15 hypothesis level: if `q ≥ 7`,
then the concrete analytic parameter satisfies `m > 8/10`. -/
theorem m_gt_four_fifths_of_seven_le_q (hyp : Hypothesis (G := G))
    (hq7 : 7 ≤ hyp.q) :
    hyp.m > (8 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_four_fifths hq7 hyp.three_le_p

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

/-- **Peterfalvi (13.11)** at the Section 15 hypothesis level: in the `q = 3`
branch, the `m > 49/100` part follows once an external argument supplies
`p ≥ 5`.  Section 16 supplies this from `q < p`. -/
theorem m_gt_49_hundredths_of_q_eq_three_of_five_le_p
    (hyp : Hypothesis (G := G)) (hq3 : hyp.q = 3) (hp5 : 5 ≤ hyp.p) :
    hyp.m > (49 / 100 : ℚ) := by
  rw [hyp.m_eq, hq3]
  exact m_value_q_three_gt_49_hundredths hp5

/-- The `m`-only part of **Peterfalvi (13.11)**.  The full `numeric_bounds`
theorem below also packages the `u/c` inequality in the `q = 3` branch, so it
still waits for the analytic estimate (13.10). -/
theorem numeric_m_bounds (hyp : Hypothesis (G := G)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 → 5 ≤ hyp.p → hyp.m > (49 / 100 : ℚ)) := by
  exact ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q,
    fun hq3 hp5 => hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq3 hp5⟩

end Hypothesis

/-- **Arithmetic bridge for Peterfalvi (13.2.c), non-Galois case**: `(p-1)^(q-1) ≤ (p^q-1)/(p-1)`.

In the non-Galois type-`P` case the Singer/semilinear bound gives `u ≤ (p-1)^(q-1)` (Coq
`FTtypeP_facts`, via `card_mx`), which this relaxes to the uniform (13.2.c) form
`u ≤ (p^q-1)/(p-1)`.  Elementary: `(p-1)^(q-1) ≤ p^(q-1) ≤ (p^q-1)/(p-1)` (the last since
`p^(q-1)·(p-1) = p^q - p^(q-1) ≤ p^q - 1`).  Pure `ℕ` arithmetic, `sorry`-free. -/
theorem pred_pow_le_cyclotomic_quotient {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  refine le_trans (Nat.pow_le_pow_left (Nat.sub_le p 1) (q - 1)) ?_
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have ha : 1 ≤ (d + 1) ^ (q - 1) := Nat.one_le_pow _ _ (by omega)
  have hap' : (d + 1) ^ (q - 1) * d + (d + 1) ^ (q - 1) = (d + 1) ^ q := by
    have h1 : (d + 1) ^ (q - 1) * d + (d + 1) ^ (q - 1) = (d + 1) ^ (q - 1) * (d + 1) := by ring
    rw [h1, ← pow_succ]; congr 1; omega
  omega

/-- **Peterfalvi (8.4.d) restricted to `C`**: `W₁` acts fixed-point-freely on `C ⊆ U` by
conjugation — no `w ∈ W₁ #` centralizes any `c ∈ C #`.  `U W₁` is a Frobenius group with kernel `U`
(`typeP_uW1_frobenius`), and `C = U ⊓ C_G(P) ≤ U`, so the Frobenius fpf condition restricts to `C`.
The fpf input to the (13.12) `c ≡ 1 (mod q)` step (Coq `dv_2q_c1`). -/
theorem Hypothesis.W1_fpf_C [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ w ∈ hyp.W1, w ≠ 1 → ∀ c ∈ hyp.C, c ≠ 1 → w * c * w⁻¹ ≠ c := by
  have hSII : IsTypeII hyp.S :=
    OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2
  have tdata : TypeIIData hyp.S := hSII.some
  have hUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have frob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hUne
  rw [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at frob
  have hCU : hyp.C ≤ hyp.U := by rw [hyp.C_eq]; exact inf_le_left
  intro w hw hw1 c hc hc1
  have hwL : w ∈ hyp.U ⊔ hyp.W1 := (le_sup_right : hyp.W1 ≤ _) hw
  have hcL : c ∈ hyp.U ⊔ hyp.W1 := (le_sup_left : hyp.U ≤ _) (hCU hc)
  have hne1 : (⟨w, hwL⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hw1 (by simpa using congrArg Subtype.val h)
  have hnec : (⟨c, hcL⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hc1 (by simpa using congrArg Subtype.val h)
  have hmemw : (⟨w, hwL⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) :=
    Subgroup.mem_subgroupOf.mpr hw
  have hmemc : (⟨c, hcL⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) :=
    Subgroup.mem_subgroupOf.mpr (hCU hc)
  have hconj := frob.conj_frobenius _ hmemw hne1 _ hmemc hnec
  intro heq
  apply hconj
  apply Subtype.ext
  push_cast
  exact heq

/-- `W₁` normalizes `C = U ⊓ C_G(P)`: `W₁ ≤ S ≤ N_G(P)` (so it normalizes `C_G(P)`) and
`W₁ ≤ N_G(U)` (`W1_normalizes_U`), hence it normalizes their intersection.  The `N_G(C)`-input to
the conjugation action of the (13.12) `c ≡ 1 (mod q)` step. -/
theorem Hypothesis.W1_le_normalizer_C (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ Subgroup.normalizer (hyp.C : Set G) := by
  have hW1S : hyp.W1 ≤ hyp.S := by
    have h1 : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have h2 : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
    exact h1.trans h2
  have hSP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  intro w hw
  have hwP := hSP (hW1S hw)
  have hwU := hyp.W1_normalizes_U hw
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  rw [hyp.C_eq]
  simp only [Subgroup.mem_inf, SetLike.mem_coe]
  -- `w` normalizes `U` and `C_G(P)`; combine.
  have hU_iff : x ∈ hyp.U ↔ w * x * w⁻¹ ∈ hyp.U :=
    Subgroup.mem_set_normalizer_iff.mp hwU x
  have hCP_iff : x ∈ Subgroup.centralizer (hyp.P : Set G) ↔
      w * x * w⁻¹ ∈ Subgroup.centralizer (hyp.P : Set G) := by
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : w⁻¹ * p * w ∈ (hyp.P : Set G) := (Subgroup.mem_set_normalizer_iff''.mp hwP p).mp hp
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) _ hp'
      calc p * (w * x * w⁻¹) = w * ((w⁻¹ * p * w) * x) * w⁻¹ := by group
        _ = w * (x * (w⁻¹ * p * w)) * w⁻¹ := by rw [hcomm]
        _ = (w * x * w⁻¹) * p := by group
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : w * p * w⁻¹ ∈ (hyp.P : Set G) := (Subgroup.mem_set_normalizer_iff.mp hwP p).mp hp
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) _ hp'
      calc p * x = w⁻¹ * ((w * p * w⁻¹) * (w * x * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * x * w⁻¹) * (w * p * w⁻¹)) * w := by rw [hcomm]
        _ = x * p := by group
  rw [hU_iff, hCP_iff]

/-- **Peterfalvi (13.12), structural step**: `c ≡ 1 (mod q)`.

The cyclic factor `W₁` (order `q`) acts fixed-point-freely on `C ⊆ U` by conjugation
(`W1_fpf_C`, `W1_le_normalizer_C`).  Since `W₁` is a `q`-group, the class equation
(`IsPGroup.card_modEq_card_fixedPoints`) gives `|C| ≡ |C_C(W₁)| (mod q)`, and the fpf condition
makes `C_C(W₁) = {1}`.  This is the Coq `dv_2q_c1` ingredient (`q ∣ c − 1`) of
`FTtypeP_Ind_Fitting_reg_Fcore`. -/
theorem Hypothesis.c_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.c ≡ 1 [MOD hyp.q] := by
  classical
  haveI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hfpf := hyp.W1_fpf_C hG
  letI : MulAction ↥hyp.W1 ↥hyp.C :=
    MulAction.compHom ↥hyp.C (Subgroup.inclusion hyp.W1_le_normalizer_C)
  have hsmul : ∀ (w : ↥hyp.W1) (x : ↥hyp.C), ((w • x : ↥hyp.C) : G) = (w : G) * (x : G) * (w : G)⁻¹ :=
    fun _ _ => rfl
  have hW1pg : IsPGroup hyp.q ↥hyp.W1 := IsPGroup.of_card (by rw [← hyp.q_eq_card_W1, pow_one])
  have hmod : Nat.card ↥hyp.C ≡ Nat.card ↥(MulAction.fixedPoints ↥hyp.W1 ↥hyp.C) [MOD hyp.q] :=
    hW1pg.card_modEq_card_fixedPoints ↥hyp.C
  -- `W₁ ≠ ⊥`, pick `w₀ ∈ W₁ #`.
  have hW1ne : hyp.W1 ≠ ⊥ := by
    intro h; have h3 := hyp.three_le_q
    rw [hyp.q_eq_card_W1, h, Subgroup.card_bot] at h3; omega
  haveI : Nontrivial ↥hyp.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
  obtain ⟨⟨w₀, hw₀W1⟩, hw₀ne⟩ := exists_ne (1 : ↥hyp.W1)
  have hw₀ne' : w₀ ≠ 1 := by rintro rfl; exact hw₀ne rfl
  -- `C_C(W₁) = {1}`.
  have hfixset : MulAction.fixedPoints ↥hyp.W1 ↥hyp.C = {1} := by
    ext a
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hafix
      by_contra hane
      have hav : (a : G) ≠ 1 := fun h => hane (Subtype.ext h)
      have hc := congrArg (Subtype.val) (hafix ⟨w₀, hw₀W1⟩)
      rw [hsmul] at hc
      exact hfpf w₀ hw₀W1 hw₀ne' (a : G) a.2 hav hc
    · rintro rfl w
      apply Subtype.ext
      rw [hsmul]; simp
  have hfix : Nat.card ↥(MulAction.fixedPoints ↥hyp.W1 ↥hyp.C) = 1 := by
    rw [hfixset]; simp
  rw [hfix, ← hyp.c_eq_card_C] at hmod
  exact hmod

/-- **Peterfalvi (13.12), `dv_2q_c1`**: `2q ∣ c − 1`.  `c ≡ 1 (mod q)` (`c_modEq_one`) and `c` is
odd (`|C| ∣ |G|`, `|G|` odd), so both `q` and `2` divide `c − 1`; coprimality (`q` odd) gives
`2q ∣ c − 1`.  In the `c > 1` branch this forces `c ≥ 2q + 1`, the lower bound Peterfalvi's numeric
elimination contradicts. -/
theorem Hypothesis.two_mul_q_dvd_c_pred [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : 2 * hyp.q ∣ hyp.c - 1 := by
  have hc1 : 1 ≤ hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hq : hyp.q ∣ hyp.c - 1 := (Nat.modEq_iff_dvd' hc1).mp (hyp.c_modEq_one hG).symm
  have hcodd : ¬ 2 ∣ hyp.c := by
    have hcG : hyp.c ∣ Nat.card G := by
      rw [hyp.c_eq_card_C]; exact Subgroup.card_subgroup_dvd_card _
    have hodd : Nat.card G % 2 = 1 := Nat.odd_iff.mp hG.odd
    intro h2c
    have h2G : (2 : ℕ) ∣ Nat.card G := h2c.trans hcG
    omega
  have h2 : 2 ∣ hyp.c - 1 := by omega
  have hcop : Nat.Coprime 2 hyp.q :=
    (Nat.coprime_primes Nat.prime_two hyp.q_prime).mpr (Ne.symm hyp.q_ne_two)
  exact hcop.mul_dvd_of_dvd_of_dvd h2 hq

/-- **Peterfalvi (13.11)**: the elementary numerical bounds for `m`.

The `q ≥ 7` and `q ≥ 5` bounds are the genuine arithmetic estimates
`m_value_gt_four_fifths` / `m_value_gt_seven_tenths` applied through the now
concrete value `m_eq` (they need only `p ≥ 3`, supplied by `three_le_p`).  The
`q = 3` value bound is available as `m_value_q_three_gt_49_hundredths` under
`p ≥ 5`, which Section 16 supplies from `q < p`; this bundled Section 15
statement still keeps the branch open because its `u/c` bound is the analytic
inequality (13.10). -/
theorem numeric_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 →
        hyp.m > (49 / 100 : ℚ) ∧
          (hyp.u : ℚ) / (hyp.c : ℚ) > (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6)) := by
  refine ⟨hyp.m_gt_four_fifths_of_seven_le_q,
    hyp.m_gt_seven_tenths_of_five_le_q, fun hq3 => ?_⟩
  · -- `q = 3`: the `m`-only API needs `p ≥ 5`, and the bundled `u/c` bound
    -- still needs the analytic inequality (13.10).
    sorry

/-- **Peterfalvi (13.12), numeric elimination** (04.15 p.85): the (13.10)+(13.2.c) upper bound
`m < q(p^q − 1)/(c · p^(q−1) · (p − 1))`, together with the fixed-point-free lower bound `c ≥ 2q+1`
(with `2q ∣ c − 1`) and the (13.11) lower bounds on `m`, forces `p = 5`, `q = 3`, `c = 7`.

This is the `sorry`-free `ℕ/ℚ`-arithmetic heart of (13.12): `q = 3` via
`caseB_numeric_forces_q_three`; the `q = 3` bound `m < 3(p³−1)/(c p²(p−1))` then eliminates `c ≥ 13`
(`< 49/100`, against (13.11.c)) forcing `c = 7`, eliminates `p ≥ 11` (`< 399/847 < 49/100`) forcing
`p < 11`, and eliminates `p = 7` (the exact value `m = ½ − 1/(2·3^{p−1}) = ½ − 1/1458` exceeds the
bound `171/343`) forcing `p = 5`.  Only the final `p = 5, q = 3, c = 7` structural contradiction
(`PC` normal nilpotent Hall ⊋ `P = S_F`) remains, isolated in `c_eq_one_final_case`. -/
theorem c_eq_one_forces_params {p q c : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hc2q1 : 2 * q + 1 ≤ c) (h2q : 2 * q ∣ c - 1)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hm49 : q = 3 → 5 ≤ p → (49 : ℚ) / 100 < m)
    (hmval : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hbound : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))) :
    p = 5 ∧ q = 3 ∧ c = 7 := by
  -- Basic positivity.
  have hpR : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hq3le : 3 ≤ q := by
    rcases hq.two_le.lt_or_eq with h | h
    · omega
    · exact absurd h.symm hq2
  have hqR : (3 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq3le
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hcpos : 0 < c := by omega
  have hcR : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hcpos
  have hc2q1R : (2 * (q : ℚ) + 1) ≤ (c : ℚ) := by
    have : ((2 * q + 1 : ℕ) : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc2q1
    push_cast at this; linarith
  -- Odd prime `≥ 3` is `3` or `≥ 5`.
  have prime_split : ∀ n : ℕ, n.Prime → 3 ≤ n → n = 3 ∨ 5 ≤ n := by
    intro n hn hn3
    by_contra hcon
    rw [not_or, not_le] at hcon
    obtain ⟨hne, hlt⟩ := hcon
    interval_cases n
    · exact hne rfl
    · exact (by norm_num : ¬ Nat.Prime 4) hn
  have hp35 : p = 3 ∨ 5 ≤ p := prime_split p hp hp3
  have hq35 : q = 3 ∨ 5 ≤ q := prime_split q hq hq3le
  -- `p^q = p^(q-1) · p`.
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  -- Step 1: derive `m < q p / ((2q+1)(p-1))`, hence `q = 3`.
  have hbound2q1 : m < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
    have hden1 : (0 : ℚ) < (c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1) := by positivity
    have hden2 : (0 : ℚ) < (2 * (q : ℚ) + 1) * ((p : ℚ) - 1) := by positivity
    have hstep : (q : ℚ) * ((p : ℚ) ^ q - 1) / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))
        < (q : ℚ) * (p : ℚ) / ((2 * (q : ℚ) + 1) * ((p : ℚ) - 1)) := by
      rw [div_lt_div_iff₀ hden1 hden2, hpexp]
      have hkey : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
          < (c : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by
        have hpp : (0 : ℚ) < (p : ℚ) ^ (q - 1) * (p : ℚ) := by positivity
        have e1 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ) - 1)
            < (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) := by nlinarith [hqR, hpp]
        have e2 : (2 * (q : ℚ) + 1) * ((p : ℚ) ^ (q - 1) * (p : ℚ))
            ≤ (c : ℚ) * ((p : ℚ) ^ (q - 1) * (p : ℚ)) :=
          mul_le_mul_of_nonneg_right hc2q1R (le_of_lt hpp)
        linarith [e1, e2]
      have hqp1 : (0 : ℚ) < (q : ℚ) * ((p : ℚ) - 1) := by positivity
      nlinarith [mul_lt_mul_of_pos_left hkey hqp1]
    linarith [hbound, hstep]
  have hq3 : q = 3 := caseB_numeric_forces_q_three hp35 hq35 hm5 hm7 hbound2q1
  -- With `q = 3`, `p ≥ 5`.
  have hp5 : 5 ≤ p := by
    rcases hp35 with h | h
    · exact absurd (h.trans hq3.symm) hpq
    · exact h
  have hpR5 : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp5
  subst hq3
  -- Specialize the bound to `q = 3`.
  have hbound3 : m < (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1)) := by
    have he : (p : ℚ) ^ (3 - 1) = (p : ℚ) ^ 2 := by norm_num
    have hc3 : ((3 : ℕ) : ℚ) = (3 : ℚ) := by norm_num
    rw [he, hc3] at hbound
    exact hbound
  have hm49p : (49 : ℚ) / 100 < m := hm49 rfl hp5
  -- `c ≡ 1 mod 6`, `c ≥ 7`, so `c = 7 ∨ c ≥ 13`.
  have h6 : 6 ∣ c - 1 := by simpa using h2q
  have hc7or13 : c = 7 ∨ 13 ≤ c := by omega
  -- Kill `c ≥ 13`.
  have hc7 : c = 7 := by
    rcases hc7or13 with h | h
    · exact h
    exfalso
    have hcR13 : (13 : ℚ) ≤ (c : ℚ) := by exact_mod_cast h
    have hden : (0 : ℚ) < (c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1) := by positivity
    have hb13 : (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((c : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1))
        < (49 : ℚ) / 100 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      nlinarith [hcR13, hpR5, mul_pos hp0 hp1, mul_pos (mul_pos hp0 hp0) hp1, hp0, hp1,
        sq_nonneg ((p : ℚ) - 5)]
    linarith [hbound3, hb13, hm49p]
  subst hc7
  -- Kill `p ≥ 11`.
  have hp_lt_11 : p < 11 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hpR11 : (11 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hcon
    have hden : (0 : ℚ) < (7 : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1) := by positivity
    have hb11 : (3 : ℚ) * ((p : ℚ) ^ 3 - 1) / ((7 : ℚ) * (p : ℚ) ^ 2 * ((p : ℚ) - 1))
        < (49 : ℚ) / 100 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      nlinarith [hpR11, mul_pos hp0 hp1, mul_pos (mul_pos hp0 hp0) hp1, hp0, hp1]
    linarith [hbound3, hb11, hm49p]
  -- Kill `p = 7` via the exact value of `m`.
  have hp_ne_7 : p ≠ 7 := by
    intro h7
    subst h7
    rw [hmval] at hbound3
    norm_num at hbound3
  -- `5 ≤ p < 11`, prime, `≠ 7` ⇒ `p = 5`.
  refine ⟨?_, rfl, rfl⟩
  interval_cases p
  · rfl
  · exact absurd hp (by norm_num)
  · exact absurd rfl hp_ne_7
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)

/-- **Peterfalvi (13.12), the isolated `PC`-Hall obligation**: for the numerically-forced
`p = 5, q = 3, c = 7`, the subgroup `PC = P ⊔ C` is contained in `M_F = maxNilpotentNormalHall S`.

Peterfalvi's argument: `PC` is **abelian** (hence nilpotent) — `P` is elementary abelian, `C ≤ U` is
abelian, and `C` centralizes `P` (`C_eq`); it is **normal** in `S` (type-`P` `W₁`-structure); and it
is a **Hall** subgroup once `gcd(c, u) = 1`, which holds because case (9.7.b) for `S` (as `p − 1 = 4`
has no odd divisor `≠ 1`) forces `u ∣ (p^q − 1)/(p − 1) = 31` (Singer / `typeP_Galois`), coprime to
`c = 7`.  By `le_maxNilpotentNormalHall` these three facts give `PC ≤ M_F`.  The `typeP_Galois`
dichotomy and the `W₁`-normality are the genuinely deep §13 σ-structure content (Coq
`FTtypeP_Ind_Fitting_reg_Fcore`: `typeP_Galois` + Fitting-core maximality `Fcore_max`), §14-gated /
multi-session — the sole remaining gap of (13.12). -/
theorem pc_le_maxNilpotentNormalHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hp5 : hyp.p = 5) (hq3 : hyp.q = 3) (hc7 : hyp.c = 7) :
    hyp.P ⊔ hyp.C ≤ maxNilpotentNormalHall hyp.S :=
  sorry

/-- **Peterfalvi (13.12), structural residual**: the numerically-forced case `p = 5, q = 3, c = 7`
is impossible.  By `pc_le_maxNilpotentNormalHall`, `PC = P ⊔ C ≤ M_F = P` (`P_eq_SF`), so `C ≤ P`;
but `|C| = c = 7` cannot divide `|P| = p^q = 125`.  The genuine gap is isolated in
`pc_le_maxNilpotentNormalHall` (the `PC`-nilpotent-normal-Hall obligation, `typeP_Galois`-gated); the
`C ≤ P ⟹ 7 ∣ 125` maximality contradiction is discharged here. -/
theorem c_eq_one_final_case [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hp5 : hyp.p = 5) (hq3 : hyp.q = 3) (hc7 : hyp.c = 7) : False := by
  -- `C ≤ P ⊔ C ≤ M_F = P`.
  have hCleP : hyp.C ≤ hyp.P := by
    have h := pc_le_maxNilpotentNormalHall hG hyp hp5 hq3 hc7
    rw [← hyp.P_eq_SF] at h
    exact le_trans le_sup_right h
  -- `|C| = 7`, `|P| = p^q = 125`.
  have hCcard : Nat.card ↥hyp.C = 7 := by rw [← hyp.c_eq_card_C, hc7]
  have hPcard : Nat.card ↥hyp.P = 5 ^ 3 := by
    obtain ⟨_, _, _, hcard, _, _⟩ := basic_structure hG hyp
    rw [hcard, hp5, hq3]
  -- `C ≤ P ⟹ |C| ∣ |P|`, i.e. `7 ∣ 125`, false.
  have hdvd : Nat.card ↥hyp.C ∣ Nat.card ↥hyp.P := by
    have hd := Subgroup.card_subgroup_dvd_card (hyp.C.subgroupOf hyp.P)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleP).toEquiv] at hd
  rw [hCcard, hPcard] at hdvd
  norm_num at hdvd

/-- **The analytic core of Peterfalvi (13.12)** (side-agnostic, pure `ℚ`-arithmetic).

From the `(13.10)` analytic inequality `u/c > m·a^(b−1)/b` and the `(13.2.c)` Singer *upper*
bound `u·(a−1) ≤ a^b − 1`, derive the upper bound `m < b·(a^b−1) / (c·a^(b−1)·(a−1))` that
(with the fixed-point-free lower bound `c ≥ 2b+1`) feeds the finite numeric elimination.

Both the `S`-side `c = 1` finish (`c_eq_one`, `a = p, b = q, u = u, c = c`) and the `T`-side
`d = 1` dual (`a = q, b = p, u = v, c = d`) instantiate this same core; extracted per issue
9013 (案A: generalize the §13 estimate so both sides `cite` it).  Uses only the Singer *upper*
bound, so it is ungated (the `T`-side lower-bound gate of the (13.15) `v`-value is a different
consumer — the ratio inequality — and does not enter here). -/
theorem analytic_singer_m_bound {a b u c : ℕ} {m : ℚ}
    (hbR : (0 : ℚ) < b) (hcR : (0 : ℚ) < c) (haR : (1 : ℚ) < a)
    (hanalytic : (u : ℚ) / c > m * (a : ℚ) ^ (b - 1) / b)
    (hsinger : (u : ℚ) * ((a : ℚ) - 1) ≤ (a : ℚ) ^ b - 1) :
    m < (b : ℚ) * ((a : ℚ) ^ b - 1)
      / ((c : ℚ) * (a : ℚ) ^ (b - 1) * ((a : ℚ) - 1)) := by
  have haR0 : (0 : ℚ) < (a : ℚ) := by linarith
  have hp1R : (0 : ℚ) < (a : ℚ) - 1 := by linarith
  -- From (13.10): `m · a^(b-1) · c < u · b`.
  rw [gt_iff_lt, div_lt_div_iff₀ hbR hcR] at hanalytic
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hanalytic hp1R,
    mul_le_mul_of_nonneg_left hsinger (le_of_lt hbR)]

/-- **Peterfalvi (13.12)**: the centralizer parameter `c` is `1`.

The numeric elimination `c_eq_one_forces_params` — fed the (13.10) analytic inequality
(`analytic_inequality`, `u/c > m p^(q-1)/q`), the (13.2.c) Singer bound (`basic_structure`,
`u ≤ (p^q-1)/(p-1)`), the fixed-point-free lower bound `c ≥ 2q+1` (`two_mul_q_dvd_c_pred`), and the
(13.11) `m`-bounds — forces `p = 5, q = 3, c = 7`, ruled out by the isolated structural residual
`c_eq_one_final_case`. -/
theorem c_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.c = 1 := by
  by_contra hne
  -- `c > 1`; with `2q ∣ c − 1` (`two_mul_q_dvd_c_pred`) this forces `c ≥ 2q + 1`.
  have hc1 : 1 ≤ hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hcgt : 1 < hyp.c := lt_of_le_of_ne hc1 (Ne.symm hne)
  have hc_ge : 2 * hyp.q + 1 ≤ hyp.c := by
    have h2q : 2 * hyp.q ≤ hyp.c - 1 := Nat.le_of_dvd (by omega) (hyp.two_mul_q_dvd_c_pred hG)
    omega
  -- (13.10) analytic inequality: `u/c > m · p^(q-1) / q`.
  obtain ⟨_, _, h1310⟩ := analytic_inequality hG hyp
  have hWcast : ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) = (hyp.p : ℚ) ^ (hyp.q - 1) := by push_cast; ring
  rw [hWcast] at h1310
  -- (13.2.c) Singer bound: `u ≤ (p^q - 1)/(p - 1)`, hence `u · (p-1) ≤ p^q - 1`.
  obtain ⟨_, _, _, _, hu_bound, _⟩ := basic_structure hG hyp
  have hp1nat : 1 ≤ hyp.p := hyp.p_prime.one_le
  have hp0nat : 0 < hyp.p - 1 := by have := hyp.three_le_p; omega
  have hpq1 : 1 ≤ hyp.p ^ hyp.q := Nat.one_le_pow _ _ hyp.p_prime.pos
  have huP : hyp.u * (hyp.p - 1) ≤ hyp.p ^ hyp.q - 1 :=
    (Nat.le_div_iff_mul_le hp0nat).mp hu_bound
  have huPR : (hyp.u : ℚ) * ((hyp.p : ℚ) - 1) ≤ (hyp.p : ℚ) ^ hyp.q - 1 := by
    have h1 : ((hyp.u * (hyp.p - 1) : ℕ) : ℚ) ≤ ((hyp.p ^ hyp.q - 1 : ℕ) : ℚ) := by
      exact_mod_cast huP
    have e1 : ((hyp.u * (hyp.p - 1) : ℕ) : ℚ) = (hyp.u : ℚ) * ((hyp.p : ℚ) - 1) := by
      push_cast [Nat.cast_sub hp1nat]; ring
    have e2 : ((hyp.p ^ hyp.q - 1 : ℕ) : ℚ) = (hyp.p : ℚ) ^ hyp.q - 1 := by
      push_cast [Nat.cast_sub hpq1]; ring
    rw [e1, e2] at h1; exact h1
  -- Positivity, then the side-agnostic analytic core (`analytic_singer_m_bound`) assembles the
  -- abstract bound `m < q(p^q-1)/(c p^(q-1)(p-1))` from (13.10) + the Singer bound.
  have hqR : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hcRpos : (0 : ℚ) < (hyp.c : ℚ) := by exact_mod_cast (show 0 < hyp.c by omega)
  have haR : (1 : ℚ) < (hyp.p : ℚ) := by
    have : (3 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hyp.three_le_p
    linarith
  have hbound := analytic_singer_m_bound hqR hcRpos haR h1310 huPR
  -- Numeric elimination forces `p = 5, q = 3, c = 7`.
  obtain ⟨hp5, hq3, hc7⟩ := c_eq_one_forces_params hyp.p_prime hyp.q_prime hyp.three_le_p
    hyp.q_ne_two hyp.p_ne_q hc_ge (hyp.two_mul_q_dvd_c_pred hG)
    (fun h => hyp.m_gt_seven_tenths_of_five_le_q h)
    (fun h => hyp.m_gt_four_fifths_of_seven_le_q h)
    (fun hq hp => hyp.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq hp)
    hyp.m_eq hbound
  exact c_eq_one_final_case hG hyp hp5 hq3 hc7

/-- **Peterfalvi (13.13)**: if case (9.7.a) holds for `S`, then
`q = 3` and `u = (p - 1)^2 / 4`. -/
theorem caseA_parameters [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (caseA_for_S : Prop) :
    caseA_for_S → hyp.q = 3 ∧ hyp.u = (hyp.p - 1) ^ 2 / 4 := by
  sorry

/-- The parity calculation behind **Peterfalvi (13.14)**: if `p` is odd, the
geometric sum of its first `q` powers has the same parity as `q`. -/
private theorem sum_range_pow_mod_two_eq {p q : ℕ} (hpodd : Odd p) :
    (∑ k ∈ Finset.range q, p ^ k) % 2 = q % 2 := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hpow : p ^ q % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow]
      omega

/-- The oddness part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_odd {p q : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.odd_iff, sum_range_pow_mod_two_eq hpodd, Nat.odd_iff.mp hqodd]

/-- The `p ≡ 1 [MOD q]` divisibility part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_dvd_of_modEq_one {p q : ℕ} (hp : p.Prime)
    (hpq : p ≡ 1 [MOD q]) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [← Nat.modEq_zero_iff_dvd]
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD q] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpq
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  exact hterms.trans (by simp [hsum_one])

/-- The coprimality part of **Peterfalvi (13.14)** when `p` is not `1 mod q`. -/
theorem cyclotomic_quotient_coprime_of_not_modEq_one {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.coprime_iff_gcd_eq_one]
  have hpmod : p ≡ 1 [MOD p - 1] := Nat.modEq_sub (le_of_lt hp.one_lt)
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD p - 1] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpmod
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  have hmod : (∑ k ∈ Finset.range q, p ^ k) ≡ q [MOD p - 1] := by
    exact hterms.trans (by rw [hsum_one])
  rw [hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp <|
    hq.coprime_iff_not_dvd.mpr fun hdiv => hpq <| by
      exact ((Nat.modEq_iff_dvd'
        (show 1 ≤ p from le_of_lt hp.one_lt)).mpr hdiv).symm

/-- If `p` is not `1 mod q`, then the prime `q` does not divide the
cyclotomic quotient in **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_not_dvd_self_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ¬ q ∣ (p ^ q - 1) / (p - 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hdiv
  rw [← Nat.geomSum_eq hp.two_le q] at hdiv
  have hsum_zero_nat : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hsum_zero_zmod : (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_pow] using hsum_zero_nat
  have hgeom :
      (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) =
        (p : ZMod q) ^ q - 1 :=
    geom_sum_mul (p : ZMod q) q
  have hp_eq_one : (p : ZMod q) = 1 := by
    have hzero :
        (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) = 0 := by
      rw [hsum_zero_zmod, zero_mul]
    rw [hgeom, ZMod.pow_card] at hzero
    exact sub_eq_zero.mp hzero
  exact hpq ((ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hp_eq_one))

/-- Prime divisors of the cyclotomic quotient in the non-`1 mod q` case are
`1 mod q`. -/
theorem cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q])
    (hr : r.Prime) (hrdvd : r ∣ (p ^ q - 1) / (p - 1)) :
    r ≡ 1 [MOD q] := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hr_ne_q : r ≠ q := by
    intro h
    exact cyclotomic_quotient_not_dvd_self_of_not_modEq_one hp hq hpq
      (by simpa [h] using hrdvd)
  have hr_not_dvd_q : ¬ r ∣ q := by
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hr_eq_one | hr_eq_q
    · exact hr.ne_one hr_eq_one
    · exact hr_ne_q hr_eq_q
  haveI : NeZero (q : ZMod r) :=
    NeZero.of_not_dvd (ZMod r) hr_not_dvd_q
  have hrdvd_sum : r ∣ ∑ k ∈ Finset.range q, p ^ k := by
    simpa [Nat.geomSum_eq hp.two_le q] using hrdvd
  have hroot :
      Polynomial.IsRoot (Polynomial.cyclotomic q (ZMod r))
        (Nat.castRingHom (ZMod r) p) := by
    rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime]
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    simpa [Nat.cast_sum, Nat.cast_pow] using
      (ZMod.natCast_eq_zero_iff (∑ k ∈ Finset.range q, p ^ k) r).mpr hrdvd_sum
  have hcop : p.Coprime r :=
    Polynomial.coprime_of_root_cyclotomic hq.pos hroot
  have hnot_r_dvd_p : ¬ r ∣ p :=
    hr.coprime_iff_not_dvd.mp hcop.symm
  have hp_ne_zero : (p : ZMod r) ≠ 0 := by
    intro hzero
    exact hnot_r_dvd_p ((ZMod.natCast_eq_zero_iff p r).mp hzero)
  have horder_dvd : orderOf (p : ZMod r) ∣ r - 1 :=
    ZMod.orderOf_dvd_card_sub_one hp_ne_zero
  have horder_eq : q = orderOf (p : ZMod r) :=
    (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  rw [← horder_eq] at horder_dvd
  exact ((Nat.modEq_iff_dvd' hr.pos).mpr horder_dvd).symm

/-- If every prime factor of `x` is `1 mod q`, then `x` is `1 mod q`. -/
theorem modEq_one_of_forall_primeFactors_modEq_one {x q : ℕ} (hx : x ≠ 0)
    (h : ∀ r ∈ x.primeFactors, r ≡ 1 [MOD q]) :
    x ≡ 1 [MOD q] := by
  rw [Nat.prod_pow_primeFactors_factorization hx]
  have hprod :
      (∏ r ∈ x.primeFactors, r ^ x.factorization r) ≡
        ∏ r ∈ x.primeFactors, 1 [MOD q] :=
    Nat.ModEq.prod fun r hr => by
      simpa using (h r hr).pow (x.factorization r)
  simpa using hprod

/-- The divisor-congruence part of **Peterfalvi (13.14)** when `p` is not
`1 mod q`. -/
theorem cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q] := by
  intro x hx hxdvd
  refine modEq_one_of_forall_primeFactors_modEq_one hx fun r hrx => ?_
  exact cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one hp hq hpq
    (Nat.prime_of_mem_primeFactors hrx)
    ((Nat.dvd_of_mem_primeFactors hrx).trans hxdvd)

/-- **Peterfalvi (13.14)**: divisibility facts for
`(p^q - 1) / (p - 1)`. -/
theorem cyclotomic_divisor_facts {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) ∧
      (p ≡ 1 [MOD q] → q ∣ (p ^ q - 1) / (p - 1)) ∧
      (¬ (p ≡ 1 [MOD q]) →
        Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ∧
          ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q]) := by
  refine ⟨cyclotomic_quotient_odd hp hpodd hqodd, ?_, ?_⟩
  · exact cyclotomic_quotient_dvd_of_modEq_one hp
  · intro hpq
    exact ⟨cyclotomic_quotient_coprime_of_not_modEq_one hp hq hpq,
      cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one hp hq hpq⟩

/-- **Peterfalvi (13.15)**: in case (9.7.b), `u` has the final cyclotomic
value, depending on whether `p` is `1 mod q`. -/
theorem caseB_order_u [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (caseB_for_S : Prop) :
    caseB_for_S →
      ((p_mod : hyp.p ≡ 1 [MOD hyp.q]) →
          hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
        (¬ (hyp.p ≡ 1 [MOD hyp.q]) →
          hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  sorry

/-- Carrier for the `u`-order conclusion in **Peterfalvi (13.15)** under
case (9.7.b).  It packages the two congruence branches so Section 16 can carry
the order data together with the case-(b) certificate. -/
structure CaseBOrderUData (hyp : Hypothesis (G := G)) (caseB_for_S : Prop) where
  caseB_holds : caseB_for_S
  u_eq_of_p_modEq_one :
    hyp.p ≡ 1 [MOD hyp.q] →
      hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))
  u_eq_of_not_modEq_one :
    ¬ hyp.p ≡ 1 [MOD hyp.q] →
      hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)

/-- Data form of **Peterfalvi (13.15)**, derived from `caseB_order_u`. -/
theorem caseB_order_u_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {caseB_for_S : Prop} (hcase : caseB_for_S) :
    CaseBOrderUData hyp caseB_for_S := by
  rcases caseB_order_u hG hyp caseB_for_S hcase with ⟨hmod, hnot⟩
  exact
    { caseB_holds := hcase
      u_eq_of_p_modEq_one := hmod
      u_eq_of_not_modEq_one := hnot }


end OddOrder.Peterfalvi.S15
