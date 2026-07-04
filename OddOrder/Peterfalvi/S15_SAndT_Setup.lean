/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S14_MaximalI
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

namespace Hypothesis

/-- Peterfalvi's `H = P C` in (13.5)--(13.10). -/
def H (hyp : Hypothesis (G := G)) : Subgroup G :=
  hyp.P ⊔ hyp.C

/-- Peterfalvi's `K = Q D`, used symmetrically for `T`. -/
def K (hyp : Hypothesis (G := G)) : Subgroup G :=
  hyp.Q ⊔ hyp.D

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
  have tdata : TypeIIData hyp.S := hSII.some
  -- `Sdata.U ≠ ⊥`: its order is the witness-independent index `[S' : S_F]`, which is `≠ 1`
  -- because the type-II witness has `U ≠ 1` at the same index.
  have hUne : hyp.Sdata.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥hyp.Sdata.U = Nat.card ↥tdata.typeP.U := by
      rw [hyp.Sdata.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hW1prime : (Nat.card ↥hyp.Sdata.W1).Prime := by
    rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]; exact hyp.q_prime
  -- the `A_0(S)` TI-subset clause of the nontrivial core depends only on `S` (witness-independent).
  have hTI := tdata.common.2.2
  -- (9.3) Wielandt order relation for the type-II setup on `S`.
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    { maximal := hyp.S_maximal
      typeP := hyp.Sdata
      nontrivial := ⟨hUne, hW1prime, hTI⟩
      type_alt := Or.inl hSII }).1 hSII
  have hord2 : Nat.card ↥hyp.Sdata.H
      = Nat.card ↥hyp.Sdata.W2 ^ Nat.card ↥hyp.Sdata.W1 := hord.2
  have hW2card : Nat.card ↥hyp.Sdata.W2 = hyp.p := by
    rw [hSdataW2, ← hyp.p_eq_card_W2]
  rw [hyp.Sdata.H_eq, ← hyp.P_eq_SF, hW2card, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at hord2
  exact hord2

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
  P_elementaryAbelian := sorry
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

/-- Character-degree and Dade-extension data from Peterfalvi (13.3). -/
structure CharacterDegreeData (hyp : Hypothesis (G := G)) where
  tau1S : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G
  tau1T : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G
  lambda : ClassFunction ↥hyp.S ℂ
  lambda_mem : lambda ∈ hyp.Sset
  lambda_irreducible : Prop
  lambda_degree : lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ)
  lambda_induced_from_PC_linear : Prop
  /-- **Peterfalvi (13.3.b) WLOG** (cf. the (13.12) proof: "By (13.3.b), we may assume that the
  hypothesis of (13.10) holds"): the distinguished `λ` *is* induced from a linear character of
  `PC` — the (13.3.b) case split is resolved into this branch, the other branch being handled by
  the `S ↔ T` symmetry upstream.  Carried as a `_holds` field so the (13.4)-dependent counting
  ((13.9.a), `|Q| = q^p`, the `|T|`-decomposition) can consume (13.4). -/
  lambda_induced_from_PC_linear_holds : lambda_induced_from_PC_linear
  mu_j_linear_induced : Prop
  mu_j_linear_induced_holds : mu_j_linear_induced
  no_lambda_forces_caseB_S : Prop
  /-- **Peterfalvi (13.3.c)**: the signs `δ_j`, `δ'_i` of (13.1.e) are all equal
  to `1` (materialized as a concrete statement about `delta`/`deltaPrime`). -/
  delta_eq_one : (∀ j : Fin hyp.p, hyp.delta j = 1) ∧ (∀ i : Fin hyp.q, hyp.deltaPrime i = 1)
  mu_tau1_formula : Prop
  mu_tau1_formula_holds : mu_tau1_formula
  sign_flip_exception : Prop

/-- **Peterfalvi (13.3)**: the `mu_j` have degree `u q`, the signs are `1`,
and the `tau_1` images are controlled by the `eta_ij` grid. -/
theorem character_degree_analysis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ data : CharacterDegreeData hyp,
      data.mu_j_linear_induced ∧ data.no_lambda_forces_caseB_S ∧
        data.mu_tau1_formula := by
  sorry

/-- **Peterfalvi (13.4)**: if `S` contains a degree-`u q` character induced
from a linear character of `P C`, then case (9.7.b) holds for `T`, with
`D = 1` and `v = (q^p - 1) / (q - 1)`.

The third conjunct `|Q| = q^p` is the kernel-order component of "case (9.7.b) holds for `T`"
(the (9.7.b) field model identifies `Q̄` with a field of cardinality `q^p`); it is what the
(13.10) counting reads off ((13.10.3) computes `|Q^#|/|T| = (q^p−1)/(pq^p v)`). -/
theorem lambda_forces_T_caseB [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (chars : CharacterDegreeData hyp) (hlambda : chars.lambda_induced_from_PC_linear) :
    hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  sorry

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

/-- Carrier for Peterfalvi (13.5), the TI-subset orthogonality calculation. -/
structure TISubsetOrthogonalityData (hyp : Hypothesis (G := G)) where
  S1 : Set (ClassFunction ↥hyp.S ℂ)
  zeta0 : ClassFunction ↥hyp.S ℂ
  zeta1 : ClassFunction ↥hyp.S ℂ
  chi : ClassFunction G ℂ
  alpha : ClassFunction ↥hyp.H ℂ
  a : ℤ
  alpha_kernel_contains_P : Prop
  point_formula : Prop
  norm_formula : Prop
  alpha_norm_bound : Prop

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
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDade (H_sharp_hypothesis71 hG hyp) ?_ hyp.H ?_ ?_ rfl
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

/-- **Peterfalvi (13.5)**: the TI-subset calculation on `H = P C` gives a
pointwise formula and two norm estimates. -/
theorem tiSubset_character_orthogonality [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ data : TISubsetOrthogonalityData hyp,
      data.point_formula ∧ data.norm_formula ∧ data.alpha_norm_bound := by
  sorry

/-- Carrier for the norm cascade (13.6)--(13.10). -/
structure NormCascadeData (hyp : Hypothesis (G := G)) where
  chars : CharacterDegreeData hyp
  lambda_norm_lower : Prop
  eta10_norm_lower : Prop
  eta01_norm_lower : Prop
  global_cover : Prop
  global_norm_lower : Prop
  analytic_inequality : Prop

/-- **Peterfalvi (13.6)**: the degree-`u q` character gives the first norm lower
bound on `H#`. -/
theorem lambda_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp, data.lambda_norm_lower := by
  sorry

/-- **Peterfalvi (13.7)**: the character `eta_10` has norm at least `|H#|` on
`H#`. -/
theorem eta10_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp, data.eta10_norm_lower := by
  sorry

/-- **Peterfalvi (13.8)**: the character `eta_01` has the corresponding lower
bound on `H#`. -/
theorem eta01_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp, data.eta01_norm_lower := by
  sorry

/-- **Peterfalvi (13.9)**: outside the conjugates of `H#` and `Q#`, the
characters `lambda^tau1` and `eta_10` cover every element. -/
theorem global_character_bound [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : NormCascadeData hyp, data.global_cover ∧ data.global_norm_lower := by
  sorry

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

/-- The distinguished `η₁₀ = τ₃(ω₁₀)` of the (13.7)/(13.9) estimates. -/
noncomputable def Hypothesis.eta10 (hyp : Hypothesis (G := G)) : ClassFunction G ℂ :=
  hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩

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
theorem reconciled_typePData_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
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
    -- The following are the genuine §13/§14 type-`P` structure of `T` (the `T`-side analogue of what
    -- `Section16TypePStructure` establishes for `S` when it builds `Sdata`).  No `T`-side carrier
    -- exists by design (`FeitThompson:276`), so these stay gated on the §13/§14 σ-structure theory.
    W2_le := sorry
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
    M_complement := sorry
    W1_normalizes_U := hyp.W2_normalizes_V
    U_nilpotent := sorry
    derived_complement := sorry
    H_noncyclic := by
      -- `H := Q = maxNilpotentNormalHall T` is the *intrinsic* Fitting Hall (choice-independent),
      -- so `¬ IsCyclic ↥Q` is read off any type-`P` datum on `T`.  The §13-level producer
      -- `typePData_of_isTypeNonI T_nonI` supplies one (no `T_typeII`/(14.9) needed, keeping this a
      -- clean §13 obligation): its `H_noncyclic` is `¬ IsCyclic` of the same subgroup `Q`.
      obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
      have hHeq : tpd0.H = hyp.Q := by rw [tpd0.H_eq, hyp.Q_eq_TF]
      exact hHeq ▸ tpd0.H_noncyclic
    secondDerived_le_fitting := sorry
    fitting_eq := sorry
    centralizer_W1 := sorry
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

open scoped FiniteInduce in
/-- **`η₁₀` is a virtual character of `G`** — real content of the 3002-threaded grid:
`η₁₀ = τ₃(ω₁₀)` (`eta_eq_tau_omega`), `ω₁₀ ∈ ZIrr W` (`omega_mem_ZIrr`), and `τ₃` preserves
virtual characters (`tau3_mem_ZIrr`). -/
theorem Hypothesis.eta10_mem_ZIrr [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.eta10 ∈ ZIrr G := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)

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
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp)
    (_hlam : chars.lambda_induced_from_PC_linear) :
    chars.tau1S chars.lambda ∈ ZIrr G ∧
      ClassFunction.inner (chars.tau1S chars.lambda) (chars.tau1S chars.lambda) = 1 := by
  sorry

/-- **Peterfalvi (13.6), textbook form**: `∑_{x∈H^#}|λ^{τ₁}(x)|² ≥ |S| − λ(1)²` (`λ(1) = uq`),
as a sum over the ambient sharp `H^# ⊂ G`.  Faithful producer; the (13.5) ρ-machinery
(`caseB_lambda_norm_bound` + `H_sharp_hypothesis76`) discharges it once the (13.5.a) point
formula is pinned to `λ^{τ₁}` — the residual is the (13.2.e) `τ`-agreement and the `u`-bound
`2u ≤ |P|−1` (issue 9000). -/
theorem lambda_tau1_sharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp)
    (_hlam : chars.lambda_induced_from_PC_linear) :
    (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
          ‖chars.tau1S chars.lambda x‖ ^ 2 := by
  sorry

/-- **Peterfalvi (13.7), textbook form**: `∑_{x∈H^#}|η₁₀(x)|² ≥ |H^#|`, as a sum over the
ambient sharp `H^# ⊂ G`.  Faithful producer; the engine is `caseB_eta_norm_bound` — the
residual is the (13.5.a) `a = 0` point formula for `η₁₀` on `H^#`. -/
theorem eta10_sharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (Nat.card ↥hyp.H : ℝ) - 1
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  sorry

/-- **Peterfalvi (13.8) applied to `T`**: `∑_{x∈Q^#}|η₁₀(x)|² ≥ |T'| − v²`, as a sum over the
ambient sharp `Q^# ⊂ G`.  Faithful producer; the engine is `caseB_eta01_norm_bound` on the
`T`-side (13.5) machinery (the `K^# = Q^#` Dade datum, `D = 1`). -/
theorem eta10_Qsharp_norm_lower [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  sorry

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
  have hlam := chars.lambda_induced_from_PC_linear_holds
  obtain ⟨hZ, hn⟩ := lambda_tau1_norm_one _hG chars hlam
  obtain ⟨hD, hv, hQ⟩ := lambda_forces_T_caseB _hG chars hlam
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  set φ : ClassFunction G ℂ := chars.tau1S chars.lambda with hφdef
  -- Global Parseval split and the term bounds.
  have hsplit := hyp.global_normSq_split _hG φ hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖φ 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharp := lambda_tau1_sharp_norm_lower _hG chars hlam
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
  obtain ⟨chars, -, -, -⟩ := character_degree_analysis _hG hyp
  have hlam := chars.lambda_induced_from_PC_linear_holds
  obtain ⟨hD, hv, hQ⟩ := lambda_forces_T_caseB _hG chars hlam
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  have hZ := hyp.eta10_mem_ZIrr
  have hn := hyp.eta10_inner_self_one
  -- Global Parseval split and the term bounds.
  have hsplit := hyp.global_normSq_split _hG hyp.eta10 hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖hyp.eta10 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharpH := eta10_sharp_norm_lower _hG hyp
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
  obtain ⟨chars, -, -, -⟩ := character_degree_analysis _hG hyp
  obtain ⟨hD, hv, hQ⟩ :=
    lambda_forces_T_caseB _hG chars chars.lambda_induced_from_PC_linear_holds
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

/-- **Peterfalvi (13.9.a), nonvanishing dichotomy**: on the generic set `G₀`, the characters
`λ^{τ₁}` and `η₁₀` do not vanish simultaneously.  Faithful producer of the textbook (13.9.a) —
the character content bottoms out at the (13.3.c) `μ_j^{τ₁} = δ·Σηᵢ₁` formula, the (13.2.e)
support fact for `(μ_j − λ)^τ`, the (3.2.c) regular-value formula, and the (3.9.b)/(3.4) grid
relations forcing `q·η₁₁(x) + 1 = 0` (impossible for an algebraic integer) in the doubly-vanishing
case. -/
theorem G0_nonvanishing_dichotomy [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (chars : CharacterDegreeData hyp)
    (_hlam : chars.lambda_induced_from_PC_linear) :
    ∀ x ∈ hyp.G0Finset, chars.tau1S chars.lambda x ≠ 0 ∨ hyp.eta10 x ≠ 0 := by
  sorry

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
  have hlam := chars.lambda_induced_from_PC_linear_holds
  obtain ⟨hZlam, -⟩ := lambda_tau1_norm_one _hG chars hlam
  have hZeta := hyp.eta10_mem_ZIrr
  set φ : ClassFunction G ℂ := chars.tau1S chars.lambda with hφdef
  set A : Finset G := hyp.G0Finset.filter (fun y => φ y ≠ 0) with hA
  set B : Finset G := hyp.G0Finset.filter (fun y => hyp.eta10 y ≠ 0) with hB
  -- The dichotomy: `G₀ ⊆ A ∪ B`.
  have hdich := G0_nonvanishing_dichotomy _hG chars hlam
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
  obtain ⟨chars, -, -, -⟩ := character_degree_analysis _hG hyp
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
  obtain ⟨chars, _⟩ := character_degree_analysis _hG hyp
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

/-- **Peterfalvi (13.12)**: the centralizer parameter `c` is `1`. -/
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
  -- The `c ≥ 2q + 1` lower bound (structural, `dv_2q_c1`) contradicts Peterfalvi's numeric
  -- elimination: the (13.10) analytic inequality bounds `m` above by `q·p^q/(c·p^(q−1)·(p−1))`, which
  -- with the `m > 7/10` lower bounds (13.11) and `c ≥ 2q+1` forces `q = 3, p = 5, c = 7, u ∣ 31`;
  -- then `PC` would be a normal nilpotent Hall subgroup of `S` strictly containing `P = S_F`,
  -- contradicting `P = maxNilpotentNormalHall S` (Coq `FTtypeP_Ind_Fitting_reg_Fcore`: `typeP_Galois`
  -- dichotomy + Fitting-core maximality `Fcore_max`).  Deep §13 char/σ residual.
  clear hcgt hc1
  sorry

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
