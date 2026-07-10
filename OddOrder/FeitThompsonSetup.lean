import OddOrder.BG.AppC_FinalContradiction
import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePComplement
import OddOrder.Peterfalvi.S06_MuColumnBridge
import OddOrder.Peterfalvi.S13_CoreStructure
import OddOrder.Peterfalvi.S13_Orthogonality

/-!
# FeitThompsonSetup

Prefix-split from `OddOrder.FeitThompson` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Feit-Thompson Theorem

This is the top-level file for Phase 4 of the project: the odd-order theorem,
*every finite group of odd order is solvable*.

## Structure of the top-level reduction

The proof is organized into a *downstream* reduction (pure group theory, fully
formalized here) and a single *upstream* obligation (the entire local + character
analysis, still to be constructed):

* `feitThompson_of_noMinimalSimpleOdd` — the **minimal-counterexample reduction**.
  By strong induction on `|G|`, if there were a finite group of odd order that is
  not solvable, a counterexample of minimal order would be a *minimal simple group
  of odd order* (`BG.IsMinimalSimpleOdd`): every proper subgroup and every proper
  quotient is solvable (induction hypothesis), so the group is simple (an extension
  of a solvable group by a solvable group is solvable). This step is `sorry`-free.

* `sectionSixteenHypothesis_of_isMinimalSimpleOdd` — the **single remaining upstream
  obligation**. From a minimal simple group of odd order, the Bender–Glauberman
  local analysis (BG §7–§16) together with Peterfalvi's character theory
  (Peterfalvi §10–§16) constructs the Section 16 field-normalizer configuration.
  This is the one `sorry` that the whole remaining project targets.

* `noMinimalSimpleOdd_of_section16` / `noMinimalSimpleOdd` — the **already-wired
  final contradiction**: once the Section 16 configuration is available,
  `BG.AppC.final_contradiction` derives `False` (BG Appendix C contradicts the
  standing inequality `q < p` of Peterfalvi §16).

`feitThompson` then combines the reduction with the (currently `sorry`-blocked)
non-existence of a minimal simple group of odd order.
-/

namespace OddOrder

open OddOrder.BG
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.RepresentationTheory
open scoped Pointwise

universe u

/-! ## The already-wired final contradiction -/

/-- The currently scaffolded final-contradiction bridge: once the BG minimal
counterexample and Peterfalvi Section 16 hypotheses are available, BG Appendix C
closes the contradiction. -/
theorem noMinimalSimpleOdd_of_section16 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G)
    (hyp : Peterfalvi.S16.Hypothesis (G := G)) :
    False :=
  BG.AppC.final_contradiction hG hyp

/-! ## The single remaining upstream obligation

The obligation `sectionSixteenHypothesis_of_isMinimalSimpleOdd` is presented as a
*gated-endpoint skeleton* (see `notes/meta/` and the
`feedback-gated-endpoint-skeleton-pattern` memo): a `sorry`-free assembly
`sectionSixteenHypothesis_of_inputs` builds the Section 16 configuration from an
explicit `Section16Inputs` menu of genuine §7–§16 witnesses, and the single
residual `sorry` is localized to "construct that menu".  The assembly *derives*
the fields of `Peterfalvi.S16.Hypothesis` that are not independent data (`η`, `m`,
the oddness facts, `finiteG`), so the menu is a strictly smaller obligation than
the raw `Hypothesis`. -/

section
open scoped OddOrder.Peterfalvi.S15.FiniteInduce

/-- **Named inputs for the Peterfalvi Section 16 configuration** (gated-endpoint
skeleton).

This bundles the genuine upstream witnesses that the Bender–Glauberman local
analysis (BG §7–§16) and Peterfalvi's character theory (Peterfalvi §3–§16) must
construct in order to enter Section 16.  It is `Peterfalvi.S15.Hypothesis`
together with the standing inequality `q < p` of (14.1), *minus* the fields that
`sectionSixteenHypothesis_of_inputs` derives mechanically.  Every field below
therefore names a real §7–§16 obligation, not a repackaging of something already
provable:

* the maximal pair `S, T`, their types, and the case-(b) trichotomy of (8.8)
  — Pf §14 / BG §16;
* the cyclic structure `W = W₁W₂`, the complements `U, V`, the primes `p, q` and
  the counting parameters `u, v, c, d` — §13–§14;
* the Dade character grids `ω, μ, ν` with the induction identities (13.1.e), the
  signs `δ, δ'`, and the integral maps `τ_S, τ_T, τ₃` — Pf §3–§9.

The residual `sorry` of `sectionSixteenHypothesis_of_isMinimalSimpleOdd` is exactly
"produce a `Section16Inputs G`"; i.e. it localizes the one remaining gap to this
explicit menu rather than to an opaque `Peterfalvi.S16.Hypothesis`. -/
structure Section16Inputs (G : Type*) [Group G] [Finite G] where
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  U : Subgroup G
  V : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  /-- **Peterfalvi (13.2.a) type determination (S-side)**: `S` is of BG type `P₂` (Peterfalvi type
  II).  Sourced from the §16 maximal pair (`Section16MaximalPair.S_typeP2`, fixed by the κ-Hall
  ordering `q < p`); threaded into `S15.Hypothesis` so §15 can read off `IsTypeII S` sorry-free
  (`isTypeII_of_isTypeP2`). -/
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
  S_deriv_eq_PU : derivedInG S = maxNilpotentNormalHall S ⊔ U
  T_deriv_eq_QV : derivedInG T = maxNilpotentNormalHall T ⊔ V
  /-- `Q ⊓ V = ⊥`: the invariant complement `V` genuinely complements `Q = T_F` in `T'` (from
  `exists_kappaHall_invariant_complement_to_MF`, ungated by (14.9)); threaded into `S15.Hypothesis`
  as `Q_inf_V_eq_bot`. -/
  V_inf_Q_eq_bot : maxNilpotentNormalHall T ⊓ V = ⊥
  /-- `T = T' ⋊ W₂`: `W₂` complements `T'` in `T` (from `typeP_derivedInG_isComplement_kappaHall`,
  ungated by (14.9)); threaded into `S15.Hypothesis` as `W2_isComplement_T_deriv`. -/
  W2_isComplement_T_deriv :
    Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)
  W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)
  W2_normalizes_V : W2 ≤ Subgroup.normalizer (V : Set G)
  q : ℕ
  p : ℕ
  q_prime : q.Prime
  p_prime : p.Prime
  q_eq_card_W1 : q = Nat.card ↥W1
  p_eq_card_W2 : p = Nat.card ↥W2
  u : ℕ
  v : ℕ
  c : ℕ
  d : ℕ
  c_eq_card_C : c = Nat.card ↥(U ⊓ Subgroup.centralizer (maxNilpotentNormalHall S : Set G))
  d_eq_card_D : d = Nat.card ↥(V ⊓ Subgroup.centralizer (maxNilpotentNormalHall T : Set G))
  card_U_eq_uc : Nat.card ↥U = u * c
  card_V_eq_vd : Nat.card ↥V = v * d
  Sset : Set (ClassFunction ↥S ℂ)
  Tset : Set (ClassFunction ↥T ℂ)
  A0S : Set ↥S
  A0T : Set ↥T
  tauS : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥S G
  tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥T G
  omega : Fin q → Fin p → ClassFunction ↥W ℂ
  mu : Fin q → Fin p → ClassFunction ↥S ℂ
  nu : Fin q → Fin p → ClassFunction ↥T ℂ
  delta : Fin p → ℤ
  deltaPrime : Fin q → ℤ
  delta_pm_one : (∀ j : Fin p, delta j = 1 ∨ delta j = -1) ∧
    (∀ i : Fin q, deltaPrime i = 1 ∨ deltaPrime i = -1)
  mu_degree_modEq_delta : ∀ (i : Fin q) (j : Fin p), ∃ a : ℤ,
    mu i j 1 = (delta j : ℂ) + (q : ℂ) * (a : ℂ)
  delta_zero_eq_one : delta ⟨0, p_prime.pos⟩ = 1
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥W G
  mu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, q_prime.pos⟩ j)
  mu_irreducible : ∀ (i : Fin q) (j : Fin p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (mu i j)
  mu_col_injective : ∀ j : Fin p, Function.Injective (fun i : Fin q => mu i j)
  /-- **Peterfalvi (4.3.b), full-grid orthonormality** (issues 9076/9014): the `μ_{ij}` are
  pairwise-distinct irreducibles across the whole grid. -/
  mu_orthonormal : ∀ (i k : Fin q) (j l : Fin p),
    OddOrder.RepresentationTheory.ClassFunction.inner (mu i j) (mu k l)
      = if i = k ∧ j = l then 1 else 0
  mu_colSum_eq_induce : ∀ j : Fin p,
    ∃ ψ : ClassFunction ↥((derivedInG S).subgroupOf S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ i : Fin q, mu i j) = ClassFunction.induce ((derivedInG S).subgroupOf S) ψ ∧
      (j ≠ ⟨0, p_prime.pos⟩ →
        ¬ (((W2.subgroupOf S).subgroupOf ((derivedInG S).subgroupOf S) :
            Set ↥((derivedInG S).subgroupOf S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  nu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, p_prime.pos⟩)
  q_lt_p : q < p
  /-- **Peterfalvi (13.1.b) carrier (S-side)**: the type-`P` data of `S` with its complement `U`
  and cyclic factor `W₁` reconciled to the menu's `U`/`W1`.  Sourced from the `tp` producer
  (`Section16TypePStructure.Sdata`); threaded into `S15.Hypothesis` to discharge its U-side. -/
  Sdata : TypePData S
  Sdata_U_eq : Sdata.U = U
  Sdata_W1_eq : Sdata.W1 = W1
  /-- **Peterfalvi (13.2.a) U-side**: `U` abelian (BG Lemma 15.1(b), `U` the `(κ∪σ)'`-Hall). -/
  S_U_commutative : IsMulCommutative ↥U
  /-- **W₂-reconciliation**: intrinsic `Sdata.W2 = C_{S'}(W₁#)` equals abstract `W₂` (= `K*`). -/
  Sdata_W2_eq : Sdata.W2 = W2
  /- Grid property fields (issue 3002): the (3.2)/(3.3)/(3.4) character-theoretic content of
  `tau3`/`omega`, threaded from `Section16CharacterData` into `S15.Hypothesis`. -/
  /-- **Peterfalvi (3.2), isometry part**: `τ₃` preserves the class-function inner product. -/
  tau3_isometry : OddOrder.Peterfalvi.S07.IsIntegralIsometry tau3
  /-- **Peterfalvi (3.2)**: `τ₃` sends the trivial character to the trivial character. -/
  tau3_trivial : tau3 (trivialClassFunction ↥W) = trivialClassFunction G
  /-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `τ₃` is the identity. -/
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
  /-- **Peterfalvi (3.9.c)** (issue-3002 keystone): on elements of order prime to `pq`, the
  `η`-grid values `(τ₃ω)_{ij}(g)` are rational integers. -/
  eta_intCast_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    ∀ (i : Fin q) (j : Fin p), ∃ m : ℤ, tau3 (omega i j) g = (m : ℂ)
  /-- **Peterfalvi (3.9.a)** (issue-3002 keystone): on elements of order prime to `pq`, the
  `η`-grid pairs under the index negation `(i,j) ↦ (−i,−j)` (`S15.finNeg`). -/
  eta_pair_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    ∀ (i : Fin q) (j : Fin p),
      tau3 (omega (OddOrder.Peterfalvi.S15.finNeg q_prime.pos i)
              (OddOrder.Peterfalvi.S15.finNeg p_prime.pos j)) g
        = tau3 (omega i j) g
  /-- **Peterfalvi (3.9)** (issue-3002 keystone): the principal grid value is `η₀₀(g) = 1`. -/
  eta_principal_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    tau3 (omega ⟨0, q_prime.pos⟩ ⟨0, p_prime.pos⟩) g = 1

/-! ### Partition of `Section16Inputs` into three independent producer obligations

`Section16Inputs G` bundles three logically distinct outputs of the §7–§16
program.  To let the corresponding lanes work in parallel without editing the same
region, we split the menu into three dependently-chained structures, give each its
own `sorry`'d producer, and assemble `Section16Inputs` from them `sorry`-free. -/

/-- **BG §16 maximal-pair / type-classification output** — *owned by lane-g*.

The maximal pair `S, T`, their (non-)types, the "at least one Type II" disjunction,
and the case-(b) trichotomy of (8.8).  These are the fields of `Section16Inputs`
that mention only `S, T`.  Producer: `section16MaximalPair_of_isMinimalSimpleOdd`
(BG §16 main results). -/
structure Section16MaximalPair (G : Type*) [Group G] [Finite G] where
  S : Subgroup G
  T : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  theorem88_caseB :
    ∀ M : Subgroup G, M ∈ maximalSubgroups G →
      IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨
        (∃ g : G, MulAut.conj g • M = T)
  /-- The κ-Hall factor `K` of `S` and its dual `K* = C_{S_σ}(K)`. -/
  K : Subgroup G
  Kstar : Subgroup G
  /-- **Canonical partner witness** (BG Theorem 14.7 / `typeP_duality`): `T` is the *canonical*
  type-`P` partner of `S`, not merely some maximal in its conjugacy class.  These fields pin the
  pairing `S ∩ T = K ⊔ K*` (the `theorem88_caseB` covering alone fixes the partner only up to
  conjugacy, which would leave `Section16TypePStructure` an empty type).  Supplied by
  `exists_section16MaximalPair_data`. -/
  K_le_S : K ≤ S
  K_hall : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S)
  Kstar_eq : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G)
  S_typeP : BG.Ch4.S14.IsTypeP S
  T_typeP : BG.Ch4.S14.IsTypeP T
  S_T_not_conj : ¬ BG.Ch4.S14.IsConjugateSubgroup S T
  Kstar_le_T : Kstar ≤ T
  Kstar_hall : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa T) (Kstar.subgroupOf T)
  K_eq : K = BG.Ch3.S10.Msigma T ⊓ Subgroup.centralizer (Kstar : Set G)
  Z_cyclic : IsCyclic ↥(K ⊔ Kstar)
  /-- **Ordering** `|K| < |K*|`: the pair is labelled so that the κ-Hall factor of `S` is the
  smaller of the two coprime factors of `W = K × K*`.  Established by relabelling `S ↔ T` in
  `exists_section16MaximalPair_data` (`card_kappaHall_ne_card_Kstar` makes the two orders distinct,
  so one of the two labellings has `|K| < |K*|`).  This pins the otherwise-ambiguous `q < p`. -/
  K_lt_Kstar : Nat.card ↥K < Nat.card ↥Kstar
  /-- **Peterfalvi (13.2.a)**: the smaller-κ member `S` of the pair (`|K| < |K*|`) is of type `P₂`
  (Type II).  This pins the type-duality disjunction `IsTypeP2 S ∨ IsTypeP2 T` (BG Theorem 14.7,
  which carries no order information) onto the side fixed by `K_lt_Kstar`.  Supplied by
  `section16MaximalPair_of_isMinimalSimpleOdd` via `isTypeP2_of_typeP_kappaHall_lt`; it is the
  determinate type the §15 `basic_structure` carrier wiring consumes
  (`exists_typePData_W1_eq_of_isTypeP2`, relane #4 / issues 4009/2019). -/
  S_typeP2 : BG.Ch4.S14.IsTypeP2 S

/-- **BG §14 type-P duality / cyclic-counting output** — *owned by lane-f*.

The cyclic structure `W = W₁W₂`, the complements `U, V`, the primes `p, q`, and the
counting parameters `u, v, c, d` with their identities.  Sibling references to the
maximal pair are taken from `mp`.  Producer:
`section16TypePStructure_of_isMinimalSimpleOdd` (BG §14 `typeP_duality`). -/
structure Section16TypePStructure {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPair G) where
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  U : Subgroup G
  V : Subgroup G
  W_eq_inter : W = mp.S ⊓ mp.T
  W_eq_join : W = W1 ⊔ W2
  W1_inf_W2_eq_bot : W1 ⊓ W2 = ⊥
  W1_commutes_W2 : ∀ x ∈ W1, ∀ y ∈ W2, Commute x y
  W_cyclic : IsCyclic ↥W
  S_deriv_eq_PU : derivedInG mp.S = maxNilpotentNormalHall mp.S ⊔ U
  T_deriv_eq_QV : derivedInG mp.T = maxNilpotentNormalHall mp.T ⊔ V
  /-- `Q ⊓ V = ⊥`: the invariant complement `V` genuinely complements `Q = T_F` in `T'` (from
  `exists_kappaHall_invariant_complement_to_MF`, ungated by (14.9)); threaded into `S15.Hypothesis`
  as `Q_inf_V_eq_bot`. -/
  V_inf_Q_eq_bot : maxNilpotentNormalHall mp.T ⊓ V = ⊥
  /-- `T = T' ⋊ W₂`: `W₂` complements `T'` in `T` (from `typeP_derivedInG_isComplement_kappaHall`,
  ungated by (14.9)); threaded into `S15.Hypothesis` as `W2_isComplement_T_deriv`. -/
  W2_isComplement_T_deriv :
    Subgroup.IsComplement' ((derivedInG mp.T).subgroupOf mp.T) (W2.subgroupOf mp.T)
  W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)
  W2_normalizes_V : W2 ≤ Subgroup.normalizer (V : Set G)
  q : ℕ
  p : ℕ
  q_prime : q.Prime
  p_prime : p.Prime
  q_eq_card_W1 : q = Nat.card ↥W1
  p_eq_card_W2 : p = Nat.card ↥W2
  u : ℕ
  v : ℕ
  c : ℕ
  d : ℕ
  c_eq_card_C : c = Nat.card ↥(U ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.S : Set G))
  d_eq_card_D : d = Nat.card ↥(V ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.T : Set G))
  card_U_eq_uc : Nat.card ↥U = u * c
  card_V_eq_vd : Nat.card ↥V = v * d
  q_lt_p : q < p
  /-- **Peterfalvi (13.1.b) carrier (S-side)**: the type-`P` structure data of the smaller-κ,
  type-`P₂` member `S` (`S = (P ⋊ U) ⋊ W₁`, `P = S_F`), with its complement `U` and cyclic factor
  `W₁` reconciled (`Sdata_U_eq`/`Sdata_W1_eq`) to the structure's `U`/`W1`.  Built from `mp.S_typeP2`
  (Pf (13.2.a)) via `typePData_of_kappaHall_hallComplement`; it supplies the U-side facts
  (`U` complements `M_F = P`, `W₁ ≤ N_G(U)`, `U` nilpotent) that Peterfalvi §15 reads off `S`
  (`basic_structure` U-side, `exists_typeI_maximal_overNormalizer_U`).  Only `S` is determinate —
  `T` (the larger-κ member) need not be type-`P₂`, so no symmetric `Tdata`. -/
  Sdata : TypePData mp.S
  Sdata_U_eq : Sdata.U = U
  Sdata_W1_eq : Sdata.W1 = W1
  /-- **Peterfalvi (13.2.a) U-side**: `U` abelian (BG Lemma 15.1(b), `U` the `(κ∪σ)'`-Hall). -/
  S_U_commutative : IsMulCommutative ↥U
  /-- **W₂-reconciliation**: intrinsic `Sdata.W2 = C_{S'}(W₁#)` equals abstract `W₂` (= `K*`). -/
  Sdata_W2_eq : Sdata.W2 = W2

/-- **Peterfalvi §13 coherent Dade-grid output** — *owned by lane-b*.

The character grids `ω, μ, ν` with the induction identities (13.1.e), the signs
`δ, δ'`, the integral maps `τ_S, τ_T, τ₃`, and the exceptional-character data
`Sset, Tset, A0S, A0T`.  Sibling references are taken from `mp` (for `S, T`) and
`tp` (for `W, p, q` and the structural facts).  Producer:
`section16CharacterData_of_isMinimalSimpleOdd` (Peterfalvi §3–§13 coherent grids). -/
structure Section16CharacterData {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPair G) (tp : Section16TypePStructure mp) where
  Sset : Set (ClassFunction ↥mp.S ℂ)
  Tset : Set (ClassFunction ↥mp.T ℂ)
  A0S : Set ↥mp.S
  A0T : Set ↥mp.T
  tauS : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥mp.S G
  tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥mp.T G
  omega : Fin tp.q → Fin tp.p → ClassFunction ↥tp.W ℂ
  mu : Fin tp.q → Fin tp.p → ClassFunction ↥mp.S ℂ
  nu : Fin tp.q → Fin tp.p → ClassFunction ↥mp.T ℂ
  delta : Fin tp.p → ℤ
  deltaPrime : Fin tp.q → ℤ
  delta_pm_one : (∀ j : Fin tp.p, delta j = 1 ∨ delta j = -1) ∧
    (∀ i : Fin tp.q, deltaPrime i = 1 ∨ deltaPrime i = -1)
  mu_degree_modEq_delta : ∀ (i : Fin tp.q) (j : Fin tp.p), ∃ a : ℤ,
    mu i j 1 = (delta j : ℂ) + (tp.q : ℂ) * (a : ℂ)
  delta_zero_eq_one : delta ⟨0, tp.p_prime.pos⟩ = 1
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥tp.W G
  mu_definition : ∀ (i : Fin tp.q) (j : Fin tp.p),
    ClassFunction.induce (tp.W.subgroupOf mp.S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, tp.q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, tp.q_prime.pos⟩ j)
  mu_irreducible : ∀ (i : Fin tp.q) (j : Fin tp.p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (mu i j)
  mu_col_injective : ∀ j : Fin tp.p, Function.Injective (fun i : Fin tp.q => mu i j)
  /-- **Peterfalvi (4.3.b), full-grid orthonormality** (issues 9076/9014): the `μ_{ij}` are
  pairwise-distinct irreducibles across the whole grid. -/
  mu_orthonormal : ∀ (i k : Fin tp.q) (j l : Fin tp.p),
    OddOrder.RepresentationTheory.ClassFunction.inner (mu i j) (mu k l)
      = if i = k ∧ j = l then 1 else 0
  mu_colSum_eq_induce : ∀ j : Fin tp.p,
    ∃ ψ : ClassFunction ↥((derivedInG mp.S).subgroupOf mp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ i : Fin tp.q, mu i j) = ClassFunction.induce ((derivedInG mp.S).subgroupOf mp.S) ψ ∧
      (j ≠ ⟨0, tp.p_prime.pos⟩ →
        ¬ (((tp.W2.subgroupOf mp.S).subgroupOf ((derivedInG mp.S).subgroupOf mp.S) :
            Set ↥((derivedInG mp.S).subgroupOf mp.S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  nu_definition : ∀ (i : Fin tp.q) (j : Fin tp.p),
    ClassFunction.induce (tp.W.subgroupOf mp.T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, tp.p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, tp.p_prime.pos⟩)
  /- Grid property fields (issue 3002): the (3.2)/(3.3)/(3.4) character-theoretic content of
  `tau3`/`omega`, supplied by the producer from `tau3W_isometry` etc. and `omegaS_inner` etc. -/
  /-- **Peterfalvi (3.2), isometry part**: `τ₃` preserves the class-function inner product. -/
  tau3_isometry : OddOrder.Peterfalvi.S07.IsIntegralIsometry tau3
  /-- **Peterfalvi (3.2)**: `τ₃` sends the trivial character to the trivial character. -/
  tau3_trivial : tau3 (trivialClassFunction ↥tp.W) = trivialClassFunction G
  /-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `τ₃` is the identity. -/
  tau3_apply_of_regular : ∀ (α : ClassFunction ↥tp.W ℂ) (w : G) (hwW : w ∈ tp.W),
    w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G) → tau3 α w = α ⟨w, hwW⟩
  /-- **Peterfalvi (3.2)**: `τ₃` sends virtual characters to virtual characters. -/
  tau3_mem_ZIrr : ∀ z ∈ ZIrr ↥tp.W, tau3 z ∈ ZIrr G
  /-- **Peterfalvi (3.3)/(3.4)**: the `ω`-grid is orthonormal. -/
  omega_orthonormal : ∀ (i k : Fin tp.q) (j l : Fin tp.p),
    ClassFunction.inner (omega i j) (omega k l) = if i = k ∧ j = l then 1 else 0
  /-- The `ω_{ij}` are linear characters: `ω_{ij}(1) = 1`. -/
  omega_apply_one : ∀ (i : Fin tp.q) (j : Fin tp.p), omega i j 1 = 1
  /-- Each `ω_{ij}` is a virtual character (in fact an irreducible character of `W`). -/
  omega_mem_ZIrr : ∀ (i : Fin tp.q) (j : Fin tp.p), omega i j ∈ ZIrr ↥tp.W
  /-- **Peterfalvi (3.3)** (issue 2033): each `ω_{ij}` is multiplicative — a linear character. -/
  omega_mul : ∀ (i : Fin tp.q) (j : Fin tp.p) (w w' : ↥tp.W),
    omega i j (w * w') = omega i j w * omega i j w'
  /-- **Peterfalvi (3.3)** (issue 2033): the column-`0` characters `ω_{i0}` are trivial on `W₂`. -/
  omega_col_zero_apply_of_mem_W2 : ∀ (i : Fin tp.q) (w : ↥tp.W), (w : G) ∈ tp.W2 →
    omega i ⟨0, tp.p_prime.pos⟩ w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): the row-`0` characters `ω_{0j}` are trivial on `W₁`. -/
  omega_row_zero_apply_of_mem_W1 : ∀ (j : Fin tp.p) (w : ↥tp.W), (w : G) ∈ tp.W1 →
    omega ⟨0, tp.q_prime.pos⟩ j w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₁` the grid values are `q`-th roots of unity. -/
  omega_pow_q_of_mem_W1 : ∀ (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W), (w : G) ∈ tp.W1 →
    omega i j w ^ tp.q = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₂` the grid values are `p`-th roots of unity. -/
  omega_pow_p_of_mem_W2 : ∀ (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W), (w : G) ∈ tp.W2 →
    omega i j w ^ tp.p = 1
  /-- **Peterfalvi (3.2.d)** (issue 2034): a class function of `G` orthogonal to the whole
  `τ₃ω`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — the grid enumerates the
  `σ`-image, and every irreducible off the image vanishes on `Ŵ`. -/
  eta_complete_vanish : ∀ χ : ClassFunction G ℂ,
    (∀ (i : Fin tp.q) (j : Fin tp.p), ClassFunction.inner (tau3 (omega i j)) χ = 0) →
    ∀ w : G, w ∈ tp.W → w ∉ (tp.W1 : Set G) ∪ (tp.W2 : Set G) → χ w = 0
  /-- **Peterfalvi (3.4)/(3.5), the four-corner vanishing** (issue 2036): off the conjugacy
  saturation of the regular set `Ŵ = W ∖ (W₁ ∪ W₂)`, the `(3.5)` relation collapses to
  `1 − (τ₃ω)_{i0}(x) − (τ₃ω)_{0j}(x) + (τ₃ω)_{ij}(x) = 0` for nonzero row/column indices. -/
  eta_fourcorner_vanish : ∀ (i : Fin tp.q) (j : Fin tp.p), i ≠ ⟨0, tp.q_prime.pos⟩ →
    j ≠ ⟨0, tp.p_prime.pos⟩ → ∀ x : G,
    x ∉ OddOrder.GroupTheory.conjClassSet ((tp.W : Set G) \ ((tp.W1 : Set G) ∪ (tp.W2 : Set G))) →
    (1 : ℂ) - tau3 (omega i ⟨0, tp.p_prime.pos⟩) x - tau3 (omega ⟨0, tp.q_prime.pos⟩ j) x
      + tau3 (omega i j) x = 0
  /-- **Peterfalvi (3.9.b), row-vanishing transport** (issue 2036): if `(τ₃ω)₁₀` vanishes at
  `x`, so do all `(τ₃ω)_{i0}` with `i ≠ 0` — the nontrivial row characters are Galois-conjugate
  powers of `ω₁₀`, and the twist fixes the vanishing value. -/
  eta_row_vanish_of_one_zero : ∀ x : G,
    tau3 (omega ⟨1, tp.q_prime.one_lt⟩ ⟨0, tp.p_prime.pos⟩) x = 0 →
    ∀ i : Fin tp.q, i ≠ ⟨0, tp.q_prime.pos⟩ → tau3 (omega i ⟨0, tp.p_prime.pos⟩) x = 0
  /-- **Peterfalvi (3.9.c)** (issue-3002 keystone): on elements of order prime to `pq`, the
  `η`-grid values `(τ₃ω)_{ij}(g)` are rational integers.  Supplied from
  `tau3W_omegaS_intCast_of_coprime` (S05 σ-Galois integrality). -/
  eta_intCast_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (tp.p * tp.q) →
    ∀ (i : Fin tp.q) (j : Fin tp.p), ∃ m : ℤ, tau3 (omega i j) g = (m : ℂ)
  /-- **Peterfalvi (3.9.a)** (issue-3002 keystone): on elements of order prime to `pq`, the
  `η`-grid pairs under the index negation `(i,j) ↦ (−i,−j)` (`S15.finNeg`). -/
  eta_pair_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (tp.p * tp.q) →
    ∀ (i : Fin tp.q) (j : Fin tp.p),
      tau3 (omega (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
              (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) g
        = tau3 (omega i j) g
  /-- **Peterfalvi (3.9)** (issue-3002 keystone): the principal grid value is `η₀₀(g) = 1`. -/
  eta_principal_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (tp.p * tp.q) →
    tau3 (omega ⟨0, tp.q_prime.pos⟩ ⟨0, tp.p_prime.pos⟩) g = 1

/-- **Canonical type-`P` maximal pair data** (issue 7005): for a minimal simple group of odd order,
there is a type-`P` dual pair `S, T` together with the full κ-Hall witness data of BG Theorem 14.7
(`typeP_duality`).  This is the data an *enriched* `Section16MaximalPair` carries so the type-`P`
structure producer can discharge the pairing `S ∩ T = K × K*`: the intrinsic covering axiom
(`theorem88_caseB`) fixes the partner only up to conjugacy, so an arbitrary maximal pair need not
have `S ∩ T` a cyclic product (the type-emptiness obstruction of the bare producer).

Mirrors the dichotomy branch of `theoremI_nilpotentHall_conjugacy_and_type_dichotomy`, additionally
exposing the canonical partner `T = Mstar` and its κ-Hall factors `K, K*` (dropped by the
dichotomy).  Case (a) of (8.8) (every maximal Type I) is excluded by Peterfalvi (12.17). -/
theorem exists_section16MaximalPair_data {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) :
    ∃ S T K Kstar : Subgroup G,
      S ∈ maximalSubgroups G ∧ T ∈ maximalSubgroups G ∧ S ≠ T ∧
      IsTypeNonI S ∧ IsTypeNonI T ∧ (IsTypeII S ∨ IsTypeII T) ∧
      (∀ M : Subgroup G, M ∈ maximalSubgroups G →
        IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = T)) ∧
      K ≤ S ∧ Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S) ∧
      Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) ∧
      BG.Ch4.S14.IsTypeP S ∧ BG.Ch4.S14.IsTypeP T ∧ ¬ BG.Ch4.S14.IsConjugateSubgroup S T ∧
      Kstar ≤ T ∧ Ch03.IsHallSubgroup (BG.Ch4.S14.kappa T) (Kstar.subgroupOf T) ∧
      K = BG.Ch3.S10.Msigma T ⊓ Subgroup.centralizer (Kstar : Set G) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ Nat.card ↥K < Nat.card ↥Kstar := by
  classical
  have notTypeI_imp_typeP : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
      ¬ IsTypeI N → BG.Ch4.S14.IsTypeP N := by
    intro N hN hnotI
    have hiff := (BG.Ch4.S16.proposition_type_classification hG hN).1
    have hnotF : ¬ BG.Ch4.S14.IsTypeF N := fun hF => hnotI (hiff.mpr hF)
    rw [BG.Ch4.S14.IsTypeP, Set.nonempty_iff_ne_empty]
    exact fun he => hnotF he
  have typeP_imp_nonI : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
      BG.Ch4.S14.IsTypeP N → IsTypeNonI N := by
    intro N hN hP
    obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ := BG.Ch4.S16.proposition_type_classification hG hN
    by_cases hk : BG.Ch4.S14.kappa N = BG.Ch4.S14.sigmaComplementPrimes N
    · have hP1 : BG.Ch4.S14.IsTypeP1 N := ⟨hP, hk⟩
      by_cases hMF : BG.Ch4.S15.MF N = BG.Ch3.S10.Msigma N
      · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
      · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
        · exact Or.inr (Or.inl hIII)
        · exact Or.inr (Or.inr (Or.inl hIV))
    · exact Or.inl (hbII.mpr ⟨hP, hk⟩)
  by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M
  · obtain ⟨cb⟩ := Peterfalvi.S14.theorem88_caseB_holds hG
    exact absurd (hall cb.S cb.S_maximal)
      (BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG cb.S_maximal cb.S_nonI)
  · push Not at hall
    obtain ⟨S, hS, hSnotI⟩ := hall
    have hSP : BG.Ch4.S14.IsTypeP S := notTypeI_imp_typeP S hS hSnotI
    haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hS
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (BG.Ch4.S14.kappa S)
    set K : Subgroup G := K'.map S.subtype with hKdef
    have hKeq : K.subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S) := by
      rw [hKeq]; exact hK'
    set Kstar : Subgroup G :=
      BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    have hKM : K ≤ S := Subgroup.map_subtype_le K'
    obtain ⟨_, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
        ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, _, hP2disj, hcover⟩, _⟩ :=
      BG.Ch4.S14.typeP_duality hG hS hSP hKM hK hKstardef
    -- The structural data is symmetric in `(S, K) ↔ (Mstar, K*)`; collect the shared facts once.
    have hSne : S ≠ Mstar := by
      rintro rfl; exact hSnconjMstar (BG.Ch4.S14.IsConjugateSubgroup.refl S)
    have hnonIS : IsTypeNonI S := typeP_imp_nonI S hS hSP
    have hnonIM : IsTypeNonI Mstar := typeP_imp_nonI Mstar hMstarMem hMstarP
    have hone : IsTypeII S ∨ IsTypeII Mstar := by
      rcases hP2disj with hP2S | hP2M
      · exact Or.inl ((BG.Ch4.S16.proposition_type_classification hG hS).2.1.mpr hP2S)
      · exact Or.inr ((BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr hP2M)
    have hcov : ∀ M : Subgroup G, M ∈ maximalSubgroups G →
        IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = Mstar) := by
      intro M hM
      by_cases hMI : IsTypeI M
      · exact Or.inl hMI
      · exact Or.inr (hcover M hM (notTypeI_imp_typeP M hM hMI))
    -- The two κ-Hall factors have distinct orders, so one of the two labellings has `|K| < |K*|`.
    rcases lt_or_gt_of_ne (BG.Ch4.S14.card_kappaHall_ne_card_Kstar hSP hKM hK hKstardef) with
      hlt | hgt
    · exact ⟨S, Mstar, K, Kstar, hS, hMstarMem, hSne, hnonIS, hnonIM, hone, hcov, hKM, hK,
        hKstardef, hSP, hMstarP, hSnconjMstar, hKstarMstar, hKstar_hall, hK_eq, hcyc, hlt⟩
    · refine ⟨Mstar, S, Kstar, K, hMstarMem, hS, hSne.symm, hnonIM, hnonIS, hone.symm, ?_,
        hKstarMstar, hKstar_hall, hK_eq, hMstarP, hSP, fun h => hSnconjMstar h.symm, hKM, hK,
        hKstardef, ?_, hgt⟩
      · intro M hM
        rcases hcov M hM with hI | hSc | hMc
        · exact Or.inl hI
        · exact Or.inr (Or.inr hSc)
        · exact Or.inr (Or.inl hMc)
      · rw [sup_comm]; exact hcyc

/-- **Peterfalvi (11.9.b), character core** (faithful obligation, *owned by lane-b* — Peterfalvi §11
coherence / Dade norm).  For a Type III/IV maximal subgroup `S` (the Hypothesis (11.2) case), with
κ-Hall factor `K` and dual factor `K* = M_σ(S) ⊓ C_G(K)`, the coherence / norm-inequality bound on
the character set `S(HC)` forces `q > p`, i.e. the dual factor is the smaller: `|K*| < |K|`
(`q = |W₁| = |K|`, `p = |W₂| = |K*|`).

The proof is now **fully assembled** from three pieces: (i) the carrier translation `|K| = w₁` (both
`K` and `W₁` complement `M'`, so both equal the derived index — `card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`); (ii) the carrier translation `|K*| = w₂`
(`card_Msigma_inf_centralizer_eq_card_W2`, axiom-clean BG §14 group theory); and (iii) the §11
character reduction `w₂ < w₁` (`S13.w2_lt_w1_of_hypothesis_H0C` — the honest narrow-`𝒮(H₀C)` route,
issue 1019; the deprecated wide `S12.w2_lt_w1_of_hypothesis` and its false uniform-degree lemma have
been retired).  All of (i)/(ii) and the reduction spine of (iii) are proven; the residual is the
genuine Peterfalvi (11.8) non-orthogonality (`S13.exists_zeta_residual_not_orthogonal_H0C`), whose
remaining `sorry`s are the §14 Sibley glue `(6.7)`/`(5.8)`, the `(9.11)` caseA refuter, and `(10.8)`. -/
theorem card_kappaHall_lt_of_isTypeIIIorIV {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hIIIorIV : IsTypeIII S ∨ IsTypeIV S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- `K` is cyclic, as a subgroup of the cyclic `Z = K ⊔ K*` (BG 14.7(d), via `typeP_duality`).
  obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
    BG.Ch4.S14.typeP_duality hG hS hSP hKS hK hKstar
  haveI : IsCyclic ↥(K ⊔ Kstar) := hcyc
  haveI : IsCyclic ↥K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  -- Build the §10 hypothesis on `S` (type III/IV ⊆ III/IV/V).
  obtain ⟨hyp⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG hS
    (hIIIorIV.imp id Or.inl)
  -- `|K| = w₁`: both `K` and `W₁` complement `M'`, so both equal the derived index.
  have hKw1 : Nat.card ↥K = hyp.w1 := by
    rw [BG.Ch4.S16.card_kappaHall_eq_derived_index hG hS hSP hKS hK]
    exact hyp.typeP.card_W1_eq_derived_index.symm
  -- `|K*| = w₂`: the carrier bridge (lane-b W3, BG §14 group theory, now in `S10`).
  have hKstarw2 : Nat.card ↥Kstar = hyp.w2 := by
    rw [hKstar]
    exact OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG hS hSP hKS hK hyp.typeP
  -- The two (11.5)/(11.7) structural facts, discharged via §13 (`secondDerived_eq_HC`,
  -- `H_elementaryAbelian`): `M'' = H ⊔ C_U(H)` and `|H| = |W₂|^{|W₁|}`.
  have hM2 : secondDerivedInAmbient S
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)) :=
    OddOrder.Peterfalvi.S13.secondDerived_eq_fitting_of_base hG hyp hIIIorIV
  have hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1 :=
    OddOrder.Peterfalvi.S13.card_H_eq_of_base hG hyp hIIIorIV
  -- `w₂ < w₁` (Peterfalvi (11.9.b), from the genuine (11.8) via the honest narrow `𝒮(H₀C)` route —
  -- `S13.w2_lt_w1_of_hypothesis_H0C`, replacing the deprecated wide `S12.w2_lt_w1_of_hypothesis`
  -- whose uniform-degree lemma is false for non-Galois type III/IV, issue 1019).
  rw [hKstarw2, hKw1]
  exact OddOrder.Peterfalvi.S13.w2_lt_w1_of_hypothesis_H0C hG hyp hIIIorIV hM2 hHcard

/-- **Peterfalvi (13.2.a), character core** (mmd §13, `references/peterfalvi/04.15_*`).

For the type-`P` member `S` of a dual maximal pair (BG Theorem 14.7), with κ-Hall factor `K` and
dual factor `K* = M_σ(S) ⊓ C_G(K)`, the type-`P₁` alternative (`S` of Type III/IV/V) carries the
*larger* κ-Hall factor: `|K*| < |K|`.  In Peterfalvi's notation `q = |W₁| = |K|`, `p = |W₂| = |K*|`,
this is "`S` of Type III ⟹ `q > p`".

**Type-V exclusion discharged (Theorem (10.10), sorry-free here)**: by the type dictionary
`proposition_type_classification`, a type-`P₁` `S` is Type III/IV (if `M_F ≠ M_σ`) or Type V (if
`M_F = M_σ`); the latter is impossible by `no_typeV_maximal` (Peterfalvi (10.10)), so `S` is
Type III/IV and the genuinely §11 character core `card_kappaHall_lt_of_isTypeIIIorIV` ((11.9.b),
lane-b) applies.  Consumed by `isTypeP2_of_typeP_kappaHall_lt`
(relane #4, issues 4009/2019; relane #6, issue 2020). -/
theorem card_kappaHall_lt_of_isTypeP1 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hP1 : BG.Ch4.S14.IsTypeP1 S) :
    Nat.card ↥Kstar < Nat.card ↥K := by
  -- Type dictionary: `S` type-`P₁` ⟹ Type III/IV (`M_F ≠ M_σ`) or Type V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ := BG.Ch4.S16.proposition_type_classification hG hS
  -- Type V is excluded by Theorem (10.10) `no_typeV_maximal`, so `M_F ≠ M_σ` and `S` is III/IV.
  have hMF : BG.Ch4.S15.MF S ≠ BG.Ch3.S10.Msigma S := fun hMF =>
    OddOrder.Peterfalvi.S12.no_typeV_maximal hG ⟨S, hS, hdV.mpr ⟨hP1, hMF⟩⟩
  -- The genuinely §11 character core (11.9.b) gives `|K*| < |K|`.
  exact card_kappaHall_lt_of_isTypeIIIorIV hG hS hSP hKS hK hKstar (hcIII_IV.mpr ⟨hP1, hMF⟩)

/-- **Peterfalvi (13.2.a)** (mmd §13, `references/peterfalvi/04.15_*`): the type-`P` member `S` of a
dual maximal pair whose κ-Hall factor `K` is the *smaller* of the two coprime factors of
`W = K × K*` is of type `P₂` (BG) / Type II (Peterfalvi).

This selects, out of the type-duality disjunction `IsTypeP2 S ∨ IsTypeP2 T` (BG Theorem 14.7,
`typeP_duality`, which carries no order information), the determinate side `IsTypeP2 S` fixed by the
ordering `|K| < |K*|`.  Skeleton proof: `S` is type-`P`, hence type `P₁` or `P₂`
(`isTypeP_iff_isTypeP1_or_isTypeP2`); the `P₁` branch is excluded by `card_kappaHall_lt_of_isTypeP1`
(the Pf §10–§11 character core, an obligation owned by lane-b), leaving `P₂`.

Consumed by `section16MaximalPair_of_isMinimalSimpleOdd` to carry `Section16MaximalPair.S_typeP2`
(relane #4, issues 4009/2019), which unblocks the §15 `basic_structure` `TypePData` carrier wiring
(`exists_typePData_W1_eq_of_isTypeP2`). -/
theorem isTypeP2_of_typeP_kappaHall_lt {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {S K Kstar : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hlt : Nat.card ↥K < Nat.card ↥Kstar) :
    BG.Ch4.S14.IsTypeP2 S := by
  rcases BG.Ch4.S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hSP with hP1 | hP2
  · exact absurd (card_kappaHall_lt_of_isTypeP1 hG hS hSP hKS hK hKstar hP1) (lt_asymm hlt)
  · exact hP2

/-- **BG §16 maximal-pair producer** — *lane-g* (BG §16 main results).
Constructs the maximal pair `S, T`, their type classification, and the case-(b)
trichotomy of (8.8) from a minimal simple group of odd order.

This is the first real consumer of the §16 main results.  Peterfalvi (8.8)
(`maximalSubgroup_type_dichotomy`, repackaging BG Theorem I) gives the dichotomy
"every maximal subgroup is Type I, or the type-P pair `S, T` covers everything".
The second branch supplies every field directly.  The first branch is impossible:
Peterfalvi (12.17) (`theorem88_caseB_holds`, the all-Type-I non-existence argument
of §7.11/§12) produces a *non-Type-I* maximal subgroup, which contradicts "every
maximal subgroup is Type I" via the type-exclusivity corollary of Proposition 16.1
(`not_isTypeI_of_isTypeNonI`). -/
noncomputable def section16MaximalPair_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : Section16MaximalPair G := by
  classical
  -- `exists_section16MaximalPair_data` supplies the canonical pair `S, T = Mstar` with the full
  -- κ-Hall witness data.  The four subgroup witnesses are extracted by choice (the `Exists` cannot
  -- be `rcases`'d into the `Type`-valued structure goal); the structural conjunction is an `And`
  -- (large-eliminating), so it `obtain`s into named hypotheses directly.
  have e := exists_section16MaximalPair_data hG
  obtain ⟨hSmax, hTmax, hSneT, hSnonI, hTnonI, hone, hcaseB, hKleS, hKhall, hKstareq,
    hStypeP, hTtypeP, hSTnconj, hKstarleT, hKstarhall, hKeq, hZcyc, hKlt⟩ :=
    e.choose_spec.choose_spec.choose_spec.choose_spec
  exact
    { S := e.choose
      T := e.choose_spec.choose
      K := e.choose_spec.choose_spec.choose
      Kstar := e.choose_spec.choose_spec.choose_spec.choose
      S_maximal := hSmax
      T_maximal := hTmax
      S_ne_T := hSneT
      S_nonI := hSnonI
      T_nonI := hTnonI
      one_typeII := hone
      theorem88_caseB := hcaseB
      K_le_S := hKleS
      K_hall := hKhall
      Kstar_eq := hKstareq
      S_typeP := hStypeP
      T_typeP := hTtypeP
      S_T_not_conj := hSTnconj
      Kstar_le_T := hKstarleT
      Kstar_hall := hKstarhall
      K_eq := hKeq
      Z_cyclic := hZcyc
      K_lt_Kstar := hKlt
      S_typeP2 := isTypeP2_of_typeP_kappaHall_lt hG hSmax hStypeP hKleS hKhall hKstareq hKlt }

open scoped IsMulCommutative in
/-- **`TypePData M` from a `K`-invariant `(κ∪σ)′`-Hall complement `U`** (`sorry`-free engine;
POLE-1 carrier, issue 4008).

Given a type-`P` maximal subgroup `M`, its cyclic κ-Hall `K`, and a `(κ∪σ)′`-Hall complement `U`
normalised by `K` (`hKnorm`), this assembles the Peterfalvi type-`P` datum `TypePData M` with the
chosen factors `data.W₁ = K`, `data.U = U` (definitionally: `…_W1`/`…_U`).  This is the
complement-specified constructor that `typePData_of_isTypeNonI` cannot provide (it builds its own
`U`), so it lets the §16 `Section16TypePStructure` carry a `TypePData` whose `W₁`/`U` agree with the
maximal-pair factors, unblocking Peterfalvi `basic_structure` (13.2).

All structural fields are discharged through BG §14/15/16 machinery (sorry-free, cited):
`typeP2_mf_internal_fitting_decomposition` (the deep `M′`-complement/Fitting fields) and
`typeP_hall_derived_eq_and_abelian` (`U` abelian, hence nilpotent), fed to
`typePData_of_isTypeP_of_inputs`.  The two structural hypotheses, `K ≤ N_G(U)` and that `U` is the
`(κ∪σ)′`-Hall, are the residual obligations discharged for the canonical pair by
`exists_kappaHall_invariant_complement_to_MF` (`K ≤ N_G(U)`) and
`Peterfalvi.S10Interface.isHall_kappaSigmaCompl_of_isTypeP2_complement` (the `(κ∪σ)′`-Hall property),
bundled in `exists_typePData_W1_eq_of_isTypeP2`. -/
noncomputable def typePData_of_kappaHall_hallComplement {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) (hUM : U ≤ M)
    (hUhall : Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa M ∪ BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G)) :
    TypePData M :=
  -- Term-mode (no `obtain`/`have` casesOn) so the `.W₁ = K`/`.U = U` projections reduce
  -- definitionally past lane-f's tactic-built `typePData_of_isTypeP_of_inputs`
  -- (memory: coupled engine fields + beta).
  let hdec := BG.Ch4.S15.typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hUhall
  let hM'ab := BG.Ch4.S15.typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hUhall
  BG.Ch4.S16.typePData_of_isTypeP_of_inputs hG hM hP2.1 hKM hKne hK
    (le_sup_left.trans_eq hM'ab.1.symm) hKnorm
    (haveI := hM'ab.2; (inferInstance : Group.IsNilpotent ↥U))
    hdec.1 hdec.2.1 hdec.2.2

/-- The chosen cyclic factor: `data.W₁ = K` (definitional). -/
theorem typePData_of_kappaHall_hallComplement_W1 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) (hUM : U ≤ M)
    (hUhall : Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa M ∪ BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G)) :
    (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).W1 = K := by
  unfold typePData_of_kappaHall_hallComplement
    BG.Ch4.S16.typePData_of_isTypeP_of_inputs BG.Ch4.S16.typePData_of_inputs
  rfl

/-- The chosen complement: `data.U = U` (definitional). -/
theorem typePData_of_kappaHall_hallComplement_U {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) (hUM : U ≤ M)
    (hUhall : Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa M ∪ BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G)) :
    (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).U = U := by
  unfold typePData_of_kappaHall_hallComplement
    BG.Ch4.S16.typePData_of_isTypeP_of_inputs BG.Ch4.S16.typePData_of_inputs
  rfl

/-- The dual factor: `data.W2 = K*` (`= M_σ ⊓ C(K)`).  Via the (8.4.b) centralizer law
`C_{M'}(k) = K*` (`typeP_derivedInG_inf_centralizer_kappaElement_eq`) applied to a nonidentity
`k ∈ W₁ = K` (`data.centralizer_W1`).  This reconciles the intrinsic `TypePData.W2` with the
maximal-pair dual factor `mp.Kstar`, discharging the `Sdata.W2 = W2` obligation of §15's
`card_P_eq` / `basic_structure_gated.P_order`. -/
theorem typePData_of_kappaHall_hallComplement_W2 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K U Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) (hUM : U ≤ M)
    (hUhall : Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa M ∪ BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G))
    (hKstar : Kstar = BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).W2 = Kstar := by
  haveI := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  obtain ⟨⟨x, hxK⟩, hxne⟩ := exists_ne (1 : ↥K)
  have hxne' : x ≠ 1 := by rintro rfl; exact hxne rfl
  have hW1 : (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).W1 = K :=
    typePData_of_kappaHall_hallComplement_W1 hG hM hP2 hKM hKne hK hUM hUhall hKnorm
  have hxW1 : x ∈ (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).W1 := by
    rw [hW1]; exact hxK
  have hcen :=
    (typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm).centralizer_W1
      x hxW1 hxne'
  have hkstar :=
    BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq hG hM hP2.1 hKM hK hKstar x hxK hxne'
  exact hcen.symm.trans hkstar

/-- **Matched `TypePData` for a type-`P₂` maximal subgroup** (`sorry`-free; POLE-1 carrier, issue
4008).  Given a type-`P₂` maximal subgroup `M` and a cyclic κ-Hall `K`, the κ-Hall-invariant
complement `U` to `M_F` in `M'` (`exists_kappaHall_invariant_complement_to_MF`, supplying
`K ≤ N_G(U)`) is the `(κ∪σ)'`-Hall (`S10Interface.isHall_kappaSigmaCompl_of_isTypeP2_complement`), so
`typePData_of_kappaHall_hallComplement` produces a `TypePData M` with the **chosen** factor
`data.W₁ = K`.  This is the bridge the §16 producer needs to carry a `TypePData mp.S` whose `W₁` is
the maximal-pair κ-Hall `mp.K` — the last carrier step before Peterfalvi `basic_structure` (13.2),
the residual gate being only that the type-II member `mp.S` of the pair is type-`P₂` (Pf (13.2.a)). -/
theorem exists_typePData_W1_eq_of_isTypeP2 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    ∃ data : TypePData M, data.W1 = K := by
  obtain ⟨U, hUsup, hKnorm, hUinf⟩ :=
    BG.Ch4.S14.exists_kappaHall_invariant_complement_to_MF hG hM hP2.1 hKM hK
  have hUM : U ≤ M := (le_sup_right.trans_eq hUsup.symm).trans (Subgroup.map_subtype_le _)
  have hUhall := Peterfalvi.S10Interface.isHall_kappaSigmaCompl_of_isTypeP2_complement hG hM hP2 hUM hUsup hUinf
  exact ⟨typePData_of_kappaHall_hallComplement hG hM hP2 hKM hKne hK hUM hUhall hKnorm,
    typePData_of_kappaHall_hallComplement_W1 hG hM hP2 hKM hKne hK hUM hUhall hKnorm⟩

/-- **Type-P structure engine from the type data** (`sorry`-free, gated-endpoint skeleton).

Given the Peterfalvi type data (`TypePData`) of both members of the maximal pair, this assembles
the full `Section16TypePStructure` with the pairing factors `W₁ = S`'s cyclic complement,
`W₂ = T`'s cyclic complement, `U, V` the type-data complements, and `W = S ∩ T`.  The fields that
are *intrinsic to a single member* are discharged directly from the type data:

* `S_deriv_eq_PU`/`T_deriv_eq_QV` from `TypePData.derivedInG_eq_fitting_sup_U` (`M' = M_F ⊔ U`);
* `q_prime`/`p_prime` from the supplied primality of `|W₁(S)|`, `|W₁(T)|` (carried by
  `TypePNontrivialCore` for type II–IV);
* the counting identities `|U| = u·c`, `|V| = v·d` by Lagrange (`C = U ∩ C_G(M_F) ≤ U`).

The *genuinely cross-member* facts — that `S ∩ T` is exactly the cyclic product
`W₁(S) × W₁(T)` (BG §16 / Peterfalvi (8.9) pairing), the normalization `W₁ ≤ N_G(U)`
(Peterfalvi (13.1.b), "remark following Def (8.4)"), and the ordering `q < p` — remain explicit
hypotheses.  Discharging them for the canonical pair is the residual obligation of the producer
`section16TypePStructure_of_isMinimalSimpleOdd` (issue 7005). -/
noncomputable def section16TypePStructure_of_components {G : Type*} [Group G] [Finite G]
    {mp : Section16MaximalPair G} (W1 W2 U V : Subgroup G)
    (hSderiv : derivedInG mp.S = maxNilpotentNormalHall mp.S ⊔ U)
    (hTderiv : derivedInG mp.T = maxNilpotentNormalHall mp.T ⊔ V)
    (hVinfQ : maxNilpotentNormalHall mp.T ⊓ V = ⊥)
    (hW2compl : Subgroup.IsComplement' ((derivedInG mp.T).subgroupOf mp.T) (W2.subgroupOf mp.T))
    (hSprime : (Nat.card ↥W1).Prime) (hTprime : (Nat.card ↥W2).Prime)
    (hWjoin : mp.S ⊓ mp.T = W1 ⊔ W2)
    (hWcyc : IsCyclic ↥(mp.S ⊓ mp.T))
    (hbot : W1 ⊓ W2 = ⊥)
    (hcomm : ∀ x ∈ W1, ∀ y ∈ W2, Commute x y)
    (hSnorm : W1 ≤ Subgroup.normalizer (U : Set G))
    (hTnorm : W2 ≤ Subgroup.normalizer (V : Set G))
    (hlt : Nat.card ↥W1 < Nat.card ↥W2)
    (Sd : TypePData mp.S) (hSdU : Sd.U = U) (hSdW1 : Sd.W1 = W1) (hSdW2 : Sd.W2 = W2)
    (hUcomm : IsMulCommutative ↥U) :
    Section16TypePStructure mp where
  W1 := W1
  W2 := W2
  W := mp.S ⊓ mp.T
  U := U
  V := V
  W_eq_inter := rfl
  W_eq_join := hWjoin
  W1_inf_W2_eq_bot := hbot
  W1_commutes_W2 := hcomm
  W_cyclic := hWcyc
  S_deriv_eq_PU := hSderiv
  T_deriv_eq_QV := hTderiv
  V_inf_Q_eq_bot := hVinfQ
  W2_isComplement_T_deriv := hW2compl
  W1_normalizes_U := hSnorm
  W2_normalizes_V := hTnorm
  q := Nat.card ↥W1
  p := Nat.card ↥W2
  q_prime := hSprime
  p_prime := hTprime
  q_eq_card_W1 := rfl
  p_eq_card_W2 := rfl
  u := Nat.card ↥U /
    Nat.card ↥(U ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.S : Set G))
  v := Nat.card ↥V /
    Nat.card ↥(V ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.T : Set G))
  c := Nat.card ↥(U ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.S : Set G))
  d := Nat.card ↥(V ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.T : Set G))
  c_eq_card_C := rfl
  d_eq_card_D := rfl
  card_U_eq_uc := (Nat.div_mul_cancel (Subgroup.card_dvd_of_le inf_le_left)).symm
  card_V_eq_vd := (Nat.div_mul_cancel (Subgroup.card_dvd_of_le inf_le_left)).symm
  q_lt_p := hlt
  Sdata := Sd
  Sdata_U_eq := hSdU
  Sdata_W1_eq := hSdW1
  S_U_commutative := hUcomm
  Sdata_W2_eq := hSdW2

/-- **BG §14 type-P duality producer** — *lane-f* (BG §14 `typeP_duality`).
Given the maximal pair, constructs the cyclic structure `W = W₁W₂`, the complements
`U, V`, the primes `p, q`, and the counting parameters.

In gated-endpoint-skeleton form (issue 7005), with `mp` now carrying the canonical partner
witness: the **W-side** (the pairing `S ∩ T = K × K*` cyclic, `K ⊓ K* = 1`, commuting) is
discharged `sorry`-free from `mp`'s κ-Hall data via `typeP_pair_W_structure` (BG Theorem 14.7).
The single remaining `sorry` is localized to the **U-side residual menu**: the semidirect
complements `U, V` with `M' = M_F ⊔ U` and `K ≤ N_G(U)` (Peterfalvi (13.1.b), "remark following
Def (8.4)"), the primality of `|K|, |K*|` (BG Theorem C(10); type II–IV via the type data,
Type-V via the partner argument), and the ordering `q < p` (Peterfalvi (13.2.a)). -/
noncomputable def section16TypePStructure_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    Section16TypePStructure mp := by
  -- **W-side** from `mp`'s canonical partner witness (`typeP_pair_W_structure`, BG 14.7).  A Hall
  -- `(κ ∪ σ)'`-subgroup `U₀` of `S` (needed only to invoke the lemma) comes from Hall's theorem.
  haveI : IsSolvable ↥mp.S := hG.solvable_of_mem_maximalSubgroups mp.S_maximal
  have hUex : ∃ U₀ : Subgroup G,
      Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa mp.S ∪ BG.Ch3.S10.sigma mp.S)ᶜ)
        (U₀.subgroupOf mp.S) := by
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥mp.S)
      ((BG.Ch4.S14.kappa mp.S ∪ BG.Ch3.S10.sigma mp.S)ᶜ)
    exact ⟨U'.map mp.S.subtype, by
      rw [show (U'.map mp.S.subtype).subgroupOf mp.S = U' from
        Subgroup.comap_map_eq_self_of_injective mp.S.subtype_injective U']
      exact hU'⟩
  have hU₀' := hUex.choose_spec
  obtain ⟨hWjoin, hWcyc, hbot, hcomm⟩ :=
    BG.Ch4.S16.typeP_pair_W_structure hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall mp.Kstar_eq
      hU₀' mp.T_maximal mp.T_typeP mp.S_T_not_conj mp.Kstar_le_T mp.Kstar_hall mp.Z_cyclic mp.K_eq
  -- **Primes** `|K|, |K*|` from **Peterfalvi (10.11)** (`theorem88_caseB_prime_orders`): the
  -- orders of the two factors of the case-(b) cyclic group are prime.  The case-(b) data is built
  -- directly from `mp` (`W₁ = K`, `W₂ = K*`, `W = K ⊔ K*` cyclic).  This delegates the primality —
  -- a Peterfalvi §10–12 character-theoretic fact — to its named home, where it is owned (lane-b).
  -- `K`, `K*` are cyclic as subgroups of the cyclic `Z = K ⊔ K*` (needed below and for the
  -- `typeP_derivedInG_isComplement_kappaHall` instance argument in the case-(b) primality data).
  haveI : IsCyclic ↥(mp.K ⊔ mp.Kstar) := mp.Z_cyclic
  haveI : IsCyclic ↥mp.K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : mp.K ≤ mp.K ⊔ mp.Kstar))
      (Subgroup.inclusion_injective _)
  haveI : IsCyclic ↥mp.Kstar :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_right : mp.Kstar ≤ mp.K ⊔ mp.Kstar))
      (Subgroup.inclusion_injective _)
  have hprimes := Peterfalvi.S12.theorem88_caseB_prime_orders hG
    { S := mp.S, T := mp.T, W1 := mp.K, W2 := mp.Kstar, W := mp.K ⊔ mp.Kstar,
      S_maximal := mp.S_maximal, T_maximal := mp.T_maximal, S_ne_T := mp.S_ne_T,
      W_eq := rfl, W_cyclic := mp.Z_cyclic,
      S_nonI := mp.S_nonI, T_nonI := mp.T_nonI, one_typeII := mp.one_typeII,
      W1_le_S := mp.K_le_S, W2_le_T := mp.Kstar_le_T,
      -- (8.8.b1): the κ-Hall factors complement the derived subgroups —
      -- `typeP_derivedInG_isComplement_kappaHall` (BG Thm 14.7(h), proved + axiom-clean), the
      -- BG↔Peterfalvi identification of BG's `κ(M)`-Hall with Peterfalvi's `W₁(M)`.
      S_compl := BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG mp.S_maximal mp.S_typeP
        mp.K_le_S mp.K_hall,
      T_compl := BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG mp.T_maximal mp.T_typeP
        mp.Kstar_le_T mp.Kstar_hall }
  -- **U-side residual**: the (13.1.b) semidirect complements `U, V` (with `M' = M_F ⊔ U` and
  -- `K ≤ N_G(U)`) and the ordering `q < p`.  A *true*, constructible §13/§14 statement for the
  -- canonical pair (`mp.K`, `mp.Kstar`).
  -- **U-side** from Peterfalvi (13.1.b): the κ-Hall-invariant complement `U` to `M_F` in `M'`
  -- (`exists_kappaHall_invariant_complement_to_MF` = invariant Schur–Zassenhaus, BG §1 Prop 1.5(b)).
  -- The ordering `|K| < |K*|` is carried by the relabelled pair (`mp.K_lt_Kstar`), so the residual
  -- is now fully discharged.
  -- `Section16TypePStructure mp` is `Type`-valued, so we cannot `obtain` the `∃`-witness into the
  -- goal (`Exists.casesOn` only eliminates into `Prop`).  Extract the data with `Exists.choose`.
  have hScompl := BG.Ch4.S14.exists_kappaHall_invariant_complement_to_MF hG
    mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
  have hTcompl := BG.Ch4.S14.exists_kappaHall_invariant_complement_to_MF hG
    mp.T_maximal mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
  -- **S-side `TypePData` carrier** (relane #4, issue 4010): the chosen complement `U = hScompl.choose`
  -- to `M_F` in `S'` is the `(κ∪σ)'`-Hall (`S10Interface.isHall_kappaSigmaCompl_of_isTypeP2_complement`, using
  -- `mp.S_typeP2`), so `typePData_of_kappaHall_hallComplement` produces a `TypePData mp.S` with
  -- `.W₁ = mp.K = W1` and `.U = U`, reconciling the carrier to the structure's factors.
  have hUM : hScompl.choose ≤ mp.S :=
    (le_sup_right.trans_eq hScompl.choose_spec.1.symm).trans (Subgroup.map_subtype_le _)
  have hUhall := Peterfalvi.S10Interface.isHall_kappaSigmaCompl_of_isTypeP2_complement hG mp.S_maximal mp.S_typeP2 hUM
    hScompl.choose_spec.1 hScompl.choose_spec.2.2
  have hKne : mp.K ≠ ⊥ := fun h =>
    BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall (Subgroup.card_eq_one.mpr h)
  exact section16TypePStructure_of_components mp.K mp.Kstar hScompl.choose hTcompl.choose
    hScompl.choose_spec.1 hTcompl.choose_spec.1 hTcompl.choose_spec.2.2
    (BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG mp.T_maximal mp.T_typeP mp.Kstar_le_T
      mp.Kstar_hall)
    hprimes.1 hprimes.2
    hWjoin hWcyc hbot hcomm hScompl.choose_spec.2.1 hTcompl.choose_spec.2.1 mp.K_lt_Kstar
    (typePData_of_kappaHall_hallComplement hG mp.S_maximal mp.S_typeP2 mp.K_le_S hKne mp.K_hall
      hUM hUhall hScompl.choose_spec.2.1)
    (typePData_of_kappaHall_hallComplement_U hG mp.S_maximal mp.S_typeP2 mp.K_le_S hKne mp.K_hall
      hUM hUhall hScompl.choose_spec.2.1)
    (typePData_of_kappaHall_hallComplement_W1 hG mp.S_maximal mp.S_typeP2 mp.K_le_S hKne mp.K_hall
      hUM hUhall hScompl.choose_spec.2.1)
    (typePData_of_kappaHall_hallComplement_W2 hG mp.S_maximal mp.S_typeP2 mp.K_le_S hKne mp.K_hall
      hUM hUhall hScompl.choose_spec.2.1 mp.Kstar_eq)
    (BG.Ch4.S15.typeP_hall_derived_eq_and_abelian hG mp.S_maximal mp.K_le_S hUM hKne mp.K_hall
      hUhall).2

/-- **Certain-type §6 hypothesis from κ-Hall pairing data** — *lane-b* (cd producer building block).

For a type-`P` maximal `M` with cyclic κ-Hall `K` and the dual factor `K* = M_σ ⊓ C(K)` (cyclic,
nontrivial), builds the Peterfalvi §6 certain-type Hypothesis (4.2) with `W₁ = K`, `W₂ = K*`,
`K(§6) = M' = [M,M]`, all transported into `↥M`.  Structural fields are discharged from the
BG §14/§16 type-`P` theory: `M = M' ⋊ K` (`typeP_derivedInG_isComplement_kappaHall`, BG 14.7(h)),
the (4.2.b) centralizer law `C_{M'}(k) = K*` for `k ∈ K#`
(`typeP_derivedInG_inf_centralizer_kappaElement_eq`, BG Thm C / Pf (8.4)), Hall coprimality
(`IsHallSubgroup.coprime_index` with `[M:M'] = |K|`), and `K* ≤ M_σ ≤ M'`.

Unlike `typePData_toS06Hypothesis` (which uses a `TypePData`'s *canonical* `W₁`), this builds the
hypothesis with `W₁ = K` the *chosen pairing factor*, so the resulting `ω`/`μ`-grids are indexed by
`tp.W₁ = mp.K`, `tp.W₂ = mp.Kstar` — exactly the indexing `Section16CharacterData` needs (no
cross-construction `W`-identification).  Applied to `(mp.S; mp.K, mp.Kstar)` and the swapped
`(mp.T; mp.Kstar, mp.K)`, it gives the two members' certain-type machinery for the cd producer. -/
noncomputable def certainTypeHypothesis_of_typeP_kappaHall {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : BG.Ch4.S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKcyc : IsCyclic ↥K) (hKstarcyc : IsCyclic ↥Kstar) (hKstarne : Kstar ≠ ⊥) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥M := by
  haveI := hKcyc
  haveI := hKstarcyc
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hKstarM' : Kstar ≤ derivedInG M := by
    rw [hKstar]; exact inf_le_left.trans (BG.Ch3.S10.Msigma_le_derived hG hM)
  have hKstarM : Kstar ≤ M := hKstarM'.trans hM'le
  have hcompl := BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  have hidx : (K.subgroupOf M).index = Nat.card ↥(derivedInG M) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have hco := hK.coprime_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hidx] at hco
  exact
    { K := (derivedInG M).subgroupOf M
      W1 := K.subgroupOf M
      W2 := Kstar.subgroupOf M
      K_normal := by
        rw [show (derivedInG M).subgroupOf M = commutator ↥M by
          rw [derivedInG, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
        infer_instance
      isComplement := hcompl
      W1_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        intro hdisj
        exact BG.Ch4.S14.card_kappaHall_ne_one hP hKM hK
          (Subgroup.card_eq_one.mpr (disjoint_self.mp (hdisj.mono_right hKM)))
      W1_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hKM).injective
      card_coprime := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
        exact hCop.symm
      W2_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hdisj => hKstarne (disjoint_self.mp (hdisj.mono_right hKstarM))
      W2_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hKstarM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hKstarM).injective
      W2_le_K := Subgroup.comap_mono hKstarM'
      centralizer_W2 := by
        intro x hx1 hx2
        have hxW1 : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx1
        have hxne : (x : G) ≠ 1 := fun h => hx2 (Subtype.ext h)
        have hamb : Subgroup.centralizer ({(x : G)} : Set G) ⊓ derivedInG M = Kstar := by
          rw [inf_comm]
          exact BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq hG hM hP hKM hK hKstar
            (x : G) hxW1 hxne
        rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, Set.image_singleton]
        simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, Subgroup.coe_subtype, hamb]
      W_odd := by
        rw [← Subgroup.subgroupOf_sup hKM hKstarM,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hKM hKstarM)).toEquiv]
        exact hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (K ⊔ Kstar)) }

/-- The cyclic factors `mp.K`, `mp.Kstar` are cyclic (subgroups of the cyclic `Z = K ⊔ K*`). -/
theorem Section16MaximalPair.isCyclic_K {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPair G) : IsCyclic ↥mp.K :=
  haveI : IsCyclic ↥(mp.K ⊔ mp.Kstar) := mp.Z_cyclic
  isCyclic_of_injective (Subgroup.inclusion (le_sup_left : mp.K ≤ mp.K ⊔ mp.Kstar))
    (Subgroup.inclusion_injective _)

/-- The cyclic factors `mp.K`, `mp.Kstar` are cyclic (subgroups of the cyclic `Z = K ⊔ K*`). -/
theorem Section16MaximalPair.isCyclic_Kstar {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPair G) : IsCyclic ↥mp.Kstar :=
  haveI : IsCyclic ↥(mp.K ⊔ mp.Kstar) := mp.Z_cyclic
  isCyclic_of_injective (Subgroup.inclusion (le_sup_right : mp.Kstar ≤ mp.K ⊔ mp.Kstar))
    (Subgroup.inclusion_injective _)

/-- **The S-side §6 certain-type Hypothesis** (cd producer building block): `mp.S` with `W₁ = mp.K`,
`W₂ = mp.Kstar`.  Wires `certainTypeHypothesis_of_typeP_kappaHall` to `mp`'s κ-Hall data
(`mp.K_hall`, `mp.Kstar_eq`); the dual `mp.Kstar ≠ 1` is the κ-Hall nontriviality of `mp.T`. -/
noncomputable def Section16MaximalPair.certainTypeS {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥mp.S :=
  haveI := mp.isCyclic_K
  haveI := mp.isCyclic_Kstar
  certainTypeHypothesis_of_typeP_kappaHall hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
    mp.Kstar_eq inferInstance inferInstance (fun hbot =>
      BG.Ch4.S14.card_kappaHall_ne_one mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
        (Subgroup.card_eq_one.mpr hbot))

/-- **The T-side §6 certain-type Hypothesis** (cd producer building block): `mp.T` with `W₁ = mp.Kstar`,
`W₂ = mp.K` (the roles of the two factors swap for the partner).  The pairing relation `mp.K =
M_σ(T) ⊓ C(mp.Kstar)` is `mp.K_eq`. -/
noncomputable def Section16MaximalPair.certainTypeT {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥mp.T :=
  haveI := mp.isCyclic_K
  haveI := mp.isCyclic_Kstar
  certainTypeHypothesis_of_typeP_kappaHall hG mp.T_maximal mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
    mp.K_eq inferInstance inferInstance (fun hbot =>
      BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall
        (Subgroup.card_eq_one.mpr hbot))

/-- Helper: in a finite group, two complementary subgroups `A`, `B` of a cyclic subgroup `W`
(`A ⊔ B = W`, `A ⊓ B = ⊥`) have `|A|·|B| = |W|`. -/
theorem card_mul_eq_of_disjoint_sup_le_isCyclic {G : Type*} [Group G] [Finite G]
    {W A B : Subgroup G} (hWcyc : IsCyclic ↥W) (hAW : A ≤ W) (hBW : B ≤ W)
    (hsup : A ⊔ B = W) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥A * Nat.card ↥B = Nat.card ↥W := by
  haveI := hWcyc
  letI : CommGroup ↥W := IsCyclic.commGroup
  haveI : (A.subgroupOf W).Normal := inferInstance
  have hinf' : (A.subgroupOf W) ⊓ (B.subgroupOf W) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxA hxB
    have hxAB : (x : G) ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [hinf, Subgroup.mem_bot] at hxAB
    rw [Subgroup.mem_bot]; exact Subtype.ext hxAB
  have hsup' : (A.subgroupOf W) ⊔ (B.subgroupOf W) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAW hBW, hsup, Subgroup.subgroupOf_self]
  have h := Subgroup.card_mul_card_of_complement_normal hinf' hsup'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv,
       Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBW).toEquiv] at h

/-- **W-structure of the canonical maximal pair** (BG Theorem 14.7, via `typeP_pair_W_structure`):
`S ∩ T = K ⊔ K*` is cyclic, `K ⊓ K* = ⊥`, and `K`, `K*` commute.  A Hall `(κ ∪ σ)'`-subgroup of
`S` (needed only to invoke the lemma) comes from Hall's theorem on the solvable `S`. -/
theorem Section16MaximalPair.W_structure {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    mp.S ⊓ mp.T = mp.K ⊔ mp.Kstar ∧ IsCyclic ↥(mp.S ⊓ mp.T) ∧
      mp.K ⊓ mp.Kstar = ⊥ ∧ (∀ x ∈ mp.K, ∀ y ∈ mp.Kstar, Commute x y) := by
  haveI : IsSolvable ↥mp.S := hG.solvable_of_mem_maximalSubgroups mp.S_maximal
  have hUex : ∃ U₀ : Subgroup G,
      Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa mp.S ∪ BG.Ch3.S10.sigma mp.S)ᶜ)
        (U₀.subgroupOf mp.S) := by
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥mp.S)
      ((BG.Ch4.S14.kappa mp.S ∪ BG.Ch3.S10.sigma mp.S)ᶜ)
    exact ⟨U'.map mp.S.subtype, by
      rw [show (U'.map mp.S.subtype).subgroupOf mp.S = U' from
        Subgroup.comap_map_eq_self_of_injective mp.S.subtype_injective U']
      exact hU'⟩
  exact BG.Ch4.S16.typeP_pair_W_structure hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
    mp.Kstar_eq hUex.choose_spec mp.T_maximal mp.T_typeP mp.S_T_not_conj mp.Kstar_le_T
    mp.Kstar_hall mp.Z_cyclic mp.K_eq

/-- **The type-`P` pairing factors are the maximal-pair κ-Hall factors** (`W₁ = mp.K`,
`W₂ = mp.Kstar`) — the cd-grid indexing alignment (HUB 1011, resolved lane-b-internally; no
producer reduction needed).  Both `W₁`/`K` are the unique order-`q` subgroup, and `W₂`/`K*` the
unique order-`p` subgroup, of the cyclic `W = K ⊔ K*` (`eq_of_card_eq_prime_of_isCyclic`); the
orderings `q < p` (`q_lt_p`) and `|K| < |K*|` (`K_lt_Kstar`) match the two labellings. -/
theorem Section16TypePStructure.W1_eq_K_and_W2_eq_Kstar {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) :
    tp.W1 = mp.K ∧ tp.W2 = mp.Kstar := by
  obtain ⟨hWjoin, _, hKbot, _⟩ := mp.W_structure hG
  have hWeq : tp.W = mp.K ⊔ mp.Kstar := tp.W_eq_inter.trans hWjoin
  haveI : IsCyclic ↥tp.W := tp.W_cyclic
  have hKle : mp.K ≤ tp.W := hWeq ▸ le_sup_left
  have hKstarle : mp.Kstar ≤ tp.W := hWeq ▸ le_sup_right
  have hW1le : tp.W1 ≤ tp.W := tp.W_eq_join ▸ le_sup_left
  have hW2le : tp.W2 ≤ tp.W := tp.W_eq_join ▸ le_sup_right
  have hcardW : tp.q * tp.p = Nat.card ↥tp.W := by
    rw [tp.q_eq_card_W1, tp.p_eq_card_W2]
    exact card_mul_eq_of_disjoint_sup_le_isCyclic tp.W_cyclic hW1le hW2le tp.W_eq_join.symm
      tp.W1_inf_W2_eq_bot
  have hcardK : Nat.card ↥mp.K * Nat.card ↥mp.Kstar = Nat.card ↥tp.W :=
    card_mul_eq_of_disjoint_sup_le_isCyclic tp.W_cyclic hKle hKstarle hWeq.symm hKbot
  have hprod : Nat.card ↥mp.K * Nat.card ↥mp.Kstar = tp.q * tp.p := by rw [hcardK, ← hcardW]
  have hKpos : 1 < Nat.card ↥mp.K := by
    have hne := BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall
    have h0 := Nat.card_pos (α := ↥mp.K)
    omega
  -- arithmetic: `|K|·|K*| = q·p`, `|K| < |K*|`, `q < p` prime, `|K| > 1` give `|K| = q`, `|K*| = p`
  have hcardKeq : Nat.card ↥mp.K = tp.q := by
    have hlt : Nat.card ↥mp.K < Nat.card ↥mp.Kstar := mp.K_lt_Kstar
    have hpdvd : tp.p ∣ Nat.card ↥mp.K * Nat.card ↥mp.Kstar := ⟨tp.q, by rw [hprod]; ring⟩
    rcases (tp.p_prime.dvd_mul).mp hpdvd with hpa | hpb
    · exfalso
      have hple : tp.p ≤ Nat.card ↥mp.K := Nat.le_of_dvd (by omega) hpa
      nlinarith [hprod, hlt, hple, tp.q_prime.two_le, tp.q_lt_p]
    · obtain ⟨b'', hb''⟩ := hpb
      have hKb : Nat.card ↥mp.K * b'' = tp.q := by
        have h2 : (Nat.card ↥mp.K * b'') * tp.p = tp.q * tp.p := by
          rw [mul_assoc, mul_comm b'' tp.p, ← hb'', hprod]
        exact Nat.eq_of_mul_eq_mul_right tp.p_prime.pos h2
      rcases (tp.q_prime.eq_one_or_self_of_dvd _ ⟨b'', hKb.symm⟩) with h1 | hq
      · omega
      · exact hq
  have hcardKstareq : Nat.card ↥mp.Kstar = tp.p := by
    have h2 : tp.q * Nat.card ↥mp.Kstar = tp.q * tp.p :=
      calc tp.q * Nat.card ↥mp.Kstar = Nat.card ↥mp.K * Nat.card ↥mp.Kstar := by rw [hcardKeq]
        _ = tp.q * tp.p := hprod
    exact Nat.eq_of_mul_eq_mul_left tp.q_prime.pos h2
  refine ⟨?_, ?_⟩
  · have hW1card : Nat.card ↥(tp.W1.subgroupOf tp.W) = tp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv, ← tp.q_eq_card_W1]
    have hKcard : Nat.card ↥(mp.K.subgroupOf tp.W) = tp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv, hcardKeq]
    have hinf := Subgroup.subgroupOf_inj.1
      (Ch06.eq_of_card_eq_prime_of_isCyclic tp.q_prime hW1card hKcard)
    rwa [inf_of_le_left hW1le, inf_of_le_left hKle] at hinf
  · have hW2card : Nat.card ↥(tp.W2.subgroupOf tp.W) = tp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv, ← tp.p_eq_card_W2]
    have hKstarcard : Nat.card ↥(mp.Kstar.subgroupOf tp.W) = tp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKstarle).toEquiv, hcardKstareq]
    have hinf := Subgroup.subgroupOf_inj.1
      (Ch06.eq_of_card_eq_prime_of_isCyclic tp.p_prime hW2card hKstarcard)
    rwa [inf_of_le_left hW2le, inf_of_le_left hKstarle] at hinf

/-- `W₁ = mp.K` (cd-grid `W₁`-index alignment; HUB 1011). -/
theorem Section16TypePStructure.W1_eq_K {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) : tp.W1 = mp.K :=
  (tp.W1_eq_K_and_W2_eq_Kstar hG).1

/-- `W₂ = mp.Kstar` (cd-grid `W₂`-index alignment; HUB 1011). -/
theorem Section16TypePStructure.W2_eq_Kstar {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) : tp.W2 = mp.Kstar :=
  (tp.W1_eq_K_and_W2_eq_Kstar hG).2

/-- `W = mp.K ⊔ mp.Kstar` — the cd-grid `ω`-codomain identification. -/
theorem Section16TypePStructure.W_eq_kappa_join {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) : tp.W = mp.K ⊔ mp.Kstar :=
  tp.W_eq_inter.trans (mp.W_structure hG).1

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

/-- `W₁` of `certainTypeS` is `mp.K.subgroupOf mp.S` (the κ-Hall factor of `S`). -/
theorem certainTypeS_W1_eq : (mp.certainTypeS hG).W1 = mp.K.subgroupOf mp.S := by
  unfold Section16MaximalPair.certainTypeS certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `W₂` of `certainTypeS` is `mp.Kstar.subgroupOf mp.S` (the dual factor of `S`). -/
theorem certainTypeS_W2_eq : (mp.certainTypeS hG).W2 = mp.Kstar.subgroupOf mp.S := by
  unfold Section16MaximalPair.certainTypeS certainTypeHypothesis_of_typeP_kappaHall; rfl

include hG in
/-- `mp.Kstar ≤ mp.S` (it lies in `S ∩ T = K ⊔ K*`). -/
theorem kstar_le_S : mp.Kstar ≤ mp.S := by
  obtain ⟨hWjoin, -, -, -⟩ := mp.W_structure hG
  have : mp.Kstar ≤ mp.S ⊓ mp.T := by rw [hWjoin]; exact le_sup_right
  exact this.trans inf_le_left

variable (tp : Section16TypePStructure mp)

/-! #### The two §6 Hypothesis instances of `S` share their `W₁`/`W₂` (issue 2038)

The κ-Hall instance `mp.certainTypeS` (grid producer, `muS`) and the `Sdata`-instance
`typePData_toS06Hypothesis tp.Sdata` (the `hypothesis46OfTypePData`/engines side) carry
propositionally equal cyclic factors: `Sdata.W1 = tp.W1 = mp.K` and `Sdata.W2 = tp.W2 =
mp.Kstar`.  These equalities ground the per-`ω` rigidity identification of the two `μ`-grids
(`irreducibleCharacterFamily_eq_of_difference_eq`). -/

/-- `W₁` of the `Sdata`-instance §6 Hypothesis equals `certainTypeS`'s. -/
theorem sdataS06_W1_eq_certainTypeS
    (hHall : Nat.Coprime (Nat.card ↥(OddOrder.GroupTheory.derivedInG mp.S))
      (Nat.card ↥tp.Sdata.W1)) :
    (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W1
      = (mp.certainTypeS hG).W1 := by
  have hlhs : (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W1
      = tp.Sdata.W1.subgroupOf mp.S := by
    unfold OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis; rfl
  rw [hlhs, tp.Sdata_W1_eq, tp.W1_eq_K hG, certainTypeS_W1_eq]

/-- `W₂` of the `Sdata`-instance §6 Hypothesis equals `certainTypeS`'s. -/
theorem sdataS06_W2_eq_certainTypeS
    (hHall : Nat.Coprime (Nat.card ↥(OddOrder.GroupTheory.derivedInG mp.S))
      (Nat.card ↥tp.Sdata.W1)) :
    (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W2
      = (mp.certainTypeS hG).W2 := by
  have hlhs : (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W2
      = tp.Sdata.W2.subgroupOf mp.S := by
    unfold OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis; rfl
  rw [hlhs, tp.Sdata_W2_eq, tp.W2_eq_Kstar hG, certainTypeS_W2_eq]

/-- The joins `W = W₁ ⊔ W₂` of the two §6 Hypothesis instances of `S` coincide. -/
theorem sdataS06_W_join_eq_certainTypeS
    (hHall : Nat.Coprime (Nat.card ↥(OddOrder.GroupTheory.derivedInG mp.S))
      (Nat.card ↥tp.Sdata.W1)) :
    (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W1
        ⊔ (OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis tp.Sdata hG.odd hHall).W2
      = (mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2 := by
  rw [sdataS06_W1_eq_certainTypeS hG mp tp hHall, sdataS06_W2_eq_certainTypeS hG mp tp hHall]

/-- `|certainTypeS.W₁| = tp.q` (both are `|mp.K|`). -/
theorem cardCertainTypeS_W1 : Nat.card ↥(mp.certainTypeS hG).W1 = tp.q := by
  rw [certainTypeS_W1_eq hG mp, Nat.card_congr (Subgroup.subgroupOfEquivOfLe mp.K_le_S).toEquiv,
    ← tp.W1_eq_K hG, ← tp.q_eq_card_W1]

/-- `|certainTypeS.W₂| = tp.p` (both are `|mp.Kstar|`). -/
theorem cardCertainTypeS_W2 : Nat.card ↥(mp.certainTypeS hG).W2 = tp.p := by
  rw [certainTypeS_W2_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (kstar_le_S hG mp)).toEquiv,
    ← tp.W2_eq_Kstar hG, ← tp.p_eq_card_W2]

/-! ### T-side mirror of the S-side identification infrastructure (cd `nu_definition`, step D)

The partner `mp.T` carries the `certain-type` Hypothesis `certainTypeT` with the roles of the two
factors swapped (`W₁ = mp.Kstar`, `W₂ = mp.K`).  These lemmas mirror the S-side
(`certainTypeS_W1_eq`, …, `gridEquivE_mem_W2`) and supply the `↥tp.W ≃* ↥(certainTypeT.sdiff.W)`
transport used to express the same `ω`-grid through `certainTypeT` (the S/T-shared-`ω` symmetry). -/

/-- `W₁` of `certainTypeT` is `mp.Kstar.subgroupOf mp.T` (the κ-Hall factor of `T`; the roles of the
two factors swap for the partner). -/
theorem certainTypeT_W1_eq : (mp.certainTypeT hG).W1 = mp.Kstar.subgroupOf mp.T := by
  unfold Section16MaximalPair.certainTypeT certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `W₂` of `certainTypeT` is `mp.K.subgroupOf mp.T` (the dual factor of `T`). -/
theorem certainTypeT_W2_eq : (mp.certainTypeT hG).W2 = mp.K.subgroupOf mp.T := by
  unfold Section16MaximalPair.certainTypeT certainTypeHypothesis_of_typeP_kappaHall; rfl

include hG in
/-- `mp.K ≤ mp.T` (it lies in `S ∩ T = K ⊔ K*`). -/
theorem k_le_T : mp.K ≤ mp.T := by
  obtain ⟨hWjoin, -, -, -⟩ := mp.W_structure hG
  have : mp.K ≤ mp.S ⊓ mp.T := by rw [hWjoin]; exact le_sup_left
  exact this.trans inf_le_right

/-- `|certainTypeT.W₁| = tp.p` (both are `|mp.Kstar|`). -/
theorem cardCertainTypeT_W1 : Nat.card ↥(mp.certainTypeT hG).W1 = tp.p := by
  rw [certainTypeT_W1_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe mp.Kstar_le_T).toEquiv,
    ← tp.W2_eq_Kstar hG, ← tp.p_eq_card_W2]

/-- `|certainTypeT.W₂| = tp.q` (both are `|mp.K|`). -/
theorem cardCertainTypeT_W2 : Nat.card ↥(mp.certainTypeT hG).W2 = tp.q := by
  rw [certainTypeT_W2_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (k_le_T hG mp)).toEquiv,
    ← tp.W1_eq_K hG, ← tp.q_eq_card_W1]

include hG in
/-- The key subgroup identity (T-side): `tp.W.subgroupOf mp.T = certainTypeT.sdiff.W`.  Both equal
`(mp.Kstar ⊔ mp.K).subgroupOf mp.T` (`tp.W = mp.K ⊔ mp.Kstar` and `certainTypeT.sdiff.W = W₁ ⊔ W₂`). -/
theorem tpW_subgroupOf_T_eq :
    tp.W.subgroupOf mp.T = (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  show tp.W.subgroupOf mp.T = (mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2
  rw [certainTypeT_W1_eq hG mp, certainTypeT_W2_eq hG mp,
    ← Subgroup.subgroupOf_sup mp.Kstar_le_T (k_le_T hG mp), sup_comm, ← tp.W_eq_kappa_join hG]

/-- The `W`-identification equiv (T-side) `↥tp.W ≃* ↥(certainTypeT.sdiff.W)`: `tp.W ≃ tp.W.subgroupOf
mp.T` then transported along `tpW_subgroupOf_T_eq`.  Mirrors `gridEquivE` with `inf_le_right`. -/
noncomputable def gridEquivE_T :
    ↥tp.W ≃* ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W :=
  (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_right)).symm.trans
    (MulEquiv.subgroupCongr (tpW_subgroupOf_T_eq hG mp tp))

/-- **`gridEquivE_T` preserves the underlying `G`-element** (composite of the element-preserving
`subgroupOfEquivOfLe` and `subgroupCongr`). -/
theorem gridEquivE_T_coe (w : ↥tp.W) :
    (((gridEquivE_T hG mp tp w : ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W) :
        ↥mp.T) : G) = (w : G) := rfl

/-- A `tp.W`-element lying in `mp.Kstar` transports under `gridEquivE_T` into `certainTypeT.W1`
(`= mp.Kstar.subgroupOf mp.T`). -/
theorem gridEquivE_T_mem_W1 (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    gridEquivE_T hG mp tp w ∈ ((mp.certainTypeT hG).W1).subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeT_W1_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_T_coe]
  exact hw

/-- A `tp.W`-element lying in `mp.K` transports under `gridEquivE_T` into `certainTypeT.W2`
(`= mp.K.subgroupOf mp.T`). -/
theorem gridEquivE_T_mem_W2 (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    gridEquivE_T hG mp tp w ∈ ((mp.certainTypeT hG).W2).subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeT_W2_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_T_coe]
  exact hw

/-- `Fin tp.q ≃ Fin |certainTypeS.W₁|`, fixing `0 ↦ 0` (so the (13.1.e) anchor `⟨0, q_prime.pos⟩`
matches `chiColumn`'s distinguished base index). -/
noncomputable def eqQ : Fin tp.q ≃ Fin (Nat.card ↥(mp.certainTypeS hG).W1) :=
  finCongr (cardCertainTypeS_W1 hG mp tp).symm

/-- The base `W₂`-column enumeration `Fin tp.p ≃ Ŵ₂` (Pontryagin: `|Ŵ₂| = |W₂| = tp.p`).  Stated in
the `sdiffTICyclicHypothesis.W₂/W` forms (defeq to `certainTypeS.W₂` / `W₁ ⊔ W₂`) so that both
`chiColumn` and `card_charGroup_subgroupOf` consume it directly.  An arbitrary bijection; the column-`0`
normalization is applied in `chi2enum`. -/
theorem cardChi2CharGroup :
    Nat.card (((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ) = tp.p := by
  rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.card_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W]
  exact cardCertainTypeS_W2 hG mp tp

/-- The `W₂`-column enumeration `Fin tp.p ≃ Ŵ₂`, realized as the **power enumeration** `j ↦ γ^j`
of a fixed generator `γ` of the cyclic dual (`S05.isCyclic_charGroup_subgroupOf` +
`cardCertainTypeS_W2`: `|Ŵ₂| = |W₂| = p`), mirroring the `w1CharEquiv` convention: column `0` is
the trivial character (`chi2enum_zero`, the `j = 0` base of the `nu_definition` T-side
difference), and column negation is character inversion (`chi2enum_finNeg`) — the honest (3.9.a)
grid pairing (issue 3002).  The `muS_definition` proof fixes the column `j` and is invariant
under the choice of column enumeration. -/
noncomputable def chi2enum :
    Fin tp.p ≃ (((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ) := by
  haveI := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  exact OddOrder.Peterfalvi.S06.cyclicPowEnum (cardChi2CharGroup hG mp tp)

/-- The normalized column enumeration sends column `0` to the trivial character (Peterfalvi's
column-`0` convention; the `j = 0` base of `nu_definition`). -/
@[simp] theorem chi2enum_zero : chi2enum hG mp tp ⟨0, tp.p_prime.pos⟩ = 1 := by
  haveI := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  rw [chi2enum, OddOrder.Peterfalvi.S06.cyclicPowEnum_apply]
  simp

/-- **Column negation is character inversion** (Peterfalvi (3.5)/(3.9.a) power-grid pairing,
`W₂`-column half): `chi2enum ((p − j) % p) = (chi2enum j)⁻¹`. -/
theorem chi2enum_finNeg (j : Fin tp.p) :
    chi2enum hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (chi2enum hG mp tp j)⁻¹ := by
  haveI := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  rw [chi2enum]
  refine OddOrder.Peterfalvi.S06.cyclicPowEnum_eq_inv_of_add_mod_eq_zero _ ?_
  show ((tp.p - (j : ℕ)) % tp.p + (j : ℕ)) % tp.p = 0
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
  · simp [h0]
  · have hj : (j : ℕ) < tp.p := j.2
    rw [Nat.mod_eq_of_lt (by omega : tp.p - (j : ℕ) < tp.p),
      Nat.sub_add_cancel hj.le, Nat.mod_self]

include hG in
/-- The key subgroup identity: `tp.W.subgroupOf mp.S = certainTypeS.sdiff.W`.  Both equal
`(mp.K ⊔ mp.Kstar).subgroupOf mp.S` (`tp.W = mp.K ⊔ mp.Kstar` and `certainTypeS.sdiff.W = W₁ ⊔ W₂`). -/
theorem tpW_subgroupOf_eq :
    tp.W.subgroupOf mp.S = (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  show tp.W.subgroupOf mp.S = (mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2
  rw [certainTypeS_W1_eq hG mp, certainTypeS_W2_eq hG mp,
    ← Subgroup.subgroupOf_sup mp.K_le_S (kstar_le_S hG mp), tp.W_eq_kappa_join hG]

/-- The `W`-identification equiv `↥tp.W ≃* ↥(certainTypeS.sdiff.W)`: `tp.W ≃ tp.W.subgroupOf mp.S`
then transported along `tpW_subgroupOf_eq`.  The `≤` proof is the *same term* as in
`Section16CharacterData.mu_definition`. -/
noncomputable def gridEquivE :
    ↥tp.W ≃* ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W :=
  (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).symm.trans
    (MulEquiv.subgroupCongr (tpW_subgroupOf_eq hG mp tp))

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

/-- S-side `ω`-grid: the `certainTypeS` `chiColumn` transported to `↥tp.W`. -/
noncomputable def omegaS (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥tp.W ℂ :=
  ClassFunction.compHom (gridEquivE hG mp tp).toMonoidHom
    ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp i) :
      ClassFunction ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W ℂ)

/-- S-side `μ`-grid: the (4.3.b) certain-type characters of `certainTypeS`. -/
noncomputable def muS (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥mp.S ℂ :=
  (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).mu (eqQ hG mp tp i) :
    ClassFunction ↥mp.S ℂ)

/-- S-side signs `δ`. -/
noncomputable def deltaS (j : Fin tp.p) : ℤ :=
  ((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).sign

/-- The `eqQ` reindex fixes the base index `0`. -/
theorem eqQ_zero : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
  apply Fin.ext; simp [eqQ]

/-- **The S-side (13.1.e) `mu_definition` identity** — the cd producer's `mu_definition` field for the
S-side grid.  Inducing the transported `ω`-column difference `Ind_W^S(ω_{ij} − ω_{0j})` gives the
signed `μ`-difference `δ_j (μ_{ij} − μ_{0j})`, via `S06.induce_chiColumn_diff_mu_diff` after the
`compHom`/`subgroupCongr` transport collapse. -/
theorem muS_definition (i : Fin tp.q) (j : Fin tp.p) :
    ClassFunction.induce (tp.W.subgroupOf mp.S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omegaS hG mp tp i j - omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j))
      = (deltaS hG mp tp j : ℂ) • (muS hG mp tp i j - muS hG mp tp ⟨0, tp.q_prime.pos⟩ j) := by
  have key : ∀ k : Fin tp.q,
      ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omegaS hG mp tp k j)
        = ClassFunction.compHom (MulEquiv.subgroupCongr (tpW_subgroupOf_eq hG mp tp)).toMonoidHom
            ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp k) :
              ClassFunction ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W ℂ) := by
    intro k
    rw [omegaS, ClassFunction.compHom_comp]
    congr 1
  rw [ClassFunction.compHom_sub, key i, key ⟨0, tp.q_prime.pos⟩, ← ClassFunction.compHom_sub,
    eqQ_zero hG mp tp, induce_compHom_subgroupCongr (tpW_subgroupOf_eq hG mp tp)]
  simp only [deltaS, muS, eqQ_zero hG mp tp, Int.cast_smul_eq_zsmul]
  exact (mp.certainTypeS hG).induce_chiColumn_diff_mu_diff (chi2enum hG mp tp j) (eqQ hG mp tp i)

/-- **A linear character of `↥tp.W` is determined by its restrictions to `tp.W1` and `tp.W2`.**
Since `tp.W = tp.W1 ⊔ tp.W2` is an internal product of two commuting subgroups, every `w : ↥tp.W`
factors as `w = a * b` with `a ∈ tp.W1`, `b ∈ tp.W2`; two monoid homs agreeing on `tp.W1` and `tp.W2`
therefore agree everywhere.  This is the generating-set half of the S/T-shared-`ω` symmetry. -/
theorem monoidHom_eq_of_eqOn_W1_W2 {χ χ' : ↥tp.W →* ℂˣ}
    (h1 : ∀ w : ↥tp.W, (w : G) ∈ tp.W1 → χ w = χ' w)
    (h2 : ∀ w : ↥tp.W, (w : G) ∈ tp.W2 → χ w = χ' w) :
    χ = χ' := by
  haveI := tp.W_cyclic
  letI : CommGroup ↥tp.W := IsCyclic.commGroup
  have hW1le : tp.W1 ≤ tp.W := by rw [tp.W_eq_join]; exact le_sup_left
  have hW2le : tp.W2 ≤ tp.W := by rw [tp.W_eq_join]; exact le_sup_right
  have htop : (tp.W1.subgroupOf tp.W) ⊔ (tp.W2.subgroupOf tp.W) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← tp.W_eq_join, Subgroup.subgroupOf_self]
  ext w
  have hmem : w ∈ (tp.W1.subgroupOf tp.W) ⊔ (tp.W2.subgroupOf tp.W) := htop ▸ Subgroup.mem_top w
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [← hab, map_mul, map_mul, h1 a (Subgroup.mem_subgroupOf.mp ha),
    h2 b (Subgroup.mem_subgroupOf.mp hb)]

/-- **`gridEquivE` preserves the underlying `G`-element.**  It is the composite of the
element-preserving subgroup equivs `subgroupOfEquivOfLe` and `subgroupCongr`, so transporting
`w : ↥tp.W` into `certainTypeS`'s `W` does not move the ambient group element. -/
theorem gridEquivE_coe (w : ↥tp.W) :
    (((gridEquivE hG mp tp w : ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W) :
        ↥mp.S) : G) = (w : G) := rfl

/-- A `tp.W`-element lying in `mp.K` transports under `gridEquivE` into `certainTypeS.W1`
(`= mp.K.subgroupOf mp.S`). -/
theorem gridEquivE_mem_W1 (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    gridEquivE hG mp tp w ∈ ((mp.certainTypeS hG).W1).subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeS_W1_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_coe]
  exact hw

/-- A `tp.W`-element lying in `mp.Kstar` transports under `gridEquivE` into `certainTypeS.W2`
(`= mp.Kstar.subgroupOf mp.S`). -/
theorem gridEquivE_mem_W2 (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    gridEquivE hG mp tp w ∈ ((mp.certainTypeS hG).W2).subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeS_W2_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_coe]
  exact hw

/-- **Value of `certainTypeS`'s product character on a transported `mp.K`-element**: only the
`W₁`-factor `a` survives (`wFst` is the identity, `wSnd` is trivial, on a `W₁`-element).  This is the
`tp.W1`-restriction value used (with its `tp.W2` mirror) to discharge the S/T-shared-`ω` symmetry on
the generators via `monoidHom_eq_of_eqOn_W1_W2`. -/
theorem omegaProdCharS_apply_mem_K
    (a : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE hG mp tp w)
      = a ⟨gridEquivE hG mp tp w, gridEquivE_mem_W1 hG mp tp w hw⟩ := by
  have mem := gridEquivE_mem_W1 hG mp tp w hw
  have hfst : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst (gridEquivE hG mp tp w)
      = ⟨gridEquivE hG mp tp w, mem⟩ :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst_W1_subtype ⟨gridEquivE hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd (gridEquivE hG mp tp w) = 1 :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd_W1_subtype ⟨gridEquivE hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, mul_one]

/-- **Value of `certainTypeS`'s product character on a transported `mp.Kstar`-element**: only the
`W₂`-factor `b` survives.  The `tp.W2`-restriction mirror of `omegaProdCharS_apply_mem_K`. -/
theorem omegaProdCharS_apply_mem_Kstar
    (a : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE hG mp tp w)
      = b ⟨gridEquivE hG mp tp w, gridEquivE_mem_W2 hG mp tp w hw⟩ := by
  have mem := gridEquivE_mem_W2 hG mp tp w hw
  have hfst : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst (gridEquivE hG mp tp w) = 1 :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst_W2_subtype ⟨gridEquivE hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd (gridEquivE hG mp tp w)
      = ⟨gridEquivE hG mp tp w, mem⟩ :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨gridEquivE hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, one_mul]

/-- **Value of `certainTypeT`'s product character on a transported `mp.K`-element**: since `mp.K` is
the `W₂`-factor of `T`, only the `W₂`-factor `b` survives.  The T-side mirror of
`omegaProdCharS_apply_mem_Kstar`. -/
theorem omegaProdCharT_apply_mem_K
    (a : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE_T hG mp tp w)
      = b ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W2 hG mp tp w hw⟩ := by
  have mem := gridEquivE_T_mem_W2 hG mp tp w hw
  have hfst : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst (gridEquivE_T hG mp tp w) = 1 :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst_W2_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd (gridEquivE_T hG mp tp w)
      = ⟨gridEquivE_T hG mp tp w, mem⟩ :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, one_mul]

/-- **Value of `certainTypeT`'s product character on a transported `mp.Kstar`-element**: since
`mp.Kstar` is the `W₁`-factor of `T`, only the `W₁`-factor `a` survives.  The T-side mirror of
`omegaProdCharS_apply_mem_K`. -/
theorem omegaProdCharT_apply_mem_Kstar
    (a : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE_T hG mp tp w)
      = a ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W1 hG mp tp w hw⟩ := by
  have mem := gridEquivE_T_mem_W1 hG mp tp w hw
  have hfst : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst (gridEquivE_T hG mp tp w)
      = ⟨gridEquivE_T hG mp tp w, mem⟩ :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst_W1_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd (gridEquivE_T hG mp tp w) = 1 :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd_W1_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, mul_one]

end Section16CharacterData
end
end OddOrder
