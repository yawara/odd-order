import OddOrder.BG.AppC_FinalContradiction

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
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥W G
  mu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, q_prime.pos⟩ j)
  nu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, p_prime.pos⟩)
  q_lt_p : q < p

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
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥tp.W G
  mu_definition : ∀ (i : Fin tp.q) (j : Fin tp.p),
    ClassFunction.induce (tp.W.subgroupOf mp.S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, tp.q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, tp.q_prime.pos⟩ j)
  nu_definition : ∀ (i : Fin tp.q) (j : Fin tp.p),
    ClassFunction.induce (tp.W.subgroupOf mp.T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq tp.W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, tp.p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, tp.p_prime.pos⟩)

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
    (hG : IsMinimalSimpleOdd G) : Section16MaximalPair G :=
  -- First establish case (b) of (8.8) *as a proposition*: the type-P pair exists.
  -- (`Or`/`Exists` live in `Prop`, so the witnesses must be extracted by choice — the
  -- dichotomy cannot be `rcases`'d directly into the `Type`-valued structure goal.)
  have hex : ∃ S T : Subgroup G,
      S ∈ maximalSubgroups G ∧ T ∈ maximalSubgroups G ∧ S ≠ T ∧
        IsTypeNonI S ∧ IsTypeNonI T ∧ (IsTypeII S ∨ IsTypeII T) ∧
          ∀ M : Subgroup G, M ∈ maximalSubgroups G →
            IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = T) := by
    rcases Peterfalvi.S10.maximalSubgroup_type_dichotomy hG with hAllI | hpair
    · -- Case (a) — every maximal subgroup is Type I — is ruled out by (12.17): its
      -- case-(b) data is a non-Type-I maximal subgroup `cb.S`.
      obtain ⟨cb⟩ := Peterfalvi.S14.theorem88_caseB_holds hG
      exact absurd (hAllI cb.S cb.S_maximal)
        (BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG cb.S_maximal cb.S_nonI)
    · exact hpair
  -- Case (b) holds, so the type-P pair `S, T` is exactly the maximal-pair output.
  have h := hex.choose_spec.choose_spec
  { S := hex.choose
    T := hex.choose_spec.choose
    S_maximal := h.1
    T_maximal := h.2.1
    S_ne_T := h.2.2.1
    S_nonI := h.2.2.2.1
    T_nonI := h.2.2.2.2.1
    one_typeII := h.2.2.2.2.2.1
    theorem88_caseB := h.2.2.2.2.2.2 }

/-- **BG §14 type-P duality producer** (`sorry`) — *lane-f* (BG §14 `typeP_duality`).
Given the maximal pair, constructs the cyclic structure `W = W₁W₂`, the complements
`U, V`, the primes `p, q`, and the counting parameters. -/
noncomputable def section16TypePStructure_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    Section16TypePStructure mp := sorry

/-- **Peterfalvi §13 coherent Dade-grid producer** (`sorry`) — *lane-b*
(Peterfalvi §3–§13 coherent grids).  Given the maximal pair and the type-P
structure, constructs the character grids `ω, μ, ν`, the signs, the integral maps,
and the exceptional-character data with the induction identities. -/
noncomputable def section16CharacterData_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) (tp : Section16TypePStructure mp) :
    Section16CharacterData mp tp := sorry

/-- **Assembly of `Section16Inputs` from the three lane producers** (`sorry`-free).
Each field of `Section16Inputs` is sourced from exactly one of `mp` / `tp` / `cd`;
the character fields unify because `mp.S, mp.T, tp.W, tp.q, tp.p` are the chosen
witnesses. -/
noncomputable def section16Inputs_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : Section16Inputs G :=
  let mp := section16MaximalPair_of_isMinimalSimpleOdd hG
  let tp := section16TypePStructure_of_isMinimalSimpleOdd hG mp
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
    tau3 := cd.tau3
    mu_definition := cd.mu_definition
    nu_definition := cd.nu_definition
    q_lt_p := tp.q_lt_p }

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
      tau3 := inp.tau3
      eta_eq_tau_omega := fun _ _ => rfl
      mu_definition := inp.mu_definition
      nu_definition := inp.nu_definition
      m := 1 - 1 / ((inp.q : ℚ) - 1) - ((inp.q : ℚ) - 1) / (inp.q : ℚ) ^ inp.p +
        1 / (((inp.q : ℚ) - 1) * (inp.q : ℚ) ^ inp.p)
      m_eq := rfl }
  q_lt_p := inp.q_lt_p

/-- **The one remaining upstream obligation.** From a minimal simple group of odd
order, the Bender–Glauberman local analysis (BG §7–§16) together with Peterfalvi's
character theory (Peterfalvi §3–§16) constructs the Section 16 field-normalizer
configuration of Peterfalvi (14.2).

In gated-endpoint-skeleton form: the `sorry`-free `sectionSixteenHypothesis_of_inputs`
already performs the assembly, so the only thing missing is a `Section16Inputs G`
witness — the explicit menu of §7–§16 obligations.  This single `sorry` is what the
whole remaining project targets.

Everything *downstream* of this point is already formalized:
`noMinimalSimpleOdd_of_section16` feeds the configuration into BG Appendix C, which
contradicts the standing inequality `q < p`. -/
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
  noMinimalSimpleOdd_of_section16 hG (sectionSixteenHypothesis_of_isMinimalSimpleOdd hG)

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
group of odd order (`noMinimalSimpleOdd`), the latter currently resting on the
single upstream obligation `sectionSixteenHypothesis_of_isMinimalSimpleOdd`. -/
theorem feitThompson {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    IsSolvable G :=
  feitThompson_of_noMinimalSimpleOdd (fun _ _ _ hG => noMinimalSimpleOdd hG) hodd

end OddOrder
