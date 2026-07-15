import OddOrder.Peterfalvi.S15_SAndT_Setup.HypothesisBasics

/-!
# Machinery135

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT_Setup.DegreesFirstSplit` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Peterfalvi (13.3)-(13.5) — character degrees, first case split, generic alpha

Split from the former monolithic `OddOrder.Peterfalvi.S15_SAndT_Setup` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


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
  /-- **Peterfalvi (4.1)+(5.3.b): the `η`-grid is orthogonal to the τ₁-image of the
  *irreducibly*-induced family** (issue 2034; honest scope 2026-07-13, issue 2035 更新 #19): the
  coherence extension of an **irreducible** `H`-induced member lands in the orthogonal complement
  of the `σ`-image grid (the member's `R`-family is a Dade-difference pair, orthogonal to the
  grid).  With the (3.2.d) completeness (`vanish_of_inner_eta_eq_zero`) this forces `λ^{τ₁}` to
  vanish on the regular set `Ŵ` (`lambda_tau1_apply_mul_eq_zero`).

  ⚠ The irreducibility hypothesis on `Ind θ` is **load-bearing**: for a *reducible* induction —
  a `μ`-column sum, (13.3.a) — the (13.3.c) formula sends `τ₁(μ_j)` *into* the grid
  (`mu_tau1_formula`, `mu_col_tau1_eta_col_one`), so the unrestricted statement contradicts the
  other fields and made this structure uninhabitable. -/
  tau1S_induce_inner_eta :
    haveI := hyp.finiteG
    ∀ (i : Fin hyp.q) (j : Fin hyp.p) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) →
      ClassFunction.inner (hyp.eta i j)
        (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0
  /-- **Peterfalvi (4.1)+(5.3.b), the grid column `0`** (issue 2035 更新 #19): against the
  *trivial-column* grid entries `η_{i0}`, the τ₁-image of **every** `H`-induced member is
  orthogonal — irreducible members by the field above, reducible members because their images
  are (signed) *nonzero-column* sums (`mu_tau1_formula`), orthogonal to column `0`.  This is the
  `θ`-uniform form the (7.7) `η₁₀`-coefficient computations consume. -/
  tau1S_induce_inner_eta_col_zero :
    haveI := hyp.finiteG
    ∀ (i : Fin hyp.q) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ClassFunction.inner (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
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

open scoped FiniteInduce in
/-- **The λ-free core of Peterfalvi (13.3)** (issue 9094 RULING 案 A + issue 2035 更新 #22): the
`τ₁`-maps and the unconditionally-available (13.3.a/c) facts, **without** the λ-cluster (which is
conditional on `𝒮` containing an irreducible `uq`-degree `PC`-induced member — Pf (13.3.b) is a
dichotomy).  Mirrors Coq `PFsection13`'s factoring: the λ-free Section `Thirteen_2_3_5_to_9`
exports these unconditionally, the λ-facts are `Variable`-scoped.

The τ₁-fields carry the **`P ⊄ Ker` guards** (2035 更新 #22): the coherence `IsCoherent` pins
`τ₁` only on `ℤ[𝒮]`, and `Ind_{PC}^S θ ∈ ℤ[𝒮]` requires `P ⊄ Ker θ` ((1.5.a)); Peterfalvi's
(13.5) proof converts `τ₁ ↔ Ind_S^G` only on such `𝒮₁`-members, the `P`-kernel side staying
inside the unknown `α` of (13.5.a).  The unconditional-in-`θ` shapes of the legacy
`CharacterDegreeData` fields are *not suppliable* from the (9.11) coherence.  The `μ`-fields
carry the matching `P ⊄ Ker` **witness** (`mu_j_isIndPC_not_ker`: `μ_j ∈ 𝒮₁`), which is what the
(13.5)-consumers thread into the guards. -/
structure CharacterDegreeCore (hyp : Hypothesis (G := G)) where
  tau1S : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G
  tau1T : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G
  /-- **(13.2.e)+(7.2), τ₁-extension semantics** on `𝒮₁`-differences: `τ₁` agrees with
  `Ind_S^G` on zero-degree differences of `P`-nonkernel `H`-induced irreducibles. -/
  tau1S_apply_induce_sub :
    haveI := hyp.finiteG
    ∀ θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ' →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ') →
      tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
          - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
        = ClassFunction.induce hyp.S
            (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
              - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
  /-- **The τ₁ coherence isometry on the `𝒮₁`-family**. -/
  tau1S_inner_induce :
    haveI := hyp.finiteG
    ∀ θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ' →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ') →
      ClassFunction.inner (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
          (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
        = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
            (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
  /-- **τ₁ sends `𝒮₁`-members to virtual characters**. -/
  tau1S_induce_mem_ZIrr :
    haveI := hyp.finiteG
    ∀ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G
  /-- **(4.1)+(5.3.b): grid orthogonality of τ₁-images of *irreducibly*-induced `𝒮₁`-members**. -/
  tau1S_induce_inner_eta :
    haveI := hyp.finiteG
    ∀ (i : Fin hyp.q) (j : Fin hyp.p) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) →
      ClassFunction.inner (hyp.eta i j)
        (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0
  /-- **(4.1)+(5.3.b)+(13.3.c): column-`0` orthogonality for *every* `𝒮₁`-member** (irreducible
  or `μ`-column). -/
  tau1S_induce_inner_eta_col_zero :
    haveI := hyp.finiteG
    ∀ (i : Fin hyp.q) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ClassFunction.inner (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
        (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0
  /-- **(13.3.a)+(13.3.c), the distinguished `μ`-column** with the `𝒮₁`-membership witness. -/
  mu_col_tau1_eta_col_one :
    haveI := hyp.finiteG
    ∃ (j : Fin hyp.p) (δ : ℤ) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      j ≠ ⟨0, hyp.p_prime.pos⟩ ∧
      (δ = 1 ∨ δ = -1) ∧
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) ∧
      (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
      tau1S (∑ i : Fin hyp.q, hyp.mu i j)
        = (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩
  /-- **(13.3.a) with the `𝒮₁`-witness**: every nonzero column sum is induced from a linear
  character of `H = PC` with `P ⊄ Ker`. -/
  mu_j_linear_induced :
    haveI := hyp.finiteG
    ∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
          ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
              Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
            OddOrder.Peterfalvi.S03.characterKernel θ) ∧
          (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
  /-- **(13.3.c), the `S`-side signs**: the `δ_j` are all `1`.

  δ′-half (`∀ i, hyp.deltaPrime i = 1`) は consumer 0 (issue 2035 #92 実測) につき
  restate-drop; 供給は `deltaPrime_eq_one_T` (`S15_CharacterDegreeEnginesSSide`) に残存、
  T-mirror 消費者が現れたら field として再追加する. -/
  delta_eq_one : ∀ j : Fin hyp.p, hyp.delta j = 1
  /-- **(13.3.c)**: the `τ₁`-images of the nonzero column sums are the `η`-column sums. -/
  mu_tau1_formula :
    (∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      tau1S (∑ i : Fin hyp.q, hyp.mu i j) = ∑ i : Fin hyp.q, hyp.eta i j) ∨
    (hyp.p = 3 ∧ ∀ j j' : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      j' ≠ ⟨0, hyp.p_prime.pos⟩ → j ≠ j' →
      tau1S (∑ i : Fin hyp.q, hyp.mu i j) = -∑ i : Fin hyp.q, hyp.eta i j')

open scoped FiniteInduce in
/-- **The λ-cluster of Peterfalvi (13.3.b)** (issue 9094 RULING 案 A): the distinguished
irreducible `λ ∈ Irr S` of degree `uq` induced from a linear character of `H = PC` with
`P ⊄ Ker` — the data whose existence is the *conditional* branch of the (13.3.b) dichotomy
("if `𝒮` contains no such character, then (9.7.b) holds with `C = 1`,
`u = (p^q−1)/(p−1)`").  Mirrors Coq's `Variable lambda … Hypotheses (Slam) (irrHlam)`
(`PFsection13:961-962`, Section `Thirteen_10_to_13_15`).  The maps and their (13.3) facts live
in the λ-free `CharacterDegreeCore`. -/
structure LambdaClusterData (hyp : Hypothesis (G := G)) where
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

/-- **Peterfalvi (13.3)**: the `mu_j` have degree `u q`, the signs are `1`,
and the `tau_1` images are controlled by the `eta_ij` grid.

⚠ **Deprecation (issue 9094 RULING 案 A)**: the unconditional λ-cluster of `CharacterDegreeData`
is a Pf (13.3.b) *dichotomy* overstatement, and the unguarded τ₁-fields are not suppliable
(issue 2035 更新 #20/#22).  New consumers should use the λ-free `CharacterDegreeCore` (producer
`characterDegreeCore_nonempty`) and the conditional/dichotomy producers
(`S15_CharacterDegreeSupply`).  This producer is kept signature-stable until the consumer
migration completes (9094 移行手順 §3). -/
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

open scoped FiniteInduce in
/-- **The `μ`-column sum has squared norm `q`** (issue 2035, (13.3.c) pin step 2): the reducible
prime-TI character `μ_j = ∑_i μ_{ij}` is a sum of `q` orthonormal irreducibles (`mu_orthonormal`),
so `⟨μ_j, μ_j⟩ = q`.  Through the coherence isometry (`extension_inner_eq`) this pins
`‖τ₁ μ_j‖² = q`, one of the two positive-definiteness inputs of the (13.3.c) column pin. -/
theorem Hypothesis.muColumn_inner_self [Finite G] (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i j) (∑ i : Fin hyp.q, hyp.mu i j)
      = (hyp.q : ℂ) := by
  rw [OddOrder.RepresentationTheory.inner_sum_left]
  have hrow : ∀ i : Fin hyp.q,
      ClassFunction.inner (hyp.mu i j) (∑ k : Fin hyp.q, hyp.mu k j) = (1 : ℂ) := by
    intro i
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_single i
        (fun k _ hki => by rw [hyp.mu_orthonormal i k j j, if_neg (fun h => hki h.1.symm)])
        (fun h => absurd (Finset.mem_univ i) h),
      hyp.mu_orthonormal i i j j]
    simp
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

open scoped FiniteInduce in
/-- **The `η`-column sum has squared norm `q`** (issue 2035, (13.3.c) pin step 1): the aligned
grid column `∑_i η_{ij}` is a sum of `q` orthonormal virtual characters (`eta_orthonormal`), so
`⟨∑_i η_{ij}, ∑_i η_{ij}⟩ = q`.  The other positive-definiteness input of the (13.3.c) column
pin `τ₁ μ_j = δ_j·∑_i η_{ij}`. -/
theorem Hypothesis.etaColumn_inner_self [Finite G] (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ClassFunction.inner (∑ i : Fin hyp.q, hyp.eta i j) (∑ i : Fin hyp.q, hyp.eta i j)
      = (hyp.q : ℂ) := by
  rw [OddOrder.RepresentationTheory.inner_sum_left]
  have hrow : ∀ i : Fin hyp.q,
      ClassFunction.inner (hyp.eta i j) (∑ k : Fin hyp.q, hyp.eta k j) = (1 : ℂ) := by
    intro i
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_single i
        (fun k _ hki => by rw [hyp.eta_orthonormal i k j j, if_neg (fun h => hki h.1.symm)])
        (fun h => absurd (Finset.mem_univ i) h),
      hyp.eta_orthonormal i i j j]
    simp
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **Positive-definiteness pin** (issue 2035, (13.3.c) pin step 4): two class functions with the
same squared norm `n` and cross inner product `⟨x, y⟩ = n` (a real value, `star n = n`) are equal.
The bilinear expansion gives `‖x − y‖² = ⟨x,x⟩ − ⟨x,y⟩ − ⟨y,x⟩ + ⟨y,y⟩ = n − n − n + n = 0`
(using `⟨y,x⟩ = star⟨x,y⟩ = n`), and positive-definiteness (`eq_zero_of_inner_self_re_eq_zero`)
forces `x = y`.  Combined with `muColumn_inner_self`/`etaColumn_inner_self` and the coherence
isometry, this reduces the (13.3.c) column pin `τ₁ μ_j = δ_j·∑_i η_{ij}` to the single cross
inner product `⟨τ₁ μ_j, δ_j·∑_i η_{ij}⟩ = q`. -/
theorem inner_pin_eq [Fintype G] [Invertible (Nat.card G : ℂ)] {x y : ClassFunction G ℂ} {n : ℂ}
    (hxx : ClassFunction.inner x x = n) (hyy : ClassFunction.inner y y = n)
    (hxy : ClassFunction.inner x y = n) (hn : star n = n) : x = y := by
  have hyx : ClassFunction.inner y x = n := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm x y, hxy, hn]
  have hzero : ClassFunction.inner (x - y) (x - y) = 0 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hxx, hyy, hxy, hyx]
    ring
  have hsub : x - y = 0 :=
    OddOrder.RepresentationTheory.eq_zero_of_inner_self_re_eq_zero (by rw [hzero]; simp)
  exact sub_eq_zero.mp hsub

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
    push Not at hneg
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
    · push Not at h
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
TI-subset with normalizer `N_G(F(S)) = S` — BG (15.7)(a), through the type-uniform
`S13.fittingIsTI_of_isTypeNonI`, with
`normalizer_fittingInAmbient_eq_self` pinning the bound to `S`.
Rewriting `H^# = F(S)^#` closes it. -/
theorem H_sharp_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S := by
  have hHF : hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := hyp.H_eq_fittingInG
  have hTI : OddOrder.BG.Ch4.S15.FittingIsTI hyp.S :=
    OddOrder.Peterfalvi.S13.fittingIsTI_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
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

end GenericAlpha
end OddOrder.Peterfalvi.S15
