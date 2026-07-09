import OddOrder.Peterfalvi.S15_SAndT_Setup.HypothesisBasics

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

end OddOrder.Peterfalvi.S15
