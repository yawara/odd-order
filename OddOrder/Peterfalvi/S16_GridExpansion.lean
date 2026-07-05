import OddOrder.Peterfalvi.S15_SAndT_Setup

/-!
# Peterfalvi (3.6)–(3.8): the grid-coefficient theory of the `W`-grid

**Peterfalvi, Character Theory for the Odd Order Theorem, §3 (pp. 15–20), instantiated to
the §13–§16 `η`-grid** (`OddOrder.Peterfalvi.S15.Hypothesis`).

For a class function `φ` of `G` vanishing on the conjugacy saturation of the regular set
`Ŵ = W ∖ (W₁ ∪ W₂)`, the grid coefficients `a_ij = ⟨φ, η_ij⟩` satisfy Peterfalvi's linear
relation and rigidity:

* **(3.7)** `a_ij + a_00 = a_i0 + a_0j` (`inner_eta_grid_relation`): the four-corner
  combination `η_ij + η_00 − η_i0 − η_0j` is supported on `Ŵ^G` (the carried
  `eta_fourcorner_vanish`, with `η_00 = 1_G` by `eta_principal_eq_trivial`), where `φ`
  vanishes, so the inner product collapses.
* **(3.8), the small-support case** (`grid_eq_zero_of_relation_of_card_le_two`): a grid
  `a : Fin q → Fin p → ℂ` satisfying the (3.7) relation with at most `2 < min q p` nonzero
  entries is identically zero.  (Peterfalvi's full trichotomy specialises to case (a): the
  row/column cases (b)/(c) force `≥ min q p ≥ 3` nonzero entries.)
* **(13.19.b)-core** (`inner_eta_eq_zero_of_vanish_of_inner_self_eq_two`): a virtual
  character `φ ∈ ℤ[Irr G]` with `‖φ‖² = 2` vanishing on `Ŵ^G` is orthogonal to the whole
  `η`-grid.  This is the engine behind Peterfalvi (13.19.b) (`ψ^{τ₁} ⊥ η_ij` for coherent
  images of type-I families, applied to `φ = (ψ − ψ̄)^τ`) and hence behind the (14.11.2)/
  (14.16) signed expansions of `β^τ` consumed by `S16_NonExistenceG`.

The `ω`-side principal identities (`omega_principal_eq_trivial`, `eta_principal_eq_trivial`)
live here as well: `ω₀₀ = 1_W` from the issue-2033 grid semantics (`omega_mul` +
row/column-zero trivialities), hence `η₀₀ = τ₃(1_W) = 1_G` by `tau3_trivial`.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-! ## The principal grid entries: `ω₀₀ = 1_W` and `η₀₀ = 1_G` -/

/-- **Peterfalvi (3.3), the trivial grid entry**: `ω₀₀ = 1_W`.  Every `w ∈ W = W₁ ⊔ W₂`
splits as `w = x·y` with `x ∈ W₁`, `y ∈ W₂` (`W` cyclic hence abelian, so the join is the
product), and the row-`0`/column-`0` trivialities (issue-2033 grid semantics) kill both
factors. -/
theorem omega_principal_eq_trivial [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    hyp.omega ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩
      = trivialClassFunction ↥hyp.W := by
  letI := hyp.W_cyclic
  letI : CommGroup ↥hyp.W := IsCyclic.commGroup
  have hW1le : hyp.W1 ≤ hyp.W := by
    rw [hyp.W_eq_join]; exact le_sup_left
  have hW2le : hyp.W2 ≤ hyp.W := by
    rw [hyp.W_eq_join]; exact le_sup_right
  ext w
  have hw : w ∈ (hyp.W1.subgroupOf hyp.W) ⊔ (hyp.W2.subgroupOf hyp.W) := by
    have h1 : (hyp.W1 ⊔ hyp.W2).subgroupOf hyp.W = ⊤ := by
      rw [← hyp.W_eq_join, Subgroup.subgroupOf_self]
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, h1]
    exact Subgroup.mem_top w
  obtain ⟨x, hxmem, y, hymem, hxy⟩ := Subgroup.mem_sup.mp hw
  have hval : hyp.omega ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ w = 1 := by
    rw [← hxy, hyp.omega_mul,
      hyp.omega_row_zero_apply_of_mem_W1 _ x (Subgroup.mem_subgroupOf.mp hxmem),
      hyp.omega_col_zero_apply_of_mem_W2 _ y (Subgroup.mem_subgroupOf.mp hymem),
      one_mul]
  rw [hval, trivialClassFunction_apply]

/-- **Peterfalvi (3.3)/(13.1.d): the principal `η`-entry is the trivial character** —
`η₀₀ = τ₃(ω₀₀) = τ₃(1_W) = 1_G` (`omega_principal_eq_trivial` + `tau3_trivial`), as an
equality of class functions. -/
theorem eta_principal_eq_trivial [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ = trivialClassFunction G := by
  rw [hyp.eta_eq_tau_omega, omega_principal_eq_trivial hyp, hyp.tau3_trivial]

/-- **Peterfalvi (3.3)/(13.1.d), pointwise form**: `η₀₀(g) = 1` for every `g ∈ G`. -/
theorem eta_principal_apply_eq_one [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (g : G) :
    hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ g = 1 := by
  rw [eta_principal_eq_trivial hyp, trivialClassFunction_apply]

/-! ## `η`-grid membership and orthonormality -/

/-- Each `η_ij = τ₃(ω_ij)` is a virtual character of `G` (`tau3_mem_ZIrr` on
`omega_mem_ZIrr`). -/
theorem eta_mem_ZIrr [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin hyp.q) (j : Fin hyp.p) :
    hyp.eta i j ∈ ZIrr G := by
  rw [hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr i j)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The `η`-grid is orthonormal**: `⟨η_ij, η_kl⟩ = δ_{(i,j),(k,l)}`, transported from the
`ω`-grid orthonormality (`omega_orthonormal`) through the `τ₃` isometry (`tau3_isometry`). -/
theorem eta_orthonormal [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i k : Fin hyp.q) (j l : Fin hyp.p) :
    ClassFunction.inner (hyp.eta i j) (hyp.eta k l)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [hyp.eta_eq_tau_omega, hyp.eta_eq_tau_omega,
    hyp.tau3_isometry.inner_eq, hyp.omega_orthonormal]

/-! ## (3.7): the grid-coefficient linear relation -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.7)** (the `(i',j') = (0,0)` instance, which generates the general four-index
relation by arithmetic): for a class function `φ` vanishing on the conjugacy saturation of the
regular set `Ŵ = W ∖ (W₁ ∪ W₂)`,

`⟨φ, η_ij⟩ + ⟨φ, η_00⟩ = ⟨φ, η_i0⟩ + ⟨φ, η_0j⟩`.

The four-corner combination `η_ij + η_00 − η_i0 − η_0j` vanishes off `Ŵ^G`
(`eta_fourcorner_vanish` + `η_00 = 1_G`), while `φ` vanishes on `Ŵ^G`, so every summand of the
inner product dies. -/
theorem inner_eta_grid_relation [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {φ : ClassFunction G ℂ}
    (hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))), φ x = 0)
    (i : Fin hyp.q) (j : Fin hyp.p) :
    ClassFunction.inner φ (hyp.eta i j)
        + ClassFunction.inner φ (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩)
      = ClassFunction.inner φ (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
        + ClassFunction.inner φ (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) := by
  classical
  by_cases hi : i = ⟨0, hyp.q_prime.pos⟩
  · subst hi; ring
  by_cases hj : j = ⟨0, hyp.p_prime.pos⟩
  · subst hj; ring
  -- the four-corner combination, supported on `Ŵ^G`
  have hcombo : ∀ x : G, x ∉ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))) →
      (hyp.eta i j + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩
        - hyp.eta i ⟨0, hyp.p_prime.pos⟩ - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) x = 0 := by
    intro x hx
    have h4 := hyp.eta_fourcorner_vanish i j hi hj x hx
    rw [ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.add_apply,
      eta_principal_apply_eq_one hyp x]
    rw [hyp.eta_eq_tau_omega i j, hyp.eta_eq_tau_omega i ⟨0, hyp.p_prime.pos⟩,
      hyp.eta_eq_tau_omega ⟨0, hyp.q_prime.pos⟩ j]
    linear_combination h4
  -- `⟨φ, c⟩ = 0`: every summand of the inner sum has a vanishing factor
  have hinner : ClassFunction.inner φ
      (hyp.eta i j + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩
        - hyp.eta i ⟨0, hyp.p_prime.pos⟩ - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum]
    have hsum : ClassFunction.innerSum φ
        (hyp.eta i j + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩
          - hyp.eta i ⟨0, hyp.p_prime.pos⟩ - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [ClassFunction.innerSum]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : x ∈ conjClassSet
          ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))
      · rw [hvanish x hx, zero_mul]
      · rw [hcombo x hx, star_zero, mul_zero]
    rw [hsum, mul_zero]
  -- expand by conjugate-linearity in the second argument
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    ClassFunction.inner_add_right] at hinner
  linear_combination hinner

/-! ## (3.8), small-support rigidity: at most two nonzero grid entries force zero -/

/-- **Peterfalvi (3.8), the small-support case** (pure combinatorics): a `q × p` grid `a`
(`3 ≤ q`, `3 ≤ p`) satisfying the (3.7) relation `a_ij + a_{i₀j₀} = a_{ij₀} + a_{i₀j}`
relative to some base point `(i₀, j₀)`, with at most `2` nonzero entries, is identically
zero.  In Peterfalvi's trichotomy the row/column cases (3.8.b)/(3.8.c) force at least
`min q p ≥ 3` nonzero entries, so only case (3.8.a) survives.

The proof mirrors the rank-one shift structure: an all-zero row exists (else every row
contributes a nonzero entry, `NC ≥ q ≥ 3`), which makes every row constant
(`a_ij = a_{ij₀} − a_{i₁j₀}`); a row with nonzero constant would contribute `p ≥ 3` nonzero
entries. -/
theorem grid_eq_zero_of_relation_of_card_le_two {q p : ℕ} (hq : 3 ≤ q) (hp : 3 ≤ p)
    {a : Fin q → Fin p → ℂ} (i0 : Fin q) (j0 : Fin p)
    (hrel : ∀ i j, a i j + a i0 j0 = a i j0 + a i0 j)
    (hNC : (Finset.univ.filter fun x : Fin q × Fin p => a x.1 x.2 ≠ 0).card ≤ 2) :
    ∀ i j, a i j = 0 := by
  classical
  set S : Finset (Fin q × Fin p) :=
    Finset.univ.filter fun x : Fin q × Fin p => a x.1 x.2 ≠ 0 with hS
  -- an all-zero row exists
  have hrow : ∃ i₁ : Fin q, ∀ j, a i₁ j = 0 := by
    by_contra hno
    push Not at hno
    choose f hf using hno
    have hcard : q ≤ S.card := by
      have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin q)),
          ((i, f i) : Fin q × Fin p) ∈ S := fun i _ =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf i⟩
      have := Finset.card_le_card_of_injOn
        (fun i : Fin q => ((i, f i) : Fin q × Fin p)) hmaps
        (fun i _ i' _ h => (Prod.ext_iff.mp h).1)
      simpa using this
    omega
  obtain ⟨i₁, hi₁⟩ := hrow
  -- every row is constant: `a i j = a i j₀ − a i₁ j₀`
  have hconst : ∀ i j, a i j = a i j0 - a i₁ j0 := by
    intro i j
    have h1 := hrel i j
    have h2 := hrel i₁ j
    rw [hi₁ j] at h2
    linear_combination h1 - h2
  -- a row with nonzero constant contributes `p ≥ 3` nonzero entries
  intro i j
  rw [hconst i j]
  by_contra hne
  have hcard : p ≤ S.card := by
    have hmaps : ∀ j' ∈ (Finset.univ : Finset (Fin p)),
        ((i, j') : Fin q × Fin p) ∈ S := fun j' _ =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hconst i j']; exact hne⟩
    have := Finset.card_le_card_of_injOn
      (fun j' : Fin p => ((i, j') : Fin q × Fin p)) hmaps
      (fun j' _ j'' _ h => (Prod.ext_iff.mp h).2)
    simpa using this
  omega

/-! ## The (13.19.b)-core engine: small norm forces grid orthogonality -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.b)-core** ((3.8) applied through Bessel): a virtual character
`φ ∈ ℤ[Irr G]` with `⟨φ, φ⟩ = 2` vanishing on the conjugacy saturation of the regular set
`Ŵ = W ∖ (W₁ ∪ W₂)` is orthogonal to the entire `η`-grid.

This is Peterfalvi's `NC(ψ) ≤ ‖ψ‖² = 2 < 2q` step: the grid coefficients
`a_ij = ⟨φ, η_ij⟩` are integers (`inner_mem_ZIrr_int`), the orthogonal projection onto the
(orthonormal) grid satisfies Bessel `∑ a_ij² ≤ ⟨φ, φ⟩ = 2`, so at most two coefficients are
nonzero; the (3.7) relation (`inner_eta_grid_relation`) then forces all of them to vanish
(`grid_eq_zero_of_relation_of_card_le_two`, using `3 ≤ q` and `3 ≤ p`).

Consumed with `φ = (ψ − ψ̄)^τ` for an irreducible `ψ` of a type-I family (Peterfalvi
(13.19.b), the `L^{τ₁} ⊥ η_ij` fact behind the (14.11.2)/(14.16) signed expansions). -/
theorem inner_eta_eq_zero_of_vanish_of_inner_self_eq_two [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) {φ : ClassFunction G ℂ}
    (hφZ : φ ∈ ZIrr G)
    (hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))), φ x = 0)
    (hnorm : ClassFunction.inner φ φ = 2) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner φ (hyp.eta i j) = 0 := by
  classical
  -- integer coefficient grid
  have hint : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ∃ m : ℤ, ClassFunction.inner φ (hyp.eta i j) = (m : ℂ) := fun i j =>
    ClassFunction.inner_mem_ZIrr_int hφZ (eta_mem_ZIrr hyp i j)
  choose m hm using hint
  -- the grid projection and its residual
  set X : ClassFunction G ℂ :=
    ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j : ℂ) • hyp.eta i j with hX
  set Y : ClassFunction G ℂ := φ - X with hY
  -- `⟨X, η_kl⟩ = m k l` by orthonormality
  have hXeta : ∀ (k : Fin hyp.q) (l : Fin hyp.p),
      ClassFunction.inner X (hyp.eta k l) = (m k l : ℂ) := by
    intro k l
    rw [hX, inner_sum_left]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => ?_)]
    · rw [inner_sum_left,
        Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => ?_)]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_pos ⟨rfl, rfl⟩, mul_one]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_neg (by rintro ⟨-, rfl⟩; exact hjl rfl), mul_zero]
    · rw [inner_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
        if_neg (by rintro ⟨rfl, -⟩; exact hik rfl), mul_zero]
  -- `⟨Y, η_kl⟩ = 0`
  have hYeta : ∀ (k : Fin hyp.q) (l : Fin hyp.p),
      ClassFunction.inner Y (hyp.eta k l) = 0 := by
    intro k l
    rw [hY, ClassFunction.inner_sub_left, hXeta k l, hm k l, sub_self]
  -- `⟨φ, X⟩ = ∑ m²` and `⟨X, X⟩ = ∑ m²`
  have hsum_sq : ∀ ψ : ClassFunction G ℂ,
      (∀ (k : Fin hyp.q) (l : Fin hyp.p),
        ClassFunction.inner ψ (hyp.eta k l) = (m k l : ℂ)) →
      ClassFunction.inner ψ X
        = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) := by
    intro ψ hψ
    rw [hX, inner_sum_right]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hψ i j, star_intCast]
    ring
  -- `⟨X, Y⟩ = 0` and `⟨Y, X⟩ = 0`
  have hXY : ClassFunction.inner X Y = 0 := by
    have h := hsum_sq X hXeta
    have h2 : ClassFunction.inner X φ
        = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hsum_sq φ hm]
      rw [star_intCast]
    rw [hY, ClassFunction.inner_sub_right, h2, h, sub_self]
  have hYX : ClassFunction.inner Y X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXY, star_zero]
  -- Pythagorean split: `⟨φ, φ⟩ = ∑ m² + ⟨Y, Y⟩`
  have hsplit : ClassFunction.inner φ φ
      = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ)
        + ClassFunction.inner Y Y := by
    have hφXY : φ = X + Y := by rw [hY]; abel
    calc ClassFunction.inner φ φ
        = ClassFunction.inner (X + Y) (X + Y) := by rw [← hφXY]
      _ = ClassFunction.inner X X + ClassFunction.inner X Y
          + (ClassFunction.inner Y X + ClassFunction.inner Y Y) := by
          rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
            ClassFunction.inner_add_right]
      _ = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ)
          + ClassFunction.inner Y Y := by
          rw [hXY, hYX, hsum_sq X hXeta]; ring
  -- `⟨Y, Y⟩` is a nonnegative real, so `∑ m² ≤ 2` over `ℤ`
  have hYY : ∃ r : ℝ, 0 ≤ r ∧ ClassFunction.inner Y Y = (r : ℂ) := by
    refine ⟨(Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (Y g), ?_,
      inner_self_eq_realCast Y⟩
    have hsum : (0 : ℝ) ≤ ∑ g : G, Complex.normSq (Y g) :=
      Finset.sum_nonneg fun g _ => Complex.normSq_nonneg _
    positivity
  obtain ⟨r, hr0, hr⟩ := hYY
  have hsq_le : ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 ≤ 2 := by
    have h2 : ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) + (r : ℂ)
        = (2 : ℂ) := by rw [← hr, ← hsplit, hnorm]
    have hreal : ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℝ) + r
        = 2 := by
      have hre := congrArg Complex.re h2
      simp only [Complex.add_re, Complex.intCast_re, Complex.ofReal_re] at hre
      norm_num at hre
      exact_mod_cast hre
    have : ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℝ) ≤ 2 := by
      linarith
    exact_mod_cast this
  -- at most two nonzero coefficients
  have hNC : (Finset.univ.filter
      fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)).card ≤ 2 := by
    have hcard_le : ((Finset.univ.filter
        fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)).card : ℤ)
        ≤ ∑ x : Fin hyp.q × Fin hyp.p, (m x.1 x.2) ^ 2 :=
      calc ((Finset.univ.filter
            fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)).card : ℤ)
          = ∑ x ∈ Finset.univ.filter
              (fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)), 1 := by
            simp
        _ ≤ ∑ x ∈ Finset.univ.filter
              (fun x : Fin hyp.q × Fin hyp.p => ((m x.1 x.2 : ℂ) ≠ 0)),
                (m x.1 x.2) ^ 2 := by
            refine Finset.sum_le_sum fun x hx => ?_
            have hne : m x.1 x.2 ≠ 0 := by
              intro h0
              exact (Finset.mem_filter.mp hx).2 (by rw [h0, Int.cast_zero])
            nlinarith [Int.one_le_abs hne, sq_abs (m x.1 x.2)]
        _ ≤ ∑ x : Fin hyp.q × Fin hyp.p, (m x.1 x.2) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun x _ _ => sq_nonneg _)
    have hprod : ∑ x : Fin hyp.q × Fin hyp.p, (m x.1 x.2) ^ 2
        = ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 := by
      rw [Fintype.sum_prod_type]
    omega
  -- the (3.7) relation on the coefficient grid, then rigidity
  have hrel : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      (m i j : ℂ) + (m ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ : ℂ)
        = (m i ⟨0, hyp.p_prime.pos⟩ : ℂ) + (m ⟨0, hyp.q_prime.pos⟩ j : ℂ) := by
    intro i j
    have h := inner_eta_grid_relation hyp hvanish i j
    rw [hm, hm, hm, hm] at h
    exact h
  have hzero := grid_eq_zero_of_relation_of_card_le_two
    hyp.three_le_q hyp.three_le_p
    ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ hrel hNC
  intro i j
  rw [hm i j, hzero i j]

end OddOrder.Peterfalvi.S16
