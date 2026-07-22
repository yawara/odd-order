/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups
import OddOrder.Peterfalvi.S08_GeneralAdjoin
import OddOrder.GroupTheory.RepresentationTheory.CliffordCorrespondence

/-!
# Peterfalvi Appendix E: The Feit-Sibley Theorem

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix IV ("The Feit--Sibley Theorem"), pp. 144--150.

The appendix proves a coherence theorem for the family
`𝒮 = {χ ∈ Irr(H) | Q₁ ⊄ Ker χ}` attached to a subgroup `H = Q ⋊ D` of `G` whose
kernel `Q` has trivial intersections in `G`.

## Honesty status

Every statement below is a genuine assertion about groups and characters: there
are no opaque `Prop` fields and no self-carried `_holds` proofs anywhere in this
file.

**What was opaque before (2026-07-18 de-opacification).**

* The `Hypothesis` structure carried `H_eq_Q_semidirect_D`,
  `Q_trivial_intersections`, `Q_eq_S_prod_Q1` and `D_fixedPointFree_on_Q1` as
  free `Prop` fields with self-carried `_holds` proofs — i.e. it asserted
  nothing beyond `coprime_Q_D`, and was satisfiable with `H = Q = D = ⊥` and
  `True` everywhere.  It also *posited* `Sset`, `A`, `tau` and `d` as arbitrary
  data, although the book **defines** all four.  They are now definitions
  (`Hypothesis.Sset`, `Hypothesis.A`, `Hypothesis.tau`, `Hypothesis.d`), and the
  semidirect decomposition, trivial intersections, `Q = S × Q₁` and
  fixed-point-freeness are actual subgroup statements.
* `coherence_adjoin_or_equal_degree` concluded
  `∃ adjoinCriterion equalDegreeCriterion : Prop, adjoinCriterion ∧
  equalDegreeCriterion`, which is provable by `⟨True, True, trivial, trivial⟩`;
  its `sorry` hid nothing.  Lemma 1 is now stated as the two actual coherence
  criteria (and part (b) is *already proved* in the repository — see below, so
  only part (a) survives here as a statement).
* `induction_isometry` concluded `∃ data : InductionIsometryData …, …` where
  every field of `InductionIsometryData` was a free `Prop` + `_holds`; the whole
  structure is deleted and Lemma 2(a)(b)(c) are stated separately as genuine
  assertions about `Ind_Q^H`, `Ind_H^G` and complex conjugation.
* `feit_sibley_coherence` had a genuine conclusion but rested on the opaque
  `Hypothesis` (and on a posited `tau`/`Sset`/`A`); it now rests on the real one
  with the book's definitions.

Per-result status:

| Result | Status |
|---|---|
| `Q1_le_H`, `S_le_H`, `disjoint_Q_D`, `disjoint_S_Q1` | **proved, sorry-free** |
| `tau` (`Ind_H^G` as a `ℤ`-linear map) | **constructed, sorry-free** |
| `SsetOf_subset`, `d_pos`, `zSpan_Sset_le_ZIrr` | **proved, sorry-free** |
| Lemma 2(b) integrality + degree (`tau_mem_ZIrr`, `tau_apply_one`) | **proved, sorry-free** |
| Lemma 1(b) (equal degree ⇒ coherent) | **already in the repo**, see below |
| Lemma 1(a) (`coherent_adjoin_of_degree_bound`) | **proved, sorry-free** (issue 1049) |
| Lemma 2(a) (`Sset_eq_induced_of_Q`) | **proved, sorry-free** (issue 1051) |
| Lemma 2(b) (`induction_isometry_on_degree_zero`) | **proved, sorry-free** (issue 1052) |
| Lemma 2(c) (`hasNoRealCharacters_Sset`) | **proved, sorry-free** (issue 1053; explicit `Odd |Q₁|` hypothesis, see its docstring) |
| Theorem (`feit_sibley_coherence`) | honest statement, `sorry` |
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **A character non-constant on a subgroup lies over a nontrivial constituent.**  If
`χ ∈ Irr(K)` is not constant on `N ≤ K` (`∃ x ∈ N, χ(x) ≠ χ(1)`, i.e. `N ⊄ Ker χ`), then some
nontrivial `θ ∈ Irr(N)` occurs in `Res_N χ`.  Fourier expansion
(`sum_inner_irreducibleCharacter_smul`): if every nontrivial `θ` had multiplicity `0`, then
`Res_N χ = ⟨Res χ, 1⟩·1`, forcing `χ` constant on `N`. -/
theorem exists_ne_trivial_liesOver_of_not_forall_eq_one
    {K : Type*} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    {N : Subgroup K} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    [Fintype (IrreducibleCharacter ↥N)]
    (χ : IrreducibleCharacter K)
    (hker : ¬ ∀ x : ↥N, (χ : ClassFunction K ℂ) (x : K) = (χ : ClassFunction K ℂ) 1) :
    ∃ θ : IrreducibleCharacter ↥N, θ ≠ trivialIrreducibleCharacter ↥N ∧
      IrreducibleCharacter.LiesOver N χ θ := by
  by_contra hcon
  apply hker
  have hzero : ∀ θ : IrreducibleCharacter ↥N, θ ≠ trivialIrreducibleCharacter ↥N →
      ClassFunction.inner (ClassFunction.restrict N (χ : ClassFunction K ℂ))
        (θ : ClassFunction ↥N ℂ) = 0 := by
    intro θ hθ
    by_contra h
    exact hcon ⟨θ, hθ, by
      rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def]; exact h⟩
  have hfourier := sum_inner_irreducibleCharacter_smul
    (ClassFunction.restrict N (χ : ClassFunction K ℂ))
  rw [Finset.sum_eq_single (trivialIrreducibleCharacter ↥N)] at hfourier
  · intro x
    have hvalx := congrArg (fun f : ClassFunction ↥N ℂ => f x) hfourier
    have hval1 := congrArg (fun f : ClassFunction ↥N ℂ => f (1 : ↥N)) hfourier
    simp only [ClassFunction.smul_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply, ClassFunction.restrict_apply, Subgroup.coe_one,
      mul_one] at hvalx hval1
    rw [← hvalx, hval1]
  · intro θ _ hθ; rw [hzero θ hθ, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Pulling a class function back along `e.symm` and then along `e` is the identity: for
`e : A ≃* B` and `φ` a class function on `A`, `(φ ∘ e.symm) ∘ e = φ`. -/
theorem compHom_toMonoidHom_compHom_symm {A B : Type*} [Group A] [Group B]
    {k : Type*} [CommRing k] (e : A ≃* B) (φ : ClassFunction A k) :
    ClassFunction.compHom e.toMonoidHom (ClassFunction.compHom e.symm.toMonoidHom φ) = φ := by
  ext x
  simp

/-- Pulling a class function back along `e` and then along `e.symm` is the identity: for
`e : A ≃* B` and `φ` a class function on `B`, `(φ ∘ e) ∘ e.symm = φ`. -/
theorem compHom_symm_toMonoidHom_compHom {A B : Type*} [Group A] [Group B]
    {k : Type*} [CommRing k] (e : A ≃* B) (φ : ClassFunction B k) :
    ClassFunction.compHom e.symm.toMonoidHom (ClassFunction.compHom e.toMonoidHom φ) = φ := by
  ext x
  simp

/-- Pullback along a group homomorphism preserves the trivial class function. -/
theorem compHom_trivialClassFunction {A B : Type*} [Group A] [Group B] (f : A →* B) :
    ClassFunction.compHom f (trivialClassFunction B) = trivialClassFunction A := by
  ext x
  simp

/-- Pullback along a `MulEquiv` preserves nontriviality of class functions. -/
theorem compHom_mulEquiv_ne_trivial {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {θ : ClassFunction B ℂ} (hθ : θ ≠ trivialClassFunction B) :
    ClassFunction.compHom e.toMonoidHom θ ≠ trivialClassFunction A := by
  intro h
  apply hθ
  calc θ = ClassFunction.compHom e.symm.toMonoidHom
        (ClassFunction.compHom e.toMonoidHom θ) := (compHom_symm_toMonoidHom_compHom e θ).symm
    _ = ClassFunction.compHom e.symm.toMonoidHom (trivialClassFunction A) := by rw [h]
    _ = trivialClassFunction B := compHom_trivialClassFunction _

/-- **A character constant on a subgroup lies only over the trivial constituent** (the converse
of `exists_ne_trivial_liesOver_of_not_forall_eq_one`): if the class function `χ` on `K` takes
the constant value `χ(1)` on all of `N ≤ K`, then every nontrivial `θ ∈ Irr(N)` has
multiplicity `0` in `Res_N χ`, since `Res_N χ = χ(1)·1_N` and `⟨1_N, θ⟩ = 0` by
orthogonality. -/
theorem restrictionMultiplicity_eq_zero_of_forall_eq_one
    {K : Type*} [Group K] {N : Subgroup K} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (χ : ClassFunction K ℂ) (hconst : ∀ x : ↥N, χ (x : K) = χ 1)
    {θ : IrreducibleCharacter ↥N} (hθ : θ ≠ trivialIrreducibleCharacter ↥N) :
    ClassFunction.restrictionMultiplicity N χ (θ : ClassFunction ↥N ℂ) = 0 := by
  have hres : ClassFunction.restrict N χ = χ 1 • trivialClassFunction ↥N := by
    ext x
    rw [ClassFunction.restrict_apply, ClassFunction.smul_apply, trivialClassFunction_apply,
      mul_one]
    exact hconst x
  rw [ClassFunction.restrictionMultiplicity_def, hres, ClassFunction.inner_smul_left,
    ← IrreducibleCharacter.coe_trivialIrreducibleCharacter,
    irreducibleCharacter_inner_eq_ite, if_neg (fun h => hθ h.symm), mul_zero]

/-- **An irreducible constituent passes through an intermediate subgroup**: if `θ` occurs in
`Res_N χ` and `N ≤ T`, then some `ψ ∈ Irr(T)` occurs in `Res_T χ` such that `θ` (transported
along `↥(N.subgroupOf T) ≃* ↥N`) occurs in `Res ψ`.  Restriction in stages
(`ClassFunction.restrict_subgroupOf_restrict`) and the Fourier expansion of `Res_T χ` give
`⟨Res_N χ, θ⟩ = ∑_{ψ ∈ Irr(T)} ⟨Res_T χ, ψ⟩·⟨Res ψ, θ'⟩`, so a nonzero left-hand side forces
a summand with both factors nonzero. -/
theorem exists_restrictionMultiplicity_ne_zero_intermediate
    {K : Type*} [Group K] {N T : Subgroup K} (hNT : N ≤ T)
    [Fintype ↥T] [Invertible (Nat.card ↥T : ℂ)]
    [Fintype ↥(N.subgroupOf T)] [Invertible (Nat.card ↥(N.subgroupOf T) : ℂ)]
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {χ : ClassFunction K ℂ} {θ : ClassFunction ↥N ℂ}
    (hne : ClassFunction.restrictionMultiplicity N χ θ ≠ 0) :
    ∃ ψ : IrreducibleCharacter ↥T,
      ClassFunction.restrictionMultiplicity T χ (ψ : ClassFunction ↥T ℂ) ≠ 0 ∧
        ClassFunction.restrictionMultiplicity (N.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom θ) ≠ 0 := by
  classical
  haveI : Finite (IrreducibleCharacter ↥T) := finite_irreducibleCharacter (G := ↥T)
  letI : Fintype (IrreducibleCharacter ↥T) := Fintype.ofFinite _
  by_contra hcon
  push_neg at hcon
  apply hne
  -- restriction in stages: `⟨Res_N χ, θ⟩ = ⟨Res (Res_T χ), θ'⟩`
  have h1 : ClassFunction.restrictionMultiplicity N χ θ
      = ClassFunction.inner (ClassFunction.restrict (N.subgroupOf T)
          (ClassFunction.restrict T χ))
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom θ) := by
    rw [ClassFunction.restrict_subgroupOf_restrict hNT]
    exact (inner_compHom_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNT)
      (ClassFunction.restrict N χ) θ).symm
  have hres_sum : ∀ (s : Finset (IrreducibleCharacter ↥T))
      (F : IrreducibleCharacter ↥T → ClassFunction ↥T ℂ),
      ClassFunction.restrict (N.subgroupOf T) (∑ ρ ∈ s, F ρ)
        = ∑ ρ ∈ s, ClassFunction.restrict (N.subgroupOf T) (F ρ) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => ext y; simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.restrict_add, ih]
  -- Fourier expansion of `Res_T χ`, pushed through the second restriction
  have h2 : ClassFunction.inner (ClassFunction.restrict (N.subgroupOf T)
        (ClassFunction.restrict T χ))
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom θ)
      = ∑ ρ : IrreducibleCharacter ↥T,
          ClassFunction.inner (ClassFunction.restrict T χ) (ρ : ClassFunction ↥T ℂ)
            * ClassFunction.inner (ClassFunction.restrict (N.subgroupOf T)
                (ρ : ClassFunction ↥T ℂ))
                (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hNT).toMonoidHom θ) := by
    conv_lhs => rw [← sum_inner_irreducibleCharacter_smul (G := ↥T)
      (ClassFunction.restrict T χ)]
    rw [hres_sum, inner_sum_left]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [ClassFunction.restrict_smul, ClassFunction.inner_smul_left]
  rw [h1, h2]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  by_cases hA : ClassFunction.restrictionMultiplicity T χ (ρ : ClassFunction ↥T ℂ) = 0
  · rw [ClassFunction.restrictionMultiplicity_def] at hA
    rw [hA, zero_mul]
  · have hB := hcon ρ hA
    rw [ClassFunction.restrictionMultiplicity_def] at hB
    rw [hB, mul_zero]

/-! ## Hypotheses and notation (p. 145) -/

/-- **Peterfalvi Appendix IV, "Hypotheses and Notation"** (p. 145).

`G` is a finite group and `H = Q ⋊ D` is a **proper** subgroup of `G`, with
`(|D|, |Q|) = 1` and `Q ∩ Q^x = 1` for `x ∈ G - H`.  Furthermore
`Q = S × Q₁` with `(|S|, |Q₁|) = 1`, `D` acts without fixed points on `Q₁`, `Q₁`
is not a `2`-group, and `S` is nilpotent.

Every field is a genuine group-theoretic assertion.  The internal semidirect
decomposition is recorded exactly as in Part II (`Q ⊴ H`, `Q ∩ D = 1`,
`QD = H`), and the internal direct decomposition `Q = S × Q₁` as
`S ∩ Q₁ = 1`, `S Q₁ = Q` together with elementwise commutation (normality of
`S` and `Q₁` in `Q` then follows).  "Acts without fixed points" is
`C_{Q₁}(g) = 1` for every `g ∈ D^#`, spelled pointwise by conjugation inside
`G` — the same shape as `Isaacs.Ch06.IsFrobeniusAction`, which is not directly
usable here because `D` and `Q₁` are subgroups of a common ambient group rather
than an abstract operator pair. -/
structure Hypothesis (G : Type*) [Group G] where
  /-- the subgroup `H = Q ⋊ D` -/
  H : Subgroup G
  /-- the normal Hall subgroup `Q ⊴ H` -/
  Q : Subgroup G
  /-- the complement `D` -/
  D : Subgroup G
  /-- the nilpotent direct factor `S ≤ Q` -/
  S : Subgroup G
  /-- the fixed-point-free direct factor `Q₁ ≤ Q` -/
  Q1 : Subgroup G
  /-- `H` is a **proper** subgroup of `G` -/
  H_ne_top : H ≠ ⊤
  Q_le_H : Q ≤ H
  D_le_H : D ≤ H
  /-- `Q ⊴ H` -/
  Q_normal_in_H : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q
  /-- `Q ∩ D = 1` -/
  Q_inf_D_eq_bot : Q ⊓ D = ⊥
  /-- `Q D = H`; with the previous two fields this is `H = Q ⋊ D` -/
  Q_mul_D_eq_H : (Q : Set G) * (D : Set G) = (H : Set G)
  /-- `(|D|, |Q|) = 1` -/
  coprime_Q_D : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥D)
  /-- `Q ∩ Q^x = 1` for `x ∈ G - H`: `Q` has trivial intersections in `G` -/
  Q_trivial_intersection : ∀ x : G, x ∉ H →
    Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥
  S_le_Q : S ≤ Q
  Q1_le_Q : Q1 ≤ Q
  /-- `S ∩ Q₁ = 1` -/
  S_inf_Q1_eq_bot : S ⊓ Q1 = ⊥
  /-- `S Q₁ = Q` -/
  S_mul_Q1_eq_Q : (S : Set G) * (Q1 : Set G) = (Q : Set G)
  /-- `S` and `Q₁` commute elementwise; with the previous two fields, `Q = S × Q₁` -/
  S_commutes_Q1 : ∀ s ∈ S, ∀ y ∈ Q1, s * y = y * s
  /-- `(|S|, |Q₁|) = 1` -/
  coprime_S_Q1 : Nat.Coprime (Nat.card ↥S) (Nat.card ↥Q1)
  /-- `S` is nilpotent -/
  S_nilpotent : Group.IsNilpotent ↥S
  /-- `Q₁` is not a `2`-group -/
  Q1_not_two_group : ¬ IsPGroup 2 ↥Q1
  /-- `D` acts on `Q₁` without fixed points -/
  D_fixedPointFree_on_Q1 : ∀ g ∈ D, g ≠ 1 → ∀ x ∈ Q1, g * x * g⁻¹ = x → x = 1

namespace Hypothesis

variable (hyp : Hypothesis G)

/-- `d = |D|` (p. 145). -/
noncomputable def d : ℕ := Nat.card ↥hyp.D

/-- `R ⊆ Ker χ` for a class function `χ` on `H` and a subgroup `R ≤ G`: the
character takes its degree value on every element of `R ∩ H`.  For a character
this is exactly containment in the kernel. -/
def LeKer (χ : ClassFunction ↥hyp.H ℂ) (R : Subgroup G) : Prop :=
  ∀ x : ↥hyp.H, (x : G) ∈ R → χ x = χ 1

/-- **`𝒮 = {χ ∈ Irr(H) | Q₁ ⊄ Ker χ}`** (p. 145).  This is a *definition*, as in
the book, not posited data. -/
def Sset : Set (ClassFunction ↥hyp.H ℂ) :=
  {χ | IsIrreducibleCharacter χ ∧ ¬ hyp.LeKer χ hyp.Q1}

/-- **`𝒮(R) = {χ ∈ 𝒮 | R ⊆ Ker χ}`** for `R ⊆ Q` (p. 145). -/
def SsetOf (R : Subgroup G) : Set (ClassFunction ↥hyp.H ℂ) :=
  {χ | χ ∈ hyp.Sset ∧ hyp.LeKer χ R}

/-- The support set for the coherence statement: `Q^#`, viewed inside `H`.  By
Lemma 2(a) the members of `𝒮` vanish on `H - Q`, and degree-zero combinations
vanish at `1`, so `ℤ[𝒮]°` is supported on `Q^#`. -/
def A : Set ↥hyp.H := {x | (x : G) ∈ hyp.Q ∧ x ≠ 1}

/-- **`τ = Ind_H^G`** as a `ℤ`-linear map on class functions (p. 145, Lemma
2(b)).  This is a *construction*, not posited data. -/
noncomputable def tau [Fintype G] [Invertible (Nat.card ↥hyp.H : ℂ)] :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.H G where
  toFun := ClassFunction.induce hyp.H
  map_add' := ClassFunction.induce_add hyp.H
  map_smul' n θ := by
    change ClassFunction.induce hyp.H (n • θ) = n • ClassFunction.induce hyp.H θ
    rw [← Int.cast_smul_eq_zsmul ℂ n θ, ClassFunction.induce_smul,
      Int.cast_smul_eq_zsmul]

@[simp] theorem tau_apply [Fintype G] [Invertible (Nat.card ↥hyp.H : ℂ)]
    (θ : ClassFunction ↥hyp.H ℂ) : hyp.tau θ = ClassFunction.induce hyp.H θ := rfl

/-- `ℤ[𝒮] ⊆ ℤ[Irr H]`: the members of `𝒮` are irreducible characters of `H`. -/
theorem zSpan_Sset_le_ZIrr :
    OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset ≤ ZIrr ↥hyp.H :=
  Submodule.span_le.mpr fun _ hχ => hχ.1.mem_ZIrr

/-- **Lemma 2(b), integrality clause** (proved, sorry-free): `τ = Ind_H^G` maps `ℤ[𝒮]` into
`ℤ[Irr G]`, since `ℤ[𝒮] ⊆ ℤ[Irr H]` and induction preserves virtual characters
(`ClassFunction.induce_mem_ZIrr`, Peterfalvi (2.6.b)). -/
theorem tau_mem_ZIrr [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.H : ℂ)] {φ : ClassFunction ↥hyp.H ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset) :
    hyp.tau φ ∈ ZIrr G := by
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ↥hyp.H := Fintype.ofFinite _
  exact ClassFunction.induce_mem_ZIrr hyp.H (hyp.zSpan_Sset_le_ZIrr hφ)

/-- **Lemma 2(b), degree clause** (proved, sorry-free): `τ` preserves the degree-zero condition,
because `Ind_H^G φ (1) = [G : H] · φ(1)` (`ClassFunction.induce_apply_one`). -/
theorem tau_apply_one [Fintype G] [Invertible (Nat.card ↥hyp.H : ℂ)]
    {φ : ClassFunction ↥hyp.H ℂ} (hφ1 : φ (1 : ↥hyp.H) = 0) : (hyp.tau φ) (1 : G) = 0 := by
  change ClassFunction.induce hyp.H φ (1 : G) = 0
  rw [ClassFunction.induce_apply_one, hφ1, mul_zero]

/-! ### Elementary consequences of the hypotheses -/

theorem S_le_H : hyp.S ≤ hyp.H := le_trans hyp.S_le_Q hyp.Q_le_H

theorem Q1_le_H : hyp.Q1 ≤ hyp.H := le_trans hyp.Q1_le_Q hyp.Q_le_H

/-- `Q ∩ D = 1`, in `Disjoint` form. -/
theorem disjoint_Q_D : Disjoint hyp.Q hyp.D := disjoint_iff.mpr hyp.Q_inf_D_eq_bot

/-- `S ∩ Q₁ = 1`, in `Disjoint` form. -/
theorem disjoint_S_Q1 : Disjoint hyp.S hyp.Q1 := disjoint_iff.mpr hyp.S_inf_Q1_eq_bot

/-- **`Q₁ ⊴ Q`** (direct-product factor, elementwise form): for `q ∈ Q` and `x ∈ Q₁`,
`q x q⁻¹ ∈ Q₁`.  Writing `q = s·y` (`s ∈ S`, `y ∈ Q₁`) via `S Q₁ = Q`, one has
`q x q⁻¹ = s (y x y⁻¹) s⁻¹ = y x y⁻¹ ∈ Q₁` since `S` centralises `Q₁`. -/
theorem Q1_conj_mem_of_mem_Q {q : G} (hq : q ∈ hyp.Q) {x : G} (hx : x ∈ hyp.Q1) :
    q * x * q⁻¹ ∈ hyp.Q1 := by
  rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hq
  obtain ⟨s, hs, y, hy, hsy⟩ := Set.mem_mul.mp hq
  rw [SetLike.mem_coe] at hs hy
  subst hsy
  have hz : y * x * y⁻¹ ∈ hyp.Q1 :=
    hyp.Q1.mul_mem (hyp.Q1.mul_mem hy hx) (hyp.Q1.inv_mem hy)
  have hcomm : s * (y * x * y⁻¹) = (y * x * y⁻¹) * s := hyp.S_commutes_Q1 s hs _ hz
  have hrw : s * y * x * (s * y)⁻¹ = y * x * y⁻¹ := by
    calc s * y * x * (s * y)⁻¹
        = s * (y * x * y⁻¹) * s⁻¹ := by group
      _ = (y * x * y⁻¹) * s * s⁻¹ := by rw [hcomm]
      _ = y * x * y⁻¹ := by group
  rw [hrw]; exact hz

/-- **`π`-element characterisation of `Q₁`** (`Q = S × Q₁`, `(|S|, |Q₁|) = 1`): an element
`w ∈ Q` whose order is coprime to `|S|` already lies in the direct factor `Q₁`.  Writing
`w = s·y` (`s ∈ S`, `y ∈ Q₁`) via `S Q₁ = Q`, the commuting coprime-order factorisation gives
`orderOf w = orderOf s · orderOf y`, so `orderOf s ∣ orderOf w` is coprime to `|S|`; but
`orderOf s ∣ |S|`, forcing `orderOf s = 1`, i.e. `s = 1` and `w = y ∈ Q₁`. -/
theorem mem_Q1_of_mem_Q_of_coprime_orderOf [Finite G] {w : G} (hw : w ∈ hyp.Q)
    (hcop : Nat.Coprime (orderOf w) (Nat.card ↥hyp.S)) : w ∈ hyp.Q1 := by
  rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hw
  obtain ⟨s, hs, y, hy, hsy⟩ := Set.mem_mul.mp hw
  rw [SetLike.mem_coe] at hs hy
  have hcomm : Commute s y := hyp.S_commutes_Q1 s hs y hy
  have hos_dvd : orderOf s ∣ Nat.card ↥hyp.S := hyp.S.orderOf_dvd_natCard hs
  have hoy_dvd : orderOf y ∣ Nat.card ↥hyp.Q1 := hyp.Q1.orderOf_dvd_natCard hy
  have hcop_orders : Nat.Coprime (orderOf s) (orderOf y) :=
    (hyp.coprime_S_Q1.coprime_dvd_left hos_dvd).coprime_dvd_right hoy_dvd
  have how : orderOf w = orderOf s * orderOf y := by
    rw [← hsy]; exact hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders
  have hos_dvd_w : orderOf s ∣ orderOf w := by rw [how]; exact dvd_mul_right _ _
  have hcs : Nat.Coprime (orderOf s) (Nat.card ↥hyp.S) := hcop.coprime_dvd_left hos_dvd_w
  have hone : orderOf s ∣ 1 := by
    have hg : Nat.gcd (orderOf s) (Nat.card ↥hyp.S) = 1 := hcs
    exact hg ▸ Nat.dvd_gcd dvd_rfl hos_dvd
  have hsone : s = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  rw [← hsy, hsone, one_mul]; exact hy

/-- **`D` normalises `Q₁`** (elementwise): for `δ ∈ D` and `x ∈ Q₁`, `δ x δ⁻¹ ∈ Q₁`.  Since
`D ≤ H` and `Q ⊴ H`, the conjugate `δ x δ⁻¹` lies in `Q`; conjugation preserves order and
`orderOf x ∣ |Q₁|` is coprime to `|S|`, so `δ x δ⁻¹` is a `π`-element of `Q` and hence in `Q₁`
by `mem_Q1_of_mem_Q_of_coprime_orderOf`.  (`Q₁` is the characteristic Hall factor of `Q`; this
gives the well-definedness of the `D`-action on `Q₁` used throughout Lemma 2.) -/
theorem D_normalizes_Q1 [Finite G] {δ : G} (hδ : δ ∈ hyp.D) {x : G} (hx : x ∈ hyp.Q1) :
    δ * x * δ⁻¹ ∈ hyp.Q1 := by
  have hconjQ : δ * x * δ⁻¹ ∈ hyp.Q :=
    hyp.Q_normal_in_H δ (hyp.D_le_H hδ) x (hyp.Q1_le_Q hx)
  have hox : orderOf x ∣ Nat.card ↥hyp.Q1 := hyp.Q1.orderOf_dvd_natCard hx
  have hoconj : orderOf (δ * x * δ⁻¹) = orderOf x := by
    have h := orderOf_injective (MulAut.conj δ).toMonoidHom (MulAut.conj δ).injective x
    simpa [MulAut.conj_apply] using h
  refine hyp.mem_Q1_of_mem_Q_of_coprime_orderOf hconjQ ?_
  rw [hoconj]
  exact hyp.coprime_S_Q1.symm.coprime_dvd_left hox

/-- **`Q₁ ⊴ H`** (elementwise): for `h ∈ H` and `x ∈ Q₁`, `h x h⁻¹ ∈ Q₁`.  Writing `h = q·δ`
(`q ∈ Q`, `δ ∈ D`) via `Q D = H`, `h x h⁻¹ = q (δ x δ⁻¹) q⁻¹` with `δ x δ⁻¹ ∈ Q₁`
(`D_normalizes_Q1`) and then `q · q⁻¹ ∈ Q₁` (`Q1_conj_mem_of_mem_Q`). -/
theorem Q1_normal_in_H [Finite G] {h : G} (hh : h ∈ hyp.H) {x : G} (hx : x ∈ hyp.Q1) :
    h * x * h⁻¹ ∈ hyp.Q1 := by
  rw [← SetLike.mem_coe, ← hyp.Q_mul_D_eq_H] at hh
  obtain ⟨q, hq, δ, hδ, hqδ⟩ := Set.mem_mul.mp hh
  rw [SetLike.mem_coe] at hq hδ
  subst hqδ
  have hδx : δ * x * δ⁻¹ ∈ hyp.Q1 := hyp.D_normalizes_Q1 hδ hx
  have hrw : q * δ * x * (q * δ)⁻¹ = q * (δ * x * δ⁻¹) * q⁻¹ := by group
  rw [hrw]
  exact hyp.Q1_conj_mem_of_mem_Q hq hδx

/-- **Coset fixed-point-freeness** (the Frobenius property of `Q₁ D`): every element `k·δ`
with `k ∈ Q₁` and `1 ≠ δ ∈ D` acts fixed-point-freely on `Q₁`.  Conjugation by `δ` is a
fixed-point-free automorphism `α` of `Q₁` (`D_fixedPointFree_on_Q1`), so its commutator map
`u ↦ u · α(u)⁻¹` is surjective (`MonoidHom.FixedPointFree.commutatorMap_surjective`); solving
`α(u)·u⁻¹ = k⁻¹` produces `y = u⁻¹ ∈ Q₁` with `y (k δ) y⁻¹ = δ`, so `k δ` is `Q₁`-conjugate to
`δ` and inherits its fixed-point-freeness.  This is the input to the Brauer-permutation inertia
bound: `δ` fixes no nonidentity conjugacy class of `Q₁`. -/
theorem fixedPointFree_of_mem_Q1_mul_D [Finite G] {k : G} (hk : k ∈ hyp.Q1)
    {δ : G} (hδ : δ ∈ hyp.D) (hδ1 : δ ≠ 1) {x : G} (hx : x ∈ hyp.Q1)
    (hfix : k * δ * x * (k * δ)⁻¹ = x) : x = 1 := by
  -- conjugation-by-`δ` automorphism of `Q₁`
  let α : hyp.Q1 ≃* hyp.Q1 :=
    { toFun := fun z => ⟨δ * (z : G) * δ⁻¹, hyp.D_normalizes_Q1 hδ z.2⟩
      invFun := fun z => ⟨δ⁻¹ * (z : G) * δ, by
        simpa using hyp.D_normalizes_Q1 (hyp.D.inv_mem hδ) z.2⟩
      left_inv := fun z => Subtype.ext (by simp only [Subgroup.coe_mk]; group)
      right_inv := fun z => Subtype.ext (by simp only [Subgroup.coe_mk]; group)
      map_mul' := fun z w => Subtype.ext (by
        simp only [Subgroup.coe_mk, Subgroup.coe_mul]; group) }
  have hαcoe : ∀ z : hyp.Q1, ((α z : hyp.Q1) : G) = δ * (z : G) * δ⁻¹ := fun _ => rfl
  have hα_fpf : MonoidHom.FixedPointFree α := by
    intro z hz
    have hzG : δ * (z : G) * δ⁻¹ = (z : G) := by rw [← hαcoe z]; exact congrArg Subtype.val hz
    exact Subtype.ext (hyp.D_fixedPointFree_on_Q1 δ hδ hδ1 (z : G) z.2 hzG)
  -- solve the commutator equation `commutatorMap α u = k`, i.e. `u δ u⁻¹ δ⁻¹ = k`
  obtain ⟨u, hu⟩ := hα_fpf.commutatorMap_surjective (⟨k, hk⟩ : hyp.Q1)
  have hval : (u : G) * (δ * (u : G) * δ⁻¹)⁻¹ = k := by
    have h := congrArg (Subtype.val) hu
    simpa only [MonoidHom.commutatorMap_apply, div_eq_mul_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_mk, hαcoe] using h
  -- `y = u⁻¹ ∈ Q₁` conjugates `k δ` to `δ`
  have huQ1 : (u : G) ∈ hyp.Q1 := u.2
  set y : G := (u : G)⁻¹ with hy
  have hyQ1 : y ∈ hyp.Q1 := hyp.Q1.inv_mem huQ1
  have hconj : y * (k * δ) * y⁻¹ = δ := by
    have hk_eq : k = (u : G) * δ * (u : G)⁻¹ * δ⁻¹ := by rw [← hval]; group
    rw [hk_eq, hy]; group
  -- transfer fixed-point-freeness from `δ` to `k δ`
  have hyxQ1 : y * x * y⁻¹ ∈ hyp.Q1 :=
    hyp.Q1.mul_mem (hyp.Q1.mul_mem hyQ1 hx) (hyp.Q1.inv_mem hyQ1)
  have hfixδ : δ * (y * x * y⁻¹) * δ⁻¹ = y * x * y⁻¹ := by
    have h1 : y * (k * δ) * y⁻¹ * (y * x * y⁻¹) * (y * (k * δ) * y⁻¹)⁻¹
        = y * (k * δ * x * (k * δ)⁻¹) * y⁻¹ := by group
    rw [hconj, hfix] at h1
    exact h1
  have hyxone : y * x * y⁻¹ = 1 :=
    hyp.D_fixedPointFree_on_Q1 δ hδ hδ1 (y * x * y⁻¹) hyxQ1 hfixδ
  have : x = y⁻¹ * 1 * y := by rw [← hyxone]; group
  simpa using this

/-- `H ≤ N_G(Q₁)`: every element of `H` normalises `Q₁` (both containments of
`Subgroup.mem_normalizer_iff` from `Q1_normal_in_H`, the backward one via `h⁻¹ ∈ H`). -/
theorem H_le_normalizer_Q1 [Finite G] : hyp.H ≤ Subgroup.normalizer hyp.Q1 := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hyp.Q1_normal_in_H hh hn, fun hn => ?_⟩
  have hkey := hyp.Q1_normal_in_H (hyp.H.inv_mem hh) hn
  have hrw : h⁻¹ * (h * n * h⁻¹) * (h⁻¹)⁻¹ = n := by group
  rwa [hrw] at hkey

/-- **`Q₁ ⊴ H`, as a `Subgroup.Normal` instance for the subtype form** `Q₁.subgroupOf H ⊴ ↥H`,
from `H ≤ N_G(Q₁)`. -/
theorem Q1_subgroupOf_H_normal [Finite G] : (hyp.Q1.subgroupOf hyp.H).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer hyp.H_le_normalizer_Q1

/-- `H ≤ N_G(Q)`: every element of `H` normalises `Q` (both containments of
`Subgroup.mem_normalizer_iff` from the `Q_normal_in_H` field, the backward one via
`h⁻¹ ∈ H`). -/
theorem H_le_normalizer_Q : hyp.H ≤ Subgroup.normalizer hyp.Q := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hyp.Q_normal_in_H h hh n hn, fun hn => ?_⟩
  have hkey := hyp.Q_normal_in_H h⁻¹ (hyp.H.inv_mem hh) _ hn
  have hrw : h⁻¹ * (h * n * h⁻¹) * (h⁻¹)⁻¹ = n := by group
  rwa [hrw] at hkey

/-- **`Q ⊴ H`, as a `Subgroup.Normal` instance for the subtype form** `Q.subgroupOf H ⊴ ↥H`,
from `H ≤ N_G(Q)`. -/
theorem Q_subgroupOf_H_normal : (hyp.Q.subgroupOf hyp.H).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer hyp.H_le_normalizer_Q

/-- **`Q^# = Q \ {1}` is a TI-subset of `G` with normalizer-bound `H`** (from the
`Q_trivial_intersection` field): for `g ∉ H`, an overlap element `g·a·g⁻¹` with
`a ∈ Q^#` and `g·a·g⁻¹ ∈ Q^#` would be a nontrivial element of
`Q ⊓ Q^g = 1`.  This is the TI input to the induction isometry of Lemma 2(b)
(Isaacs Lemma 7.7, `ClassFunction.inner_induce_eq_of_isTISubset`). -/
theorem isTISubset_Q_sdiff_one :
    OddOrder.GroupTheory.IsTISubset ((hyp.Q : Set G) \ {1}) hyp.H := by
  refine OddOrder.GroupTheory.IsTISubset.of_disjoint_conj fun g hg a ha hga => ?_
  obtain ⟨haQ, ha1⟩ := ha
  obtain ⟨hgaQ, -⟩ := hga
  have hmem : g * a * g⁻¹ ∈ hyp.Q ⊓ hyp.Q.map (MulAut.conj g).toMonoidHom :=
    ⟨hgaQ, Subgroup.mem_map.mpr ⟨a, haQ, by simp [MulAut.conj_apply]⟩⟩
  rw [hyp.Q_trivial_intersection g hg, Subgroup.mem_bot] at hmem
  refine ha1 (Set.mem_singleton_iff.mpr ?_)
  have hrw : a = g⁻¹ * (g * a * g⁻¹) * g := by group
  rw [hrw, hmem, mul_one, inv_mul_cancel]

/-- **`δ` fixes no nonidentity conjugacy class of `Q₁`** (viewed inside `↥H`): for `1 ≠ δ ∈ D`,
a `δ`-fixed class of `Q₁.subgroupOf H` is the identity class.  A fixed class `⟦h⟧` gives
`c·(δ h δ⁻¹)·c⁻¹ = h` for some `c ∈ Q₁`, i.e. `(c δ) h (c δ)⁻¹ = h`; since `c δ` acts
fixed-point-freely on `Q₁` (`fixedPointFree_of_mem_Q1_mul_D`), `h = 1`. -/
theorem delta_fixed_class_eq_one [Finite G] [(hyp.Q1.subgroupOf hyp.H).Normal] {δ : ↥hyp.H}
    (hδD : (δ : G) ∈ hyp.D) (hδ1 : δ ≠ 1)
    {C : ConjClasses ↥(hyp.Q1.subgroupOf hyp.H)}
    (hfix : ConjClasses.conjByPerm (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) δ C = C) :
    C = 1 := by
  rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
  by_cases hh : h = 1
  · rw [hh, ConjClasses.one_eq_mk_one]
  exfalso
  have hmk : ConjClasses.mk (ClassFunction.conjByMulEquiv
      (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) δ h) = ConjClasses.mk h := by
    simpa [ConjClasses.conjByPerm_mk] using hfix
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hmk)
  -- push the conjugacy equation to `↥H` then to `G`
  have hcH : (c : ↥hyp.H) * (δ * (h : ↥hyp.H) * δ⁻¹) * (c : ↥hyp.H)⁻¹ = (h : ↥hyp.H) := by
    have := congrArg (fun z : ↥(hyp.Q1.subgroupOf hyp.H) => (z : ↥hyp.H)) hc
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ClassFunction.conjByMulEquiv_apply] using this
  have hcG := congrArg (fun z : ↥hyp.H => (z : G)) hcH
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcG
  -- apply the coset fixed-point-freeness
  have hcG_mem : ((c : ↥hyp.H) : G) ∈ hyp.Q1 := (Subgroup.mem_subgroupOf).mp c.2
  have hhG_mem : ((h : ↥hyp.H) : G) ∈ hyp.Q1 := (Subgroup.mem_subgroupOf).mp h.2
  have hfixG : ((c : ↥hyp.H) : G) * (δ : G) * ((h : ↥hyp.H) : G)
      * (((c : ↥hyp.H) : G) * (δ : G))⁻¹ = ((h : ↥hyp.H) : G) := by
    have e : ((c : ↥hyp.H) : G) * (δ : G) * ((h : ↥hyp.H) : G)
        * (((c : ↥hyp.H) : G) * (δ : G))⁻¹
        = ((c : ↥hyp.H) : G) * ((δ : G) * ((h : ↥hyp.H) : G) * (δ : G)⁻¹)
          * ((c : ↥hyp.H) : G)⁻¹ := by group
    rw [e, hcG]
  have hδG1 : (δ : G) ≠ 1 := fun hc => hδ1 (Subtype.ext (by simpa using hc))
  have hhG1 : ((h : ↥hyp.H) : G) = 1 :=
    hyp.fixedPointFree_of_mem_Q1_mul_D hcG_mem hδD hδG1 hhG_mem hfixG
  exact hh (Subtype.ext (Subtype.ext (by simpa using hhG1)))

/-- **Brauer count**: `δ ∈ D^#` fixes exactly one conjugacy class of `Q₁.subgroupOf H` — the
identity class (`delta_fixed_class_eq_one`). -/
theorem card_fixedClasses_Q1_eq_one [Finite G] [(hyp.Q1.subgroupOf hyp.H).Normal] {δ : ↥hyp.H}
    (hδD : (δ : G) ∈ hyp.D) (hδ1 : δ ≠ 1) :
    Nat.card (Function.fixedPoints (ConjClasses.conjByPerm
      (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) δ)) = 1 := by
  have hfix_one : ∀ E : Function.fixedPoints (ConjClasses.conjByPerm
      (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) δ), (E : ConjClasses _) = 1 :=
    fun E => hyp.delta_fixed_class_eq_one hδD hδ1 E.2.eq
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun C D => Subtype.ext ((hfix_one C).trans (hfix_one D).symm)⟩,
    ⟨⟨1, ConjClasses.conjByPerm_one (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) δ⟩⟩⟩

/-- **`δ ∈ D^#` is not in the inertia group of any nontrivial `θ ∈ Irr(Q₁)`** (viewed inside
`↥H`).  Brauer's permutation lemma (`not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one`)
turns the single-fixed-class count `card_fixedClasses_Q1_eq_one` into inertia exclusion. -/
theorem delta_notMem_inertia_Q1 [Finite G] [(hyp.Q1.subgroupOf hyp.H).Normal] {δ : ↥hyp.H}
    (hδD : (δ : G) ∈ hyp.D) (hδ1 : δ ≠ 1)
    {θ : IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H)}
    (hθ : θ ≠ trivialIrreducibleCharacter _) :
    δ ∉ IrreducibleCharacter.inertia (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) θ := by
  haveI : Finite ↥(hyp.Q1.subgroupOf hyp.H) := Finite.of_injective _ Subtype.val_injective
  exact not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one δ
    (hyp.card_fixedClasses_Q1_eq_one hδD hδ1) hθ

/-- **`↥H = QH · DH`** (subtype form of `H = Q ⋊ D`): every `g : ↥H` factors as `q · δ`
with `q` in `Q.subgroupOf H` and `δ` in `D.subgroupOf H`. -/
theorem exists_mem_Q_mul_mem_D_subtype (g : ↥hyp.H) :
    ∃ q : ↥hyp.H, (q : G) ∈ hyp.Q ∧ ∃ δ : ↥hyp.H, (δ : G) ∈ hyp.D ∧ g = q * δ := by
  have hgH : (g : G) ∈ hyp.H := g.2
  rw [← SetLike.mem_coe, ← hyp.Q_mul_D_eq_H] at hgH
  obtain ⟨q₀, hq₀, d₀, hd₀, hqd⟩ := Set.mem_mul.mp hgH
  rw [SetLike.mem_coe] at hq₀ hd₀
  exact ⟨⟨q₀, hyp.Q_le_H hq₀⟩, hq₀, ⟨d₀, hyp.D_le_H hd₀⟩, hd₀,
    Subtype.ext (by simpa using hqd.symm)⟩

/-- **`Q` acts trivially on `Irr(Q₁)`** (viewed inside `↥H`): for `q : ↥H` with `(q:G) ∈ Q`,
`conjBy q` fixes every class function of `Q₁.subgroupOf H`.  Writing `(q:G) = s·y`
(`s ∈ S`, `y ∈ Q₁`), conjugation by `q` on `Q₁` equals conjugation by the `Q₁`-element `y`
(since `S` centralises `Q₁`), which is inner in `Q₁` and hence fixes class functions. -/
theorem Q_conjBy_eq [Finite G] [(hyp.Q1.subgroupOf hyp.H).Normal] {q : ↥hyp.H}
    (hq : (q : G) ∈ hyp.Q) (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ) :
    ClassFunction.conjBy (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) q θ = θ := by
  rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hq
  obtain ⟨s, hs, y, hy, hsy⟩ := Set.mem_mul.mp hq
  rw [SetLike.mem_coe] at hs hy
  set y' : ↥hyp.H := ⟨y, hyp.Q_le_H (hyp.Q1_le_Q hy)⟩ with hy'
  have hy'Q1H : y' ∈ hyp.Q1.subgroupOf hyp.H := by rw [Subgroup.mem_subgroupOf]; exact hy
  have hqy : ClassFunction.conjBy (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) q θ
      = ClassFunction.conjBy (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) y' θ := by
    ext x
    rw [ClassFunction.conjBy_apply, ClassFunction.conjBy_apply]
    refine congrArg (⇑θ) (Subtype.ext (Subtype.ext ?_))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    set X : G := ((x : ↥hyp.H) : G) with hX
    have hxQ1 : X ∈ hyp.Q1 := (Subgroup.mem_subgroupOf).mp x.2
    have hw : y * X * y⁻¹ ∈ hyp.Q1 :=
      hyp.Q1.mul_mem (hyp.Q1.mul_mem hy hxQ1) (hyp.Q1.inv_mem hy)
    have hscomm : s * (y * X * y⁻¹) = (y * X * y⁻¹) * s := hyp.S_commutes_Q1 s hs _ hw
    have hqG : ((q : ↥hyp.H) : G) = s * y := hsy.symm
    have hy'G : ((y' : ↥hyp.H) : G) = y := rfl
    rw [hqG, hy'G]
    calc s * y * X * (s * y)⁻¹
        = s * (y * X * y⁻¹) * s⁻¹ := by group
      _ = (y * X * y⁻¹) * s * s⁻¹ := by rw [hscomm]
      _ = y * X * y⁻¹ := by group
  rw [hqy]
  exact ClassFunction.conjBy_eq_self_of_mem hy'Q1H θ

/-- **The inertia crux** (Lemma 2(a), step 5): for a nontrivial `θ ∈ Irr(Q₁)`, the inertia group
of `θ` in `↥H` is exactly `Q`.  `Q` centralises `θ` (`Q_conjBy_eq`), so `Q ≤ I_H(θ)`; conversely
any `g = q·δ ∈ I_H(θ)` has `δ = q⁻¹g ∈ I_H(θ) ∩ D`, and `δ ≠ 1` is impossible
(`delta_notMem_inertia_Q1`), so `g ∈ Q`.  This is the `I_G(θ) = T` input to the Clifford
correspondence (`isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq`) with `T = Q`. -/
theorem inertia_theta_eq_Q [Finite G] [(hyp.Q1.subgroupOf hyp.H).Normal]
    {θ : IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H)}
    (hθ : θ ≠ trivialIrreducibleCharacter _) :
    ClassFunction.inertia (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H)
        (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ) = hyp.Q.subgroupOf hyp.H := by
  apply le_antisymm
  · intro g hg
    obtain ⟨q, hqQ, δ, hδD, rfl⟩ := hyp.exists_mem_Q_mul_mem_D_subtype g
    have hqInertia : q ∈ ClassFunction.inertia (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H)
        (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ) := by
      rw [ClassFunction.mem_inertia]; exact hyp.Q_conjBy_eq hqQ _
    have hδInertia : δ ∈ ClassFunction.inertia (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H)
        (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ) := by
      have h := (ClassFunction.inertia (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H)
        (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ)).mul_mem
          (Subgroup.inv_mem _ hqInertia) hg
      simpa using h
    rw [Subgroup.mem_subgroupOf]
    by_cases hδ1 : δ = 1
    · have : ((q * δ : ↥hyp.H) : G) = (q : G) := by rw [hδ1, mul_one]
      rw [this]; exact hqQ
    · exact absurd hδInertia (hyp.delta_notMem_inertia_Q1 hδD hδ1 hθ)
  · intro q hq
    rw [Subgroup.mem_subgroupOf] at hq
    rw [ClassFunction.mem_inertia]
    exact hyp.Q_conjBy_eq hq _

/-- `d = |D| > 0`. -/
theorem d_pos [Finite G] : 0 < hyp.d := Nat.card_pos

/-- `𝒮(R) ⊆ 𝒮`. -/
theorem SsetOf_subset (R : Subgroup G) : hyp.SsetOf R ⊆ hyp.Sset := fun _ hχ => hχ.1

/-- Members of `𝒮` are irreducible characters of `H`. -/
theorem isIrreducibleCharacter_of_mem_Sset {χ : ClassFunction ↥hyp.H ℂ}
    (hχ : χ ∈ hyp.Sset) : IsIrreducibleCharacter χ := hχ.1

end Hypothesis

/-! ## Lemma 1: coherence criteria (p. 144)

Peterfalvi's Lemma 1 has two parts, both quoted from Isaacs, *Character Theory
of Finite Groups*:

* **(a)** (Isaacs Thm. 7.14) if `𝒮 = 𝒮₀ ∪ {ψ}`, `(𝒮₀, τ)` is coherent, and some
  `χ₀ ∈ 𝒮₀` satisfies `χ₀(1) ∣ ψ(1)` and `2 χ₀(1) ψ(1) < ∑_{χ ∈ 𝒮₀} χ(1)²`, then
  `(𝒮, τ)` is coherent;
* **(b)** (Isaacs Cor. 7.15) if `|𝒮| ≥ 2` and all `χ ∈ 𝒮` have the same degree,
  then `(𝒮, τ)` is coherent.

Part **(b) is already formalized** in this repository, as Peterfalvi (5.7):
`OddOrder.Peterfalvi.S07.coherent_of_constant_degree`.  Per the repository's
no-wrapper policy it is not restated here; consumers should cite it directly.
Only part (a) is stated below. -/

section LemmaOne

open OddOrder.Peterfalvi.S07

variable {L : Type*} [Group L] [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
variable {S : Set (ClassFunction L ℂ)} {A : Set L}

open scoped Classical in
/-- **Peterfalvi Appendix IV, Lemma 1(a)** (p. 144; Isaacs, *Character Theory of
Finite Groups*, Theorem 7.14) — the degree-bound coherence adjoin, in **pair-adjoin
form**, wired to the general engine.

Adjoin a non-real irreducible conjugate pair `{χ, χ̄} ⊆ 𝒮` to a coherent subfamily
`(𝒮₁, τ)` (`𝒮₁ ⊆ 𝒮`, `χ, χ̄ ⊥ 𝒮₁`, orthonormal), given

* an orthonormal, conjugate-closed member family `{χmem i}ᵢ∈ₛ` enumerating `𝒮₁`
  (`hcover`/`hmemS1`; unit norm and conjugate-closedness come from `𝒮 ⊆ Irr(H)` at the
  call site), with absolute degrees `degMem i = χmem i (1)` (`hdegMem`);
* a distinguished anchor `χmem i₁ ∈ 𝒮₁` (`degMem i₁ > 0`) whose degree divides `χ(1)`
  (`χ(1) = a · χmem i₁(1)`, `hχdeg`); the member ratios `χmem i (1)/χmem i₁(1)` may be
  **rational** (issue 1050 — Peterfalvi requires anchor divisibility only for `ψ`);
* the `A`-support of the conjugate differences and of the degree-matched scaled
  differences `χmem i₁(1)·χmem i − χmem i(1)·χmem i₁` (`hmemdiffsupp`/`hdegdiffsupp`; the
  Lemma 2(a) content that `𝒮` vanishes off `Q`), and the integrality
  `τ(χ − a·χmem i₁) ∈ ℤ[Irr G]`;
* Peterfalvi's degree inequality `2·χ(1)·χmem i₁(1) < ∑ χmem i (1)²`, in the normalized
  form `2a < ∑ (degMem i / degMem i₁)²` (`hDeg`).

Then `(𝒮₁ ∪ {χ, χ̄}, τ)` is coherent.

**Design note (issues 1049/1050).**  Peterfalvi phrases this as single-`ψ` adjoin
`𝒮 = 𝒮₀ ∪ {ψ}`, but `𝒮` is conjugate-closed so `ψ̄ ∈ 𝒮₀`; the honest content is the
conjugate-*pair* adjoin (Isaacs 7.14, and the Theorem's step (1) uses pair-successive
adjoins `𝒮(S'Q₂) ⊆ 𝒮(S'Q₃)`).  The proof is a direct instantiation of the general
engine `OddOrder.Peterfalvi.S07.adjoinPairCoherent_general` (`S08_GeneralAdjoin.lean`):
`hisom` from `Hypothesis.adjoin_hisom`, the `R`-families from `Hypothesis.difference_image`
with their cross-orthogonality from `Hypothesis.difference_images_orthogonal`, the scaled
generation `hSgen` per member from the supported scaled differences (`hdegdiffsupp`), and
`hgen` from `zSupportedSpan_adjoinPair_subset_span_of_diffSupports`.  This is the
**faithful abstract-rational form** (issue 1050): only the anchor divisibility
`χ₀(1) ∣ χ(1)` is required, matching Peterfalvi's statement; step (3) Part B of the
Feit–Sibley Theorem genuinely needs the rational case (anchor `Ind(1·θ)` of degree `d·θ(1)`
against members of degree `d·λ(1)·θ_x(1)`). -/
theorem coherent_adjoin_of_degree_bound
    (hyp : OddOrder.Peterfalvi.S07.Hypothesis (L := L) (G := G) S A)
    (h1A : (1 : L) ∉ A)
    {S₁ : Set (ClassFunction L ℂ)} (hS₁S : S₁ ⊆ S)
    (hcoh : Nonempty (IsCoherent hyp.tau S₁ A))
    {χ : ClassFunction L ℂ} (hχS : χ ∈ S)
    (hχχ : ClassFunction.inner χ χ = 1) (hχbarχbar : ClassFunction.inner χ.conj χ.conj = 1)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    (hdiffsuppχ : (χ.conj - χ).support ⊆ A)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction L ℂ) (degMem : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hcover : ∀ x ∈ S₁, ∃ i, i ∈ s ∧ χmem i = x)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁) (hmembarS1 : ∀ i ∈ s, (χmem i).conj ∈ S₁)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (1 : ℂ) else 0)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i) (χmem i).conj = 0)
    (hdegpos : 0 < degMem i₁)
    (hdegMem : ∀ i ∈ s, ((χmem i : ClassFunction L ℂ) : L → ℂ) 1 = (degMem i : ℂ))
    (hmemdiffsupp : ∀ i ∈ s, ((χmem i).conj - χmem i).support ⊆ A)
    (hdegdiffsupp : ∀ i ∈ s, (degMem i₁ • χmem i - degMem i • χmem i₁).support ⊆ A)
    {a : ℕ} (hχdeg : ((χ : ClassFunction L ℂ) : L → ℂ) 1 = (a : ℂ) * (degMem i₁ : ℂ))
    (hdiffasuppχ : (χ - a • χmem i₁).support ⊆ A)
    (htau1_memaχ : hyp.tau (χ - a • χmem i₁) ∈ ZIrr G)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((degMem i : ℝ) / (degMem i₁ : ℝ)) ^ 2) :
    Nonempty (IsCoherent hyp.tau (S₁ ∪ {χ, χ.conj}) A) := by
  classical
  obtain ⟨hc⟩ := hcoh
  have hχbarS : χ.conj ∈ S := hyp.conjugate_mem hχS
  have hχχbar : ClassFunction.inner χ χ.conj = 0 :=
    hyp.pairwise_orthogonal hχS hχbarS (hyp.ne_conj hχS)
  have hχbarχ : ClassFunction.inner χ.conj χ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχχbar, star_zero]
  -- `hSgen` (scaled generation, issue 1050): `d₁ • χmem i = (d₁•χmem i − dᵢ•χ₁) + dᵢ•χ₁`
  -- with the scaled difference supported (`hdegdiffsupp`), so every member lifts into
  -- `ℤ[ℤ[𝒮₁,A] ∪ {χ₁}]` after scaling by `d₁ > 0`.  No member-degree divisibility is needed.
  have hSgen : ∀ x ∈ S₁, ∃ n : ℕ, 0 < n ∧
      (n : ℤ) • x ∈ Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χmem i₁}) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hcover x hx
    refine ⟨degMem i₁, hdegpos, ?_⟩
    have hδℤ : degMem i₁ • χmem i - degMem i • χmem i₁ ∈ Submodule.span ℤ S₁ := by
      refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ (degMem i₁) (χmem i)]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i hi))
      · rw [← Nat.cast_smul_eq_nsmul ℤ (degMem i) (χmem i₁)]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
    have hsplit : (degMem i₁ : ℤ) • χmem i
        = (degMem i₁ • χmem i - degMem i • χmem i₁) + (degMem i : ℤ) • χmem i₁ := by
      rw [Nat.cast_smul_eq_nsmul ℤ (degMem i₁) (χmem i),
        Nat.cast_smul_eq_nsmul ℤ (degMem i) (χmem i₁)]
      abel
    rw [hsplit]
    exact Submodule.add_mem _
      (Submodule.subset_span (Set.mem_union_left _ ⟨hδℤ, hdegdiffsupp i hi⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_union_right _ rfl)))
  -- `hgen`: from the `A`-supports of the two adjoined differences alone (issue 1050).
  have hdiffconj : (χ - χ.conj).support ⊆ A := by
    rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]
    exact hdiffsuppχ
  have hgen := zSupportedSpan_adjoinPair_subset_span_of_diffSupports (a := a)
    (hmemS1 i₁ hi₁) hdiffconj hdiffasuppχ
  -- `R(χmem i) ⊥ R(χ)` for each member, from `χmem i ⊥ χ, χ̄`.
  have hmemOrtho : ∀ i (hi : i ∈ s),
      (hyp.difference_image (hS₁S (hmemS1 i hi))).Orthogonal (hyp.difference_image hχS) :=
    fun i hi => hyp.difference_images_orthogonal (hS₁S (hmemS1 i hi)) hχS
      (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 (χmem i) (hmemS1 i hi),
        star_zero])
      (by rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 (χmem i) (hmemS1 i hi),
        star_zero])
  exact ⟨adjoinPairCoherent_general (Samb := S) hc hS₁S hyp.adjoin_hisom
    (hyp.difference_image hχS) hχS hχbarS hdiffsuppχ hχχ hχbarχbar hχχbar hχbarχ hχ_S1 hχbar_S1
    s χmem degMem i₁ hi₁ (fun i hi => hyp.difference_image (hS₁S (hmemS1 i hi)))
    hdegpos hmemdiffsupp hdegdiffsupp hmemS1 hmembarS1 hmemconjortho hmemortho
    hmemOrtho hdiffasuppχ htau1_memaχ hDeg hSgen hgen⟩

end LemmaOne

/-! ## Lemma 2: the induced family and the induction isometry (p. 145) -/

section LemmaTwo

set_option linter.unusedSectionVars false

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (hyp : Hypothesis G) [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

omit [Fintype G] in
open scoped ComplexOrder in
/-- **Peterfalvi Appendix IV, Lemma 2(a)** (p. 145).  `𝒮` is exactly the set of
characters `Ind_Q^H φ` induced from those `φ ∈ Irr(Q)` with `Q₁ ⊄ Ker φ`.

Peterfalvi writes `φ = λθ` with `λ ∈ Irr(S)`, `θ ∈ Irr(Q₁) - {1}` and cites the Frobenius
structure of `Q₁D` (Isaacs 6.34); here the inertia computation is done directly, avoiding
the product-character decomposition (issue 1051).  **Forward**: for `φ ∈ Irr(Q)` with
`Q₁ ⊄ Ker φ`, extract a nontrivial constituent `θ ∈ Irr(Q₁)` of `Res φ`
(`exists_ne_trivial_liesOver_of_not_forall_eq_one`); its inertia group in `H` is exactly `Q`
(`Hypothesis.inertia_theta_eq_Q`, from the fixed-point-free action of `D` on `Q₁`), so
`Ind_Q^H φ` is irreducible by the Clifford correspondence
(`isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq`, Isaacs 6.11); and `Ind_Q^H φ` is
not constant on `Q₁`, since the θ-part bound
(`restrictionMultiplicity_mul_le_restrictionMultiplicity`, with `⟨Res_Q Ind φ, φ⟩ = 1` by
Frobenius reciprocity) gives it a nontrivial `Q₁`-constituent, which a character constant on
`Q₁` cannot have (`restrictionMultiplicity_eq_zero_of_forall_eq_one`).  **Converse**: `χ ∈ 𝒮`
lies over some nontrivial `θ ∈ Irr(Q₁)`; the constituent passes through the intermediate
subgroup `Q` (`exists_restrictionMultiplicity_ne_zero_intermediate`), giving `ψ ∈ Irr(Q)`
over `θ` with `⟨Res_Q χ, ψ⟩ ≠ 0`; then `Ind_Q^H ψ` is irreducible as above and
`⟨Ind_Q^H ψ, χ⟩ ≠ 0` (Frobenius reciprocity), so `χ = Ind_Q^H ψ` by orthogonality of
distinct irreducible characters, and `Q₁ ⊄ Ker ψ` since `ψ` lies over the nontrivial `θ`. -/
theorem Sset_eq_induced_of_Q [Finite G] :
    hyp.Sset =
      (fun φ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ =>
          ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ) ''
        {φ | IsIrreducibleCharacter φ ∧
          ¬ ∀ x : ↥(hyp.Q.subgroupOf hyp.H), ((x : ↥hyp.H) : G) ∈ hyp.Q1 → φ x = φ 1} := by
  classical
  haveI hQ1n : (hyp.Q1.subgroupOf hyp.H).Normal := hyp.Q1_subgroupOf_H_normal
  have hHT : hyp.Q1.subgroupOf hyp.H ≤ hyp.Q.subgroupOf hyp.H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hyp.Q1_le_Q (Subgroup.mem_subgroupOf.mp hx))
  -- finiteness / invertibility bookkeeping
  letI : Fintype ↥(hyp.Q.subgroupOf hyp.H) := Fintype.ofFinite _
  letI : Fintype ↥(hyp.Q1.subgroupOf hyp.H) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hyp.Q1.subgroupOf hyp.H) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) :=
    Fintype.ofFinite _
  letI : Invertible
      ((Nat.card ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Finite (IrreducibleCharacter
      ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))) :=
    finite_irreducibleCharacter
  letI : Fintype (IrreducibleCharacter
      ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))) := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H)) :=
    finite_irreducibleCharacter
  letI : Fintype (IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H)) := Fintype.ofFinite _
  ext χ
  constructor
  · -- `𝒮 ⊆` the induced set
    intro hχmem
    obtain ⟨hχirr, hχker⟩ := hχmem
    -- a nontrivial constituent `θ ∈ Irr(Q₁)` of `Res χ`
    have hker' : ¬ ∀ y : ↥(hyp.Q1.subgroupOf hyp.H), χ (y : ↥hyp.H) = χ 1 := fun hall =>
      hχker fun x hx => hall ⟨x, Subgroup.mem_subgroupOf.mpr hx⟩
    obtain ⟨θ, hθne, hθover⟩ := exists_ne_trivial_liesOver_of_not_forall_eq_one
      (⟨χ, hχirr⟩ : IrreducibleCharacter ↥hyp.H) hker'
    have hinertia := hyp.inertia_theta_eq_Q hθne
    -- the constituent passes through `Q`: some `ψ ∈ Irr(Q)` over `θ` with `⟨Res_Q χ, ψ⟩ ≠ 0`
    obtain ⟨ψ, hψχ, hψover⟩ := exists_restrictionMultiplicity_ne_zero_intermediate hHT
      (χ := χ) (θ := (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ)) hθover
    -- `Ind_Q^H ψ` is irreducible (Clifford correspondence)
    have hindirr : IsIrreducibleCharacter (ClassFunction.induce (hyp.Q.subgroupOf hyp.H)
        (ψ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ)) :=
      isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq hHT θ.isIrreducible hinertia ψ
        hψover
    -- `Ind_Q^H ψ = χ` by orthogonality of distinct irreducible characters
    have hfrob := inner_induce_coe_eq_restrictionMultiplicity (G := ↥hyp.H) ψ
      (⟨χ, hχirr⟩ : IrreducibleCharacter ↥hyp.H)
    simp only [IrreducibleCharacter.coe_mk] at hfrob
    have hinner : ClassFunction.inner (ClassFunction.induce (hyp.Q.subgroupOf hyp.H)
        (ψ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ)) χ ≠ 0 :=
      fun h0 => hψχ (hfrob.symm.trans h0)
    have heq : (⟨_, hindirr⟩ : IrreducibleCharacter ↥hyp.H)
        = (⟨χ, hχirr⟩ : IrreducibleCharacter ↥hyp.H) := by
      by_contra hneq
      have hite := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
        (⟨_, hindirr⟩ : IrreducibleCharacter ↥hyp.H)
        (⟨χ, hχirr⟩ : IrreducibleCharacter ↥hyp.H)
      rw [if_neg hneq] at hite
      simp only [IrreducibleCharacter.coe_mk] at hite
      exact hinner hite
    refine ⟨(ψ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ), ⟨ψ.isIrreducible, ?_⟩, ?_⟩
    · -- `Q₁ ⊄ Ker ψ`: `ψ` constant on `Q₁` would contradict `ψ` lying over the nontrivial `θ`
      intro hall
      have hθ'irr : IsIrreducibleCharacter (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom
          (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ)) :=
        IsIrreducibleCharacter.compHom_of_surjective
          (Subgroup.subgroupOfEquivOfLe hHT).surjective θ.isIrreducible
      have hθ'ne : (⟨_, hθ'irr⟩ : IrreducibleCharacter
          ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)))
          ≠ trivialIrreducibleCharacter _ := fun h =>
        compHom_mulEquiv_ne_trivial (Subgroup.subgroupOfEquivOfLe hHT)
          (fun hc => hθne (Subtype.ext hc)) (congrArg Subtype.val h)
      have hzero := restrictionMultiplicity_eq_zero_of_forall_eq_one
        (N := (hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))
        (ψ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ)
        (fun y => hall (y : ↥(hyp.Q.subgroupOf hyp.H))
          (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp y.2)))
        hθ'ne
      simp only [IrreducibleCharacter.coe_mk] at hzero
      exact hψover hzero
    · exact congrArg Subtype.val heq
  · -- the induced set `⊆ 𝒮`
    rintro ⟨φ, ⟨hφirr, hφker⟩, rfl⟩
    -- a nontrivial constituent `θ'' ∈ Irr(Q₁-in-Q)` of `Res φ`
    have hker' : ¬ ∀ y : ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)),
        φ (y : ↥(hyp.Q.subgroupOf hyp.H)) = φ 1 := fun hall =>
      hφker fun x hx =>
        hall ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hx)⟩
    obtain ⟨θ'', hθ''ne, hθ''over⟩ := exists_ne_trivial_liesOver_of_not_forall_eq_one
      (⟨φ, hφirr⟩ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H)) hker'
    -- transport `θ''` to `Irr(Q₁)` along `↥(Q₁-in-Q) ≃* ↥Q₁`
    have hθirr : IsIrreducibleCharacter (ClassFunction.compHom
        (Subgroup.subgroupOfEquivOfLe hHT).symm.toMonoidHom
        (θ'' : ClassFunction
          ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) ℂ)) :=
      IsIrreducibleCharacter.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe hHT).symm.surjective θ''.isIrreducible
    have hθne : (⟨_, hθirr⟩ : IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H))
        ≠ trivialIrreducibleCharacter _ := fun h =>
      compHom_mulEquiv_ne_trivial (Subgroup.subgroupOfEquivOfLe hHT).symm
        (fun hc => hθ''ne (Subtype.ext hc)) (congrArg Subtype.val h)
    have hinertia := hyp.inertia_theta_eq_Q hθne
    simp only [IrreducibleCharacter.coe_mk] at hinertia
    -- transporting back along the equivalence recovers `θ''`
    have hround : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).symm.toMonoidHom
          (θ'' : ClassFunction
            ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) ℂ))
        = (θ'' : ClassFunction
            ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) ℂ) :=
      compHom_toMonoidHom_compHom_symm (Subgroup.subgroupOfEquivOfLe hHT) _
    -- Clifford: `Ind_Q^H φ` is irreducible
    have hover : ClassFunction.restrictionMultiplicity
        ((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) φ
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).symm.toMonoidHom
            (θ'' : ClassFunction
              ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) ℂ))) ≠ 0 := by
      rw [hround]
      exact hθ''over
    have hindirr : IsIrreducibleCharacter
        (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ) :=
      isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq hHT hθirr hinertia
        (⟨φ, hφirr⟩ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H)) hover
    refine ⟨hindirr, ?_⟩
    intro hLe
    -- `Ind φ` constant on `Q₁` kills the `θ`-multiplicity …
    have hzero := restrictionMultiplicity_eq_zero_of_forall_eq_one
      (N := hyp.Q1.subgroupOf hyp.H) (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ)
      (fun x => hLe (x : ↥hyp.H) (Subgroup.mem_subgroupOf.mp x.2)) hθne
    simp only [IrreducibleCharacter.coe_mk] at hzero
    -- … but the θ-part bound forces it nonzero: `⟨Res_Q (Ind φ), φ⟩ = 1` and `φ` lies over `θ`
    have hfrob := inner_induce_coe_eq_restrictionMultiplicity (G := ↥hyp.H)
      (⟨φ, hφirr⟩ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H))
      (⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ, hindirr⟩ :
        IrreducibleCharacter ↥hyp.H)
    have hself := irreducibleCharacter_inner_eq_ite (G := ↥hyp.H)
      (⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ, hindirr⟩ :
        IrreducibleCharacter ↥hyp.H)
      (⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ, hindirr⟩ :
        IrreducibleCharacter ↥hyp.H)
    rw [if_pos rfl] at hself
    simp only [IrreducibleCharacter.coe_mk] at hfrob hself
    have hfirst := hfrob.symm.trans hself
    have hbound := restrictionMultiplicity_mul_le_restrictionMultiplicity (G := ↥hyp.H) hHT
      (⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ, hindirr⟩ :
        IrreducibleCharacter ↥hyp.H)
      (⟨φ, hφirr⟩ : IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.H)) hθirr
    simp only [IrreducibleCharacter.coe_mk] at hbound
    rw [hfirst, one_mul, hround, hzero] at hbound
    have hnonneg := ClassFunction.restrictionMultiplicity_nonneg
      ((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) hφirr
      θ''.isIrreducible
    exact hθ''over (le_antisymm hbound hnonneg)

omit [Fintype G] in
/-- **Corollary of Lemma 2(a)**: every member of `𝒮` vanishes on `H − Q`.  The members of
`𝒮` are induced from `Q ⊴ H` (`Sset_eq_induced_of_Q`), and class functions induced from a
normal subgroup vanish off it (`ClassFunction.induce_apply_eq_zero_of_not_mem_normal`).
This is the support input to the induction isometry of Lemma 2(b) (Isaacs Lemma 7.7) and to
the `A`-support hypotheses of Lemma 1(a) at the Theorem's call sites. -/
theorem apply_eq_zero_of_mem_Sset_of_not_mem_Q [Finite G]
    {χ : ClassFunction ↥hyp.H ℂ} (hχ : χ ∈ hyp.Sset)
    {h : ↥hyp.H} (hh : (h : G) ∉ hyp.Q) : χ h = 0 := by
  haveI : (hyp.Q.subgroupOf hyp.H).Normal := hyp.Q_subgroupOf_H_normal
  have hmem := hχ
  rw [Sset_eq_induced_of_Q hyp] at hmem
  obtain ⟨φ, _, rfl⟩ := hmem
  exact ClassFunction.induce_apply_eq_zero_of_not_mem_normal (hyp.Q.subgroupOf hyp.H) φ
    (fun hmem' => hh (Subgroup.mem_subgroupOf.mp hmem'))

omit [Fintype G] in
/-- **Members of `ℤ[𝒮]` vanish on `H − Q`** (span form of
`apply_eq_zero_of_mem_Sset_of_not_mem_Q`, by induction over the `ℤ`-span). -/
theorem zSpan_Sset_apply_eq_zero_of_not_mem_Q [Finite G]
    {φ : ClassFunction ↥hyp.H ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset)
    {x : ↥hyp.H} (hx : (x : G) ∉ hyp.Q) : φ x = 0 := by
  induction hφ using Submodule.span_induction with
  | mem χ hχ => exact apply_eq_zero_of_mem_Sset_of_not_mem_Q hyp hχ hx
  | zero => simp
  | add χ ρ _ _ hχ hρ => rw [ClassFunction.add_apply, hχ, hρ, add_zero]
  | smul n χ _ hχ =>
      rw [← Int.cast_smul_eq_zsmul ℂ n χ, ClassFunction.smul_apply, hχ, mul_zero]

/-- **Peterfalvi Appendix IV, Lemma 2(b)** (p. 145).  `ψ ↦ Ind_H^G ψ` is an
isometry from `ℤ[𝒮]°` (the degree-zero part of the lattice spanned by `𝒮`) to
`ℤ[Irr G]°`: it preserves inner products, lands in `ℤ[Irr G]`, and preserves the
degree-zero condition.

The **integrality** clause is `Hypothesis.tau_mem_ZIrr` and the **degree-zero** clause is
`Hypothesis.tau_apply_one`.  For the **isometry**, the book cites Isaacs Lemma 7.7: a
degree-zero member of `ℤ[𝒮]` vanishes off `Q^# = Q \ {1}` (Lemma 2(a) via
`zSpan_Sset_apply_eq_zero_of_not_mem_Q`, plus the degree-zero condition at `1`), `Q^#` is a
TI-subset of `G` with normalizer-bound `H` (`Hypothesis.isTISubset_Q_sdiff_one`, from
`Q_trivial_intersection`), and induction from a TI-subset-supported class function is an
isometry (`ClassFunction.inner_induce_eq_of_isTISubset`). -/
theorem induction_isometry_on_degree_zero
    (φ ψ : ClassFunction ↥hyp.H ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset)
    (hψ : ψ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset)
    (hφ1 : φ (1 : ↥hyp.H) = 0) (hψ1 : ψ (1 : ↥hyp.H) = 0) :
    ClassFunction.inner (hyp.tau φ) (hyp.tau ψ) = ClassFunction.inner φ ψ ∧
      hyp.tau φ ∈ ZIrr G ∧ (hyp.tau φ) (1 : G) = 0 := by
  refine ⟨?_, hyp.tau_mem_ZIrr hφ, hyp.tau_apply_one hφ1⟩
  haveI : Finite G := Finite.of_fintype G
  -- degree-zero members of `ℤ[𝒮]` vanish off the TI-subset `A = Q \ {1}`
  have hoff : ∀ ρ : ClassFunction ↥hyp.H ℂ,
      ρ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset → ρ (1 : ↥hyp.H) = 0 →
      ∀ x : ↥hyp.H, (x : G) ∉ ((hyp.Q : Set G) \ {1}) → ρ x = 0 := by
    intro ρ hρ hρ1 x hx
    by_cases hxQ : (x : G) ∈ hyp.Q
    · have hx1 : (x : G) = 1 := by
        by_contra h1
        exact hx ⟨hxQ, h1⟩
      have hxone : x = (1 : ↥hyp.H) := Subtype.ext hx1
      rw [hxone]
      exact hρ1
    · exact zSpan_Sset_apply_eq_zero_of_not_mem_Q hyp hρ hxQ
  exact ClassFunction.inner_induce_eq_of_isTISubset hyp.H hyp.isTISubset_Q_sdiff_one
    (hoff φ hφ hφ1) (hoff ψ hψ hψ1)

omit [Fintype G] [Fintype ↥hyp.H] in
/-- **Peterfalvi Appendix IV, Lemma 2(c)** (p. 145).  If `d = |D|` and `|Q₁|` are odd
then no `χ ∈ 𝒮` is real: `χ̄ ≠ χ`.

The book states the lemma for `d` odd alone, and its proof reads "the restriction of
`χ` to the odd order group `Q₁D` is irreducible and non-principal, whence `χ̄ ≠ χ` by
[H], Kapitel V, Satz 13.8".  The oddness of `|Q₁D| = |Q₁|·d` uses oddness of `|Q₁|`,
which the hypothesis block does not supply: `D` acting fixed-point-freely on the
non-`2`-group `Q₁` with `d` odd is satisfiable with `|Q₁|` even (e.g.
`Q₁ = V₄ × C₇`, `D = C₃`).  At the Theorem's call sites this is harmless: after the
reductions (1)–(2) of the Theorem's proof (pp. 146–147), `Q₁` is a `p`-group for a
single prime `p`, and `p ≠ 2` since `Q₁` is not a `2`-group — so `|Q₁|` is odd there.
We therefore take `Odd |Q₁|` as an explicit hypothesis.

The proof avoids the book's Mackey restriction computation.  A real `χ ∈ 𝒮` lies over
a nontrivial `θ ∈ Irr(Q₁)` (`exists_ne_trivial_liesOver_of_not_forall_eq_one`) and,
being real, also over `θ̄`; Clifford's single-orbit theorem
(`restrictionConstituentsSingleOrbit_of_isIrreducible`) gives `θ̄ = θ^g` for some
`g = q·δ ∈ QD = H`, and `Q` acts trivially on `Irr(Q₁)` (`Q_conjBy_eq`), so
`θ̄ = θ^δ` with `δ ∈ D`.  Applying `^δ` again, `θ^{δ²} = θ̄̄ = θ`, so
`δ² ∈ I_H(θ) = Q` (`inertia_theta_eq_Q`); but `δ² ∈ D` too and `Q ∩ D = 1`, so
`δ² = 1`, and `δ` has odd order (`d` odd), forcing `δ = 1`.  Hence `θ` is a real
nontrivial irreducible character of the odd-order group `Q₁`, contradicting
Peterfalvi (1.1) (`not_isReal_of_ne_trivial_of_odd_card'`). -/
theorem hasNoRealCharacters_Sset [Finite G] (hd : Odd hyp.d)
    (hQ1odd : Odd (Nat.card ↥hyp.Q1)) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Sset := by
  classical
  haveI hQ1n : (hyp.Q1.subgroupOf hyp.H).Normal := hyp.Q1_subgroupOf_H_normal
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  letI : Fintype ↥(hyp.Q1.subgroupOf hyp.H) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(hyp.Q1.subgroupOf hyp.H) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Finite (IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H)) :=
    finite_irreducibleCharacter
  letI : Fintype (IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H)) := Fintype.ofFinite _
  intro χ hχmem hreal
  obtain ⟨hχirr, hχker⟩ := hχmem
  have hconjχ : χ.conj = χ := hreal
  -- a nontrivial constituent `θ ∈ Irr(Q₁)` of `Res χ`
  have hker' : ¬ ∀ y : ↥(hyp.Q1.subgroupOf hyp.H), χ (y : ↥hyp.H) = χ 1 := fun hall =>
    hχker fun x hx => hall ⟨x, Subgroup.mem_subgroupOf.mpr hx⟩
  obtain ⟨θ, hθne, hθover⟩ := exists_ne_trivial_liesOver_of_not_forall_eq_one
    (⟨χ, hχirr⟩ : IrreducibleCharacter ↥hyp.H) hker'
  -- `χ` is real, so `Res χ` is a real class function
  have hres_conj : (ClassFunction.restrict (hyp.Q1.subgroupOf hyp.H) χ).conj
      = ClassFunction.restrict (hyp.Q1.subgroupOf hyp.H) χ := by
    have h1 : (ClassFunction.restrict (hyp.Q1.subgroupOf hyp.H) χ).conj
        = ClassFunction.restrict (hyp.Q1.subgroupOf hyp.H) χ.conj := rfl
    rw [h1, hconjχ]
  -- … so `θ̄` is also a constituent of `Res χ`
  have hover_bar : IrreducibleCharacter.LiesOver (hyp.Q1.subgroupOf hyp.H)
      (⟨χ, hχirr⟩ : IrreducibleCharacter ↥hyp.H)
      (⟨(θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ).conj, θ.isIrreducible.conj⟩ :
        IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H)) := by
    rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def]
    simp only [IrreducibleCharacter.coe_mk]
    rw [← hres_conj, inner_conj_conj]
    intro h0
    rw [star_eq_zero] at h0
    have hover' := hθover
    rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def] at hover'
    simp only [IrreducibleCharacter.coe_mk] at hover'
    exact hover' h0
  -- Clifford single-orbit: `θ̄ = θ^g` for some `g ∈ H`; write `g = q·δ` and kill `q`
  obtain ⟨g, hg⟩ := restrictionConstituentsSingleOrbit_of_isIrreducible
    (H := hyp.Q1.subgroupOf hyp.H) (⟨χ, hχirr⟩ : IrreducibleCharacter ↥hyp.H)
    θ _ hθover hover_bar
  obtain ⟨q, hqQ, δ, hδD, rfl⟩ := hyp.exists_mem_Q_mul_mem_D_subtype g
  have hq1 : IrreducibleCharacter.conjBy (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) q θ
      = θ := by
    apply IrreducibleCharacter.ext
    rw [IrreducibleCharacter.coe_conjBy]
    exact hyp.Q_conjBy_eq hqQ _
  rw [IrreducibleCharacter.conjBy_mul, hq1] at hg
  -- class-function form `θ^δ = θ̄`
  have hδconj : ClassFunction.conjBy (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) δ
      (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ)
      = (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ).conj := by
    have hcoe := congrArg
      (fun ξ : IrreducibleCharacter ↥(hyp.Q1.subgroupOf hyp.H) =>
        (ξ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ)) hg
    simpa [IrreducibleCharacter.coe_conjBy] using hcoe
  -- `θ^{δ²} = θ`, so `δ² ∈ I_H(θ) = Q`; but `δ² ∈ D` and `Q ∩ D = 1`
  have hcomm : (ClassFunction.conjBy (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) δ
      (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ)).conj
      = ClassFunction.conjBy (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) δ
        (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ).conj := by
    ext x
    rw [ClassFunction.conj_apply, ClassFunction.conjBy_apply, ClassFunction.conjBy_apply,
      ClassFunction.conj_apply]
  have hg2 : ClassFunction.conjBy (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H) (δ * δ)
      (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ)
      = (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ) := by
    rw [ClassFunction.conjBy_mul, hδconj, ← hcomm, hδconj, ClassFunction.conj_conj]
  have hδ2Q : δ * δ ∈ hyp.Q.subgroupOf hyp.H := by
    have hmem : δ * δ ∈ ClassFunction.inertia (G := ↥hyp.H) (H := hyp.Q1.subgroupOf hyp.H)
        (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ) :=
      ClassFunction.mem_inertia.mpr hg2
    rwa [hyp.inertia_theta_eq_Q hθne] at hmem
  have hδ2_one : (δ : G) * (δ : G) = 1 := by
    have hQmem : ((δ * δ : ↥hyp.H) : G) ∈ hyp.Q := Subgroup.mem_subgroupOf.mp hδ2Q
    have hDmem : ((δ * δ : ↥hyp.H) : G) ∈ hyp.D := by
      rw [Subgroup.coe_mul]; exact hyp.D.mul_mem hδD hδD
    have hbot : ((δ * δ : ↥hyp.H) : G) ∈ hyp.Q ⊓ hyp.D := ⟨hQmem, hDmem⟩
    rw [hyp.Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
    simpa [Subgroup.coe_mul] using hbot
  -- `δ` has odd order and squares to `1`, so `δ = 1`
  have hdvd : orderOf ((δ : ↥hyp.H) : G) ∣ hyp.d := hyp.D.orderOf_dvd_natCard hδD
  have hoddδ : Odd (orderOf ((δ : ↥hyp.H) : G)) := hd.of_dvd_nat hdvd
  have hpow : ((δ : ↥hyp.H) : G) ^ 2 = 1 := by rw [pow_two]; exact hδ2_one
  have hδG1 : ((δ : ↥hyp.H) : G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow) with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · rw [h2] at hoddδ
      exact absurd hoddδ (by decide)
  have hδ1 : δ = 1 := Subtype.ext (by simpa using hδG1)
  -- hence `θ` is real — impossible in the odd-order group `Q₁`
  have hθreal : ClassFunction.IsReal (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ) := by
    have hcoeθ : (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ).conj
        = (θ : ClassFunction ↥(hyp.Q1.subgroupOf hyp.H) ℂ) := by
      rw [← hδconj, hδ1, ClassFunction.conjBy_one]
    exact hcoeθ
  have hoddN : Odd (Nat.card ↥(hyp.Q1.subgroupOf hyp.H)) := by
    have hcard : Nat.card ↥(hyp.Q1.subgroupOf hyp.H) = Nat.card ↥hyp.Q1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q1_le_H).toEquiv
    rw [hcard]; exact hQ1odd
  exact not_isReal_of_ne_trivial_of_odd_card' hoddN hθne hθreal

end LemmaTwo

/-! ## The Feit-Sibley Theorem (pp. 146--150) -/

section MainTheorem

/-- **Peterfalvi Appendix IV, Theorem** (p. 146).  If `d = |D|` is odd, then `𝒮`
is coherent with respect to the induction isometry `τ = Ind_H^G` of Lemma 2(b).

**Status: honestly stated, not proved.**  Every ingredient is now a real
statement: `hyp` is the book's hypothesis block, `hyp.Sset` and `hyp.A` are the
book's `𝒮` and `Q^#`, and `hyp.tau` *is* `Ind_H^G`.

Peterfalvi's proof is the eight-step argument on pp. 146--150: reductions (1)
and (2) (`𝒮(S')` coherent when `|Q₁|` has two prime divisors; `𝒮` coherent when
`𝒮(S')` is) let one assume `Q₁` is a non-abelian `p`-group; step (3) makes
`𝒳 = 𝒮 - 𝒮(Z)` coherent for `1 ≠ Z ⊴ H` with `Z ≤ Z(Q₁)`; steps (4)--(6) set up
`𝒴 = 𝒮(Q')` and reduce coherence of `𝒮` to `a ∣ λ`; step (7) is the class-algebra
congruence `ψ(z) ≡ ψ(1) (mod |Q|)` for `ψ ∈ Irr(G)` constant on `Z^#`; step (8)
combines them.  Lemma 1(a) (`coherent_adjoin_of_degree_bound`, issue 1049),
Lemma 2(a) (`Sset_eq_induced_of_Q`, issue 1051), Lemma 2(b)
(`induction_isometry_on_degree_zero`, issue 1052) and Lemma 2(c)
(`hasNoRealCharacters_Sset`, issue 1053; its `Odd |Q₁|` hypothesis is available
here post-reduction, where `Q₁` is a `p`-group for a prime `p ≠ 2`) are now
proved.  Steps (1)--(6) are formalized (reductions
`ssetOf_sder_coherent_of_two_primes`/`sset_coherent_of_ssetOf_sder_coherent`,
step (3) `xset_coherent_of_le_center_Q1`, and the (6) union coherence
`union_coherent_of_lambda_dvd`, `a ∣ λ ⟹ 𝒳 ∪ 𝒴` coherent).  Step (7)'s class-sum
congruence for a Hall TI subgroup is now in the repository
(`peterfalvi_67_hall_of_odd`, `HallTICongruence.lean`), together with the (8)
divisibility core `dvd_of_isIntegral_ratio` and the regular-character value
`sum_degree_mul_charValue_XsetOf_bot`.  The remaining work is the (8) final
assembly (`Res_H e'₁` analysis → `a ∣ λ`) and the step-(5) adjoin closing `𝒮`
(campaign issue 1054). -/
theorem feit_sibley_coherence [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis G) [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
    (hd : Odd hyp.d) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  sorry

end MainTheorem

end OddOrder.Peterfalvi.Appendices.FeitSibley
