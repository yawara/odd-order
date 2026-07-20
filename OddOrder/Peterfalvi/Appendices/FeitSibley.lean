/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups

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
| Lemma 1(a) (`coherent_adjoin_of_degree_bound`) | honest statement, `sorry` |
| Lemma 2(a) (`Sset_eq_induced_of_Q`) | honest statement, `sorry` |
| Lemma 2(b) (`induction_isometry_on_degree_zero`) | honest statement; isometry clause `sorry` |
| Lemma 2(c) (`hasNoRealCharacters_Sset`) | honest statement, `sorry` |
| Theorem (`feit_sibley_coherence`) | honest statement, `sorry` |
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

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

/-- **Peterfalvi Appendix IV, Lemma 1(a)** (p. 144; Isaacs, *Character Theory of
Finite Groups*, Theorem 7.14).  Let `𝒮 = 𝒮₀ ∪ {ψ}` with `(𝒮₀, τ)` coherent, and
suppose some `χ₀ ∈ 𝒮₀` satisfies

`χ₀(1) ∣ ψ(1)`  and  `2 χ₀(1) ψ(1) < ∑_{χ ∈ 𝒮₀} χ(1)²`.

Then `(𝒮, τ)` is coherent.

Degrees are carried by an explicit `deg : ClassFunction L ℂ → ℕ` with
`χ 1 = deg χ`, so the divisibility and the inequality are honest statements
about natural numbers (character degrees are positive integers).

**Status: honestly stated, not proved.**  This is Isaacs' "adjoin one character
to a coherent set" theorem, whose proof is the norm computation on
`ψ - (ψ(1)/χ₀(1)) χ₀` followed by the sign/uniqueness analysis of its image.
The repository has the machinery for the equal-degree case
(`coherent_of_constant_degree`, `coherentEqualDegree_extension`) and the
retargeting apparatus (`S07_RetargetScaled`), but not the mixed-degree adjoin
step; that is the precise missing prerequisite. -/
theorem coherent_adjoin_of_degree_bound
    (hyp : OddOrder.Peterfalvi.S07.Hypothesis (L := L) (G := G) S A)
    (S0 : Set (ClassFunction L ℂ)) (hS0fin : S0.Finite)
    (ψ χ0 : ClassFunction L ℂ) (hS : S = S0 ∪ {ψ}) (hψ : ψ ∉ S0) (hχ0 : χ0 ∈ S0)
    (hcoh : Nonempty (IsCoherent hyp.tau S0 A))
    (deg : ClassFunction L ℂ → ℕ)
    (hdeg : ∀ χ ∈ S, ((χ : ClassFunction L ℂ) : L → ℂ) 1 = (deg χ : ℂ))
    (hdvd : deg χ0 ∣ deg ψ)
    (hlt : 2 * deg χ0 * deg ψ < ∑ χ ∈ hS0fin.toFinset, (deg χ) ^ 2) :
    Nonempty (IsCoherent hyp.tau S A) := by
  sorry

end LemmaOne

/-! ## Lemma 2: the induced family and the induction isometry (p. 145) -/

section LemmaTwo

set_option linter.unusedSectionVars false

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (hyp : Hypothesis G) [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

omit [Fintype G] in
/-- **Peterfalvi Appendix IV, Lemma 2(a)** (p. 145).  `𝒮` is exactly the set of
characters `Ind_Q^H φ` induced from those `φ ∈ Irr(Q)` with `Q₁ ⊄ Ker φ`.

**Status: honestly stated, not proved.**  Peterfalvi's proof: write
`φ = λ θ` with `λ ∈ Irr(S)`, `θ ∈ Irr(Q₁) - {1}`; the inertia group of `φ` in
`H` is `Q` because `Q₁ D` is a Frobenius group (Isaacs Thm. 6.34), so
`Ind_Q^H φ` is irreducible (Isaacs Thm. 6.11), and its restriction to `Q₁ D` is
`Ind_{Q₁}^{Q₁ D} θ`, whence `Q₁ ⊄ Ker Ind_Q^H φ`.  Conversely a `χ ∈ 𝒮`
restricted to `Q` has a constituent `φ` with `Q₁ ⊄ Ker φ`, so `χ = Ind_Q^H φ`.
The missing prerequisites are the Frobenius-inertia step (Isaacs 6.34 applied to
`Q₁ D`, which needs `D_fixedPointFree_on_Q1` transported to an abstract operator
action) and the induced-irreducibility criterion (Isaacs 6.11) for this
configuration. -/
theorem Sset_eq_induced_of_Q :
    hyp.Sset =
      (fun φ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ =>
          ClassFunction.induce (hyp.Q.subgroupOf hyp.H) φ) ''
        {φ | IsIrreducibleCharacter φ ∧
          ¬ ∀ x : ↥(hyp.Q.subgroupOf hyp.H), ((x : ↥hyp.H) : G) ∈ hyp.Q1 → φ x = φ 1} := by
  sorry

/-- **Peterfalvi Appendix IV, Lemma 2(b)** (p. 145).  `ψ ↦ Ind_H^G ψ` is an
isometry from `ℤ[𝒮]°` (the degree-zero part of the lattice spanned by `𝒮`) to
`ℤ[Irr G]°`: it preserves inner products, lands in `ℤ[Irr G]`, and preserves the
degree-zero condition.

**Status: partially proved.**  The **integrality** clause (`τ φ ∈ ℤ[Irr G]`) and the
**degree-zero** clause are proved sorry-free just above (`Hypothesis.tau_mem_ZIrr`,
`Hypothesis.tau_apply_one`) and are discharged in the proof below; only the
**isometry** clause is `sorry`.

For the isometry the book cites Isaacs Lemma 7.7, using that the elements of
`𝒮` vanish on `H - Q` (Lemma 2(a)) and that `Q` has trivial intersections in `G`
(`Q_trivial_intersection`).  The missing prerequisite is therefore Lemma 2(a)
together with the TI-vanishing form of the induction isometry for the subgroup
`Q` — the repository's TI-isometry material (`OddOrder.GroupTheory.TISubset`,
Peterfalvi §2--§4) is stated for `A`-supported class functions on a TI subset,
and has not been specialized to this `Q`-vanishing configuration. -/
theorem induction_isometry_on_degree_zero
    (φ ψ : ClassFunction ↥hyp.H ℂ)
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset)
    (hψ : ψ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.H) hyp.Sset)
    (hφ1 : φ (1 : ↥hyp.H) = 0) (hψ1 : ψ (1 : ↥hyp.H) = 0) :
    ClassFunction.inner (hyp.tau φ) (hyp.tau ψ) = ClassFunction.inner φ ψ ∧
      hyp.tau φ ∈ ZIrr G ∧ (hyp.tau φ) (1 : G) = 0 := by
  refine ⟨?_, hyp.tau_mem_ZIrr hφ, hyp.tau_apply_one hφ1⟩
  sorry

omit [Fintype G] [Fintype ↥hyp.H] in
/-- **Peterfalvi Appendix IV, Lemma 2(c)** (p. 145).  If `d = |D|` is odd then no
`χ ∈ 𝒮` is real: `χ̄ ≠ χ`.

**Status: honestly stated, not proved.**  By Lemma 2(a) the restriction of `χ`
to the odd-order group `Q₁ D` is irreducible and non-principal, so `χ̄ ≠ χ` by
Huppert, *Endliche Gruppen* I, Kapitel V, Satz 13.8 (a group of odd order has no
nonprincipal real irreducible character — a consequence of Burnside's
`|{real classes}| = |{real characters}|`).  The missing prerequisites are Lemma
2(a) and that odd-order statement, neither of which is in the repository. -/
theorem hasNoRealCharacters_Sset (hd : Odd hyp.d) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Sset := by
  sorry

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
combines them.  Every step consumes Lemma 1(a) (`coherent_adjoin_of_degree_bound`
above, unproved) and Lemma 2 (unproved), and step (7) needs the class-sum
congruence machinery for a Hall TI subgroup, which is not in the repository. -/
theorem feit_sibley_coherence [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis G) [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
    (hd : Odd hyp.d) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  sorry

end MainTheorem

end OddOrder.Peterfalvi.Appendices.FeitSibley
