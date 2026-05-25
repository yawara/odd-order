/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutation
import OddOrder.GroupTheory.RepresentationTheory.Clifford
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality
import OddOrder.Peterfalvi.S02_Notation

/-!
# Peterfalvi §3: Preliminary Results from Character Theory

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§3, pp. 5-9.

This file is the Lean entry point for Peterfalvi §3.  The numbered assertions
(1.1)-(1.10) depend on the Wave 1a character-theory modules imported above:
Brauer permutation, Clifford theory, induced characters, second orthogonality,
and the isometry difference-pair lemma.

The current slice records shared predicates and submodules used by §4-§8 while
the deferred character-theory statements remain routed to those Wave 1a modules.

Reference note: `notes/peterfalvi/s03_preliminary_character.md`.
-/

namespace OddOrder.Peterfalvi.S03

open OddOrder.RepresentationTheory
open scoped BigOperators

variable {G : Type*} [Group G]

/- 1: Preliminary character-theory notation (pp. 5-9) -/

/-- The nonidentity part `G#`, used throughout Peterfalvi's reduced character
spaces. -/
def nonidentityElements (G : Type*) [One G] : Set G :=
  {g | g ≠ 1}

@[simp] theorem mem_nonidentityElements {g : G} :
    g ∈ nonidentityElements G ↔ g ≠ 1 :=
  Iff.rfl

/-- Peterfalvi's reduced class-function space `CF(G, G#)`. -/
abbrev ReducedClassFunctions (k : Type*) [CommRing k] (G : Type*) [Group G] :=
  ↥(ClassFunction.supportedSubmodule (G := G) (k := k) (nonidentityElements G))

/-- A set of class functions is closed under complex conjugation. -/
def ClosedUnderConjugate (S : Set (ClassFunction G ℂ)) : Prop :=
  ∀ ⦃χ : ClassFunction G ℂ⦄, χ ∈ S → χ.conj ∈ S

/-- A set of class functions contains no real class functions. -/
def HasNoRealCharacters (S : Set (ClassFunction G ℂ)) : Prop :=
  ∀ ⦃χ : ClassFunction G ℂ⦄, χ ∈ S → ¬ χ.IsReal

/-- **Peterfalvi (1.1)**, cardinal form.

If `G` has odd order, then there is exactly one real irreducible complex
character.  The sharper textbook phrasing says that every nontrivial
irreducible character is non-real; identifying this unique real character with
the trivial character is routed to the later trivial-character API. -/
theorem card_realIrreducibleCharacters_eq_one_of_odd_card [Finite G]
    (hodd : Odd (Nat.card G)) :
    Nat.card (RealIrreducibleCharacter G) = 1 :=
  OddOrder.RepresentationTheory.card_realIrreducibleCharacters_eq_one_of_odd_card hodd

/-- The degree of a complex class function, i.e. its value at the identity.

For genuine characters this is the representation degree.  Naming it here keeps
Peterfalvi's degree hypotheses from unfolding to raw evaluation at `1`. -/
def characterDegree (χ : ClassFunction G ℂ) : ℂ :=
  χ 1

@[simp] theorem characterDegree_def (χ : ClassFunction G ℂ) :
    characterDegree χ = χ 1 :=
  rfl

@[simp] theorem characterDegree_conj (χ : ClassFunction G ℂ) :
    characterDegree χ.conj = star (characterDegree χ) :=
  rfl

/-- A family of class functions has constant degree. -/
def SameDegreeFamily {ι : Type*} (χ : ι → ClassFunction G ℂ) : Prop :=
  ∀ i j, characterDegree (χ i) = characterDegree (χ j)

/-- A set of class functions has constant degree. -/
def HasUniformDegree (S : Set (ClassFunction G ℂ)) : Prop :=
  ∃ d : ℂ, ∀ ⦃χ : ClassFunction G ℂ⦄, χ ∈ S → characterDegree χ = d

/-- `C_H(g)`, viewed as a subgroup of the ambient group `G`.  This is the
centralizer expression in Peterfalvi (1.2). -/
def centralizerInSubgroup (H : Subgroup G) (g : G) : Subgroup G :=
  H ⊓ Subgroup.centralizer ({g} : Set G)

@[simp] theorem mem_centralizerInSubgroup {H : Subgroup G} {g x : G} :
    x ∈ centralizerInSubgroup H g ↔ x ∈ H ∧ x * g = g * x := by
  simp [centralizerInSubgroup, Subgroup.mem_centralizer_singleton_iff]

/-- Peterfalvi (1.2)-style vanishing target: a class function vanishes at every
element whose centralizer in `H` is trivial. -/
def VanishesOnTrivialSubgroupCentralizers (H : Subgroup G) (χ : ClassFunction G ℂ) :
    Prop :=
  ∀ g : G, centralizerInSubgroup H g = ⊥ → χ g = 0

/-- The character kernel predicate `g ∈ ker χ`, expressed at the class-function
level by `χ(g) = χ(1)`.  For genuine characters this matches the usual kernel
condition. -/
def characterKernel (χ : ClassFunction G ℂ) : Set G :=
  {g | χ g = characterDegree χ}

@[simp] theorem mem_characterKernel {χ : ClassFunction G ℂ} {g : G} :
    g ∈ characterKernel χ ↔ χ g = characterDegree χ :=
  Iff.rfl

@[simp] theorem one_mem_characterKernel (χ : ClassFunction G ℂ) :
    (1 : G) ∈ characterKernel χ :=
  rfl

/-- A subset is contained in the character kernel.  This is the set-level shape
used in Peterfalvi (1.6). -/
def SubsetCharacterKernel (A : Set G) (χ : ClassFunction G ℂ) : Prop :=
  A ⊆ characterKernel χ

/-- Pairwise orthogonality for a set of class functions, using the normalized
inner product. -/
def PairwiseOrthogonal (S : Set (ClassFunction G ℂ))
    [Fintype G] [Invertible (Nat.card G : ℂ)] : Prop :=
  ∀ ⦃χ ψ : ClassFunction G ℂ⦄, χ ∈ S → ψ ∈ S → χ ≠ ψ →
    ClassFunction.inner χ ψ = 0

/-- The coefficient of `χ` in the induced-character expansion of a class
function `ψ` on a subgroup `H`.

This names the normalized inner product `(ψ, Res χ)_H` from Peterfalvi (1.3).
The numerical Frobenius-reciprocity theorem proving that these are the actual
induction coefficients remains routed to the `InducedCharacter` proof core. -/
def inductionCoefficient (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)]
    (ψ : ClassFunction H ℂ) (χ : ClassFunction G ℂ) : ℂ :=
  ClassFunction.inner ψ (ClassFunction.restrict H χ)

@[simp] theorem inductionCoefficient_def (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)]
    (ψ : ClassFunction H ℂ) (χ : ClassFunction G ℂ) :
    inductionCoefficient H ψ χ =
      ClassFunction.inner ψ (ClassFunction.restrict H χ) :=
  rfl

/-- Peterfalvi (1.3)-style induced-character expansion data.

`basis` is the family whose restrictions provide the coefficients, while
`image` is the target family appearing in the expansion of `Ind_H^G ψ`.  The
definition is intentionally predicate-shaped so later proof cores can establish
it for the concrete Dade/Fourier bases without introducing a new type of basis
up front. -/
def IsInductionExpansion {ι : Type*} [Fintype ι] (H : Subgroup G)
    [Fintype G] [Fintype H] [Invertible (Nat.card H : ℂ)]
    (ψ : ClassFunction H ℂ)
    (basis image : ι → ClassFunction G ℂ) : Prop :=
  ClassFunction.induce H ψ =
    ∑ i : ι, inductionCoefficient H ψ (basis i) • image i

/-- The character difference `χ - χ.conj` that appears in Peterfalvi §7.

This helper exists to keep later statements from accidentally using
`χ - 1`, which is not the expression in §7. -/
def conjugateDifference (χ : ClassFunction G ℂ) : ClassFunction G ℂ :=
  χ - χ.conj

@[simp] theorem conjugateDifference_apply (χ : ClassFunction G ℂ) (g : G) :
    conjugateDifference χ g = χ g - χ.conj g :=
  rfl

@[simp] theorem conjugateDifference_conj (χ : ClassFunction G ℂ) :
    conjugateDifference χ.conj = -conjugateDifference χ := by
  ext g
  simp [conjugateDifference, sub_eq_add_neg, add_comm]

theorem conjugateDifference_eq_zero_iff_isReal (χ : ClassFunction G ℂ) :
    conjugateDifference χ = 0 ↔ χ.IsReal := by
  constructor
  · intro hχ
    rw [ClassFunction.IsReal.iff_forall]
    intro g
    have hχg := congrArg (fun φ : ClassFunction G ℂ => φ g) hχ
    have hsub : χ g - star (χ g) = 0 := by
      simpa [conjugateDifference] using hχg
    exact (sub_eq_zero.mp hsub).symm
  · intro hχ
    ext g
    have hχg := (ClassFunction.IsReal.iff_forall χ).mp hχ g
    simp [conjugateDifference, hχg]

theorem conjugateDifference_ne_zero_iff_not_isReal (χ : ClassFunction G ℂ) :
    conjugateDifference χ ≠ 0 ↔ ¬ χ.IsReal := by
  constructor
  · intro hne hreal
    exact hne ((conjugateDifference_eq_zero_iff_isReal χ).mpr hreal)
  · intro hnot hzero
    exact hnot ((conjugateDifference_eq_zero_iff_isReal χ).mp hzero)

end OddOrder.Peterfalvi.S03
