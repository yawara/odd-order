/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutation
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional
import OddOrder.GroupTheory.RepresentationTheory.Clifford
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
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

In particular, the cardinal and pointwise Brauer-permutation forms of Peterfalvi (1.1) are
`OddOrder.RepresentationTheory.card_realIrreducibleCharacters_eq_one_of_odd_card` and
`OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card`; this file uses the shared
results directly rather than re-exporting renamed copies.

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

theorem ClosedUnderConjugate.conj_mem {S : Set (ClassFunction G ℂ)}
    (hS : ClosedUnderConjugate S) {χ : ClassFunction G ℂ} (hχ : χ ∈ S) :
    χ.conj ∈ S :=
  hS hχ

theorem ClosedUnderConjugate.conj_mem_iff {S : Set (ClassFunction G ℂ)}
    (hS : ClosedUnderConjugate S) {χ : ClassFunction G ℂ} :
    χ.conj ∈ S ↔ χ ∈ S := by
  constructor
  · intro hχ
    simpa using hS hχ
  · intro hχ
    exact hS hχ

theorem HasNoRealCharacters.mono {S T : Set (ClassFunction G ℂ)}
    (hS : HasNoRealCharacters S) (hTS : T ⊆ S) :
    HasNoRealCharacters T := by
  intro χ hχ
  exact hS (hTS hχ)

theorem HasNoRealCharacters.not_mem_of_isReal {S : Set (ClassFunction G ℂ)}
    (hS : HasNoRealCharacters S) {χ : ClassFunction G ℂ} (hχ : χ.IsReal) :
    χ ∉ S := by
  intro hmem
  exact hS hmem hχ

/-- The set of class functions arising from the *nontrivial* irreducible complex
characters of `G`.

This is Peterfalvi's `Irr(G) ∖ {1_G}`, viewed inside `CF(G)`.  It is the concrete
source set whose `HasNoRealCharacters` property (under odd order) discharges the
`no_real_characters` field of the §7 coherence hypothesis. -/
def nontrivialIrreducibleClassFunctions (G : Type*) [Group G] :
    Set (ClassFunction G ℂ) :=
  {φ | ∃ χ : IrreducibleCharacter G,
    χ ≠ trivialIrreducibleCharacter G ∧ (χ : ClassFunction G ℂ) = φ}

@[simp] theorem mem_nontrivialIrreducibleClassFunctions {φ : ClassFunction G ℂ} :
    φ ∈ nontrivialIrreducibleClassFunctions G ↔
      ∃ χ : IrreducibleCharacter G,
        χ ≠ trivialIrreducibleCharacter G ∧ (χ : ClassFunction G ℂ) = φ :=
  Iff.rfl

theorem irreducibleCharacter_mem_nontrivialIrreducibleClassFunctions
    {χ : IrreducibleCharacter G} (hχ : χ ≠ trivialIrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) ∈ nontrivialIrreducibleClassFunctions G :=
  ⟨χ, hχ, rfl⟩

/-- **Peterfalvi (1.1)**, set form (discharge of the §7 coherence hypothesis).

If `G` has odd order, then the set of nontrivial irreducible complex characters
contains no real class function.  This is the set-level statement of (1.1) — every
nontrivial irreducible character is non-self-conjugate — packaged as the
`HasNoRealCharacters` predicate so that the `no_real_characters` field of a §7
coherence hypothesis is supplied directly from oddness, with no extra input.

It is the unconditional consequence of `not_isReal_of_ne_trivial_of_odd_card'`
quantified over the whole nontrivial-irreducible source set. -/
theorem hasNoRealCharacters_nontrivialIrreducibleClassFunctions [Finite G]
    (hodd : Odd (Nat.card G)) :
    HasNoRealCharacters (nontrivialIrreducibleClassFunctions G) := by
  rintro φ ⟨χ, hχ, rfl⟩
  exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hodd hχ

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

@[simp] theorem characterDegree_trivialClassFunction :
    characterDegree (trivialClassFunction G) = 1 :=
  rfl

/-- **The degree of an irreducible character divides the group order**, phrased through Peterfalvi's
`characterDegree` (Isaacs, *Character Theory of Finite Groups*, Thm 3.11; the degree datum behind
Peterfalvi (6.7)).  For an irreducible character `χ` of a finite group `G` there is a positive
natural number `n` with `characterDegree χ = n` and `n ∣ |G|`.

This is the consumer-facing form of the integrality theory: `characterDegree χ` is definitionally
`χ 1` (`characterDegree_def`), and the `IsIrreducibleCharacter`/`ClassFunction` bridge
`exists_natDegree_charValue_one_dvd_card` carries `finrank_dvd_card` (the dimension of any
witnessing representation divides `|G|`) onto that value.  Because `characterDegree` ranges over
`ℂ`, the divisibility is recorded on the natural witness `n`, with `characterDegree χ = (n : ℂ)`
tying the two together. -/
theorem exists_natDegree_characterDegree_dvd_card [Finite G]
    (χ : IrreducibleCharacter G) :
    ∃ n : ℕ, 0 < n ∧ characterDegree (χ : ClassFunction G ℂ) = (n : ℂ) ∧ n ∣ Nat.card G := by
  obtain ⟨n, hpos, hval, hdvd⟩ := χ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  exact ⟨n, hpos, by rw [characterDegree_def]; exact hval, hdvd⟩

/-- **The degree of an irreducible character of a `p`-group is a power of `p`**, phrased through
Peterfalvi's `characterDegree` (Isaacs, *Character Theory of Finite Groups*, Cor. 3.12; the degree
datum behind Peterfalvi (6.6)).  For an irreducible character `χ` of a finite `p`-group `G` there
is a natural number `k` with `characterDegree χ = p ^ k`.

This is the consumer-facing form, through `characterDegree`, of
`IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup`: under Hypothesis (6.4) with
`M = 1`, once (6.5.b) gives that `K` is a non-abelian `p`-group, every `θ ∈ Irr K` has `θ(1)` a
power of `p` (Peterfalvi (6.6) proof, mmd L80).  Because `characterDegree χ` is *definitionally*
`χ 1` (`characterDegree_def`), this is exactly that statement recast over the value `χ 1`. -/
theorem exists_characterDegree_eq_prime_pow_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) (χ : IrreducibleCharacter G) :
    ∃ k : ℕ, characterDegree (χ : ClassFunction G ℂ) = (p ^ k : ℂ) := by
  obtain ⟨k, hk⟩ := χ.isIrreducible.exists_charValue_one_eq_prime_pow_of_isPGroup hp
  exact ⟨k, by rw [characterDegree_def]; exact hk⟩

/-- **Natural degree witness for p-group irreducible characters.**

This packages the p-power degree result in the form consumed by the (6.6) degree-gap assembly:
the same natural witness `d` both evaluates `characterDegree χ = d` and is a prime power `p^k`.
The positivity is included so downstream ratio and divisibility lemmas can avoid reopening the
irreducible-character degree witness. -/
theorem exists_natDegree_characterDegree_eq_prime_pow_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) (χ : IrreducibleCharacter G) :
    ∃ d k : ℕ, 0 < d ∧ characterDegree (χ : ClassFunction G ℂ) = (d : ℂ) ∧ d = p ^ k := by
  obtain ⟨k, hk⟩ := exists_characterDegree_eq_prime_pow_of_isPGroup hp χ
  have hk_nat : characterDegree (χ : ClassFunction G ℂ) = ((p ^ k : ℕ) : ℂ) := by
    simpa [Nat.cast_pow] using hk
  refine ⟨p ^ k, k, ?_, hk_nat, rfl⟩
  exact pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) k

/-- **Degree-ratio integrality** (Peterfalvi (5.6), opening step "Set `χ(1) = a·χ₁(1)`").

If `χ₁` is an irreducible character whose natural degree divides that of an irreducible
character `χ` — the divisibility hypothesis (5.6)(b) — then the ratio is a *positive
natural number* `a`, and the complex degrees scale by it:
`characterDegree χ = a • characterDegree χ₁`.

The divisibility hypothesis is phrased intrinsically: for the (unique, by `Nat.cast`
injectivity) natural witnesses `d, d₁` of the two degrees, `d₁ ∣ d`.  This is the honest
form of the §5.6 step — the literal "ratio of two positive integers is an integer" is false
without divisibility (e.g. degrees `2, 3`), so the divisibility datum is essential, not
scaffolding: it is exactly Peterfalvi's hypothesis (b).  The quotient `a` is what the §5.6
proof denotes `a` (and the `a_i` for the family), feeding the Cauchy–Schwarz degree bound (c). -/
theorem exists_pos_natDegreeRatio_of_dvd [Finite G]
    (χ χ₁ : IrreducibleCharacter G)
    (hdvd : ∀ d d₁ : ℕ, (χ : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ) → d₁ ∣ d) :
    ∃ a : ℕ, 0 < a ∧ characterDegree (χ : ClassFunction G ℂ) =
      (a : ℂ) * characterDegree (χ₁ : ClassFunction G ℂ) := by
  obtain ⟨d, hd_pos, hd_val, _⟩ := χ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  obtain ⟨d₁, hd₁_pos, hd₁_val, _⟩ := χ₁.isIrreducible.exists_natDegree_charValue_one_dvd_card
  obtain ⟨a, rfl⟩ := hdvd d d₁ hd_val hd₁_val
  refine ⟨a, ?_, ?_⟩
  · -- `a > 0`: from `d₁ * a = d > 0` with `d₁ > 0`.
    rcases Nat.eq_zero_or_pos a with ha | ha
    · simp [ha] at hd_pos
    · exact ha
  · rw [characterDegree_def, characterDegree_def, hd_val, hd₁_val, Nat.cast_mul]
    ring

/-- **Degree-ratio family from divisibility data.**

Given a finite family of irreducible characters and a distinguished index `i₁`, if the natural
degree of `χ i₁` divides the natural degree of every `χ i` in the finite support `s`, then there
is a positive natural ratio function `deg` with `deg i₁ = 1` and
`χᵢ(1)=degᵢ χ₁(1)` on `s`.  The definition pins the distinguished ratio to `1` explicitly,
so downstream finite-family interfaces do not need a uniqueness argument for the quotient
at `i₁`. -/
theorem exists_pos_natDegreeRatioFamily_of_dvd [Finite G]
    {ι : Type*} {s : Finset ι} (χ : ι → IrreducibleCharacter G) {i₁ : ι}
    (hdvd : ∀ i ∈ s, ∀ d d₁ : ℕ,
      (χ i : ClassFunction G ℂ) 1 = (d : ℂ) →
      (χ i₁ : ClassFunction G ℂ) 1 = (d₁ : ℂ) → d₁ ∣ d) :
    ∃ deg : ι → ℕ, deg i₁ = 1 ∧ (∀ i ∈ s, 0 < deg i) ∧
      ∀ i ∈ s, (χ i : ClassFunction G ℂ) 1 =
        (deg i : ℂ) * (χ i₁ : ClassFunction G ℂ) 1 := by
  classical
  let ratio : (i : ι) → i ∈ s → ℕ := fun i hi =>
    (exists_pos_natDegreeRatio_of_dvd (χ i) (χ i₁) (hdvd i hi)).choose
  have hratio : ∀ i hi, characterDegree (χ i : ClassFunction G ℂ) =
      (ratio i hi : ℂ) * characterDegree (χ i₁ : ClassFunction G ℂ) := by
    intro i hi
    exact (exists_pos_natDegreeRatio_of_dvd (χ i) (χ i₁) (hdvd i hi)).choose_spec.2
  let deg : ι → ℕ := fun i => if h : i = i₁ then 1 else if hi : i ∈ s then ratio i hi else 1
  refine ⟨deg, by simp [deg], ?_, ?_⟩
  · intro i hi
    by_cases h : i = i₁
    · subst i
      simp [deg]
    · have hpos : 0 < ratio i hi :=
        (exists_pos_natDegreeRatio_of_dvd (χ i) (χ i₁) (hdvd i hi)).choose_spec.1
      simpa [deg, h, hi, ratio] using hpos
  · intro i hi
    by_cases h : i = i₁
    · subst i
      simp [deg]
    · have hri := hratio i hi
      rw [characterDegree_def, characterDegree_def] at hri
      simpa [deg, h, hi, ratio] using hri

/-- A family of class functions has constant degree. -/
def SameDegreeFamily {ι : Type*} (χ : ι → ClassFunction G ℂ) : Prop :=
  ∀ i j, characterDegree (χ i) = characterDegree (χ j)

theorem SameDegreeFamily.eq {ι : Type*} {χ : ι → ClassFunction G ℂ}
    (hχ : SameDegreeFamily χ) (i j : ι) :
    characterDegree (χ i) = characterDegree (χ j) :=
  hχ i j

theorem sameDegreeFamily_const {ι : Type*} (χ : ClassFunction G ℂ) :
    SameDegreeFamily (fun _ : ι => χ) := by
  intro i j
  rfl

theorem sameDegreeFamily_of_characterDegree_eq {ι : Type*}
    {χ : ι → ClassFunction G ℂ} {d : ℂ}
    (hχ : ∀ i, characterDegree (χ i) = d) :
    SameDegreeFamily χ := by
  intro i j
  rw [hχ i, hχ j]

/-- A set of class functions has constant degree. -/
def HasUniformDegree (S : Set (ClassFunction G ℂ)) : Prop :=
  ∃ d : ℂ, ∀ ⦃χ : ClassFunction G ℂ⦄, χ ∈ S → characterDegree χ = d

theorem HasUniformDegree.eq_of_mem {S : Set (ClassFunction G ℂ)}
    (hS : HasUniformDegree S) {χ ψ : ClassFunction G ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) :
    characterDegree χ = characterDegree ψ := by
  rcases hS with ⟨d, hd⟩
  rw [hd hχ, hd hψ]

theorem HasUniformDegree.mono {S T : Set (ClassFunction G ℂ)}
    (hS : HasUniformDegree S) (hTS : T ⊆ S) :
    HasUniformDegree T := by
  rcases hS with ⟨d, hd⟩
  exact ⟨d, by
    intro χ hχ
    exact hd (hTS hχ)⟩

theorem hasUniformDegree_empty :
    HasUniformDegree (∅ : Set (ClassFunction G ℂ)) := by
  exact ⟨0, by
    intro χ hχ
    exact False.elim hχ⟩

theorem hasUniformDegree_singleton (χ : ClassFunction G ℂ) :
    HasUniformDegree ({χ} : Set (ClassFunction G ℂ)) := by
  refine ⟨characterDegree χ, ?_⟩
  intro ψ hψ
  rw [Set.mem_singleton_iff] at hψ
  subst hψ
  rfl

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

@[simp] theorem characterKernel_trivialClassFunction :
    characterKernel (trivialClassFunction G) = Set.univ := by
  ext g
  simp [characterKernel, characterDegree]

@[simp] theorem characterKernel_conj (χ : ClassFunction G ℂ) :
    characterKernel χ.conj = characterKernel χ := by
  ext g
  change star (χ g) = star (χ 1) ↔ χ g = χ 1
  exact star_inj

/-- A subset is contained in the character kernel.  This is the set-level shape
used in Peterfalvi (1.6). -/
def SubsetCharacterKernel (A : Set G) (χ : ClassFunction G ℂ) : Prop :=
  A ⊆ characterKernel χ

theorem subsetCharacterKernel_iff {A : Set G} {χ : ClassFunction G ℂ} :
    SubsetCharacterKernel A χ ↔ A ⊆ characterKernel χ :=
  Iff.rfl

theorem SubsetCharacterKernel.mono {A B : Set G} {χ : ClassFunction G ℂ}
    (hχ : SubsetCharacterKernel B χ) (hAB : A ⊆ B) :
    SubsetCharacterKernel A χ :=
  fun _ hg => hχ (hAB hg)

theorem subsetCharacterKernel_empty (χ : ClassFunction G ℂ) :
    SubsetCharacterKernel (∅ : Set G) χ := by
  intro g hg
  exact False.elim hg

theorem subsetCharacterKernel_trivialClassFunction (A : Set G) :
    SubsetCharacterKernel A (trivialClassFunction G) := by
  intro g hg
  simp

@[simp] theorem subsetCharacterKernel_conj_iff {A : Set G} {χ : ClassFunction G ℂ} :
    SubsetCharacterKernel A χ.conj ↔ SubsetCharacterKernel A χ := by
  simp [SubsetCharacterKernel]

theorem subsetCharacterKernel_univ_iff {χ : ClassFunction G ℂ} :
    SubsetCharacterKernel (Set.univ : Set G) χ ↔ characterKernel χ = Set.univ := by
  constructor
  · intro hχ
    exact Set.eq_univ_iff_forall.mpr fun g => hχ (Set.mem_univ g)
  · intro hχ g _
    rw [hχ]
    exact Set.mem_univ g

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

@[simp] theorem restrict_trivialClassFunction (H : Subgroup G) :
    ClassFunction.restrict H (trivialClassFunction G) = trivialClassFunction H := by
  ext h
  simp

@[simp] theorem inductionCoefficient_zero_left (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)] (χ : ClassFunction G ℂ) :
    inductionCoefficient H (0 : ClassFunction H ℂ) χ = 0 := by
  simp [inductionCoefficient]

@[simp] theorem inductionCoefficient_zero_right (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)] (ψ : ClassFunction H ℂ) :
    inductionCoefficient H ψ (0 : ClassFunction G ℂ) = 0 := by
  simp [inductionCoefficient]

theorem inductionCoefficient_add_left (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)]
    (ψ₁ ψ₂ : ClassFunction H ℂ) (χ : ClassFunction G ℂ) :
    inductionCoefficient H (ψ₁ + ψ₂) χ =
      inductionCoefficient H ψ₁ χ + inductionCoefficient H ψ₂ χ := by
  exact ClassFunction.inner_add_left ψ₁ ψ₂ (ClassFunction.restrict H χ)

theorem inductionCoefficient_add_right (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)]
    (ψ : ClassFunction H ℂ) (χ₁ χ₂ : ClassFunction G ℂ) :
    inductionCoefficient H ψ (χ₁ + χ₂) =
      inductionCoefficient H ψ χ₁ + inductionCoefficient H ψ χ₂ := by
  rw [inductionCoefficient, ClassFunction.restrict_add]
  exact ClassFunction.inner_add_right ψ (ClassFunction.restrict H χ₁)
    (ClassFunction.restrict H χ₂)

theorem inductionCoefficient_smul_left (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)]
    (c : ℂ) (ψ : ClassFunction H ℂ) (χ : ClassFunction G ℂ) :
    inductionCoefficient H (c • ψ) χ = c * inductionCoefficient H ψ χ := by
  exact ClassFunction.inner_smul_left c ψ (ClassFunction.restrict H χ)

@[simp] theorem inductionCoefficient_trivial_right (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)] (ψ : ClassFunction H ℂ) :
    inductionCoefficient H ψ (trivialClassFunction G) =
      ClassFunction.inner ψ (trivialClassFunction H) := by
  simp [inductionCoefficient]

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

/-- **Peterfalvi (1.1)**, conjugate-difference (nondegeneracy) form, used in §7.

If `G` has odd order and `χ` is a *nontrivial* irreducible complex character, then the
conjugate difference `χ - χ̄` is nonzero.  Together with `conjugateDifference_conj`
(which gives `(χ̄ - χ) = -(χ - χ̄)`) this is the nondegeneracy fact that makes the
`χ - χ̄` constructions of Peterfalvi §7 nonzero: a nontrivial odd-order irreducible
character is genuinely non-self-conjugate, so its conjugate difference does not collapse.

This is the unconditional consequence of Peterfalvi (1.1) (`G` of odd order has no
nontrivial real irreducible character) specialised to the `χ - χ̄` expression. -/
theorem conjugateDifference_ne_zero_of_ne_trivial_of_odd_card [Finite G]
    (hodd : Odd (Nat.card G)) {χ : IrreducibleCharacter G}
    (hχ : χ ≠ trivialIrreducibleCharacter G) :
    conjugateDifference (χ : ClassFunction G ℂ) ≠ 0 :=
  (conjugateDifference_ne_zero_iff_not_isReal (χ : ClassFunction G ℂ)).mpr
    (OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hodd hχ)

/-! ### Peterfalvi (1.6.a): kernel of an induced character

For `A ⊴ G` with `A ≤ H` (and `θ` a class function on `H`), the normal subgroup `A` lies in
the kernel of `θ` if and only if it lies in the kernel of the induced character `Ind_H^G θ`.
The forward direction is elementary from the value formula
`ClassFunction.induce_apply_of_mem_normal_of_const`: when `θ` is constant on `A`, every term
of the induction sum at `a ∈ A` is that constant, so `Ind_H^G θ` is constant on `A` as well.
The backward direction (the converse) is [Is] *Character Theory* Lemma 2.21, an eigenvalue
argument on the genuine character `θ`, and is **not** formalised here. -/

section InducedKernel

variable {A H : Subgroup G} [Fintype G] [Fintype H] [Invertible (Nat.card H : ℂ)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- For `a ∈ A`, the constant value taken by the induced character `Ind_H^G θ` on a normal
subgroup `A ≤ H` on which `θ` is constant `= θ(1)`.  This is the explicit value formula
`Ind_H^G θ(a) = |G|·θ(1)·|H|⁻¹`, derived from
`ClassFunction.induce_apply_of_mem_normal_of_const` with the kernel hypothesis. -/
theorem induce_apply_eq_of_subgroupOf_subset_characterKernel (hAH : A ≤ H) [A.Normal]
    (θ : ClassFunction ↥H ℂ)
    (hker : (A.subgroupOf H : Set ↥H) ⊆ characterKernel θ) {a : G} (ha : a ∈ A) :
    ClassFunction.induce H θ a =
      ⅟(Nat.card H : ℂ) * ((Nat.card G : ℂ) * characterDegree θ) := by
  refine ClassFunction.induce_apply_of_mem_normal_of_const hAH θ
    (c := characterDegree θ) (fun a' ha' => ?_) ha
  -- `θ` is constant `= characterDegree θ` on `A`, by the kernel hypothesis.
  have hmem : (⟨a', hAH ha'⟩ : ↥H) ∈ A.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]; exact ha'
  exact hker hmem

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (1.6.a)**, forward direction.  Let `A ⊴ G` with `A ≤ H` and let `θ` be a class
function on `H`.  If `A` is contained in the kernel of `θ` (as a subgroup of `H`), then `A` is
contained in the kernel of the induced character `Ind_H^G θ` (as a subgroup of `G`).

This is the elementary half of (1.6.a): when `θ` is constant on `A`, so is `Ind_H^G θ` (every
term of the induction sum at `a ∈ A` is `θ` evaluated at a conjugate `x⁻¹ a x ∈ A`, hence the
common constant).  The converse is [Is] Lemma 2.21 and is not formalised here.

The (6.6) use case is the contrapositive: if `Z ⊄ Ker (Ind_H^G θ)` then `Z ⊄ Ker θ`. -/
theorem subsetCharacterKernel_induce_of_subgroupOf (hAH : A ≤ H) [A.Normal]
    (θ : ClassFunction ↥H ℂ)
    (hker : (A.subgroupOf H : Set ↥H) ⊆ characterKernel θ) :
    SubsetCharacterKernel (A : Set G) (ClassFunction.induce H θ) := by
  intro a ha
  rw [mem_characterKernel]
  -- both `Ind θ(a)` and `Ind θ(1) = characterDegree (Ind θ)` equal the common constant.
  have hval : ClassFunction.induce H θ a =
      ⅟(Nat.card H : ℂ) * ((Nat.card G : ℂ) * characterDegree θ) :=
    induce_apply_eq_of_subgroupOf_subset_characterKernel hAH θ hker ha
  have hval1 : characterDegree (ClassFunction.induce H θ) =
      ⅟(Nat.card H : ℂ) * ((Nat.card G : ℂ) * characterDegree θ) := by
    rw [characterDegree_def]
    exact induce_apply_eq_of_subgroupOf_subset_characterKernel hAH θ hker A.one_mem
  rw [hval, hval1]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (1.6.a), contrapositive form.**  Let `A ⊴ G` with `A ≤ H` and let `θ` be a
class function on `H`.  If `A` is *not* contained in the kernel of the induced character
`Ind_H^G θ`, then `A` is *not* contained in the kernel of `θ` (as a subgroup of `H`).

This is the exact direction the (6.6) `X`-characterization consumes (mmd 04.8 L76, "by (1.6),
`Z ⊄ Ker θ`"): once `χ = Ind_K^L θ` (or, more generally, `Z ⊄ Ker (Ind_K^L θ)`), the normal
subgroup `Z` escapes the kernel of `θ` as well.  It is the literal contrapositive of the
forward (1.6.a) lemma `subsetCharacterKernel_induce_of_subgroupOf`. -/
theorem not_subsetCharacterKernel_of_not_induce (hAH : A ≤ H) [A.Normal]
    (θ : ClassFunction ↥H ℂ)
    (hind : ¬ SubsetCharacterKernel (A : Set G) (ClassFunction.induce H θ)) :
    ¬ ((A.subgroupOf H : Set ↥H) ⊆ characterKernel θ) :=
  fun hker => hind (subsetCharacterKernel_induce_of_subgroupOf hAH θ hker)

end InducedKernel

/-! ### Peterfalvi (6.6): the `X`-characterization — constituent of an induced character

The (6.6) `X`-characterization (mmd 04.8 L76) opens: "Let `χ ∈ Irr L` be such that
`Z ⊄ Ker χ`.  There is a character `θ ∈ Irr K` for which `χ` is an irreducible component of
`Ind_K^L θ`."  The *existence* of such a constituent `θ` is unconditional — it holds for
**every** `χ ∈ Irr L`, with no reference to `Z` at all — and is the backbone of the
characterization.  It is Frobenius reciprocity packaged through the Clifford `LiesOver` bridge:
`χ` lies over *some* `θ ∈ Irr K` (`IrreducibleCharacter.exists_liesOver`), and lying over `θ`
is exactly being a constituent of `Ind_K^L θ`
(`IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver`).

Combined with `not_subsetCharacterKernel_of_not_induce` (the (1.6.a) contrapositive above), this
delivers the two honest halves of the (6.6) `X`-characterization: every `χ ∈ Irr L` is a
constituent of some `Ind_K^L θ`, and from `Z ⊄ Ker (Ind_K^L θ)` one reads off `Z ⊄ Ker θ`.  The
remaining link — that a constituent `χ` of `Ind_K^L θ` with `Z ⊄ Ker χ` forces
`Z ⊄ Ker (Ind_K^L θ)` (equivalently `Z ⊆ Ker (Ind_K^L θ) ⟹ Z ⊆ Ker χ`, "an irreducible
constituent inherits a kernel containment of the ambient character") — is the standard
character-value inequality `|χ(a)| ≤ χ(1)` with its equality case, which is not yet available in
this development and is recorded as the residual of (6.6) G2.2. -/

section InducedConstituent

variable {H : Subgroup G} [Fintype G] [Fintype H]
  [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]

set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (6.6) `X`-characterization, constituent-existence half** (mmd 04.8 L76).  For
any subgroup `H` of `G` and any irreducible character `χ` of `G`, there is an irreducible
character `θ` of `H` of which `χ` is a constituent of the induced character `Ind_H^G θ`, i.e.
`⟨Ind_H^G θ, χ⟩ ≠ 0`.

This is the "`χ = Ind_K^L θ` constituent" step of (6.6), in its honest unconditional generality:
it requires nothing about a center `Z`, only Frobenius reciprocity.  The proof composes
`IrreducibleCharacter.exists_liesOver` (every `χ` lies over some `θ ∈ Irr H`) with
`IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver` (lying over `θ` ⟺ being a constituent
of `Ind_H^G θ`).

(The `Fintype H` instance feeds the Frobenius-reciprocity bridge in the proof; it does not appear
in the statement.) -/
theorem exists_inner_induce_ne_zero
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G) :
    ∃ θ : OddOrder.RepresentationTheory.IrreducibleCharacter H,
      ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (χ : ClassFunction G ℂ) ≠ 0 := by
  obtain ⟨θ, hθ⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver (G := G) H χ
  exact ⟨θ,
    (OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver
      (G := G) H χ θ).mpr hθ⟩

end InducedConstituent

/-! ### Peterfalvi (6.6) G2.2: a constituent inherits a kernel containment

The (6.6) G2.2 residual is "an irreducible constituent `χ` of a genuine character `ψ` inherits
`g ∈ Ker ψ`": from `ψ(g) = ψ(1)` one reads `χ(g) = χ(1)`.  Writing `ψ = ∑ mᵢ χᵢ` as a
non-negative integer combination of irreducible characters, this is the **equality case of the
character-value bound** `|χᵢ(g)| ≤ χᵢ(1)` applied to each summand: the real part of
`ψ(g) = ∑ mᵢ χᵢ(g)` is `∑ mᵢ Re χᵢ(g) ≤ ∑ mᵢ |χᵢ(g)| ≤ ∑ mᵢ χᵢ(1) = ψ(1) = ψ(g)`, and the
equality forces every summand with `mᵢ ≠ 0` to have `Re χᵢ(g) = χᵢ(1)`, hence (with
`|χᵢ(g)| ≤ χᵢ(1)`) `χᵢ(g) = χᵢ(1)`.

The bound and its equality case are supplied by the **diagonalization keystone**
(`OddOrder.RepresentationTheory.norm_character_le_finrank` and
`character_eq_one_iff_rep_eq_id`), the machinery `notes/peterfalvi/s03` previously flagged as the
`needs-infra` piece of G2.2.  The statement below is the honest, fully-general equality case; a
future G2.2 assembly supplies the `ψ = ∑ mᵢ χᵢ` decomposition of `Ind_K^L θ`. -/

section ConstituentKernel

variable [Finite G]

/-- **Character-value bound `‖χ(g)‖ ≤ χ(1)`** for an irreducible character, in the
`characterDegree` form ([Isaacs] *Character Theory*, the inequality of (2.27)).  Here `d` is the
natural degree (`(χ : G → ℂ) 1 = d`), and `‖χ(g)‖ ≤ d`.  This is the consumer-facing form, through
`IrreducibleCharacter`, of the keystone bound
`OddOrder.RepresentationTheory.norm_character_le_finrank`. -/
theorem norm_irreducibleCharacter_le_natDegree
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G) {d : ℕ}
    (hd : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) (g : G) :
    ‖(χ : ClassFunction G ℂ) g‖ ≤ (d : ℝ) := by
  obtain ⟨V, _, _, _, ρ, _, hχ⟩ := χ.isIrreducible
  -- `χ g = ρ.character g` and the natural degree `d` is the `finrank`.
  have hcharg : (χ : ClassFunction G ℂ) g = ρ.character g := congrFun hχ g
  have hfin : (Module.finrank ℂ V : ℂ) = (d : ℂ) := by
    rw [← ρ.char_one, ← congrFun hχ 1, hd]
  have hfin' : (Module.finrank ℂ V : ℝ) = (d : ℝ) := by exact_mod_cast hfin
  rw [hcharg, ← hfin']
  exact OddOrder.RepresentationTheory.norm_character_le_finrank ρ g

/-- **Peterfalvi (6.6) G2.2: a constituent inherits a kernel containment** (the equality case of
`‖χ(g)‖ ≤ χ(1)`).  Let `χ : ι → Irr G` be a finite family of irreducible characters with
non-negative integer multiplicities `m : ι → ℕ`.  If the value of `ψ = ∑ mᵢ χᵢ` at `g` equals its
value at `1`, then every constituent `χ i` with `m i ≠ 0` satisfies `χ i (g) = χ i (1)`, i.e.
`g ∈ characterKernel (χ i)`.

This is the keystone-driven closure of the G2.2 residual: it sharpens the central Schur equality
to the general element `g`, using `norm_irreducibleCharacter_le_natDegree` (the bound) and
`RCLike.re_eq_self_of_le` (the unit-circle rigidity) at each summand. -/
theorem irreducibleCharacter_mem_characterKernel_of_natSum_value_eq (g : G)
    {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (χ : ι → OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (d : ι → ℕ) (hd : ∀ i ∈ s, (χ i : ClassFunction G ℂ) 1 = (d i : ℂ))
    (hval : ∑ i ∈ s, (m i : ℂ) * (χ i : ClassFunction G ℂ) g
      = ∑ i ∈ s, (m i : ℂ) * (χ i : ClassFunction G ℂ) 1) :
    ∀ i ∈ s, m i ≠ 0 → g ∈ characterKernel (χ i : ClassFunction G ℂ) := by
  classical
  -- Bound `‖χᵢ(g)‖ ≤ dᵢ`, and `Re χᵢ(g) ≤ ‖χᵢ(g)‖ ≤ dᵢ`, for every `i ∈ s`.
  have hbound : ∀ i ∈ s, ‖(χ i : ClassFunction G ℂ) g‖ ≤ (d i : ℝ) := fun i hi =>
    norm_irreducibleCharacter_le_natDegree (χ i) (hd i hi) g
  have hre_le : ∀ i ∈ s, ((χ i : ClassFunction G ℂ) g).re ≤ (d i : ℝ) := fun i hi =>
    le_trans (by rw [← RCLike.re_eq_complex_re]; exact RCLike.re_le_norm _) (hbound i hi)
  -- Real parts: `∑ mᵢ Re χᵢ(g) = ∑ mᵢ dᵢ` (the RHS is real, `= ∑ mᵢ χᵢ(1)`).
  have hre : ∑ i ∈ s, (m i : ℝ) * ((χ i : ClassFunction G ℂ) g).re
      = ∑ i ∈ s, (m i : ℝ) * (d i : ℝ) := by
    have hcast := congrArg Complex.re hval
    rw [Complex.re_sum, Complex.re_sum] at hcast
    refine Eq.trans ?_ (hcast.trans ?_) <;> refine Finset.sum_congr rfl fun i hi => ?_
    · simp [Complex.mul_re]
    · rw [hd i hi]; simp [Complex.mul_re]
  -- Each summand deficit `mᵢ(dᵢ - Re χᵢ(g)) ≥ 0`, summing to `0`, so each is `0`.
  have hnn : ∀ i ∈ s, (0 : ℝ) ≤ (m i : ℝ) * ((d i : ℝ) - ((χ i : ClassFunction G ℂ) g).re) :=
    fun i hi => mul_nonneg (by positivity) (by linarith [hre_le i hi])
  have hsum0 : ∑ i ∈ s, (m i : ℝ) * ((d i : ℝ) - ((χ i : ClassFunction G ℂ) g).re) = 0 := by
    have hexp : ∀ i ∈ s, (m i : ℝ) * ((d i : ℝ) - ((χ i : ClassFunction G ℂ) g).re)
        = (m i : ℝ) * (d i : ℝ) - (m i : ℝ) * ((χ i : ClassFunction G ℂ) g).re :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← hre, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  -- For `mᵢ ≠ 0`: `Re χᵢ(g) = dᵢ`, and with `‖χᵢ(g)‖ ≤ dᵢ` rigidity gives `χᵢ(g) = dᵢ = χᵢ(1)`.
  intro i hi hmi
  have hmi' : (m i : ℝ) ≠ 0 := by exact_mod_cast hmi
  have hre_eq : ((χ i : ClassFunction G ℂ) g).re = (d i : ℝ) := by
    have hterm : (d i : ℝ) - ((χ i : ClassFunction G ℂ) g).re = 0 :=
      (mul_eq_zero.mp (hzero i hi)).resolve_left hmi'
    linarith
  -- `‖χᵢ(g)‖ ≤ dᵢ = Re χᵢ(g)`; unit-circle rigidity gives `χᵢ(g) = (Re χᵢ(g) : ℂ) = dᵢ`.
  have hle : ‖(χ i : ClassFunction G ℂ) g‖ ≤ RCLike.re ((χ i : ClassFunction G ℂ) g) := by
    rw [RCLike.re_eq_complex_re, hre_eq]; exact hbound i hi
  have haeq : (χ i : ClassFunction G ℂ) g = (d i : ℂ) := by
    rw [← RCLike.re_eq_self_of_le (K := ℂ) hle, RCLike.re_eq_complex_re, hre_eq]
    push_cast
    ring
  rw [mem_characterKernel, characterDegree_def, haeq, hd i hi]

end ConstituentKernel

/-! ### Kernel descent along induction

For a normal subgroup `H ◁ L` and an irreducible `θ ∈ Irr(H)`, the kernel of the induced
character `Ind_H^L θ` meets `H` inside the kernel of `θ`.  Consumers: the §9/§13 `𝒮`-family
bookkeeping (a family member `Ind θ` kills a subgroup `Y ≤ H` iff its source does). -/

section InducedKernelDescent

/-- **Kernel descent for induced characters**: if `x ∈ H` lies in the kernel of `Ind_H^L θ`
(`θ` irreducible, `H ◁ L`), then `x` lies in the kernel of `θ` itself.
Mackey (`card_smul_restrict_induce_eq_inertia_smul_orbitSum`) writes `|H|·(Ind θ)|_H` as
`|I(θ)|·∑_{orbit} θ^g`; the kernel hypothesis equates the orbit sums at `x` and `1`, and the
triangle-equality keystone (`irreducibleCharacter_mem_characterKernel_of_natSum_value_eq`)
forces every orbit member — in particular `θ` — to have `x` in its kernel.  Contrapositive:
`P ⊄ Ker θ ⟹ P ⊄ Ker (Ind θ)`. -/
theorem mem_characterKernel_of_mem_characterKernel_induce
    {L : Type*} [Group L] [Fintype L] {H : Subgroup L} [H.Normal]
    [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    {θ : ClassFunction ↥H ℂ} (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    {x : L} (hxH : x ∈ H)
    (hker : x ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce H θ)) :
    (⟨x, hxH⟩ : ↥H) ∈ OddOrder.Peterfalvi.S03.characterKernel θ := by
  classical
  -- the Mackey orbit identity, applied at `⟨x,hxH⟩` and at `1`
  have hid :=
    OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
      (G := L) (H := H) (k := ℂ) θ
  rw [← Nat.cast_smul_eq_nsmul ℂ] at hid
  have happ : ∀ a : ↥H,
      (Nat.card ↥H : ℂ) * ClassFunction.induce H θ (a : L)
        = (Nat.card ↥(ClassFunction.inertia (G := L) (H := H) θ) : ℂ)
          * ∑ ψ ∈ Finset.univ.image (fun g : L => ClassFunction.conjBy g⁻¹ θ), ψ a := by
    intro a
    have h1 := congrArg (fun f : ClassFunction ↥H ℂ => f a) hid
    simpa only [ClassFunction.smul_apply, ClassFunction.restrict_apply, smul_eq_mul,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply] using h1
  -- kernel hypothesis ⟹ the orbit sums at `x` and `1` agree
  have hI0 : (Nat.card ↥(ClassFunction.inertia (G := L) (H := H) θ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hxval : ClassFunction.induce H θ x = ClassFunction.induce H θ (1 : L) := by
    have := (OddOrder.Peterfalvi.S03.mem_characterKernel).mp hker
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using this
  have hsum : ∑ ψ ∈ Finset.univ.image (fun g : L => ClassFunction.conjBy g⁻¹ θ),
        ψ (⟨x, hxH⟩ : ↥H)
      = ∑ ψ ∈ Finset.univ.image (fun g : L => ClassFunction.conjBy g⁻¹ θ), ψ 1 := by
    have h1 := happ ⟨x, hxH⟩
    have h2 := happ 1
    rw [show ((⟨x, hxH⟩ : ↥H) : L) = x from rfl] at h1
    rw [show ((1 : ↥H) : L) = 1 from rfl] at h2
    rw [hxval] at h1
    exact mul_left_cancel₀ hI0 (h1.symm.trans h2)
  -- the orbit members are irreducible of the common degree `θ(1) = n`
  obtain ⟨n, -, hn, -⟩ :=
    OddOrder.Peterfalvi.S03.exists_natDegree_characterDegree_dvd_card (G := ↥H) ⟨θ, hθ⟩
  have hdeg : θ 1 = (n : ℂ) := by
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hn
  set S : Finset (ClassFunction ↥H ℂ) :=
    Finset.univ.image (fun g : L => ClassFunction.conjBy g⁻¹ θ) with hSdef
  have hmemirr : ∀ ψ ∈ S, OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ := by
    intro ψ hψ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hψ
    exact OddOrder.RepresentationTheory.ClassFunction.IsIrreducibleCharacter.conjBy
      (H := H) hθ g⁻¹
  set fam : ClassFunction ↥H ℂ → OddOrder.RepresentationTheory.IrreducibleCharacter ↥H :=
    fun ψ => if h : OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ
      then ⟨ψ, h⟩ else ⟨θ, hθ⟩ with hfam
  have hfamcoe : ∀ ψ ∈ S, (fam ψ : ClassFunction ↥H ℂ) = ψ := by
    intro ψ hψ
    simp only [hfam]
    rw [dif_pos (hmemirr ψ hψ)]
  have hfamdeg : ∀ ψ ∈ S, (fam ψ : ClassFunction ↥H ℂ) 1 = (n : ℂ) := by
    intro ψ hψ
    rw [hfamcoe ψ hψ]
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hψ
    rw [ClassFunction.conjBy_apply]
    refine (congrArg θ (Subtype.ext ?_)).trans hdeg
    simp
  have hval : ∑ ψ ∈ S, ((1 : ℕ) : ℂ) * (fam ψ : ClassFunction ↥H ℂ) (⟨x, hxH⟩ : ↥H)
      = ∑ ψ ∈ S, ((1 : ℕ) : ℂ) * (fam ψ : ClassFunction ↥H ℂ) 1 := by
    have e1 : ∀ pt : ↥H, ∑ ψ ∈ S, ((1 : ℕ) : ℂ) * (fam ψ : ClassFunction ↥H ℂ) pt
        = ∑ ψ ∈ S, ψ pt := fun pt =>
      Finset.sum_congr rfl (fun ψ hψ => by rw [hfamcoe ψ hψ, Nat.cast_one, one_mul])
    rw [e1, e1]
    exact hsum
  -- keystone: every orbit member has `x` in its kernel; take `ψ = θ` (the `g = 1` member)
  have hθS : θ ∈ S := by
    rw [hSdef]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩
  have hkey := OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq
    (⟨x, hxH⟩ : ↥H) S (fun _ => 1) fam (fun _ => n) hfamdeg hval θ hθS one_ne_zero
  rwa [hfamcoe θ hθS] at hkey

end InducedKernelDescent

end OddOrder.Peterfalvi.S03
