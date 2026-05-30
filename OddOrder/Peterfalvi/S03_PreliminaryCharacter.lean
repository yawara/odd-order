/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutation
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional
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

/-- **Peterfalvi (1.1)**, cardinal form.

If `G` has odd order, then there is exactly one real irreducible complex
character.  The sharper textbook phrasing says that every nontrivial
irreducible character is non-real; identifying this unique real character with
the trivial character is routed to the later trivial-character API.

The hypotheses `idx`, `hrow`, `σ`, `h_real_irr`, `h_compat` package the
data needed by Brauer's permutation lemma: character-table indexing, weighted
row orthogonality, the conjugation involution `χ ↦ χ̄`, its fixed-point
characterization, and the compatibility with class inversion.  Constructing
these from mathlib's representation theory is the remaining external gap. -/
theorem card_realIrreducibleCharacters_eq_one_of_odd_card [Finite G]
    (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (σ : Equiv.Perm (IrreducibleCharacter G))
    (h_real_irr : ∀ χ : IrreducibleCharacter G,
      σ χ = χ ↔ ClassFunction.IsReal (χ : ClassFunction G ℂ))
    (h_compat : ∀ (χ : IrreducibleCharacter G) (C : ConjClasses G),
      characterTableEntry (σ χ) C = characterTableEntry χ (ConjClasses.inv C))
    (hodd : Odd (Nat.card G)) :
    Nat.card (RealIrreducibleCharacter G) = 1 :=
  OddOrder.RepresentationTheory.card_realIrreducibleCharacters_eq_one_of_odd_card
    idx hrow σ h_real_irr h_compat hodd

/-- **Peterfalvi (1.1)**, pointwise form.

If `G` has odd order, then every nontrivial irreducible complex character is
non-real. -/
theorem not_isReal_of_ne_trivial_irreducible_of_odd_card [Finite G]
    (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (σ : Equiv.Perm (IrreducibleCharacter G))
    (h_real_irr : ∀ χ : IrreducibleCharacter G,
      σ χ = χ ↔ ClassFunction.IsReal (χ : ClassFunction G ℂ))
    (h_compat : ∀ (χ : IrreducibleCharacter G) (C : ConjClasses G),
      characterTableEntry (σ χ) C = characterTableEntry χ (ConjClasses.inv C))
    (hodd : Odd (Nat.card G)) {χ : IrreducibleCharacter G}
    (hχ : χ ≠ trivialIrreducibleCharacter G) :
    ¬ ClassFunction.IsReal (χ : ClassFunction G ℂ) :=
  OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card
    idx hrow σ h_real_irr h_compat hodd hχ

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

end OddOrder.Peterfalvi.S03
