/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_SixTwoThreeFromImageFamilies
import OddOrder.Peterfalvi.S07_CoherenceConstantDegree
import OddOrder.Peterfalvi.S08_CoherenceCorePart1
import OddOrder.GroupTheory.NilpotentAbelianization

/-!
# Peterfalvi (6.5) for a general kernel: the (6.3.b) coherence input

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §6, (6.5)
(p. 31).

## What this leaf supplies

Peterfalvi's proof of (6.5)(a) opens with

> *Hypothesis (a) of Theorem (6.3) holds with `H = K`.  Since `K/H₁` is abelian and non-trivial,
> (6.3.b) holds by (5.7).*

so the general-kernel (6.5) needs the general-kernel form of that one sentence: **`𝒮(X)` is
coherent whenever `K/X` is abelian**.  That is what
`inducedKernelFamily_isCoherent_of_isMulCommutative_quotient` proves, from

* `InducedFamilyImageData` — the whole of Hypothesis (5.2) for the (6.1) family
  `𝒮 = inducedKernelFamily K ⊥` (issue 0154), restricted to the subfamily `𝒮(X)` by
  `InducedFamilyTauData.hypothesis`;
* the constant degree `|L:K|` of every member, which is exactly where `K/X` abelian enters: a
  source `θ ∈ Irr K` trivial on `X` inflates from the abelian `K/X`, hence is linear
  (`apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`), so
  `(Ind_K^L θ)(1) = |L:K|`;
* the standing irreducibility of the members (`hirr`), which is what the repo's (5.7)
  (`S07.coherent_of_constant_degree`) asks for on top of Hypothesis (5.2).  ⚠ **The book's (5.7)
  does not assume it** (Hypothesis (5.2) only asks for pairwise orthogonality); the repo's
  extra `hirr` is a specialization of (5.7) inherited from the orthonormal `coherentEqualDegree`
  builder.  In the (6.4) application it *is* available: (6.4.c) makes `L/H₁` a Frobenius group with
  kernel `K/H₁`, whose nontrivial linear characters have inertia group exactly `K`, so
  `Ind_K^L θ` is irreducible ([Is] Thm 6.34).

## Relation to the Sibley layer

The `K = H` instance of all of this is the `SibleyDadeHypothesis` development in
`S08_DegreeSums/CoherenceGlue` and `S08_CoherenceBasic`.  Nothing here is Sibley-specific: `K` is
an arbitrary solvable normal subgroup of `L`, and members of `𝒮(X)` are allowed to be reducible
everywhere except in the two theorems that explicitly take `hirr`.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {A₀ : Set ↥L} {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-! ### (5.3.a): the two-element `R(χ)` shape for an irreducible member -/

/-- **Peterfalvi (5.3.a) for an arbitrary `τ`.**  If `χ` is an irreducible non-real character and
`τ` is a (5.2.b) map — an isometry at `χ − χ̄`, landing in `ℤ[Irr G]` and vanishing at `1` (the
book's codomain `ℤ[Irr G, G^#]`) — then `τ(χ − χ̄) = ε·(μ − ν)` for distinct irreducible `μ, ν`
and a sign `ε`.

*Proof.*  `‖χ − χ̄‖² = 2` since `χ` is irreducible and `χ̄ ≠ χ`, so `‖τ(χ − χ̄)‖² = 2`; a virtual
character of norm-square `2` is a signed pair `ε_α·α + ε_β·β` of distinct irreducibles
(`exists_signed_pair_of_mem_ZIrr_inner_self_eq_two`, mathcomp `dirr_small_norm`).  Evaluating at
`1` gives `ε_α·α(1) + ε_β·β(1) = 0` with `α(1), β(1) > 0`, so the signs are opposite.

This is the book's "for `χ ∈ 𝒮`, `‖(χ − χ̄)^τ‖² = 2` and so (5.2.d) holds with `|R(χ)| = 2`"
(p. 25), made explicit in the signed shape that this repository's `S07.Hypothesis` takes. -/
theorem nonempty_characterDifferenceImage_of_irreducible
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G} {χ : ClassFunction ↥L ℂ}
    (hirr : IsIrreducibleCharacter χ) (hreal : ¬ ClassFunction.IsReal χ)
    (hisom : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) =
      ClassFunction.inner (χ - χ.conj) (χ - χ.conj))
    (hZ : τ (χ - χ.conj) ∈ ZIrr G) (h1 : τ (χ - χ.conj) (1 : G) = 0) :
    Nonempty (OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ χ) := by
  classical
  -- `‖χ − χ̄‖² = ⟨χ,χ⟩ − ⟨χ,χ̄⟩ − ⟨χ̄,χ⟩ + ⟨χ̄,χ̄⟩ = 1 − 0 − 0 + 1 = 2`.
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  have hne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  have hcross : ClassFunction.inner χ χ.conj = 0 := by
    simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ.conj, hconjirr⟩ |>.trans (if_neg (Ne.symm hne))
  have hcross' : ClassFunction.inner χ.conj χ = 0 := by
    simpa using irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hirr⟩ |>.trans (if_neg hne)
  have hnorm2 : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) = 2 := by
    rw [hisom, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hirr.inner_self_eq_one, hconjirr.inner_self_eq_one,
      hcross, hcross']
    ring
  obtain ⟨α, β, εα, εβ, hαirr, hβirr, hαβ, hεα, hεβ, hsum⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two hZ hnorm2
  -- degrees are positive naturals
  obtain ⟨a, hapos, ha⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨α, hαirr⟩ : IrreducibleCharacter G)
  obtain ⟨b, hbpos, hb⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨β, hβirr⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at ha hb
  -- evaluating at `1`: `εα·a + εβ·b = 0`, so the signs are opposite.
  have heval : (εα : ℂ) * (a : ℂ) + (εβ : ℂ) * (b : ℂ) = 0 := by
    have := congrArg (fun f : ClassFunction G ℂ => f (1 : G)) hsum
    simp only [ClassFunction.add_apply, ClassFunction.smul_apply] at this
    rw [h1, ha, hb] at this
    exact this.symm
  have hopp : εβ = -εα := by
    rcases hεα with rfl | rfl <;> rcases hεβ with rfl | rfl
    · exfalso
      have hz : ((a + b : ℕ) : ℂ) = 0 := by push_cast at heval ⊢; linear_combination heval
      have : a + b = 0 := by exact_mod_cast hz
      omega
    · rfl
    · rfl
    · exfalso
      have hz : ((a + b : ℕ) : ℂ) = 0 := by push_cast at heval ⊢; linear_combination -heval
      have : a + b = 0 := by exact_mod_cast hz
      omega
  exact ⟨
    { mu := ⟨α, hαirr⟩
      nu := ⟨β, hβirr⟩
      distinct := fun h => hαβ (congrArg Subtype.val h)
      sign := εα
      sign_eq := hεα
      image_eq := by
        rw [hsum, hopp]
        push_cast
        module }⟩

/-- The chosen (5.3.a) two-element image datum of an irreducible member — see
`nonempty_characterDifferenceImage_of_irreducible`.  Only its `image_eq` is ever used downstream
(through `signedDifference_eq`), so the choice is harmless. -/
noncomputable def characterDifferenceImage_of_irreducible
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G} {χ : ClassFunction ↥L ℂ}
    (hirr : IsIrreducibleCharacter χ) (hreal : ¬ ClassFunction.IsReal χ)
    (hisom : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) =
      ClassFunction.inner (χ - χ.conj) (χ - χ.conj))
    (hZ : τ (χ - χ.conj) ∈ ZIrr G) (h1 : τ (χ - χ.conj) (1 : G) = 0) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ χ :=
  (nonempty_characterDifferenceImage_of_irreducible hirr hreal hisom hZ h1).some

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [K.Normal] [Invertible (Nat.card ↥K : ℂ)] in
/-- `R(χ)`'s signed difference **is** `τ(χ − χ̄)` — `image_eq` read backwards.  Holds for *any*
`CharacterDifferenceImage`, so it is insensitive to the choice above. -/
theorem signedDifference_eq {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G}
    {χ : ClassFunction ↥L ℂ}
    (R : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ χ) :
    R.signedDifference = τ (χ - χ.conj) := R.image_eq.symm

/-! ### Hypothesis (5.2) for the sub-family `𝒮(X)` -/

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **`ℤ[𝒮(X), A₀] ⊆ ℤ[𝒮, A₀]`** — the sub-family's supported lattice sits inside the full
family's, since `𝒮(X) ⊆ 𝒮` (`inducedKernelFamily_subset_bot`) and `zSpan` is monotone. -/
theorem zSupportedSpan_inducedKernelFamily_subset (X : Subgroup ↥L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K X) A₀ ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ := by
  rintro φ ⟨hspan, hsupp⟩
  exact ⟨Submodule.span_mono (inducedKernelFamily_subset_bot (K := K) X) hspan, hsupp⟩

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **A member's conjugate difference lies in `ℤ[𝒮, A₀]`.**  `χ̄ ∈ 𝒮(X)` by conjugation closure
and has the same degree as `χ` (`ClassFunction.conj` preserves the value at `1` up to complex
conjugation and degrees are real), so `χ − χ̄` is `K^#`-supported. -/
theorem conjDiff_mem_zSupportedSpan
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {X : Subgroup ↥L} {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ inducedKernelFamily K X) :
    (χ - χ.conj : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ := by
  have hconj : χ.conj ∈ inducedKernelFamily K X :=
    inducedKernelFamily_closedUnderConjugate (K := K) X hχ
  refine ⟨Submodule.sub_mem _
    (Submodule.subset_span (inducedKernelFamily_subset_bot X hχ))
    (Submodule.subset_span (inducedKernelFamily_subset_bot X hconj)), ?_⟩
  have hneg : (χ - χ.conj : ClassFunction ↥L ℂ) = -(χ.conj - χ) := by abel
  rw [hneg, ClassFunction.support_neg]
  exact inducedKernelFamily_conjDiff_support hKsupp hχ

/-- **Peterfalvi (5.2.e) for irreducible members, derived** (the book's (5.3.a) argument): if
`φ ⊥ {χ, χ̄}` then `⟨(φ − φ̄)^τ, (χ − χ̄)^τ⟩ = ⟨φ − φ̄, χ − χ̄⟩ = 0`, because all four cross terms
vanish — two by hypothesis and two because `φ̄ ≠ χ`, `φ̄ ≠ χ̄` (else the hypothesis would read
`⟨φ, φ⟩ = 0` or `⟨φ, χ⟩ = ⟨χ, χ⟩ = 0`), so `inducedKernelFamily_pairwise_orthogonal` applies.

Stated for an arbitrary conjugation-closed subfamily `T ⊆ 𝒮` so that both the (6.5) filtrations
`𝒮(X)` and the (6.6) set `𝒳 = 𝒮 − 𝒮(Z)` can use it. -/
theorem tau_conjDiff_inner_eq_zero_of_orthogonal
    (RD : InducedFamilyTauData (G := G) A₀ K)
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {T : Set (ClassFunction ↥L ℂ)} (hTsub : T ⊆ inducedKernelFamily K ⊥)
    (hTconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate T)
    (hirr : ∀ φ ∈ T, IsIrreducibleCharacter φ)
    {φ χ : ClassFunction ↥L ℂ} (hφ : φ ∈ T) (hχ : χ ∈ T)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    ClassFunction.inner (RD.tau (φ - φ.conj)) (RD.tau (χ - χ.conj)) = 0 := by
  have hφc : φ.conj ∈ T := hTconj hφ
  have hχc : χ.conj ∈ T := hTconj hχ
  -- `φ ≠ χ` and `φ̄ ≠ χ`, else the two hypotheses would read `⟨φ, φ⟩ = 0`.
  have hne : φ ≠ χ := fun h => by
    rw [h, (hirr χ hχ).inner_self_eq_one] at h1; exact one_ne_zero h1
  have hcne : φ.conj ≠ χ := fun h => by
    rw [← h, ClassFunction.conj_conj, (hirr φ hφ).inner_self_eq_one] at h2
    exact one_ne_zero h2
  have hccne : φ.conj ≠ χ.conj := fun h => hne (by
    rw [← ClassFunction.conj_conj φ, h, ClassFunction.conj_conj])
  rw [RD.tau_isometry (conjDiff_mem_zSupportedSpan hKsupp (hTsub hφ))
      (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ)),
    ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, h1, h2,
    inducedKernelFamily_pairwise_orthogonal (hTsub hφc) (hTsub hχ) hcne,
    inducedKernelFamily_pairwise_orthogonal (hTsub hφc) (hTsub hχc) hccne]
  ring

omit [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] [K.Normal]
  [Invertible (Nat.card ↥K : ℂ)] in
/-- **(5.2.e) in the two-element shape**: once the two signed differences `τ(φ − φ̄)` and
`τ(χ − χ̄)` are orthogonal, the image sets `R(φ)`, `R(χ)` share no irreducible — Peterfalvi (4.1)
at `u = v = 1` (`inner_eq_zero_of_signedDifference_inner_zero_of_mem`). -/
theorem orthogonal_of_tau_conjDiff_inner_eq_zero
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G} {φ χ : ClassFunction ↥L ℂ}
    (Rφ : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ φ)
    (Rχ : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ χ)
    (h : ClassFunction.inner (τ (φ - φ.conj)) (τ (χ - χ.conj)) = 0) :
    Rφ.Orthogonal Rχ := fun _a _b ha hb =>
  S07.CharacterDifferenceImage.inner_eq_zero_of_signedDifference_inner_zero_of_mem Rφ Rχ
    (by rw [signedDifference_eq, signedDifference_eq]; exact h) ha hb

/-- **Hypothesis (5.2) for a conjugation-closed subfamily `T ⊆ 𝒮` with irreducible members.**
Every clause is inherited: (5.2.a) from `hTconj` plus non-reality on `𝒮` (`|L|` odd — Peterfalvi
(1.1)), (5.2.b) from the `InducedFamilyImageData` isometry restricted along `T ⊆ 𝒮`, (5.2.c) from
`inducedKernelFamily_pairwise_orthogonal`, (5.2.d) from the (5.3.a) two-element shape
`characterDifferenceImage_of_irreducible` — which is why the irreducibility `hirr` is required
here (it is *not* a hypothesis of the book's (5.2); see the module docstring) — and (5.2.e) from
`tau_conjDiff_inner_eq_zero_of_orthogonal`. -/
noncomputable def InducedFamilyTauData.hypothesisOfSubfamily
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {T : Set (ClassFunction ↥L ℂ)} (hTsub : T ⊆ inducedKernelFamily K ⊥)
    (hTconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate T)
    (hirr : ∀ φ ∈ T, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥L) (G := G) T A₀ where
  tau := RD.tau
  tau_isometry_diff _ _ hφ hζ :=
    RD.tau_isometry ⟨Submodule.span_mono hTsub hφ.1, hφ.2⟩
      ⟨Submodule.span_mono hTsub hζ.1, hζ.2⟩
  conjugate_closed := hTconj
  no_real_characters := (inducedKernelFamily_hasNoRealCharacters (K := K) hodd ⊥).mono hTsub
  pairwise_orthogonal _ _ hφ hφ' hne :=
    inducedKernelFamily_pairwise_orthogonal (hTsub hφ) (hTsub hφ') hne
  difference_image χ hχ :=
    characterDifferenceImage_of_irreducible (hirr χ hχ)
      ((inducedKernelFamily_hasNoRealCharacters (K := K) hodd ⊥).mono hTsub hχ)
      (RD.tau_isometry (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ))
        (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ)))
      (RD.tau_mem_ZIrr (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ)))
      (RD.tau_apply_one (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ)))
  difference_images_orthogonal _φ _χ hφ hχ h1 h2 :=
    orthogonal_of_tau_conjDiff_inner_eq_zero _ _
      (tau_conjDiff_inner_eq_zero_of_orthogonal RD hKsupp hTsub hTconj hirr hφ hχ h1 h2)

/-- **Hypothesis (5.2) for the filtration `𝒮(X)`** — the `T = inducedKernelFamily K X` instance of
`hypothesisOfSubfamily`. -/
noncomputable def InducedFamilyTauData.hypothesis
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {X : Subgroup ↥L} (hirr : ∀ φ ∈ inducedKernelFamily K X, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥L) (G := G) (inducedKernelFamily K X) A₀ :=
  RD.hypothesisOfSubfamily hodd hKsupp (inducedKernelFamily_subset_bot X)
    (inducedKernelFamily_closedUnderConjugate (K := K) X) hirr

@[simp] theorem InducedFamilyTauData.hypothesisOfSubfamily_tau
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {T : Set (ClassFunction ↥L ℂ)} (hTsub : T ⊆ inducedKernelFamily K ⊥)
    (hTconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate T)
    (hirr : ∀ φ ∈ T, IsIrreducibleCharacter φ) :
    (RD.hypothesisOfSubfamily hodd hKsupp hTsub hTconj hirr).tau = RD.tau := rfl

/-! ### Constant degree over an abelian section -/

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **Every member of `𝒮(X)` has degree `|L:K|` when `K/X` is abelian.**  A source
`θ ∈ Irr K` trivial on `X` inflates from `K/X`; an irreducible character of an abelian group is
linear, so `θ(1) = 1` and `(Ind_K^L θ)(1) = |L:K|·θ(1) = |L:K|`.

This is the "`K/H₁` is abelian" half of Peterfalvi's appeal to (5.7) inside the proof of
(6.5)(a). -/
theorem inducedKernelFamily_apply_one_eq_index_of_isMulCommutative_quotient
    {X : Subgroup ↥L} [(X.subgroupOf K).Normal]
    [IsMulCommutative (↥K ⧸ X.subgroupOf K)]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    φ (1 : ↥L) = (K.index : ℂ) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨θ, -, hθker, rfl⟩ := hφ
  rw [ClassFunction.induce_apply_one,
    apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := X.subgroupOf K) θ hθker, mul_one]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [K.Normal] [Invertible (Nat.card ↥K : ℂ)] in
/-- `|L:K| ≠ 0` as a complex number — `K` has finite index in the finite `L`.  (Degree
non-vanishing input of (5.7).) -/
theorem index_ne_zero_cast [Finite ↥L] : ((K.index : ℂ)) ≠ 0 := by
  exact_mod_cast K.index_ne_zero_of_finite

/-! ### Peterfalvi (6.3.b) for a general kernel: `𝒮(X)` is coherent when `K/X` is abelian -/

/-- **Peterfalvi (6.3.b) via (5.7), general kernel.**  If `K/X` is abelian (and `𝒮(X) ≠ ∅`, and
each member is irreducible), then `𝒮(X)` is coherent.

*Proof.*  All members have the common degree `|L:K|`
(`inducedKernelFamily_apply_one_eq_index_of_isMulCommutative_quotient`), so every member
difference is `K^#`-supported (`inducedKernelFamily_scaledDiff_support` at `d = 1`) and lies in
`ℤ[𝒮, A₀]`, where the (5.2.b) isometry `τ` applies and lands in `ℤ[Irr G]`.  Hypothesis (5.2)
holds for `𝒮(X)` (`InducedFamilyTauData.hypothesis`), and `|𝒮(X)| ≥ 2` because `𝒮(X)` is
conjugation-closed with no real members (Peterfalvi (1.1), `|L|` odd).  Then (5.7)
(`S07.coherent_of_constant_degree`) applies.

This is the input Peterfalvi cites as "(6.3.b) holds by (5.7)" in the proof of (6.5)(a), with
`X = H₁` the preimage of `[K/M, K/M]`. -/
theorem inducedKernelFamily_isCoherent_of_isMulCommutative_quotient
    (RD : InducedFamilyImageData A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀) (h1A : (1 : ↥L) ∉ A₀)
    {X : Subgroup ↥L} [(X.subgroupOf K).Normal]
    [IsMulCommutative (↥K ⧸ X.subgroupOf K)]
    (hXne : (inducedKernelFamily K X).Nonempty)
    (hirr : ∀ φ ∈ inducedKernelFamily K X, IsIrreducibleCharacter φ) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau (inducedKernelFamily K X) A₀) := by
  classical
  -- common degree `|L:K|`
  have hdeg : ∀ φ ∈ inducedKernelFamily K X, φ (1 : ↥L) = (K.index : ℂ) :=
    fun _ hφ => inducedKernelFamily_apply_one_eq_index_of_isMulCommutative_quotient hφ
  -- member differences are `A₀`-supported (the `d = 1` case of the scaled-difference lemma)
  have hsuppdiff : ∀ a ∈ inducedKernelFamily K X, ∀ b ∈ inducedKernelFamily K X,
      ((a - b : ClassFunction ↥L ℂ)).support ⊆ A₀ := by
    intro a ha b hb
    have h1 : a - b = a - (1 : ℕ) • b := by simp
    rw [h1]
    exact inducedKernelFamily_scaledDiff_support hKsupp ha hb
      (by rw [hdeg a ha, hdeg b hb]; simp)
  -- member differences lie in `ℤ[𝒮, A₀]`, so `τ` maps them into `ℤ[Irr G]`
  have hmemspan : ∀ a ∈ inducedKernelFamily K X, ∀ b ∈ inducedKernelFamily K X,
      (a - b : ClassFunction ↥L ℂ) ∈
        OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ := by
    intro a ha b hb
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span (inducedKernelFamily_subset_bot X ha))
      (Submodule.subset_span (inducedKernelFamily_subset_bot X hb)), hsuppdiff a ha b hb⟩
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree (RD.hypothesis hodd hKsupp hirr)
    (inducedKernelFamily_finite (K := K) X)
    (OddOrder.Peterfalvi.S07.two_le_ncard_of_conjugate_closed_of_noReal
      (inducedKernelFamily_finite (K := K) X) hXne
      (inducedKernelFamily_closedUnderConjugate (K := K) X)
      (inducedKernelFamily_hasNoRealCharacters (K := K) hodd X))
    (fun ζ hζ => (hirr ζ hζ).inner_self_eq_one)
    (fun a ha b hb => RD.tau_mem_ZIrr (hmemspan a ha b hb))
    (fun a ha b hb => by rw [hdeg a ha, hdeg b hb])
    (fun a ha => by rw [hdeg a ha]; exact index_ne_zero_cast) h1A hsuppdiff

/-! ### Peterfalvi (6.5)(a) for a general kernel -/

/-- **Peterfalvi (6.5)(a), index bound**: `|K : H₁| ≤ 4|L:K|² + 1`.

*Assume Hypothesis (6.4) and that `S(M)` is not coherent.  Then ... `|K:H₁| ≤ 4|L:K|²+1`.*
(p. 31.)  The book's proof is one line: *"Hypothesis (a) of Theorem (6.3) holds with `H = K`.
Since `K/H₁` is abelian and non-trivial, (6.3.b) holds by (5.7).  Therefore, from Theorem (6.3),
we obtain `|K:H₁| ≤ 4|L:K|²+1`."*  Here that is the contrapositive of `six_three_of_imageData`
at `H = K`, whose coherence input `(6.3.b)` is
`inducedKernelFamily_isCoherent_of_isMulCommutative_quotient` — the general-kernel (5.7) step —
and whose `S(H₁) ≠ ∅` witness comes from the solvability of `K`
(`commutator_quotient_ne_top_of_lt`).

The abelianness of `K/H₁` is Hypothesis (6.4)(c) (`H₁/M = [K/M, K/M]`), carried here as the
instance `[IsMulCommutative (↥K ⧸ H₁.subgroupOf K)]`.

⚠ `K` is taken nilpotent where the book takes `K/M` nilpotent — inherited from
`six_three_of_imageData` (the two agree at `M = 1`, which is the case (6.6) uses). -/
theorem relIndex_le_of_not_isCoherent
    [IsSolvable ↥K] [Group.IsNilpotent ↥K] (RD : InducedFamilyImageData A₀ K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀) (h1A : (1 : ↥L) ∉ A₀)
    {M H₁ : Subgroup ↥L} [M.Normal] [H₁.Normal]
    [IsMulCommutative (↥K ⧸ H₁.subgroupOf K)]
    (hMH₁ : M ≤ H₁) (hH₁K : H₁ < K)
    (hirr : ∀ φ ∈ inducedKernelFamily K H₁, IsIrreducibleCharacter φ)
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K M) A₀)) :
    H₁.relIndex K ≤ 4 * K.index ^ 2 + 1 := by
  haveI : (H₁.subgroupOf K).Normal := ‹H₁.Normal›.subgroupOf K
  by_contra hcon
  push Not at hcon
  refine hncoh (six_three_of_imageData RD hodd hKsupp h1A ‹K.Normal› hMH₁ hH₁K le_rfl
    (inducedKernelFamily_isCoherent_of_isMulCommutative_quotient RD hodd hKsupp h1A
      (inducedKernelFamily_nonempty_of_commutator_ne_top
        (commutator_quotient_ne_top_of_lt hH₁K)) hirr) ?_)
  simpa [Subgroup.relIndex, Subgroup.index] using hcon

/-- **Peterfalvi (6.5)(a), chief-factor clause**: `K/H₁` is a chief factor of `L`.

The group-theoretic half (`isChiefFactor_of_relIndex_le_of_odd_dvd`) needs only the (6.4)(c)
Frobenius divisibility `hdvd` and the index bound of `relIndex_le_of_not_isCoherent`; the whole
character-theoretic content of (6.5)(a) is in that bound. -/
theorem isChiefFactor_of_not_isCoherent
    [IsSolvable ↥K] [Group.IsNilpotent ↥K] (RD : InducedFamilyImageData A₀ K)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀) (h1A : (1 : ↥L) ∉ A₀)
    {M H₁ : Subgroup ↥L} [M.Normal] [H₁.Normal]
    [IsMulCommutative (↥K ⧸ H₁.subgroupOf K)]
    (hMH₁ : M ≤ H₁) (hH₁K : H₁ < K)
    (hdvd : ∀ W : Subgroup ↥L, W.Normal → H₁ ≤ W → W ≤ K →
      K.index ∣ W.relIndex K - 1 ∧ K.index ∣ H₁.relIndex W - 1)
    (hirr : ∀ φ ∈ inducedKernelFamily K H₁, IsIrreducibleCharacter φ)
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K M) A₀)) :
    OddOrder.GroupTheory.IsChiefFactor K H₁ :=
  isChiefFactor_of_relIndex_le_of_odd_dvd hodd hH₁K hdvd
    (relIndex_le_of_not_isCoherent RD hodd hKsupp h1A hMH₁ hH₁K hirr hncoh)

/-! ### Peterfalvi (6.5)(b),(c) for a general kernel -/

section SixFiveBC

variable [IsSolvable ↥K] [Group.IsNilpotent ↥K]
variable {H₁ : Subgroup ↥L} [H₁.Normal]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [K.Normal] [Invertible (Nat.card ↥K : ℂ)] [IsSolvable ↥K] [Group.IsNilpotent ↥K]
  [H₁.Normal] in
/-- `|K : H₁| = |Abelianization K|` when `H₁` traces out the commutator subgroup of `K` — the
`M = 1` case of Hypothesis (6.4)(c) (`H₁/M = [K/M, K/M]`). -/
theorem card_abelianization_eq_relIndex (hH₁comm : H₁.subgroupOf K = _root_.commutator ↥K) :
    Nat.card (Abelianization ↥K) = H₁.relIndex K := by
  rw [Subgroup.relIndex, Subgroup.index, hH₁comm]
  rfl

/-- **Peterfalvi (6.5)(b) for a general kernel**: `K` is a `p`-group for some prime `p`.

*"Since `S(H₁)` is coherent, `M ≠ H₁`, and so `K/M` is not abelian.  Since `K/M` is a nilpotent
group whose commutator subgroup is `H₁/M` and since `K/H₁` is a chief factor of `L`, `K/M` is a
`p`-group for some prime number `p`."*  (p. 31, at `M = 1`.)

The group-theoretic content is the already-general
`isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization`; its single character-theoretic
input is the (6.5)(a) bound `|K:H₁| ≤ 4|L:K|² + 1` supplied by `relIndex_le_of_not_isCoherent`.
The fixed-point-free `R`-action on `Abelianization K = K/H₁` with `|R| = |L:K|` is exactly what
Hypothesis (6.4)(c) provides (`L/H₁` is a Frobenius group with kernel `K/H₁`, so its complement
acts fixed-point-freely on the kernel). -/
theorem exists_prime_isPGroup_of_not_isCoherent
    (RD : InducedFamilyImageData A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀) (h1A : (1 : ↥L) ∉ A₀)
    [IsMulCommutative (↥K ⧸ H₁.subgroupOf K)]
    (hH₁comm : H₁.subgroupOf K = _root_.commutator ↥K) (hH₁K : H₁ < K)
    {R : Type*} [Group R] [Finite R] [MulDistribMulAction R (Abelianization ↥K)]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R (Abelianization ↥K))
    (hRcard : Nat.card R = K.index)
    (hirr : ∀ φ ∈ inducedKernelFamily K H₁, IsIrreducibleCharacter φ)
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K ⊥) A₀)) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥K := by
  have hcard := card_abelianization_eq_relIndex (K := K) hH₁comm
  have hAodd : Odd (Nat.card (Abelianization ↥K)) := by
    rw [hcard]
    exact hodd.of_dvd_nat ((Subgroup.relIndex_dvd_index_of_le hH₁K.le).trans H₁.index_dvd_card)
  have hRodd : Odd (Nat.card R) := by
    rw [hRcard]; exact hodd.of_dvd_nat K.index_dvd_card
  refine isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrob hAodd hRodd ?_
  rw [hcard, hRcard]
  exact relIndex_le_of_not_isCoherent RD hodd hKsupp h1A bot_le hH₁K hirr hncoh

/-- **Peterfalvi (6.5)(c) for a general kernel**: `|L:K|` does not divide `p − 1`.

*"If `|L:K|` divides `p − 1`, then `p ≥ 2|L:K| + 1`.  Since `K/M` is a non-abelian `p`-group,
`|K:H₁| ≥ p² ≥ (2|L:K|+1)² > 4|L:K|² + 1`, which is a contradiction."*  (p. 31, at `M = 1`.)

The non-abelianness enters through `commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient`: a
`p`-group `K` with `|K : K′| < p²` has cyclic abelianization (order `1` or `p`), hence is abelian
when nilpotent.  The rest is `six_five_c_arith` against the (6.5)(a) bound. -/
theorem not_dvd_sub_one_of_not_isCoherent
    (RD : InducedFamilyImageData A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀) (h1A : (1 : ↥L) ∉ A₀)
    [IsMulCommutative (↥K ⧸ H₁.subgroupOf K)]
    (hH₁comm : H₁.subgroupOf K = _root_.commutator ↥K) (hH₁K : H₁ < K)
    {p : ℕ} (hp : p.Prime) (hPgroup : IsPGroup p ↥K)
    (hnonab : _root_.commutator ↥K ≠ ⊥)
    (hirr : ∀ φ ∈ inducedKernelFamily K H₁, IsIrreducibleCharacter φ)
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent RD.tau
      (inducedKernelFamily K ⊥) A₀)) :
    ¬ (K.index ∣ p - 1) := by
  intro hdvd
  have hcard := card_abelianization_eq_relIndex (K := K) hH₁comm
  have hbound : H₁.relIndex K ≤ 4 * K.index ^ 2 + 1 :=
    relIndex_le_of_not_isCoherent RD hodd hKsupp h1A bot_le hH₁K hirr hncoh
  have hAodd : Odd (Nat.card (Abelianization ↥K)) := by
    rw [hcard]
    exact hodd.of_dvd_nat ((Subgroup.relIndex_dvd_index_of_le hH₁K.le).trans H₁.index_dvd_card)
  have hdodd : Odd K.index := hodd.of_dvd_nat K.index_dvd_card
  haveI : Fact p.Prime := ⟨hp⟩
  -- `K ≠ 1` (its commutator subgroup is nontrivial), so `p ∣ |K|`, and `|K|` divides the odd `|L|`.
  have hKnt : Nontrivial ↥K := by
    rcases subsingleton_or_nontrivial ↥K with hs | hn
    · exact absurd (Subgroup.eq_bot_of_subsingleton _) hnonab
    · exact hn
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hPgroup
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (Nat.card_eq_one_iff_unique.mp (by simpa using hm)).1
        (not_subsingleton ↥K)
    · exact h
  have hpodd : Odd p :=
    (hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)).of_dvd_nat
      (hm ▸ dvd_pow_self p (by omega))
  -- `p² ≤ |K : K′|`, else the abelianization is cyclic and `K` (nilpotent) would be abelian.
  have hpsq : p ^ 2 ≤ Nat.card (Abelianization ↥K) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp
      (hPgroup.to_quotient (_root_.commutator ↥K))
    have hn' : Nat.card (Abelianization ↥K) = p ^ n := hn
    have hn1 : n ≤ 1 := by
      by_contra hn2
      push Not at hn2
      have hle : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.one_lt.le hn2
      rw [hn'] at hlt
      omega
    haveI : IsCyclic (↥K ⧸ _root_.commutator ↥K) := by
      interval_cases n
      · have : Nat.card (↥K ⧸ _root_.commutator ↥K) = 1 := by simpa using hn
        haveI : Subsingleton (↥K ⧸ _root_.commutator ↥K) :=
          (Nat.card_eq_one_iff_unique.mp this).1
        exact isCyclic_of_subsingleton
      · exact isCyclic_of_prime_card (p := p) (by simpa using hn)
    exact hnonab
      (OddOrder.GroupTheory.commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient
        (G := ↥K) ‹_›)
  exact six_five_c_arith hp hpodd hdodd hdvd (hcard ▸ hpsq) (hcard ▸ hbound)

end SixFiveBC

end OddOrder.Peterfalvi.S08
