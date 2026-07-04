/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordDecomposition
import OddOrder.Peterfalvi.S08_CoherenceCorePart1
import OddOrder.Peterfalvi.S08_Theorem62_63_Standalone

/-!
# Peterfalvi (6.2), general kernel: the induced family `S(X)`

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.1)/(6.2).

This leaf builds the *general-kernel* (6.1) induced family for the general (6.2) index bound
`|K:A| − 1 ≤ 2ψ(1)` — the `h56` oracle of `six_three_of_six_two_oracle`
(`S08_Theorem62_63_Standalone`, issue 2022).  The Sibley-case analogue (`SsubFiltration`,
`S08_CoherenceCorePart2`) is tied to the capstone kernel `K = H` (nilpotent, with a Frobenius
action making every member irreducible); the §11 setting needs `K = M'` (solvable), where
members `Ind_K^M θ` can be *reducible* (the μ-columns), so the family is (re)built here over
an arbitrary kernel subgroup `K ≤ L` with no irreducibility anywhere:

* `inducedKernelFamily K X` — Peterfalvi's `S(X) = {Ind_K^L θ | θ ∈ Irr K, θ ≠ 1, X ⊆ Ker θ}`
  (Coq: `seqIndD K L K X`), with the mem/antitone/finite/conjugation-closed/anchor lemma suite
  mirroring the Sibley `SsubFiltration_*` family.

The break-pair extractor for the general (6.2) chain is `exists_coherentBreakPair_general`
(`S08_CoherenceCorePart1`, already irreducibility-free); the (5.6) norm-weighted engine
consuming the break is `S08_CoherenceWeighted` (`coherentDegreeSqNormBound_of_not_coherentW`/
`_k`); the `S(A)` degree-square identity (B2) is `sum_div_normSq_induce_kernelFilter_eq`
(`S08_CoherenceCorePart1`, already general).  Reference: issue 2022; Coq `PFsection6.v`
`coherent_seqIndD_bound` (the `\unless` induction whose contrapositive the break realizes).
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]
variable {L : Subgroup G} [Fintype ↥L]

/-! ### The general (6.1) induced family `S(X)` -/

section InducedKernelFamily

variable (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)]

/-- **Peterfalvi (6.1) filtration `S(X)` for a general kernel `K ≤ L`** (Coq `seqIndD K L K X`):
the induced characters `Ind_K^L θ` of nontrivial irreducible sources `θ ∈ Irr K` whose kernel
contains `X`.  `S(⊥) = S` is the full induced family; the §11 consumer instantiates `K = M'`
(solvable), where members can be *reducible* (the μ-columns), unlike the Sibley `SsubFiltration`
(`K = H` with a Frobenius action making every member irreducible). -/
def inducedKernelFamily (X : Subgroup ↥L) : Set (ClassFunction ↥L ℂ) :=
  {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥K,
    θ ≠ trivialIrreducibleCharacter ↥K ∧
    (X.subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) ∧
    φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ)}

variable {K}

theorem mem_inducedKernelFamily {X : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} :
    φ ∈ inducedKernelFamily K X ↔ ∃ θ : IrreducibleCharacter ↥K,
      θ ≠ trivialIrreducibleCharacter ↥K ∧
      (X.subgroupOf K : Set ↥K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) ∧
      φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) :=
  Iff.rfl

/-- `S(X)` is antitone in the kernel demand `X`. -/
theorem inducedKernelFamily_antitone {X Y : Subgroup ↥L} (hXY : X ≤ Y) :
    inducedKernelFamily K Y ⊆ inducedKernelFamily K X := by
  intro φ hφ
  obtain ⟨θ, hθne, hker, hφeq⟩ := hφ
  refine ⟨θ, hθne, ?_, hφeq⟩
  intro x hxX
  exact hker (Subgroup.mem_subgroupOf.mpr (hXY (Subgroup.mem_subgroupOf.mp hxX)))

/-- Every filtration layer lies in the full family `S = S(⊥)`. -/
theorem inducedKernelFamily_subset_bot (X : Subgroup ↥L) :
    inducedKernelFamily K X ⊆ inducedKernelFamily K ⊥ :=
  inducedKernelFamily_antitone bot_le

/-- `S(X)` is finite (image of the finite irreducible-character set of `↥K`). -/
theorem inducedKernelFamily_finite (X : Subgroup ↥L) :
    (inducedKernelFamily K X).Finite := by
  classical
  haveI : Fintype ↥K := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥K) := finite_irreducibleCharacter (G := ↥K)
  refine (Set.finite_range
    (fun θ : IrreducibleCharacter ↥K =>
      ClassFunction.induce K (θ : ClassFunction ↥K ℂ))).subset ?_
  rintro φ ⟨θ, -, -, rfl⟩
  exact ⟨θ, rfl⟩

omit [Fintype ↥L] [Invertible (Nat.card ↥K : ℂ)] in
/-- A nontrivial irreducible character of `↥K` stays nontrivial after complex conjugation
(the trivial character is real, and conjugation is involutive). -/
theorem irreducibleCharacter_conj_ne_trivial_of_ne_trivial [Finite ↥K]
    {θ : IrreducibleCharacter ↥K}
    (hθne : θ ≠ trivialIrreducibleCharacter ↥K) :
    (⟨(θ : ClassFunction ↥K ℂ).conj, θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥K) ≠
      trivialIrreducibleCharacter ↥K := by
  intro hθc
  apply hθne
  apply IrreducibleCharacter.ext
  have hval : (θ : ClassFunction ↥K ℂ).conj =
      (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) :=
    congrArg (fun η : IrreducibleCharacter ↥K => (η : ClassFunction ↥K ℂ)) hθc
  calc (θ : ClassFunction ↥K ℂ)
      = ((θ : ClassFunction ↥K ℂ).conj).conj := by rw [ClassFunction.conj_conj]
    _ = (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ).conj := by rw [hval]
    _ = (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by ext x; simp

/-- `S(X)` is closed under complex conjugation: conjugating the source
(`ClassFunction.induce_conj`) preserves nontriviality and the kernel condition
(`characterKernel_conj`). -/
theorem inducedKernelFamily_closedUnderConjugate (X : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (inducedKernelFamily K X) := by
  intro φ hφ
  obtain ⟨θ, hθne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥K := ⟨(θ : ClassFunction ↥K ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, irreducibleCharacter_conj_ne_trivial_of_ne_trivial hθne, ?_, ?_⟩
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj K (θ : ClassFunction ↥K ℂ)

/-- **Member degree formula**: an `S(X)`-member `Ind_K^L θ` has degree `|L:K| · θ(1)`. -/
theorem inducedKernelFamily_apply_one {X : Subgroup ↥L} {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ inducedKernelFamily K X) :
    ∃ θ : IrreducibleCharacter ↥K,
      θ ≠ trivialIrreducibleCharacter ↥K ∧
      φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) ∧
      φ 1 = (K.index : ℂ) * (θ : ClassFunction ↥K ℂ) 1 := by
  obtain ⟨θ, hθne, -, hφeq⟩ := hφ
  exact ⟨θ, hθne, hφeq, by rw [hφeq, ClassFunction.induce_apply_one]⟩

/-- **The degree-`|L:K|` anchor member of `S(X)`** (the (6.2) anchor source, mmd 04.8 L14; Coq
`exists_linInd`): when `K/X` has proper commutator subgroup, a nontrivial linear character of
`K/X` inflates to a degree-one `θ ∈ Irr K` trivial on `X`, whose induction is an `S(X)`-member
of degree `|L:K|`. -/
theorem exists_inducedKernelFamily_member_degree_index {X : Subgroup ↥L}
    [(X.subgroupOf K).Normal]
    (hXcomm : commutator (↥K ⧸ X.subgroupOf K) ≠ ⊤) :
    ∃ φ ∈ inducedKernelFamily K X, φ (1 : ↥L) = (K.index : ℂ) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨θ, hθne, hθker, hθdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top
      (X.subgroupOf K) hXcomm
  exact ⟨ClassFunction.induce K (θ : ClassFunction ↥K ℂ),
    ⟨θ, hθne, hθker, rfl⟩,
    by rw [ClassFunction.induce_apply_one, hθdeg, mul_one]⟩

end InducedKernelFamily

/-! ### Family structure: orthogonality, norms, real-freeness -/

section FamilyStructure

variable [Invertible (Nat.card ↥L : ℂ)]
variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-- **Distinct members of `S(X)` are orthogonal** (members from distinct source orbits;
`induce_eq_induce_iff_conj` + `inner_induce_eq_zero_of_not_conj`).  No irreducibility of the
members: this is the pairwise orthogonality of the possibly-reducible general family. -/
theorem inducedKernelFamily_pairwise_orthogonal {X Y : Subgroup ↥L}
    {φ φ' : ClassFunction ↥L ℂ}
    (hφ : φ ∈ inducedKernelFamily K X) (hφ' : φ' ∈ inducedKernelFamily K Y)
    (hne : φ ≠ φ') :
    ClassFunction.inner φ φ' = 0 := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨θ', -, -, rfl⟩ := hφ'
  haveI : Fintype ↥K := Fintype.ofFinite _
  refine inner_induce_eq_zero_of_not_conj θ θ' (fun g hg => hne ?_)
  exact (induce_eq_induce_iff_conj θ θ').mpr ⟨g, hg⟩

/-- **Members of `S(X)` have real, positive squared norm** — `⟨φ, φ⟩ = ‖φ‖²·1` with
`0 < ‖φ‖².re` (`|K| · ⟨Ind θ, Ind θ⟩ = |I_L(θ)| > 0`,
`card_mul_inner_self_induce_eq_card_inertia`). -/
theorem inducedKernelFamily_inner_self_real_pos {X : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    ClassFunction.inner φ φ = ((ClassFunction.inner φ φ).re : ℂ) ∧
      0 < (ClassFunction.inner φ φ).re := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  haveI : Fintype ↥K := Fintype.ofFinite _
  constructor
  · rw [inner_self_eq_realCast (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)),
      Complex.ofReal_re]
  · have hcard := card_mul_inner_self_induce_eq_card_inertia (G := ↥L) (H := K) (θ := θ)
    set φ := ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
    -- take real parts: `|K| · ⟨φ,φ⟩.re = |I_L(θ)|`
    have hre : (Nat.card ↥K : ℝ) * (ClassFunction.inner φ φ).re
        = (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℝ) := by
      have := congrArg Complex.re hcard
      simpa [Complex.mul_re] using this
    have hKpos : (0 : ℝ) < (Nat.card ↥K : ℝ) := by exact_mod_cast Nat.card_pos
    have hIpos : (0 : ℝ)
        < (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℝ) := by
      exact_mod_cast Nat.card_pos
    nlinarith [hre]

/-- **`S(X)` has no real members** for `L` of odd order (Peterfalvi (1.1) extended to the
possibly-reducible family): `Ind_K^L θ` real would force `θ̄ = θ^g` for some `g ∈ L`
(`induce_conj` + `induce_eq_induce_iff_conj`), impossible in odd order
(`conjBy_ne_conj_of_odd` — `θ = θ^{g²}` and `⟨g⟩ = ⟨g²⟩` give `θ̄ = θ`, but a nontrivial
irreducible of an odd-order group is non-real). -/
theorem inducedKernelFamily_hasNoRealCharacters (hodd : Odd (Nat.card ↥L)) (X : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (inducedKernelFamily K X) := by
  rintro φ ⟨θ, hθne, -, rfl⟩ hreal
  haveI : Fintype ↥K := Fintype.ofFinite _
  -- realness transfers to the sources: `Ind θ = (Ind θ)̄ = Ind θ̄`.
  let θc : IrreducibleCharacter ↥K := ⟨(θ : ClassFunction ↥K ℂ).conj, θ.isIrreducible.conj⟩
  have hind : ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
      = ClassFunction.induce K (θc : ClassFunction ↥K ℂ) := by
    have h1 : (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)).conj
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) := hreal
    calc ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
        = (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)).conj := h1.symm
      _ = ClassFunction.induce K (θc : ClassFunction ↥K ℂ) :=
          ClassFunction.induce_conj K (θ : ClassFunction ↥K ℂ)
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ θc).mp hind
  have hθneCF : (θ : ClassFunction ↥K ℂ) ≠ trivialClassFunction ↥K :=
    fun h => hθne (Subtype.ext h)
  refine conjBy_ne_conj_of_odd hodd θ.isIrreducible hθneCF g ?_
  have := congrArg (fun η : IrreducibleCharacter ↥K => (η : ClassFunction ↥K ℂ)) hg
  simpa [IrreducibleCharacter.coe_conjBy, θc] using this

end FamilyStructure

/-! ### Support and lattice membership of family differences -/

section SupportLemmas

variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

omit [K.Normal] in
/-- Every `S(X)`-member is a virtual character of `L` (`Ind_K^L θ ∈ ℤ[Irr L]`). -/
theorem inducedKernelFamily_mem_ZIrr [Invertible (Nat.card ↥L : ℂ)] {X : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    φ ∈ ZIrr ↥L := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  haveI : Fintype ↥K := Fintype.ofFinite _
  exact ClassFunction.induce_mem_ZIrr K θ.mem_ZIrr

/-- **Scaled member differences are `K^#`-supported.**  For members `φ, φ' ∈ S(X)`/`S(Y)` with
matching degrees `φ(1) = d·φ'(1)`, the difference `φ − d·φ'` vanishes off `K` (induced characters
of the normal `K` vanish there, `induce_apply_eq_zero_of_not_mem_normal`) and at `1` (degree
match), so its support lies in any set containing `K ∖ {1}`.  This discharges the (5.6) engine's
support conditions (`hmemdegdiffsupp`/`hdiffasuppχ`) once the §11 consumer knows
`K^# ⊆ A₀` for its Dade support set `A₀`. -/
theorem inducedKernelFamily_scaledDiff_support {A0 : Set ↥L}
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A0)
    {X Y : Subgroup ↥L} {φ φ' : ClassFunction ↥L ℂ}
    (hφ : φ ∈ inducedKernelFamily K X) (hφ' : φ' ∈ inducedKernelFamily K Y)
    {d : ℕ} (hdeg : φ 1 = (d : ℂ) * φ' 1) :
    (φ - d • φ').support ⊆ A0 := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨θ', -, -, rfl⟩ := hφ'
  intro x hx
  rw [ClassFunction.mem_support] at hx
  have hnsmul : ∀ (ψ : ClassFunction ↥L ℂ) (y : ↥L), (d • ψ) y = (d : ℂ) * ψ y := by
    intro ψ y
    rw [← Nat.cast_smul_eq_nsmul ℂ d ψ, ClassFunction.smul_apply]
  have hval : ∀ y : ↥L,
      (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
        - d • ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) y
      = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) y
        - (d : ℂ) * ClassFunction.induce K (θ' : ClassFunction ↥K ℂ) y := by
    intro y
    rw [ClassFunction.sub_apply, hnsmul]
  refine hKsupp x ?_ ?_
  · -- off `K` both induced characters vanish
    by_contra hxK
    refine hx ?_
    rw [hval, ClassFunction.induce_apply_eq_zero_of_not_mem_normal K _ hxK,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal K _ hxK, mul_zero, sub_zero]
  · -- at `1` the degrees cancel
    intro hx1
    refine hx ?_
    rw [hx1, hval, hdeg, sub_self]

/-- **Conjugate member differences are `K^#`-supported**: `(φ̄ − φ).support ⊆ A₀` for a member
`φ ∈ S(X)` (the (5.6) engine's `hdiffsuppχ`/`hmemdiffsupp`).  Special case of the scaled
difference at `d = 1`: `φ̄` is again a member (`inducedKernelFamily_closedUnderConjugate`) of the
same (real, integral) degree `φ̄(1) = star φ(1) = φ(1)`. -/
theorem inducedKernelFamily_conjDiff_support {A0 : Set ↥L}
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A0)
    {X : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    (φ.conj - φ).support ⊆ A0 := by
  have hφc := inducedKernelFamily_closedUnderConjugate X hφ
  have hdeg : φ.conj 1 = ((1 : ℕ) : ℂ) * φ 1 := by
    obtain ⟨θ, -, -, rfl⟩ := hφ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    rw [Nat.cast_one, one_mul, ClassFunction.conj_apply, ClassFunction.induce_apply_one, hd]
    rw [show ((K.index : ℂ) * (d : ℂ)) = ((K.index * d : ℕ) : ℂ) by push_cast; ring]
    exact star_natCast _
  have h := inducedKernelFamily_scaledDiff_support hKsupp hφc hφ (d := 1) hdeg
  simpa using h

end SupportLemmas

/-! ### Break-character fields and member degree ratios -/

section BreakFields

variable [Invertible (Nat.card ↥L : ℂ)]
variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

omit [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **Member degree ratio against the index anchor.**  Every `S(X)`-member has degree an
integral multiple of `|L:K|`: `φ(1) = d · (K.index : ℂ)` with `d = θ(1) ∈ ℕ` positive.  This is
the divisibility `|L:K| ∣ ψ(1)` of the (6.2) proof (Coq: `dvdC_mulr`/`Cnat_irr1`), producing the
(5.6) engine's `deg` ratios once the anchor `χ₁(1) = |L:K|` is fixed. -/
theorem inducedKernelFamily_degree_ratio {X : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    ∃ d : ℕ, 0 < d ∧ φ 1 = (d : ℂ) * (K.index : ℂ) := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  exact ⟨d, hdpos, by rw [ClassFunction.induce_apply_one, hd]; ring⟩

/-- **The general break-character fields** — the break-side inputs of the norm-weighted (5.6)
engine, packaged for a break `ψ ∈ S(B)` whose conjugate pair avoids `S₁ ⊆ S = S(⊥)`.

General-family analogue of `caseB_breakChar_fields`/`caseB_breakChar_fields_columnBreak`
(`S08_CaseBEnumeration`): non-reality (odd order), nonzero self-norms (norm positivity), vanishing
cross-norms and orthogonality to `S₁` (distinct family members are orthogonal), and the
`A₀`-supported conjugate difference. -/
theorem inducedKernelFamily_breakChar_fields
    (hodd : Odd (Nat.card ↥L)) {A0 : Set ↥L}
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A0)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
      ClassFunction.inner ψ ψ ≠ 0 ∧ ClassFunction.inner ψ.conj ψ.conj ≠ 0 ∧
      ClassFunction.inner ψ.conj ψ = 0 ∧ ClassFunction.inner ψ ψ.conj = 0 ∧
      ((ψ.conj - ψ).support ⊆ A0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ χ = 0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ.conj χ = 0) := by
  have hψc := inducedKernelFamily_closedUnderConjugate B hψB
  have hreal : ¬ ClassFunction.IsReal ψ := inducedKernelFamily_hasNoRealCharacters hodd B hψB
  have hψconj_ne : ψ.conj ≠ ψ := fun h => hreal h
  have hnormψ := inducedKernelFamily_inner_self_real_pos hψB
  have hnormψc := inducedKernelFamily_inner_self_real_pos hψc
  refine ⟨hreal, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnormψ.1]
    exact_mod_cast hnormψ.2.ne'
  · rw [hnormψc.1]
    exact_mod_cast hnormψc.2.ne'
  · exact inducedKernelFamily_pairwise_orthogonal hψc hψB hψconj_ne
  · exact inducedKernelFamily_pairwise_orthogonal hψB hψc (fun h => hψconj_ne h.symm)
  · exact inducedKernelFamily_conjDiff_support hKsupp hψB
  · intro χ hχ
    exact inducedKernelFamily_pairwise_orthogonal
      (inducedKernelFamily_subset_bot B hψB) (hS₁sub hχ)
      (fun h => hψnotS1 (h ▸ hχ))
  · intro χ hχ
    exact inducedKernelFamily_pairwise_orthogonal
      (inducedKernelFamily_subset_bot B hψc) (hS₁sub hχ)
      (fun h => hψcnotS1 (h ▸ hχ))

end BreakFields

/-! ### The (6.2) B2 degree-square identity over `S(X)`, real form -/

section DegreeSum

variable [Invertible (Nat.card ↥L : ℂ)]
variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

omit [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
open scoped Classical in
/-- The kernel-filter image Finset of `sum_div_normSq_induce_kernelFilter_eq` enumerates exactly
the family `S(X) = inducedKernelFamily K X` (as a set). -/
theorem coe_kernelFilter_image_eq_inducedKernelFamily (X : Subgroup ↥L) :
    ↑((Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
          (↑(X.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥K ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥K)).image
        (fun θ => ClassFunction.induce K θ.toClassFunction))
      = inducedKernelFamily K X := by
  ext φ
  rw [Finset.coe_image, Set.mem_image]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter] at hθ
    exact ⟨θ, hθ.2.2, hθ.2.1, rfl⟩
  · rintro ⟨θ, hθne, hker, rfl⟩
    exact ⟨θ, by rw [Finset.mem_coe, Finset.mem_filter]; exact ⟨Finset.mem_univ θ, hker, hθne⟩,
      rfl⟩

open scoped Classical in
/-- **(6.2) degree-square sum over the general filtration `S(X)`, real form.**

The norm-weighted degree-square sum over `S(X) = {Ind_K^L θ | X ⊆ Ker θ, θ ≠ 1}` is
`|L:K|·(|K:X| − 1)` (Peterfalvi (6.2) proof, mmd 04.8 L13-17; Coq `sum_seqIndD_square`).
General-kernel form of `sum_re_div_normSq_SsubFiltration_eq` (`S08_Theorem63`, `K = H` Sibley):
the complex orbit-count identity `sum_div_normSq_induce_kernelFilter_eq` followed by the
per-summand real conversion (`χ(1)` a real degree, `⟨χ,χ⟩` real). -/
theorem sum_re_div_normSq_inducedKernelFamily_eq (X : Subgroup ↥L) [X.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
            (↑(X.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥K ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥K)).image
          (fun θ => ClassFunction.induce K θ.toClassFunction),
        ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      = (K.index : ℝ) * ((Nat.card (↥K ⧸ X.subgroupOf K) : ℝ) - 1) := by
  -- the complex weighted `S(X)` identity.
  have hcomplex := @sum_div_normSq_induce_kernelFilter_eq ↥L _ _ _ K _ _ X _
  -- per-summand real conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)`.
  have hconv : ∀ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
          (↑(X.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥K ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥K)).image
        (fun θ => ClassFunction.induce K θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ
        = (((χ 1).re ^ 2 / (ClassFunction.inner χ χ).re : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hχ1 : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : ↥L)
        = ((K.index * d : ℕ) : ℂ) := by
      rw [ClassFunction.induce_apply_one, hd]; push_cast; ring
    have hr : (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : ↥L)).re
        = ((K.index * d : ℕ) : ℝ) := by
      rw [hχ1, Complex.natCast_re]
    rw [hr, hχ1, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    congr 1
    rw [inner_self_eq_realCast (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)),
      Complex.ofReal_re]
  -- combine: cast the real sum to `ℂ`, rewrite each summand, identify with `hcomplex`.
  have key : (((∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
              (↑(X.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥K ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥K)).image
            (fun θ => ClassFunction.induce K θ.toClassFunction),
          ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re : ℝ)) : ℂ)
      = (((K.index : ℝ) * ((Nat.card (↥K ⧸ X.subgroupOf K) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hconv χ hχ).symm), hcomplex]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

end DegreeSum

/-! ### The break pair for incomparable filtrations -/

/-- **First obstruction to coherence, union form** — the (6.2) break pair for **incomparable**
`Sa`, `Sb` (no `Sa ⊆ Sb` demanded).

Peterfalvi (6.2) makes no inclusion assumption between the coherent `S(A)` and the incoherent
`S(B)` — the §11 instance (11.4) applies it with `(A, B) = (H₁, H₀C)` where neither contains the
other.  The absorption chain then runs over `X = Sa ∪ Sb` from the base `Sa` (Coq: `S1 = S2 ++ S A`
with `S2` the absorbed pairs of `S B`): if every pair of `Sb ∖ Sa` were absorbed coherently the
chain would reach `Sa ∪ Sb` coherent, hence `Sb` coherent by restriction
(`IsCoherent.subset`, with the nonzero supported witness `hne`) — contradiction.  So some pair
breaks, and the break `ψ` lies in `Sb` (the cover's pairs avoid the base `Sa`).

The inclusion-form extractor is `exists_coherentBreakPair_general`
(`S08_CoherenceCorePart1`); this wrapper instantiates it at `Sb := Sa ∪ Sb`. -/
theorem exists_coherentBreakPair_union
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) {A : Set ↥L}
    {Sa Sb : Set (ClassFunction ↥L ℂ)}
    (hSafin : Sa.Finite) (hSbfin : Sb.Finite)
    (hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sa)
    (hSbconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sb)
    (hSareal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sa)
    (hSbreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sb)
    (hne : ∃ φ : ClassFunction ↥L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) Sb A ∧ φ ≠ 0)
    (hSacoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sa A))
    (hSbncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sb A)) :
    ∃ (S₁ : Set (ClassFunction ↥L ℂ)) (ψ : ClassFunction ↥L ℂ),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ ∧ Sa ⊆ S₁ ∧ S₁ ⊆ Sa ∪ Sb ∧ ψ ∈ Sb ∧
      ψ ∉ S₁ ∧ ψ.conj ∉ S₁ ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A) ∧
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A) := by
  -- the union `Sa ∪ Sb` is finite, conjugation-closed, real-free, and *not* coherent
  -- (else `Sb ⊆ Sa ∪ Sb` would be coherent by restriction).
  have huncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (Sa ∪ Sb) A) := fun h =>
    hSbncoh (h.map (fun hcoh => hcoh.subset Set.subset_union_right hne))
  have hunconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (Sa ∪ Sb) := fun φ hφ => by
    rcases hφ with hφa | hφb
    · exact Or.inl (hSaconj hφa)
    · exact Or.inr (hSbconj hφb)
  have hunreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (Sa ∪ Sb) := fun φ hφ => by
    rcases hφ with hφa | hφb
    · exact hSareal hφa
    · exact hSbreal hφb
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁un, hψun, hψnotS₁, hψcnotS₁, hS₁coh, hbreak⟩ :=
    exists_coherentBreakPair_general τ Set.subset_union_left (hSafin.union hSbfin)
      hunconj hunreal hSaconj hSacoh huncoh
  -- the break lies in `Sb`: it avoids `S₁ ⊇ Sa`.
  have hψSb : ψ ∈ Sb := by
    rcases hψun with hψa | hψb
    · exact absurd (hSaS₁ hψa) hψnotS₁
    · exact hψb
  exact ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁un, hψSb, hψnotS₁, hψcnotS₁, hS₁coh, hbreak⟩

end OddOrder.Peterfalvi.S08
