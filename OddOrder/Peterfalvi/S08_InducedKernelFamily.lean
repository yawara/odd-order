/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_YsetInner.CharacterBreaks

/-!
# Peterfalvi (6.1): the induced family `S(X)` for a general kernel, and the (6.6) `X`-set

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §6, Hypothesis
(6.1) and Theorem (6.6).

## Why this leaf exists (issue 0154 follow-up)

Hypothesis (6.1) fixes a solvable normal `K ⊴ L` and sets
`𝒮 = {Ind_K^L θ | θ ∈ Irr K, θ ≠ 1}`, with the filtration `𝒮(X)` cutting down to sources whose
kernel contains `X`.  That family (`inducedKernelFamily`) is defined here rather than in
`S08_SixTwoGeneral` because two independent §8 developments need it and they sit on *opposite*
sides of the import DAG:

* `S08_SixTwoGeneral` / `S08_SixTwoThreeFromImageFamilies` — the general-kernel (6.2)/(6.3);
* `S08_DegreeSums/CoherenceGlue` — the Sibley `SsubFiltration` (the `K = H` instance, whose
  definition is *verbatim* `inducedKernelFamily H`), which is **upstream** of the former.

Keeping the definition and its elementary API here lets the Sibley layer read its (6.6)
`X`-characterization off the general one instead of carrying a `K = H` copy of the proof.  The
namespace is unchanged (`OddOrder.Peterfalvi.S08`), so every existing consumer is unaffected.

## The (6.6) `X`-characterization

`inducedKernelFamily_sdiff_eq_irreducible_not_subset_characterKernel` is Peterfalvi (6.6)'s
set identity `X = 𝒮 − 𝒮(Z) = {χ ∈ Irr L | Z ⊄ Ker χ}`, for **any** normal `K` and `Z ≤ K`, under
the book's standing side condition that every member of `X` is irreducible.  Both inclusions route
the kernel comparison through a genuine character — `Res_K φ` for `⊆` and `Ind_K^L θ` for `⊇` —
together with the (1.6.a) forward bridge `subsetCharacterKernel_induce_of_subgroupOf`; no use of
[Is] Lemma 2.21 is needed.
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

end InducedKernelFamily

/-! ### Peterfalvi (6.6): the `X`-characterization at a general kernel -/

section XCharacterization

variable [Invertible (Nat.card ↥L : ℂ)]
variable {K : Subgroup ↥L} [Invertible (Nat.card ↥K : ℂ)]

/-- **Peterfalvi (6.6) `X`-characterization, general kernel** (mmd 04.8 L74-76).

For a normal `Z ≤ K` such that every member of `X = 𝒮 − 𝒮(Z)` is irreducible (the (6.8)
Frobenius/case-A side condition `hX`), `X` is exactly the set of irreducible characters of `L`
whose kernel does not contain `Z`:
`𝒮 − 𝒮(Z) = {χ ∈ Irr L | Z ⊄ Ker χ}`.

Nothing about the Feit–Thompson/Sibley setting enters: the argument uses only the *shape* of the
induced family — in fact `K` need not even be **normal** in `L` (the book has `K ⊴ L` from
Hypothesis (6.1), but this identity never uses it), so the statement is slightly stronger
than (6.6).  The Sibley `K = H` instance is
`SibleyDadeHypothesis.Xset_eq_irreducible_not_subset_characterKernel`
(`S08_DegreeSums/CoherenceGlue`), which is this theorem transported along
`SsubFiltration = inducedKernelFamily H`. -/
theorem inducedKernelFamily_sdiff_eq_irreducible_not_subset_characterKernel
    {Z : Subgroup ↥L} [Z.Normal] (hZK : Z ≤ K)
    (hX : ∀ φ ∈ inducedKernelFamily K ⊥ \ inducedKernelFamily K Z, IsIrreducibleCharacter φ) :
    inducedKernelFamily K ⊥ \ inducedKernelFamily K Z =
      {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
        ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)} := by
  have : Fintype ↥K := Fintype.ofFinite _
  ext φ
  constructor
  · -- (⊆): `φ ∈ X` is irreducible (`hX`); if `Z ⊆ Ker φ` then `φ ∈ 𝒮(Z)`, contradiction.
    intro hφX
    have hφirr : IsIrreducibleCharacter φ := hX φ hφX
    refine ⟨hφirr, ?_⟩
    obtain ⟨hφS, hφnotSZ⟩ := hφX
    obtain ⟨θ, hθ_ne, -, hφeq⟩ := hφS
    intro hZker
    refine hφnotSZ ⟨θ, hθ_ne, ?_, hφeq⟩
    -- `Z.subgroupOf K ⊆ Ker θ`: read off from `Res_K φ` (a genuine character with `θ` a
    -- constituent).
    have hRes : IsCharacter (ClassFunction.restrict K φ) := isCharacter_restrict hφirr.isCharacter K
    have hθirr : IsIrreducibleCharacter (θ : ClassFunction ↥K ℂ) := θ.property
    have hnorm : ClassFunction.inner φ φ = 1 := by
      have h := irreducibleCharacter_inner_eq_ite (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
      simpa using h
    have hinner_ne : ClassFunction.inner (ClassFunction.restrict K φ)
        (θ : ClassFunction ↥K ℂ) ≠ 0 := by
      have hfrob := ClassFunction.inner_induce_eq_inner_restrict K (θ : ClassFunction ↥K ℂ) φ
      rw [← hφeq, hnorm] at hfrob
      rw [inner_conj_symm θ (ClassFunction.restrict K φ), ← hfrob]
      simp
    intro n hn
    refine characterKernel_subset_of_isCharacter_of_inner_ne_zero hRes hθirr hinner_ne ?_
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    simp only [ClassFunction.restrict_apply]
    have hnZ : ((n : ↥L)) ∈ Z := Subgroup.mem_subgroupOf.mp hn
    have hker := hZker hnZ
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hker
    rw [hker, OneMemClass.coe_one]
  · -- (⊇): `χ` irreducible with `Z ⊄ Ker χ`.  Take a source `θ` of `χ`; show `Ind θ ∈ X`, hence
    -- irreducible (`hX`), hence `= χ` by orthonormality.
    rintro ⟨hχirr, hχZ⟩
    obtain ⟨θ, hθinner⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero (H := K)
      (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
    -- A source `θ'` of `χ` with `Z.subgroupOf K ⊆ Ker θ'` would force `Z ⊆ Ker χ` (contradiction).
    have hkey : ∀ θ' : IrreducibleCharacter ↥K,
        ClassFunction.inner (ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) φ ≠ 0 →
        ((Z.subgroupOf K : Set ↥K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥K ℂ)) → False := by
      intro θ' hθ'inner hθ'ker
      apply hχZ
      have hZind := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (G := ↥L) hZK (θ' : ClassFunction ↥K ℂ) hθ'ker
      intro z hz
      exact characterKernel_subset_of_inner_induce_ne_zero
        θ'.property.isCharacter hχirr hθ'inner (hZind hz)
    have hθ_ne : θ ≠ trivialIrreducibleCharacter ↥K := by
      intro hθtriv
      refine hkey θ hθinner (fun n _ => ?_)
      rw [hθtriv]
      simp [OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    have hIndnotSZ : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) ∉
        inducedKernelFamily K Z := by
      intro hmem
      obtain ⟨θ', _, hθ'ker, hθ'eq⟩ := hmem
      exact hkey θ' (by rw [← hθ'eq]; exact hθinner) hθ'ker
    have hIndX : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) ∈
        inducedKernelFamily K ⊥ \ inducedKernelFamily K Z := by
      refine ⟨⟨θ, hθ_ne, ?_, rfl⟩, hIndnotSZ⟩
      rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
    have hIndirr : IsIrreducibleCharacter (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)) :=
      hX _ hIndX
    have heq : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) = φ := by
      have hite := irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce K (θ : ClassFunction ↥K ℂ), hIndirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      by_cases hAB : (⟨ClassFunction.induce K (θ : ClassFunction ↥K ℂ), hIndirr⟩ :
          IrreducibleCharacter ↥L) = (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      · exact congrArg Subtype.val hAB
      · rw [if_neg hAB] at hite
        exact absurd hite hθinner
    rw [← heq]; exact hIndX

end XCharacterization

end OddOrder.Peterfalvi.S08
