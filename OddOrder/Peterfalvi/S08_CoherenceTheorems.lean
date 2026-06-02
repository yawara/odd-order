/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S07_Coherence
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Complement
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# Peterfalvi §8: Some Coherence Theorems

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37.

This module records the main carrier structures for the §8 coherence theorems:
the solvable-normal filtration setup (6.1), the odd-order specialization
(6.4), and the Sibley-style final setup (6.8).  The hard numerical and
class-sum-algebra proofs are intentionally not asserted here.

Reference note: `notes/peterfalvi/s08_coherence_theorems.md`.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

/- 6: Some coherence theorems (pp. 30-37) -/

/-- Peterfalvi (6.1): the filtration `S(A)` attached to the base character set
`S`.  In the text, larger kernel conditions give smaller subsets:
if `A ≤ B`, then `S(B) ⊆ S(A)`. -/
structure FiltrationData (S : Set (ClassFunction L ℂ)) where
  carrier : Subgroup L → Set (ClassFunction L ℂ)
  subset_base : ∀ A, carrier A ⊆ S
  mono : ∀ ⦃A B : Subgroup L⦄, A ≤ B → carrier B ⊆ carrier A

namespace FiltrationData

variable {S : Set (ClassFunction L ℂ)}

theorem subset_base_apply (F : FiltrationData (L := L) S) (A : Subgroup L) :
    F.carrier A ⊆ S :=
  F.subset_base A

theorem mem_base (F : FiltrationData (L := L) S) {A : Subgroup L}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ F.carrier A) : χ ∈ S :=
  F.subset_base A hχ

theorem mono_apply (F : FiltrationData (L := L) S) {A B : Subgroup L}
    (hAB : A ≤ B) : F.carrier B ⊆ F.carrier A :=
  F.mono hAB

theorem zSupportedSpan_subset_base (F : FiltrationData (L := L) S)
    (A : Subgroup L) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S B := by
  intro φ hφ
  exact OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left (L := L)
    (F.subset_base A) hφ

theorem zSupportedSpan_mono_apply (F : FiltrationData (L := L) S)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A₂) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) (F.carrier A₁) B := by
  intro φ hφ
  exact OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left (L := L)
    (F.mono hA) hφ

end FiltrationData

/-- Peterfalvi (6.1): solvable-normal filtration setup for applying coherence
descent. -/
structure DescentHypothesis (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  coherence : OddOrder.Peterfalvi.S07.Hypothesis (L := L) (G := G) S A
  K : Subgroup L
  K_normal : K.Normal
  K_solvable : IsSolvable K
  filtration : FiltrationData (L := L) S

namespace DescentHypothesis

variable {S : Set (ClassFunction L ℂ)} {A : Set L}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

theorem filtration_subset_base (hyp : DescentHypothesis (L := L) (G := G) S A)
    (A' : Subgroup L) : hyp.filtration.carrier A' ⊆ S :=
  hyp.filtration.subset_base A'

theorem filtration_mem_base (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A' : Subgroup L} {χ : ClassFunction L ℂ}
    (hχ : χ ∈ hyp.filtration.carrier A') : χ ∈ S :=
  hyp.filtration.mem_base hχ

theorem filtration_mono (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) :
    hyp.filtration.carrier A₂ ⊆ hyp.filtration.carrier A₁ :=
  hyp.filtration.mono hA

theorem filtration_zSupportedSpan_subset_base
    (hyp : DescentHypothesis (L := L) (G := G) S A)
    (A' : Subgroup L) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A') B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S B :=
  hyp.filtration.zSupportedSpan_subset_base A' B

theorem filtration_zSupportedSpan_mono
    (hyp : DescentHypothesis (L := L) (G := G) S A)
    {A₁ A₂ : Subgroup L} (hA : A₁ ≤ A₂) (B : Set L) :
    OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A₂) B ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L)
        (hyp.filtration.carrier A₁) B :=
  hyp.filtration.zSupportedSpan_mono_apply hA B

end DescentHypothesis

/-- Peterfalvi (6.4): the odd-order specialization used before (6.5)-(6.6). -/
structure OddOrderSpecialization (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] : Type _ extends
    DescentHypothesis (L := L) (G := G) S A where
  card_L_odd : Odd (Nat.card L)
  M : Subgroup L
  M_le_K : M ≤ K
  quotient_nilpotent : Prop

-- The legacy `SibleySetup`/`CoherenceTarget` (which carried an opaque `coherence.tau` with a
-- *global* `IsIntegralIsometry`, nonexistent in Feit–Thompson) is replaced by the Dade-based
-- `SibleyDadeHypothesis` below (T1; see issue 0046 / notes/peterfalvi/s08_6_8_assembly_plan.md).

/-- `H^# = H ∖ {1}` viewed as a subset of the ambient group `G`, for `H ≤ L ≤ G`.  This is the
support set `A` of the §4 Dade hypothesis in Peterfalvi (6.8): the nonidentity elements of `H`,
mapped from `↥L` into `G` along the inclusions. -/
def sharpImage {G : Type*} [Group G] {L : Subgroup G} (H : Subgroup ↥L) : Set G :=
  ((Subgroup.map L.subtype H : Subgroup G) : Set G) \ {1}

/-- **Peterfalvi (6.8): Dade-based carrier** (T1, faithful replacement of `SibleySetup`).

The legacy `SibleySetup` carried an opaque `coherence.tau` with a *global* `IsIntegralIsometry`,
which does not exist in Feit–Thompson (`dim CF(L) > dim CF(G)`); its `CoherenceTarget` was
therefore undischargeable. This carrier instead packages the genuine §4 Dade datum
`dade : S04.Hypothesis G H^# L`, so the coherence map `tau` is the **real**
`dadeIntegralCharacterMap` and `CoherenceTarget` is `IsCoherent` for that map — exactly the shape
the §7 coherence engine produces (`coherentUnion_of_glued`, `coherentEqualDegree_fromDade`, …),
realizing "τ coincides with the Dade isometry relative to (A,L,G)" (mmd 04.8 L150).

**Migration status (T1, `notes/peterfalvi/s08_6_8_assembly_plan.md`)**: this commit lands the
re-parametrization (`L : Subgroup G`, source type `↥L`) and the real-`tau` `CoherenceTarget`. The
remaining (6.8) hypotheses — `S = {Ind_H^L θ | θ ≠ 1}`, the split `L = H ⋊ W₁`, `H` nilpotent, and
the case (c1)/(c2) disjunction (`S06.CertainTypeHypothesis`) — are added next, after which
`sibleySetup_is_coherent` is restated against this carrier and the legacy `SibleySetup` removed. -/
structure SibleyDadeHypothesis (G : Type*) [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (L : Subgroup G) [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (H : Subgroup ↥L) [Invertible (Nat.card ↥H : ℂ)] where
  /-- A complement-side subgroup `W₁`; the split `L = H ⋊ W₁` is added in the next migration step. -/
  W1 : Subgroup ↥L
  H_ne_bot : H ≠ ⊥
  H_normal : H.Normal
  /-- `H` is nilpotent (Peterfalvi (6.8.a)). -/
  H_nilpotent : Group.IsNilpotent ↥H
  /-- `L = H ⋊ W₁`: `W₁` is a complement to the normal `H` (Peterfalvi (6.8.a)). -/
  split : Subgroup.IsComplement' H W1
  W1_nontrivial : W1 ≠ ⊥
  card_L_odd : Odd (Nat.card L)
  /-- `H^#` is a TI-subset of `G` relative to `L` (corrected ambient: TI in `G`, not in `↥L`). -/
  H_sharp_ti : OddOrder.GroupTheory.IsTISubset (sharpImage H) L
  /-- The §4 Dade datum on `A = H^#`; its Dade isometry *is* `tau`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G (sharpImage H) L
  hconj : dade.HConjInvariant
  /-- The base character set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (Peterfalvi (6.8.b)). -/
  S : Set (ClassFunction ↥L ℂ)
  /-- `S` is exactly the set of characters induced from nontrivial irreducibles of `H`. -/
  S_eq : S = {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}
  /-- Peterfalvi (6.8)(c): the configuration is one of two cases.

  * **(c1)** `L` is a Frobenius group with kernel `H` and complement `W₁`.
  * **(c2)** Hypothesis (4.6) holds — encoded by a `S06.CertainTypeHypothesis` on the *same* Dade
    datum (`cert.dade = dade`) whose kernel is `K = H` — with `w₂ = |W₂|` prime and `W₂ ⊆ [H,H]`.

  The (4.6)↔(6.8) renaming sets the (4.6)-kernel `K` to the (6.8) `H` (hence `cert.K = H`), and the
  (4.2)/(6.8) complement is shared (`cert.W1 = W1`, both giving `L = H ⋊ W₁`). With the S06 audit
  done (`S06.CertainTypeHypothesis` now faithfully encodes (4.2): the false `W₁ ⊔ W₂ = ⊤` removed,
  and complement / cyclic / `W₂ ≤ K` / `C_K(x) = W₂` / odd-`W` added), this matches textbook
  (6.8)(c2). -/
  cases :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H W1 ∨
    ∃ cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L,
      cert.dade = dade ∧ cert.K = H ∧ cert.W1 = W1 ∧
        (Nat.card cert.W2).Prime ∧ cert.W2 ≤ ⁅H, H⁆

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- The coherence map `τ` of the (6.8) setup, realized as the genuine §4 Dade isometry
(`dadeIntegralCharacterMap`) — **not** an opaque global isometry. -/
noncomputable abbrev tau (hyp : SibleyDadeHypothesis G L H) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
    (hyp.dade.fullDadeIsometryData hyp.hconj)

/-- The (6.8) coherence target: `S` is coherent for the **real Dade map** `tau`.  This is exactly
the conclusion shape produced by the §7 engine, hence honestly dischargeable — unlike the legacy
`SibleySetup.CoherenceTarget`, which required a nonexistent global isometry. -/
abbrev CoherenceTarget (hyp : SibleyDadeHypothesis G L H) :=
  OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.S
    (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)

/-- (6.8)(a) consequence: `[L : H] = |W₁|`.  From the complement `L = H ⋊ W₁` (`hyp.split`).
This is the common degree of the members of `Y = S(H')`: by [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`), `(Ind_H^L θ)(1) = [L:H]·θ(1) = |W₁|` for the
degree-`1` characters `θ ∈ Irr(H/H')`. -/
theorem index_H_eq_card_W1 (hyp : SibleyDadeHypothesis G L H) :
    H.index = Nat.card hyp.W1 :=
  (Subgroup.IsComplement.card_right (Subgroup.isComplement'_def.mp hyp.split)).symm

/-- Degree-one source characters induce to class functions of degree |W1| in the (6.8)
setup. This is the degree side of the Y = S(Hprime) family used in the final coherence assembly. -/
theorem induce_apply_one_eq_card_W1_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L) =
      (Nat.card hyp.W1 : ℂ) := by
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ_one, mul_one,
    hyp.index_H_eq_card_W1]

/-- If two source class functions induce to the same value at 1, their induced difference is
supported on H-sharp in the (6.8) Dade support. -/
theorem support_sub_induce_subset_sharpImage_of_apply_one_eq
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : ClassFunction ↥H ℂ)
    (hone : OddOrder.RepresentationTheory.ClassFunction.induce H θ (1 : ↥L) =
      OddOrder.RepresentationTheory.ClassFunction.induce H ψ (1 : ↥L)) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H θ -
        OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  letI : H.Normal := hyp.H_normal
  intro x hx
  have hθsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H θ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H θ
  have hψsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H ψ
  have hxH : x ∈ H := by
    rcases OddOrder.RepresentationTheory.ClassFunction.support_sub_subset
        (OddOrder.RepresentationTheory.ClassFunction.induce H θ)
        (OddOrder.RepresentationTheory.ClassFunction.induce H ψ) hx with hxθ | hxψ
    · exact hθsupp hxθ
    · exact hψsupp hxψ
  have hxne : x ≠ 1 := by
    intro hx1
    apply hx
    rw [hx1, OddOrder.RepresentationTheory.ClassFunction.sub_apply, hone, sub_self]
  change (x : G) ∈ sharpImage H
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  · intro hx1G
    exact hxne (Subtype.ext hx1G)

/-- Degree-one source characters give induced differences supported on H-sharp. -/
theorem support_sub_induce_subset_sharpImage_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hψ_one : (ψ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) -
        OddOrder.RepresentationTheory.ClassFunction.induce H (ψ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  hyp.support_sub_induce_subset_sharpImage_of_apply_one_eq
    (θ : ClassFunction ↥H ℂ) (ψ : ClassFunction ↥H ℂ) (by
      rw [hyp.induce_apply_one_eq_card_W1_of_degree_one θ hθ_one,
        hyp.induce_apply_one_eq_card_W1_of_degree_one ψ hψ_one])

end SibleyDadeHypothesis

/-- **Peterfalvi (6.8) Theorem** (statement; proof deferred).  Under the faithful Sibley
hypotheses `SibleyDadeHypothesis` (a)/(b)/(c), the set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` is
coherent: there is an integral isometric extension of the §4 Dade map `τ` from `Z[S, H^#]` to
`Z[S]` (`hyp.CoherenceTarget = IsCoherent hyp.tau S H^#`).

The full proof is the central technical content of §8 — the reduction to `H` a non-abelian
`p`-group ((6.5)), the case split (A)/(B) on `Z(H) ∩ W₂` (mmd L150-), and gluing the
`Y = S(H')`-coherence (equal degree `|W₁|`, via [Is] Thm 6.34, now available as
`isIrreducibleCharacter_induce_of_inertia_eq`) with the `X = S − S(Z)`-coherence ((6.6)) through
the §7 engine `coherentUnion_of_glued`. This is one of the two sorries blocking §9 (7.10)
`card_G0_lower_bound`; see `issues/0046-peterfalvi-s08-6-8-coherence.md` and
`notes/peterfalvi/s08_6_8_assembly_plan.md` (task DAG T0–T11).

`noncomputable def` (not `theorem`) because `CoherenceTarget` (an `IsCoherent`) carries the
extension map `ν` as data, living in `Type`, not `Prop`. -/
noncomputable def sibleySetup_is_coherent {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : SibleyDadeHypothesis G L H) : hyp.CoherenceTarget := by
  sorry

/-- **Peterfalvi (6.8) → (7.10) consumer interface.**
A degree-scaled `Z`-chain decomposition: given a coherence input `τ` on `(S, A)`
and an orthonormal family `ζ : Fin n → ClassFunction L ℂ` in `S` with explicit
integer degree ratios `d : Fin n → ℤ` (`d 0 = 1`), the family of images
`χ t = ν (ζ t)` under the coherence extension `ν` is orthonormal, and
`τ (ζ t - d t • ζ 0) = χ t - d t • χ 0`.

This packages the orthonormal-subsets-with-Ind-equation language used in the
(7.10) proof (see `references/peterfalvi/04.9_*.mmd` L133-135). -/
structure IndChainDecomposition
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G)
    {n : ℕ} [NeZero n]
    (ζ : Fin n → ClassFunction L ℂ) (d : Fin n → ℤ)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The orthonormal output family `χ_t = ν(ζ_t)` in `ClassFunction G ℂ`. -/
  χ : Fin n → ClassFunction G ℂ
  /-- Each `χ_t` has norm `1`. -/
  norm_one : ∀ t, ClassFunction.inner (χ t) (χ t) = 1
  /-- Distinct indices give orthogonal `χ`. -/
  pairwise_inner_zero :
    ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (χ t) (χ u) = 0
  /-- The reference index has trivial scaling: `d 0 = 1`. -/
  d_zero : d 0 = 1
  /-- The Ind equation: `τ(ζ_t - d_t · ζ_0) = χ_t - d_t · χ_0`. -/
  image_eq :
    ∀ t, τ (ζ t - (d t) • ζ 0) = χ t - (d t) • χ 0

namespace IndChainDecomposition

variable {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
variable {n : ℕ} [NeZero n]

/-- The Ind-chain decomposition vanishes at the reference index: for `t = 0`,
`τ(ζ 0 - d 0 · ζ 0) = 0`. -/
@[simp] theorem image_eq_zero
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ (ζ 0 - (d 0) • ζ 0) = 0 := by
  rw [data.d_zero, one_smul, sub_self, map_zero]

/-- The output family of an `IndChainDecomposition` is orthonormal, packaged as a
single `if` formula. -/
theorem inner_chi_eq_ite
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) (t u : Fin n) :
    ClassFunction.inner (data.χ t) (data.χ u) = if t = u then 1 else 0 := by
  by_cases htu : t = u
  · subst u
    rw [if_pos rfl, data.norm_one]
  · rw [if_neg htu, data.pairwise_inner_zero htu]

/-- The weighted output sum `∑ d_t χ_t` used in Peterfalvi (7.10). -/
noncomputable def weightedOutput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) : ClassFunction G ℂ :=
  ∑ t : Fin n, (d t : ℂ) • data.χ t

/-- Coefficient recovery for the weighted output sum. -/
theorem inner_chi_weightedOutput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) (t : Fin n) :
    ClassFunction.inner (data.χ t) data.weightedOutput = (d t : ℂ) := by
  classical
  rw [weightedOutput, inner_sum_right]
  have hsum :
      (∑ u : Fin n, ClassFunction.inner (data.χ t) ((d u : ℂ) • data.χ u)) =
        ∑ u : Fin n, (if u = t then (d u : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, data.inner_chi_eq_ite t u, star_intCast]
    by_cases hut : u = t
    · subst u
      rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg (Ne.symm hut), if_neg hut, mul_zero]
  rw [hsum, Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) t]
  simp

/-- Parseval for the weighted output: `‖∑ d_tχ_t‖² = ∑ d_t²`. -/
theorem weightedOutput_inner_self_eq_sum_sq
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    ClassFunction.inner data.weightedOutput data.weightedOutput =
      ∑ t : Fin n, (d t : ℂ) ^ 2 := by
  classical
  rw [weightedOutput, inner_sum_left]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ClassFunction.inner_smul_left]
  have hinner := data.inner_chi_weightedOutput t
  rw [weightedOutput] at hinner
  rw [hinner]
  ring

/-- Construct an `IndChainDecomposition` from a coherence input `hτ : IsCoherent τ S A`
together with the membership `ζ_t ∈ S`, the orthonormality of the input family `ζ`,
and the support of each scaled difference `ζ_t - d_t · ζ_0` in `Z[S, A]`.

The orthonormality of the images `χ_t = ν(ζ_t)` uses the **lattice-relative**
isometry `hτ.extension_inner_eq` on the generators `ζ_t ∈ S ⊆ Z[S] = zSpan S`
(`Submodule.subset_span`); this is all the weakened `IsCoherent` interface
supplies, and all it needs to. -/
noncomputable def ofIsCoherent
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hτ : OddOrder.Peterfalvi.S07.IsCoherent (L := L) (G := G) τ S A)
    {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A) :
    IndChainDecomposition (L := L) (G := G) τ ζ d where
  χ t := hτ.extension (ζ t)
  norm_one t := by
    rw [hτ.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem t)), hζ_norm]
  pairwise_inner_zero t u htu := by
    rw [hτ.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem u)), hζ_pairwise htu]
  d_zero := hd_zero
  image_eq t := by
    rw [← hτ.extends_on_supported _ (hsupp t), LinearMap.map_sub, map_zsmul]

end IndChainDecomposition

end OddOrder.Peterfalvi.S08
