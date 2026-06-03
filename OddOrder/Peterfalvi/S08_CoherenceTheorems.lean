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
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.BG.Ch1_Preliminary.S03_FrobeniusActions

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
open scoped commutatorElement

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
    datum (`cert.dade = dade`) whose kernel is `K = H` — with `w₂ = |W₂|` prime, `W₂ ⊆ [H,H]`, and
    the Hall coprimality `gcd(|H|, |W₁|) = 1` (Peterfalvi (4.2.a): `W₁` is a cyclic *Hall* subgroup
    of `L = H ⋊ W₁`, so its order is coprime to `|H| = [L : W₁]`).  This coprimality is the input to
    Isaacs (3.28) that lifts a `W₁`-fixed coset of `H/[H,H]` to a `W₁`-fixed element of `H`.

  The (4.6)↔(6.8) renaming sets the (4.6)-kernel `K` to the (6.8) `H` (hence `cert.K = H`), and the
  (4.2)/(6.8) complement is shared (`cert.W1 = W1`, both giving `L = H ⋊ W₁`). With the S06 audit
  done (`S06.CertainTypeHypothesis` now faithfully encodes (4.2): the false `W₁ ⊔ W₂ = ⊤` removed,
  and complement / cyclic / `W₂ ≤ K` / `C_K(x) = W₂` / odd-`W` added), this matches textbook
  (6.8)(c2). -/
  cases :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H W1 ∨
    ∃ cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L,
      cert.dade = dade ∧ cert.K = H ∧ cert.W1 = W1 ∧
        (Nat.card cert.W2).Prime ∧ cert.W2 ≤ ⁅H, H⁆ ∧
        Nat.Coprime (Nat.card ↥H) (Nat.card W1)

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

/-- Equal-degree induced irreducible families from degree-one source characters are coherent for
Sibley's Dade map. This is the engine-call form of the (6.8) Y = S(Hprime) step: once the
eta-family of irreducible induced characters is constructed and shown injective, the remaining
(1.1)+(1.4) equal-degree coherence hypotheses are discharged by the Sibley carrier. -/
noncomputable def coherentInducedDegreeOneFamily
    (hyp : SibleyDadeHypothesis G L H) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (θ : Fin n → IrreducibleCharacter ↥H) (η : Fin n → IrreducibleCharacter ↥L)
    (hη_ind : ∀ j,
      (η j : ClassFunction ↥L ℂ) =
        OddOrder.RepresentationTheory.ClassFunction.induce H (θ j : ClassFunction ↥H ℂ))
    (hηinj : Function.Injective η)
    (hθ_one : ∀ j, (θ j : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => (η j : ClassFunction ↥L ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hdeg : ∀ j, ((η j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 =
      ((η 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    rw [hη_ind j, hη_ind 0,
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ j) (hθ_one j),
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ 0) (hθ_one 0)]
  have hsuppdiff : ∀ j,
      (OddOrder.RepresentationTheory.irreducibleCharacterDifference η j).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    simpa [OddOrder.RepresentationTheory.irreducibleCharacterDifference, hη_ind j, hη_ind 0] using
      hyp.support_sub_induce_subset_sharpImage_of_degree_one (θ j) (θ 0)
        (hθ_one j) (hθ_one 0)
  have h1notA : (1 : G) ∉ sharpImage H := by
    intro h
    exact h.2 rfl
  exact OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hyp.hconj hn η hηinj
    hdeg hsuppdiff h1notA

/-- **(6.8)(c2) inertia equality** for a nontrivial linear `θ`.

Under the (4.6)/(c2) data — `H ⋊ W₁`, `C_H(w) = W₂ ⊆ ⁅H,H⁆` for `w ∈ W₁∖1`, and the Hall
coprimality `gcd(|H|,|W₁|) = 1` — the inertia group of a nontrivial degree-one `θ` is exactly `H`.

Proof.  Pass to `Ḡ = L/⁅H,H⁆`, `H̄ = H/⁅H,H⁆` (abelian).  `θ` is linear, so inflates from a
nontrivial `θ̄ ∈ Irr H̄`.  The coprimality + Isaacs (3.28) lift gives `C_{H̄}(w̄) = 1` for
`w̄ ∈ W̄₁∖1`; since `H̄` is abelian, Brauer's permutation lemma turns this into "`w̄` fixes only the
trivial irreducible", so `w̄ ∉ I_{Ḡ}(θ̄)`.  The inertia-transfer bridge then gives `w ∉ I_L(θ)` for
`w ∈ W₁∖1`, and the complement `L = H ⋊ W₁` reduces a general `g ∉ H` to this case (`I_L(θ) ⊇ H`, so
the `H`-part is absorbed). -/
theorem inertia_eq_H_of_c2 (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  -- The quotient `Ḡ = L/⁅H,H⁆` and the image `H̄ = H/⁅H,H⁆`.
  set M : Subgroup ↥L := ⁅H, H⁆ with hM_def
  haveI hMnormal : M.Normal := by rw [hM_def]; infer_instance
  set mkM : ↥L →* (↥L ⧸ M) := QuotientGroup.mk' M with hmkM_def
  set Hbar : Subgroup (↥L ⧸ M) := H.map mkM with hHbar_def
  haveI hHbar_normal : Hbar.Normal := by rw [hHbar_def, hmkM_def]; infer_instance
  -- `H̄` is abelian: images of `H` commute since their commutators land in `⁅H,H⁆ = ker mkM`.
  have hHbar_comm : ∀ a b : ↥Hbar, Commute a b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [hHbar_def, Subgroup.mem_map] at ha hb
    obtain ⟨x, hxH, rfl⟩ := ha
    obtain ⟨y, hyH, rfl⟩ := hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    -- `mkM x` and `mkM y` commute because `⁅x,y⁆ ∈ ⁅H,H⁆ = ker mkM`.
    have hcomm_elt : ⁅(x : ↥L), (y : ↥L)⁆ ∈ M := by
      rw [hM_def]; exact Subgroup.commutator_mem_commutator hxH hyH
    have hmk_one : mkM ⁅(x : ↥L), (y : ↥L)⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm_elt
    rw [map_commutatorElement] at hmk_one
    exact commutatorElement_eq_one_iff_mul_comm.mp hmk_one
  -- The corestriction `q : ↥H →* ↥H̄` with `(q x : Ḡ) = mkM x`.
  set q : ↥H →* ↥Hbar :=
    (mkM.comp H.subtype).codRestrict Hbar (fun x => by
      rw [hHbar_def]; exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩) with hq_def
  have hq : ∀ x : ↥H, ((q x : ↥Hbar) : ↥L ⧸ M) = mkM (x : ↥L) := fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩
    rw [hHbar_def, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz
    exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q : ClassFunction ↥Hbar ℂ → ClassFunction ↥H ℂ) :=
    ClassFunction.compHom_injective_of_surjective hq_surj
  -- `θ` is linear, hence kills `⁅H,H⁆.subgroupOf H = commutator ↥H`, so inflates from `H̄`.
  set N : Subgroup ↥H := M.subgroupOf H with hN_def
  haveI hN_normal : N.Normal := by rw [hN_def, hM_def]; exact hMnormal.subgroupOf H
  have hN_eq : N = _root_.commutator ↥H := by
    rw [hN_def, hM_def, ← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hker : (N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro n hn
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, hθ_one]
    -- `θ` is multiplicative with `θ(1)=1`, so `{x | θ x = 1}` is a subgroup containing commutators.
    have hθ1 : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1 := hθ_one
    have hn' : n ∈ Subgroup.closure (commutatorSet ↥H) := by
      have : n ∈ N := hn
      rwa [hN_eq, _root_.commutator_eq_closure] at this
    refine Subgroup.closure_induction
      (p := fun g _ => (θ : ClassFunction ↥H ℂ) g = 1) ?_ ?_ ?_ ?_ hn'
    · rintro _ ⟨a, b, rfl⟩
      exact θ.isIrreducible.apply_commutatorElement_eq_one_of_apply_one_eq_one hθ1 a b
    · exact hθ1
    · intro a b _ _ ha hb
      rw [θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1, ha, hb, one_mul]
    · intro a _ ha
      have hai := θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1 a a⁻¹
      rw [mul_inv_cancel, hθ1, ha, one_mul] at hai
      exact hai.symm
  have hkerq : q.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    change q x = 1 ↔ (x : ↥L) ∈ M
    constructor
    · intro hx
      have hx1 : mkM (x : ↥L) = 1 := by rw [← hq x, hx]; rfl
      rw [hmkM_def] at hx1
      exact (QuotientGroup.eq_one_iff _).mp hx1
    · intro hx
      apply Subtype.ext
      rw [hq x, hmkM_def]
      exact (QuotientGroup.eq_one_iff _).mpr hx
  -- `θ` inflates from a `θ̄ : Irr ↥H̄` along the surjection `q` (linear ⟹ `ker q = N ⊆ ker θ`).
  obtain ⟨θbar, hcompq⟩ :=
    exists_compHom_eq_of_subset_characterKernel hq_surj θ (by rw [hkerq]; exact hker)
  -- `θ̄` is nontrivial, else `θ = compHom q (triv) = triv`.
  have hθbar_ne : θbar ≠ trivialIrreducibleCharacter ↥Hbar := by
    intro hbar
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hcompq, hbar]
    ext x
    simp [ClassFunction.compHom_apply, trivialIrreducibleCharacter,
      trivialClassFunction_apply]
  -- **B1′** (fixed-point-free action of `W̄₁` on `H̄`): `C_{H̄}(w̄) = 1` for `w̄ ∈ W̄₁∖1`.
  -- We only need the specific `w̄ = mkM w`; the S03 `≤ N` quotient lemma supplies it.
  have hNK : (⁅H, H⁆ : Subgroup ↥L) ≤ H := Subgroup.commutator_le_left H H
  have hcentral : ∀ x ∈ hyp.W1, x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥L) ⊓ H ≤ M := by
    intro x hxW1 hxne
    have hcw2 : Subgroup.centralizer ({x} : Set ↥L) ⊓ cert.K = cert.W2 :=
      cert.centralizer_W2 x (hW1 ▸ hxW1) hxne
    rw [hK] at hcw2
    rw [hcw2, hM_def]; exact hW2
  have hlift : ∀ x ∈ hyp.W1, x ≠ 1 → ∀ y ∈ H,
      mkM (x * y * x⁻¹) = mkM y →
        ∃ c : ↥L, c ∈ H ∧ mkM c = mkM y ∧ x * c * x⁻¹ = c := by
    intro x hxW1 hxne y hyH hfix
    have hcop_x : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥H) := by
      rw [Nat.card_zpowers]
      have hdvd : orderOf x ∣ Nat.card hyp.W1 := hyp.W1.orderOf_dvd_natCard hxW1
      exact (hcop.coprime_dvd_right hdvd).symm
    exact OddOrder.BG.Ch1.S03.fixedPoint_lift_of_generator_quotient_fixed
      hNK hcop_x (Or.inl (by infer_instance)) hyH hfix
  have hB1 : ∀ qx ∈ hyp.W1.map mkM, qx ≠ 1 →
      Subgroup.centralizer ({qx} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ := by
    rw [hHbar_def, hmkM_def]
    exact OddOrder.BG.Ch1.S03.quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift_of_le
      hcentral hlift
  -- Assemble: `I_L(θ) = H` by `le_antisymm`.
  apply le_antisymm
  · -- `I_L(θ) ≤ H`: a `g ∉ H` is `h·w` with `w ∈ W₁∖1`, and `w ∉ I_L(θ)`.
    intro g hg
    by_contra hgH
    -- Write `g = h * w` via the complement `L = H ⋊ W₁`.
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    -- `w ≠ 1`, else `g = h ∈ H`.
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1
      apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    -- `h ∈ H ⊆ I_L(θ)`, so `w = h⁻¹·g ∈ I_L(θ)`.
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).mul_mem
        ((ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).inv_mem hhinertia)
        (ClassFunction.mem_inertia.mpr hg)
    -- Transfer `w ∈ I_L(θ)` to `w̄ ∈ I_{Ḡ}(θ̄)`.
    rw [← hcompq] at hwinertia
    have hwbar : mkM (w : ↥L) ∈ ClassFunction.inertia (θbar : ClassFunction ↥Hbar ℂ) :=
      (mem_inertia_compHom_iff q hq hqinj (θbar : ClassFunction ↥Hbar ℂ) (w : ↥L)).mp hwinertia
    -- But `w̄ ∉ I_{Ḡ}(θ̄)`: `C_{H̄}(w̄) = 1`, abelian Brauer, `θ̄ ≠ triv`.
    have hwbar_mem : mkM (w : ↥L) ∈ hyp.W1.map mkM :=
      Subgroup.mem_map.mpr ⟨w, w.property, rfl⟩
    have hwbar_ne : mkM (w : ↥L) ≠ 1 := by
      intro hw1
      have hwM : (w : ↥L) ∈ M := by
        rw [hmkM_def, QuotientGroup.mk'_apply] at hw1
        exact (QuotientGroup.eq_one_iff _).mp hw1
      exact hwne (Subgroup.disjoint_def.mp hyp.split.disjoint (hNK (hM_def ▸ hwM)) w.property)
    have hfree : Subgroup.centralizer ({mkM (w : ↥L)} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ :=
      hB1 (mkM (w : ↥L)) hwbar_mem hwbar_ne
    have hclass : Nat.card (Function.fixedPoints
        (ConjClasses.conjByPerm (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)))) = 1 :=
      card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot
        (mkM (w : ↥L)) hHbar_comm hfree
    exact not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one
      (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)) hclass hθbar_ne hwbar
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **Peterfalvi (6.8) Y-family irreducibility.**  For a nontrivial degree-one (linear) source
character `θ` of `H`, the induced character `Ind_H^L θ` is irreducible.  Inertia `I_L(θ) = H`
(free action of `W₁`) is discharged via the (6.8)(c) disjunction and fed to [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`):

* **(c1)** `L` Frobenius with kernel `H`: `isIrreducibleCharacter_induce_of_frobeniusGroup`
  (needs only `θ ≠ 1`; degree-one not used).
* **(c2)** Hyp (4.6): the inertia bridge `inertia_eq_H_of_c2` from
  `CertainTypeHypothesis.centralizer_W2` + Hall coprimality + Isaacs 3.28 on `H/H'` (T6 §5). -/
theorem isIrreducibleCharacter_induce_of_degree_one (hyp : SibleyDadeHypothesis G L H)
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rcases hyp.cases with hF | ⟨cert, _hdade, hK, hW1, _hprime, hW2, hcop⟩
  · exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne
  · -- (c2) inertia bridge: `I_L(θ) = H` via the abelian quotient `H/⁅H,H⁆` (Brauer + Isaacs 3.28).
    exact isIrreducibleCharacter_induce_of_inertia_eq θ
      (hyp.inertia_eq_H_of_c2 cert hK hW1 hW2 hcop hθ_one hθ_ne)

/-- **(6.8) `Y = S(H')` coherence (engine call from a constructed family).**  Given a family of
nontrivial linear source characters `χ_j : H →* ℂˣ` indexed by `Fin n` (`n ≥ 2`), pairwise
non-`L`-conjugate, with each `Ind_H^L (linear χ_j)` irreducible (`hirr`), the induced family
`Y = {Ind_H^L (linear χ_j)}` is coherent for Sibley's Dade map `tau`.

This is the (6.8) `Y`-step: the `χ_j` are the `Irr(H/H') ∖ {1}` orbit representatives (degree one,
so each `Ind` has the common degree `|W₁|`).  `hirr` and the pairwise non-conjugacy come from the
free `W₁`-action (`isIrreducibleCharacter_induce_of_degree_one`).  Injectivity of
`j ↦ Ind_H^L (linear χ_j)` is the cross-Mackey orthogonality `inner_induce_eq_zero_of_not_conj`;
the equal-degree coherence is then `coherentInducedDegreeOneFamily`. -/
noncomputable def coherentYFamily (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j))
    (hirr : ∀ j, IsIrreducibleCharacter
      (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hηinj : Function.Injective
      (fun j => (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
        hirr j⟩ : IrreducibleCharacter ↥L)) := by
    intro i j hij
    by_contra hne
    have h0 := inner_induce_eq_zero_of_not_conj
      (linearIrreducibleCharacter (χ i)) (linearIrreducibleCharacter (χ j))
      (fun g => hpairwise i j hne g)
    have hcoe : ClassFunction.induce H (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
        ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      congrArg Subtype.val hij
    rw [hcoe] at h0
    have h1 : ClassFunction.inner
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)) = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
          hirr j⟩ : IrreducibleCharacter ↥L)
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ), hirr j⟩)
    rw [h1] at h0
    exact one_ne_zero h0
  exact coherentInducedDegreeOneFamily hyp hn
    (fun j => linearIrreducibleCharacter (χ j))
    (fun j => ⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
      hirr j⟩)
    (fun _ => rfl) hηinj (fun j => linearIrreducibleCharacter_apply_one (χ j))

/-! ### Peterfalvi (6.8) `X`-characterization (T7): the sets `S(A)`, `X = S − S(Z)`, `Y = S(H')`

mmd 04.8 L150-164.  The (6.8) proof denotes `H' = [H,H]`, sets `Z = Z(H) ∩ H'` in case (A) and
`Z = W₂` in case (B), and forms `X = S − S(Z)`, `Y = S(H')` (`Z ⊆ H'` makes `X ∩ Y = ∅`).
`S(A)` is the (6.1) filtration: the members of `S` whose source `θ` has `A` in its kernel. -/

/-- **Peterfalvi (6.1) filtration `S(A)`** in the (6.8) setup: the members `Ind_H^L θ` of `S`
(`θ ∈ Irr H`, `θ ≠ 1_H`) whose source `θ` has `A` (as a subgroup of `H`) inside its kernel.
`S(1) = S`, and the (6.8) sets are `X = S − S(Z)` and `Y = S(H')`. -/
def SsubFiltration (_hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    (A.subgroupOf H : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}

/-- The (6.8) set `X = S − S(Z)` (the (6.6) `X`-set) for a normal `Z ⊆ Z(H)`. -/
def Xset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  hyp.S \ hyp.SsubFiltration Z

/-- The (6.8) set `Y = S(H')` (`H' = [H,H]`), the equal-degree family handled by T6. -/
def Yset (hyp : SibleyDadeHypothesis G L H) : Set (ClassFunction ↥L ℂ) :=
  hyp.SsubFiltration ⁅H, H⁆

/-- Membership in `S(A)`, unfolded. -/
theorem mem_SsubFiltration (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.SsubFiltration A ↔ ∃ θ : IrreducibleCharacter ↥H,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
      (A.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
      φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
  Iff.rfl

/-- Membership in `X = S − S(Z)`, unfolded. -/
theorem mem_Xset (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Xset Z ↔ φ ∈ hyp.S ∧ φ ∉ hyp.SsubFiltration Z :=
  Iff.rfl

/-- **(6.8.1), case (c1):** in the Frobenius case every member of `S` is irreducible (hence
`X ⊆ Irr L`).  By [Is] Thm 6.34 (`isIrreducibleCharacter_induce_of_frobeniusGroup`), inducing any
nontrivial irreducible of the kernel `H` to the Frobenius group `L` gives an irreducible. -/
theorem isIrreducibleCharacter_of_mem_S_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.S) : IsIrreducibleCharacter φ := by
  letI : H.Normal := hyp.H_normal
  haveI : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hφ
  obtain ⟨θ, hθ_ne, rfl⟩ := hφ
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne

/-- **(6.8.1), case (c1):** `X ⊆ Irr L` in the Frobenius case, since `X ⊆ S` and `S ⊆ Irr L`.
This is the irreducibility input the §6 coherence engine (T8) consumes for the `X`-family (and the
`hX` hypothesis of the (6.6) characterization). -/
theorem isIrreducibleCharacter_of_mem_Xset_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Xset Z) :
    IsIrreducibleCharacter φ :=
  hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hyp.mem_Xset.mp hφ).1

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
