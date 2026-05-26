/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import OddOrder.GroupTheory.RepresentationTheory.Inertia
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing

/-!
# Clifford's theorem on irreducible characters of a normal subgroup

For a normal subgroup `H ⊴ G` and an irreducible complex character `χ ∈ Irr G`,
**Clifford's theorem** ([Is] Thm 6.5) describes the restriction `Res_H^G χ` in terms of
the `G`-conjugation action on `Irr H`:

> Every irreducible component `θ ∈ Irr H` of `Res χ` is a `G`-conjugate of every other,
> all of them appear with the same multiplicity, and
>
>   `Res_H^G χ = e_χ · (θ^{g_1} + θ^{g_2} + … + θ^{g_t})`,
>
> where `{g_1, …, g_t}` runs over a transversal of the inertia subgroup `T = I_G(θ)`
> in `G` (so `t = [G : T]`) and `e_χ = ⟨Res χ, θ⟩_H` is the common multiplicity.

A companion result ([Is] Thm 6.11) is the **inertia bijection**: induction from `T`
gives a bijection between `Irr(T)` lying over `θ` and `Irr(G)` lying over `θ`. The
precise statement is left as a TODO since it requires extra setup
(`InducedCharacter` numerical Frobenius reciprocity + multiplicity counting).

## Status

* The Clifford decomposition `clifford_decomposition` is stated below; the proof is
  deferred. It will follow from `InducedCharacter` + `SecondOrthogonality` once those
  Wave 1a modules have working proofs.
* `ClassFunction.restrictionMultiplicity`, `ClassFunction.IsRestrictionConstituent`,
  and `IrreducibleCharacter.LiesOver` name the restriction-constituent API that the
  proof core needs.
* `clifford_orbit_subset_inertia` is immediate from `ClassFunction.subgroup_le_inertia`.
* Proof-core routing: the remaining Clifford theorem proof is split into
  `issues/0026-peterfalvi-clifford-core.md`.  The blocker is not the current
  statement shape; it is the missing character-level induction/restriction API:
  numerical Frobenius reciprocity, restriction multiplicities, orbit equality of
  irreducible constituents, and the inertia-bijection package.

## Main statements

* `OddOrder.RepresentationTheory.clifford_decomposition` — the Clifford decomposition.
* `OddOrder.RepresentationTheory.ClassFunction.IsRestrictionConstituent` — a
  constituent of a restricted class function, expressed by inner product.
* `OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver` — irreducible-character
  notation for the same nonzero restriction multiplicity.
* `OddOrder.RepresentationTheory.IrreducibleCharacter.RestrictionConstituentsSingleOrbit`
  and `HasCommonRestrictionMultiplicity` — predicate-level Clifford conclusions.
* `OddOrder.RepresentationTheory.IrreducibleCharacter.HasCyclicInertiaQuotient` —
  the Peterfalvi §3 (1.7) cyclic inertia-quotient hypothesis.
* `OddOrder.RepresentationTheory.clifford_orbit_subset_inertia` — `H ≤ I_G(θ)`.

## References

* Isaacs, *Character Theory of Finite Groups*, Theorem 6.5 (Clifford) and Theorem 6.11
  (Induction from inertia).
* Peterfalvi §3 (1.5) (Clifford suite), (1.7) (multiplicity-one for cyclic inertia).
* Bender–Glauberman §2 Prop 2.2 (Clifford for cyclic quotient `G/H`) — uses the same
  decomposition.
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

namespace Representation

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Pulling a representation back along a group automorphism preserves irreducibility. -/
theorem IsIrreducible.comp_mulEquiv
    (ρ : Representation k G V) [Representation.IsIrreducible ρ] (e : G ≃* G) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  change IsSimpleOrder (Subrepresentation (ρ.comp e.toMonoidHom))
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot
    have hsub :
        ((⊥ : Subrepresentation (ρ.comp e.toMonoidHom)).toSubmodule) =
          ((⊤ : Subrepresentation (ρ.comp e.toMonoidHom)).toSubmodule) :=
      congrArg Subrepresentation.toSubmodule hbot
    have hρbot : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using hsub
    exact IsSimpleOrder.bot_ne_top hρbot
  · intro W
    let Wρ : Subrepresentation ρ := {
      toSubmodule := W.toSubmodule
      apply_mem_toSubmodule h {v} hv := by
        rcases e.surjective h with ⟨h', rfl⟩
        exact W.apply_mem_toSubmodule h' hv }
    rcases IsSimpleOrder.eq_bot_or_eq_top Wρ with hbot | htop
    · left
      apply Subrepresentation.toSubmodule_injective
      simpa [Wρ] using congrArg (fun X : Subrepresentation ρ => X.toSubmodule) hbot
    · right
      apply Subrepresentation.toSubmodule_injective
      simpa [Wρ] using congrArg (fun X : Subrepresentation ρ => X.toSubmodule) htop

end Representation

namespace ClassFunction

variable (H : Subgroup G) [Fintype H] [Invertible (Nat.card H : ℂ)]

/-- The normalized inner-product multiplicity of `θ` in `Res^G_H χ`.

For irreducible characters this is the usual constituent multiplicity.  It is
kept as a complex scalar here because the integral/nonnegative-integer
multiplicity theorem is part of the later Clifford proof core. -/
def restrictionMultiplicity (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) : ℂ :=
  inner (restrict H χ) θ

@[simp] theorem restrictionMultiplicity_def
    (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H χ θ = inner (restrict H χ) θ :=
  rfl

@[simp] theorem restrictionMultiplicity_zero_left (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H (0 : ClassFunction G ℂ) θ = 0 := by
  simp [restrictionMultiplicity]

@[simp] theorem restrictionMultiplicity_zero_right (χ : ClassFunction G ℂ) :
    restrictionMultiplicity H χ (0 : ClassFunction H ℂ) = 0 := by
  simp [restrictionMultiplicity]

theorem restrictionMultiplicity_add_left
    (χ₁ χ₂ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H (χ₁ + χ₂) θ =
      restrictionMultiplicity H χ₁ θ + restrictionMultiplicity H χ₂ θ := by
  rw [restrictionMultiplicity, restrict_add]
  exact inner_add_left (restrict H χ₁) (restrict H χ₂) θ

theorem restrictionMultiplicity_neg_left
    (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H (-χ) θ = -restrictionMultiplicity H χ θ := by
  rw [restrictionMultiplicity, restrict_neg]
  exact inner_neg_left (restrict H χ) θ

theorem restrictionMultiplicity_sub_left
    (χ₁ χ₂ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H (χ₁ - χ₂) θ =
      restrictionMultiplicity H χ₁ θ - restrictionMultiplicity H χ₂ θ := by
  rw [restrictionMultiplicity, restrict_sub]
  exact inner_sub_left (restrict H χ₁) (restrict H χ₂) θ

theorem restrictionMultiplicity_smul_left
    (c : ℂ) (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H (c • χ) θ = c * restrictionMultiplicity H χ θ := by
  rw [restrictionMultiplicity, restrict_smul]
  exact inner_smul_left c (restrict H χ) θ

theorem restrictionMultiplicity_add_right
    (χ : ClassFunction G ℂ) (θ₁ θ₂ : ClassFunction H ℂ) :
    restrictionMultiplicity H χ (θ₁ + θ₂) =
      restrictionMultiplicity H χ θ₁ + restrictionMultiplicity H χ θ₂ :=
  inner_add_right (restrict H χ) θ₁ θ₂

theorem restrictionMultiplicity_neg_right
    (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H χ (-θ) = -restrictionMultiplicity H χ θ :=
  inner_neg_right (restrict H χ) θ

theorem restrictionMultiplicity_sub_right
    (χ : ClassFunction G ℂ) (θ₁ θ₂ : ClassFunction H ℂ) :
    restrictionMultiplicity H χ (θ₁ - θ₂) =
      restrictionMultiplicity H χ θ₁ - restrictionMultiplicity H χ θ₂ :=
  inner_sub_right (restrict H χ) θ₁ θ₂

theorem restrictionMultiplicity_conjBy_right [H.Normal]
    (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) (g : G) :
    restrictionMultiplicity H χ (conjBy (G := G) (H := H) g θ) =
      restrictionMultiplicity H χ θ := by
  change inner (restrict H χ) (conjBy (G := G) (H := H) g θ) =
    inner (restrict H χ) θ
  calc
    inner (restrict H χ) (conjBy (G := G) (H := H) g θ) =
        inner (conjBy (G := G) (H := H) g (restrict H χ))
          (conjBy (G := G) (H := H) g θ) := by
          rw [conjBy_restrict (G := G) (H := H) g χ]
    _ = inner (restrict H χ) θ :=
        inner_conjBy_conjBy (G := G) (H := H) g (restrict H χ) θ

/-- `θ` is an irreducible constituent of the restriction `Res^G_H χ`, expressed
by nonzero normalized inner product. -/
def IsRestrictionConstituent (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) :
    Prop :=
  IsIrreducibleCharacter θ ∧ restrictionMultiplicity H χ θ ≠ 0

theorem IsRestrictionConstituent.isIrreducible
    {χ : ClassFunction G ℂ} {θ : ClassFunction H ℂ}
    (hθ : IsRestrictionConstituent H χ θ) : IsIrreducibleCharacter θ :=
  hθ.1

theorem IsRestrictionConstituent.multiplicity_ne_zero
    {χ : ClassFunction G ℂ} {θ : ClassFunction H ℂ}
    (hθ : IsRestrictionConstituent H χ θ) : restrictionMultiplicity H χ θ ≠ 0 :=
  hθ.2

omit [Fintype H] [Invertible (Nat.card H : ℂ)] in
theorem IsIrreducibleCharacter.conjBy [H.Normal]
    {θ : ClassFunction H ℂ} (hθ : IsIrreducibleCharacter θ) (g : G) :
    IsIrreducibleCharacter (conjBy (G := G) (H := H) g θ) := by
  rcases hθ with ⟨V, hVAdd, hVModule, hVFinite, ρ, hρ, hchar⟩
  letI : AddCommGroup V := hVAdd
  letI : Module ℂ V := hVModule
  letI : FiniteDimensional ℂ V := hVFinite
  let ρg : Representation ℂ H V :=
    ρ.comp (conjByMulEquiv (G := G) (H := H) g).toMonoidHom
  refine ⟨V, inferInstance, inferInstance, inferInstance, ρg, ?_, ?_⟩
  · exact Representation.IsIrreducible.comp_mulEquiv ρ
      (conjByMulEquiv (G := G) (H := H) g)
  · funext h
    change θ (conjByMulEquiv (G := G) (H := H) g h) = ρg.character h
    rw [hchar]
    rfl

theorem IsRestrictionConstituent.conjBy [H.Normal]
    {χ : ClassFunction G ℂ} {θ : ClassFunction H ℂ}
    (hθ : IsRestrictionConstituent H χ θ) (g : G) :
    IsRestrictionConstituent H χ (conjBy (G := G) (H := H) g θ) := by
  constructor
  · exact IsIrreducibleCharacter.conjBy (H := H) hθ.isIrreducible g
  · rw [restrictionMultiplicity_conjBy_right (H := H) χ θ g]
    exact hθ.multiplicity_ne_zero

end ClassFunction

namespace IrreducibleCharacter

variable (H : Subgroup G) [Fintype H] [Invertible (Nat.card H : ℂ)]

/-- An irreducible character `χ` of `G` **lies over** an irreducible character
`θ` of `H` if `θ` occurs in `Res^G_H χ` with nonzero multiplicity. -/
def LiesOver (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter H) : Prop :=
  ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
      (θ : ClassFunction H ℂ) ≠ 0

theorem liesOver_iff (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter H) :
    LiesOver H χ θ ↔
      ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
          (θ : ClassFunction H ℂ) ≠ 0 :=
  Iff.rfl

theorem liesOver_restrictionConstituent
    {χ : IrreducibleCharacter G} {θ : IrreducibleCharacter H}
    (hθ : LiesOver H χ θ) :
    ClassFunction.IsRestrictionConstituent H (χ : ClassFunction G ℂ)
      (θ : ClassFunction H ℂ) :=
  ⟨θ.isIrreducible, hθ⟩

theorem liesOver_iff_restrictionConstituent
    (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter H) :
    LiesOver H χ θ ↔
      ClassFunction.IsRestrictionConstituent H (χ : ClassFunction G ℂ)
        (θ : ClassFunction H ℂ) := by
  constructor
  · exact liesOver_restrictionConstituent (H := H)
  · intro hθ
    exact hθ.multiplicity_ne_zero

end IrreducibleCharacter

variable {H : Subgroup G} [hH : H.Normal]

namespace IrreducibleCharacter

variable [Fintype H] [Invertible (Nat.card H : ℂ)]

/-- Predicate form of the Clifford conclusion that all irreducible constituents
of `Res^G_H χ` lie in one `G`-conjugation orbit. -/
def RestrictionConstituentsSingleOrbit (χ : IrreducibleCharacter G) : Prop :=
  ∀ θ η : IrreducibleCharacter H,
    LiesOver H χ θ → LiesOver H χ η →
      ∃ g : G, ClassFunction.conjBy g (θ : ClassFunction H ℂ) =
        (η : ClassFunction H ℂ)

/-- Predicate form of the Clifford conclusion that all constituents of
`Res^G_H χ` occur with a common normalized inner-product multiplicity. -/
def HasCommonRestrictionMultiplicity (χ : IrreducibleCharacter G) : Prop :=
  ∃ e : ℂ, ∀ θ : IrreducibleCharacter H, LiesOver H χ θ →
    ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
      (θ : ClassFunction H ℂ) = e

/-- The cyclic inertia-quotient hypothesis from Peterfalvi §3 (1.7):
`I_G(θ)/H` is cyclic. -/
def HasCyclicInertiaQuotient (θ : IrreducibleCharacter H) : Prop :=
  IsCyclic (ClassFunction.inertiaQuotient (G := G) (H := H)
    (θ : ClassFunction H ℂ))

theorem RestrictionConstituentsSingleOrbit.exists_conj
    {χ : IrreducibleCharacter G}
    (hχ : RestrictionConstituentsSingleOrbit (H := H) χ)
    {θ η : IrreducibleCharacter H}
    (hθ : LiesOver H χ θ) (hη : LiesOver H χ η) :
    ∃ g : G, ClassFunction.conjBy g (θ : ClassFunction H ℂ) =
      (η : ClassFunction H ℂ) :=
  hχ θ η hθ hη

omit hH in
theorem HasCommonRestrictionMultiplicity.eq_of_liesOver
    {χ : IrreducibleCharacter G}
    (hχ : HasCommonRestrictionMultiplicity (H := H) χ)
    {θ η : IrreducibleCharacter H}
    (hθ : LiesOver H χ θ) (hη : LiesOver H χ η) :
    ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
        (θ : ClassFunction H ℂ) =
      ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
        (η : ClassFunction H ℂ) := by
  rcases hχ with ⟨e, he⟩
  rw [he θ hθ, he η hη]

end IrreducibleCharacter

/-- **Clifford's theorem** ([Is] Thm 6.5): for `H ⊴ G` and `χ ∈ Irr G`, the restriction
`Res_H^G χ` decomposes as a positive multiple of a `G`-orbit sum of irreducible characters
of `H`.

The data `(t, e, θ)` provided by the conclusion:
* `t ≥ 1` — the orbit size `[G : I_G(θ_0)]`;
* `e ≥ 1` — the common multiplicity `⟨Res χ, θ_i⟩_H`;
* `θ : Fin t → ClassFunction ↥H ℂ` — an enumeration of the `G`-orbit of the irreducible
  components, with each `θ i` an irreducible character and pairwise distinct.

(Proof deferred: requires `InducedCharacter` + `SecondOrthogonality` machinery.) -/
theorem clifford_decomposition
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) :
    ∃ (t : ℕ) (h_pos : 0 < t) (e : ℕ) (_ : 0 < e) (θ : Fin t → ClassFunction ↥H ℂ),
      Function.Injective θ ∧
      (∀ i, IsIrreducibleCharacter (θ i)) ∧
      (∀ i, ∃ g : G, ClassFunction.conjBy g (θ ⟨0, h_pos⟩) = θ i) ∧
      ClassFunction.restrict H χ = (e : ℂ) • (∑ i : Fin t, θ i) := by
  sorry

/-- A corollary of the Clifford / inertia setup: the inertia subgroup of any class
function on `H` contains `H` itself. Immediate from `ClassFunction.subgroup_le_inertia`. -/
theorem clifford_orbit_subset_inertia (θ : ClassFunction ↥H ℂ) :
    H ≤ ClassFunction.inertia θ :=
  ClassFunction.subgroup_le_inertia θ

end OddOrder.RepresentationTheory
