/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.GeneratedAction
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The standard Borel subgroup of the projective unitary permutation group

The standard Borel subgroup is the image of the faithful semidirect-product
representation

`RootGroup n semidirect[psuTorusScaleHom n] PSUTorusParameter n -> standardPermGroup n`,

whose element `(u,c)` acts as the root-times-torus product `R(u) T(c)`.
The torus is the determinant-one projective torus, rather than the larger full
diagonal parameter group. The torus-root conjugation formula proves the
homomorphism law. Evaluating at the affine origin recovers `u`, after which
torus faithfulness recovers `c`; this gives the unique normal form and exact
subgroup order.

This supplies standard unitary-group structure used in **Peterfalvi, Part II,
Chapter I §3, Lemma 1** (pp. 100-107).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

variable {n : ℕ}

section /- Part II, Chapter I §3, Lemma 1: the standard PSU Borel -/

/-- The abstract root-torus semidirect product underlying the standard
projective unitary Borel subgroup. -/
abbrev BorelModel (n : ℕ) :=
  RootGroup n ⋊[psuTorusScaleHom n] PSUTorusParameter n

/-- The root-torus semidirect product represented inside the standard unitary
permutation group, in root-times-torus order. -/
noncomputable def borelHom (n : ℕ) : BorelModel n →* standardPermGroup n :=
  SemidirectProduct.lift (rootHom n) (psuTorusHom n) fun c => by
    apply MonoidHom.ext
    intro u
    change rootHom n (psuTorusScaleHom n c u) =
      psuTorusHom n c * rootHom n u * (psuTorusHom n c)⁻¹
    exact (psuTorusHom_mul_rootHom_mul_inv c u).symm

@[simp] theorem borelHom_apply (x : BorelModel n) :
    borelHom n x = rootHom n x.left * psuTorusHom n x.right :=
  rfl

/-- A Borel element sends the affine origin to the affine point indexed by its
root coordinate. -/
@[simp] theorem borelHom_smul_origin (x : BorelModel n) :
    borelHom n x • Unital.origin n = Unital.affine x.left := by
  rw [borelHom_apply, mul_smul, Unital.origin,
    psuTorusHom_smul_affine, map_one, rootHom_smul_affine, mul_one]

/-- Every element of the abstract Borel model fixes infinity. -/
@[simp] theorem borelHom_smul_infinity (x : BorelModel n) :
    borelHom n x • Unital.infinity n = Unital.infinity n := by
  rw [borelHom_apply, mul_smul,
    psuTorusHom_smul_infinity, rootHom_smul_infinity]

/-- The root-times-determinant-one-torus representation is faithful. -/
theorem borelHom_injective (n : ℕ) : Function.Injective (borelHom n) := by
  intro x y hxy
  have horigin := congrArg
    (fun g : standardPermGroup n => g • Unital.origin n) hxy
  have hleft : x.left = y.left := by
    have haffine : Unital.affine x.left = Unital.affine y.left := by
      simpa only [borelHom_smul_origin] using horigin
    exact Option.some.inj haffine
  apply SemidirectProduct.ext
  · exact hleft
  · apply psuTorusHom_injective n
    have hprod :
        rootHom n x.left * psuTorusHom n x.right =
          rootHom n y.left * psuTorusHom n y.right := by
      simpa only [borelHom_apply] using hxy
    rw [hleft] at hprod
    exact mul_left_cancel hprod

/-- The standard projective unitary Borel subgroup, defined as the range of
the faithful root-torus semidirect representation. -/
noncomputable def standardBorel (n : ℕ) : Subgroup (standardPermGroup n) :=
  (borelHom n).range

/-- Every standard root element belongs to the standard Borel subgroup. -/
theorem rootHom_mem_standardBorel (u : RootGroup n) :
    rootHom n u ∈ standardBorel n :=
  ⟨SemidirectProduct.inl u, SemidirectProduct.lift_inl _ _ _ _⟩

/-- Every determinant-one torus element belongs to the standard Borel
subgroup. -/
theorem psuTorusHom_mem_standardBorel (c : PSUTorusParameter n) :
    psuTorusHom n c ∈ standardBorel n :=
  ⟨SemidirectProduct.inr c, SemidirectProduct.lift_inr _ _ _ _⟩

/-- Membership in the standard Borel subgroup is equivalent to a unique
root-times-determinant-one-torus normal form. -/
theorem mem_standardBorel_iff_existsUnique_root_torus
    (g : standardPermGroup n) :
    g ∈ standardBorel n ↔
      ∃! p : RootGroup n × PSUTorusParameter n,
        g = rootHom n p.1 * psuTorusHom n p.2 := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x.left, x.right), rfl, ?_⟩
    intro p hp
    have hx : x = (⟨p.1, p.2⟩ : BorelModel n) := by
      apply borelHom_injective n
      exact hp
    exact Prod.ext (congrArg SemidirectProduct.left hx).symm
      (congrArg SemidirectProduct.right hx).symm
  · rintro ⟨p, hp, _⟩
    refine ⟨(⟨p.1, p.2⟩ : BorelModel n), ?_⟩
    exact hp.symm

/-- Every standard Borel element fixes the point at infinity. The reverse
inclusion is a consequence of the later Bruhat decomposition. -/
theorem standardBorel_le_infinityStabilizer :
    standardBorel n ≤
      MulAction.stabilizer (standardPermGroup n) (Unital.infinity n) := by
  rintro _ ⟨x, rfl⟩
  rw [MulAction.mem_stabilizer_iff]
  exact borelHom_smul_infinity x

/-- **Peterfalvi Part II, Chapter I §3, Lemma 1 (unitary target).** The exact
order of the standard Borel subgroup is
`q³ * ((q² - 1) / gcd(q + 1, 3))`, where `q = 2^n`. -/
theorem natCard_standardBorel (n : ℕ) (hn : 0 < n) :
    Nat.card (standardBorel n) =
      2 ^ (3 * n) *
        ((2 ^ (2 * n) - 1) / (2 ^ n + 1).gcd 3) := by
  trans Nat.card (BorelModel n)
  · rw [standardBorel]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (borelHom_injective n)).toEquiv).symm
  · rw [SemidirectProduct.card, RootGroup.natCard n hn,
      natCard_psuTorus_standard n hn]

end

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
