/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_NormSet
import OddOrder.Peterfalvi.S15_SAndT

/-!
# Peterfalvi Section 16: Non-existence of G

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 16, pp. 87--92.

This is the final character-theoretic section of Peterfalvi's proof.  It
continues the `S,T` setup of Section 15, adds the standing inequality `q < p`,
and derives the field-normalizer configuration stated in Peterfalvi (14.2).
Together with Bender--Glauberman Appendix C, that configuration forces
`p <= q`, contradicting the section hypothesis.

The file is a scaffold for (14.1)--(14.16).  The substantial Dade-isometry,
orthogonality, and numerical arguments are exposed as named theorem statements
and proposition fields, so the final integration point with BG Appendix C is
already explicit.
-/

namespace OddOrder.Peterfalvi.S16
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

/-! ## (14.1)--(14.2): section hypothesis and final target -/

/-- **Peterfalvi (14.1)**: Section 16 continues Hypothesis (13.1) and assumes
`q < p`. -/
structure Hypothesis where
  base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)
  q_lt_p : base.q < base.p

namespace Hypothesis

/-- Under **Peterfalvi (14.1)**, the two prime parameters are distinct. -/
theorem p_ne_q (hyp : Hypothesis (G := G)) : hyp.base.p ≠ hyp.base.q := by
  exact ne_of_gt hyp.q_lt_p

/-- Under **Peterfalvi (14.1)**, the larger prime parameter is at least `5`. -/
theorem five_le_p (hyp : Hypothesis (G := G)) : 5 ≤ hyp.base.p := by
  have hp_gt_three : 3 < hyp.base.p := lt_of_le_of_lt hyp.base.three_le_q hyp.q_lt_p
  have hp_ne_four : hyp.base.p ≠ 4 := by
    intro hp4
    have hodd : Odd 4 := by simpa [hp4] using hyp.base.p_odd
    rcases hodd with ⟨k, hk⟩
    omega
  omega

/-- The congruence used in **Peterfalvi (14.4)**: from `q < p` and `q` prime,
`q` cannot be `1 mod p`. -/
theorem q_not_modEq_one_mod_p (hyp : Hypothesis (G := G)) :
    ¬ hyp.base.q ≡ 1 [MOD hyp.base.p] := by
  intro hmod
  have hp_gt_one : 1 < hyp.base.p := hyp.base.q_prime.one_lt.trans hyp.q_lt_p
  have hq_eq_one : hyp.base.q = 1 :=
    Nat.ModEq.eq_of_lt_of_lt hmod hyp.q_lt_p hp_gt_one
  exact hyp.base.q_prime.ne_one hq_eq_one

/-- The T-side cyclotomic quotient from **Peterfalvi (14.4)** is odd. -/
theorem tSide_cyclotomic_quotient_odd (hyp : Hypothesis (G := G)) :
    Odd ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)) :=
  OddOrder.Peterfalvi.S15.cyclotomic_quotient_odd
    hyp.base.q_prime hyp.base.q_odd hyp.base.p_odd

/-- The T-side cyclotomic quotient from **Peterfalvi (14.4)** is coprime to
`q - 1`. -/
theorem tSide_cyclotomic_quotient_coprime (hyp : Hypothesis (G := G)) :
    Nat.Coprime ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
      (hyp.base.q - 1) :=
  OddOrder.Peterfalvi.S15.cyclotomic_quotient_coprime_of_not_modEq_one
    hyp.base.q_prime hyp.base.p_prime hyp.q_not_modEq_one_mod_p

/-- Every positive divisor of the T-side cyclotomic quotient from
**Peterfalvi (14.4)** is `1 mod p`. -/
theorem tSide_cyclotomic_quotient_divisor_modEq_one (hyp : Hypothesis (G := G)) :
    ∀ x : ℕ, x ≠ 0 →
      x ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) →
        x ≡ 1 [MOD hyp.base.p] :=
  OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one
    hyp.base.q_prime hyp.base.p_prime hyp.q_not_modEq_one_mod_p

end Hypothesis

/-- The concrete norm relation produced by the generator-relation argument in
**BG Appendix C, Lemma C.3**, expressed at the Peterfalvi Section 16 interface.
For every `a` in the norm set `E`, the relation should give `N(2 * a - 1) = 1`;
BG then converts this finite-field statement into `a⁻¹ ∈ E`. -/
def appCNormSetGeneratorRelation (hyp : Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  ∀ a : GaloisField hyp.base.p hyp.base.q,
    a ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
      OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
        ((2 : GaloisField hyp.base.p hyp.base.q) * a - 1) = 1

/-- The field-element one-step twisted-inverse output of
**BG Appendix C, Lemma C.3, Step 4**, expressed at the Peterfalvi Section 16
interface.  This is closest to the line in BG proving `(a⁻¹)^{t^3} ∈ E` for
`a ∈ E`; the unit-group formulation used for the final odd iteration is derived
from this. -/
def appCNormSetTwistedFieldStep (hyp : Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  ∃ φ : MulAut (GaloisField hyp.base.p hyp.base.q)ˣ,
    φ ^ hyp.base.p = 1 ∧
      OddOrder.BG.AppC.NormSet.normSetETwistedFieldStep
        (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos φ

/-- The one-step twisted-inverse output of **BG Appendix C, Lemma C.3, Step 4**,
expressed at the Peterfalvi Section 16 interface.  This is closer to the group
calculation in BG: for a field automorphism of `p`-power order, every
`u ∈ E` is sent to `φ(u⁻¹) ∈ E`. -/
def appCNormSetTwistedUnitStep (hyp : Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  ∃ φ : MulAut (GaloisField hyp.base.p hyp.base.q)ˣ,
    φ ^ hyp.base.p = 1 ∧
      ∀ u : (GaloisField hyp.base.p hyp.base.q)ˣ,
        ((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) ∈
          OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
          ((OddOrder.BG.AppC.NormSet.twistedInv φ u :
              (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) ∈
            OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q

/-- The same one-step output, narrowed to the concrete norm-one unit group `U`.
This matches the actual BG Step 4 action by conjugation with `t`; no extension to
all of `𝔽_{p^q}ˣ` is required. -/
def appCNormSetTwistedNormOneStep (hyp : Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  ∃ φ : MulAut (OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q),
    φ ^ hyp.base.p = 1 ∧
      OddOrder.BG.AppC.NormSet.normSetETwistedNormOneStep
        (p := hyp.base.p) (q := hyp.base.q) φ

/-- The field-element Step 4 output implies the unit-group Step 4 output used by
BG's final odd-iterate argument. -/
theorem appCNormSetTwistedUnitStep_of_field_step
    (hyp : Hypothesis (G := G)) :
    appCNormSetTwistedFieldStep hyp → appCNormSetTwistedUnitStep hyp := by
  intro htwist
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rcases htwist with ⟨φ, hφp, hstep⟩
  exact ⟨φ, hφp,
    OddOrder.BG.AppC.NormSet.twisted_unit_step_of_twisted_field_step
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos φ hstep⟩

/-- The BG Step 4 twisted-inverse output implies the norm relation currently
consumed by `FieldNormalizerData`.  This keeps the S16 producer obligation close
to the group-theoretic calculation while preserving the downstream AppC
interface. -/
theorem appCNormSetGeneratorRelation_of_twisted_unit_step
    (hyp : Hypothesis (G := G)) :
    appCNormSetTwistedUnitStep hyp → appCNormSetGeneratorRelation hyp := by
  intro htwist
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rcases htwist with ⟨φ, hφp, hstep⟩
  exact OddOrder.BG.AppC.NormSet.forall_normN_two_mul_sub_one_of_twisted_unit_step
    (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos hyp.base.p_odd φ hφp hstep

/-- The norm-one Step 4 output implies the norm relation consumed by AppC. -/
theorem appCNormSetGeneratorRelation_of_twisted_normOne_step
    (hyp : Hypothesis (G := G)) :
    appCNormSetTwistedNormOneStep hyp → appCNormSetGeneratorRelation hyp := by
  intro htwist
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rcases htwist with ⟨φ, hφp, hstep⟩
  exact OddOrder.BG.AppC.NormSet.forall_normN_two_mul_sub_one_of_twisted_normOne_step
    (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos hyp.base.p_odd φ hφp hstep

/-- The concrete Frobenius group `H = P \rtimes U` from BG Appendix C,
with Peterfalvi Section 16 parameters. -/
abbrev fieldNormalizerFrobeniusGroup (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup hyp.base.p hyp.base.q

/-- The additive kernel `P ≤ H` in the concrete BG Frobenius group. -/
noncomputable def fieldNormalizerKernel (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp).range

/-- The prime-field additive line `P₀ ≤ P` inside the concrete BG Frobenius
group, generated by `1 : F_{p^q}`. -/
noncomputable def fieldNormalizerPrimeLine (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneFrobeniusSubspaceKernel hyp.base.p hyp.base.q
    (Submodule.span (ZMod hyp.base.p)
      ({(1 : GaloisField hyp.base.p hyp.base.q)} :
        Set (GaloisField hyp.base.p hyp.base.q)))

/-- The norm-one complement `U ≤ H` inside the concrete BG Frobenius group. -/
noncomputable def fieldNormalizerComplement (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  (SemidirectProduct.inr :
      OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp).range

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and the
norm-one complement meet trivially. -/
theorem fieldNormalizerKernel_inf_complement_eq_bot (hyp : Hypothesis (G := G)) :
    fieldNormalizerKernel hyp ⊓ fieldNormalizerComplement hyp = ⊥ := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  apply le_antisymm ?_ bot_le
  intro x hx
  rcases hx.1 with ⟨p, rfl⟩
  rcases hx.2 with ⟨u, hu⟩
  have hp : p = 1 := by
    have hleft := congrArg
      (fun g : fieldNormalizerFrobeniusGroup hyp => g.left) hu
    simpa using hleft.symm
  subst p
  simp

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and
norm-one complement generate the whole group. -/
theorem fieldNormalizerKernel_sup_complement_eq_top (hyp : Hypothesis (G := G)) :
    fieldNormalizerKernel hyp ⊔ fieldNormalizerComplement hyp = ⊤ := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  apply le_antisymm le_top
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact Subgroup.mul_mem_sup ⟨g.left, rfl⟩ ⟨g.right, rfl⟩

/-- The concrete norm-one unit group used as the BG complement before transport
through the field-normalizer embedding. -/
abbrev fieldNormalizerNormOneUnits (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q

/-- The concrete norm-one complement has more than one element.  This is the
lightweight cardinality input needed to turn BG Appendix C, Lemma C.3 Step 2
into the assertion that the prime line `P₀` cannot normalize `U`, without
importing the class-sum file. -/
theorem fieldNormalizerNormOneUnits_card_gt_one (hyp : Hypothesis (G := G)) :
    1 < Nat.card (fieldNormalizerNormOneUnits hyp) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
  have hq0 : hyp.base.q ≠ 0 := hyp.base.q_prime.ne_zero
  have hq2 : 2 ≤ hyp.base.q := by
    have hq3 : 3 ≤ hyp.base.q := hyp.base.three_le_q
    omega
  rw [OddOrder.BG.AppC.NormSet.normOneUnits_card hyp.base.p hyp.base.q hq0,
    ← Nat.geomSum_eq hp2 hyp.base.q]
  have hrange : Finset.range 2 ⊆ Finset.range hyp.base.q := by
    intro k hk
    exact Finset.mem_range.mpr (by
      have hk2 : k < 2 := Finset.mem_range.mp hk
      exact Nat.lt_of_lt_of_le hk2 hq2)
  have hle :
      (∑ k ∈ Finset.range 2, hyp.base.p ^ k) ≤
        ∑ k ∈ Finset.range hyp.base.q, hyp.base.p ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange
      (fun _ _ _ => zero_le _)
  have htwo : 1 < (∑ k ∈ Finset.range 2, hyp.base.p ^ k) := by
    simp
    omega
  exact htwo.trans_le hle

/-- There is a nonidentity norm-one unit in the concrete complement. -/
theorem exists_fieldNormalizerNormOneUnit_ne_one (hyp : Hypothesis (G := G)) :
    ∃ u : fieldNormalizerNormOneUnits hyp, u ≠ 1 := by
  haveI : Nontrivial (fieldNormalizerNormOneUnits hyp) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (fieldNormalizerNormOneUnits_card_gt_one hyp)
  exact exists_ne 1

/-- The distinguished nonidentity element of the prime-field line `P₀`,
corresponding to `1 : F_{p^q}` in BG Appendix C. -/
noncomputable def fieldNormalizerPrimeLineGenerator (hyp : Hypothesis (G := G)) :
    fieldNormalizerFrobeniusGroup hyp :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  SemidirectProduct.inl
    (Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q))

/-- The element of the concrete prime-field line corresponding to a scalar
`c : ZMod p`. -/
noncomputable def fieldNormalizerPrimeLineElement (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) : fieldNormalizerFrobeniusGroup hyp :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  SemidirectProduct.inl
    (Multiplicative.ofAdd
      (algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c))

/-- Prime-line scalar elements lie in the concrete subgroup `P₀`. -/
theorem fieldNormalizerPrimeLineElement_mem (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) :
    fieldNormalizerPrimeLineElement hyp c ∈ fieldNormalizerPrimeLine hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [fieldNormalizerPrimeLineElement, fieldNormalizerPrimeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  have h1 : (1 : GaloisField hyp.base.p hyp.base.q) ∈
      Submodule.span (ZMod hyp.base.p)
        ({(1 : GaloisField hyp.base.p hyp.base.q)} :
          Set (GaloisField hyp.base.p hyp.base.q)) :=
    Submodule.subset_span (by simp)
  simpa [Algebra.smul_def] using
    (Submodule.smul_mem
      (Submodule.span (ZMod hyp.base.p)
        ({(1 : GaloisField hyp.base.p hyp.base.q)} :
          Set (GaloisField hyp.base.p hyp.base.q))) c h1)

/-- The scalar `1` element is the distinguished prime-line generator. -/
theorem fieldNormalizerPrimeLineElement_one (hyp : Hypothesis (G := G)) :
    fieldNormalizerPrimeLineElement hyp 1 = fieldNormalizerPrimeLineGenerator hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerPrimeLineElement, fieldNormalizerPrimeLineGenerator]

/-- Prime-line scalar elements invert by negating the scalar. -/
theorem fieldNormalizerPrimeLineElement_neg (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) :
    fieldNormalizerPrimeLineElement hyp (-c) =
      (fieldNormalizerPrimeLineElement hyp c)⁻¹ := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerPrimeLineElement]

/-- The distinguished generator lies in the concrete prime-field line `P₀`. -/
theorem fieldNormalizerPrimeLineGenerator_mem (hyp : Hypothesis (G := G)) :
    fieldNormalizerPrimeLineGenerator hyp ∈ fieldNormalizerPrimeLine hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [fieldNormalizerPrimeLineGenerator, fieldNormalizerPrimeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  exact Submodule.subset_span (by simp)

/-- The distinguished generator of `P₀` is nontrivial. -/
theorem fieldNormalizerPrimeLineGenerator_ne_one (hyp : Hypothesis (G := G)) :
    fieldNormalizerPrimeLineGenerator hyp ≠ 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro h
  have hfield : (1 : GaloisField hyp.base.p hyp.base.q) = 0 :=
    ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h)
  exact one_ne_zero hfield

/-- The distinguished generator of `P₀` has order dividing `p`. -/
theorem fieldNormalizerPrimeLineGenerator_pow_p (hyp : Hypothesis (G := G)) :
    (fieldNormalizerPrimeLineGenerator hyp) ^ hyp.base.p = 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : CharP (GaloisField hyp.base.p hyp.base.q) hyp.base.p := by
    rw [← Algebra.charP_iff (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q)
      hyp.base.p]
    exact ZMod.charP hyp.base.p
  dsimp [fieldNormalizerPrimeLineGenerator]
  let inlHom :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inl
  rw [← map_pow inlHom, ← map_one inlHom, SemidirectProduct.inl_inj]
  rw [← ofAdd_nsmul]
  congr
  simp

/-- The additive kernel of the concrete BG Frobenius group, with the local
`Fact p.Prime` bundled into the abbreviation. -/
abbrev fieldNormalizerAdditiveGroup (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q

/-- The concrete `p`-power Frobenius on the additive kernel of BG's model
`P ⋊ U`, written multiplicatively via `Multiplicative`. -/
noncomputable def fieldNormalizerAdditiveFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerAdditiveGroup hyp →* fieldNormalizerAdditiveGroup hyp where
  toFun x := Multiplicative.ofAdd (x.toAdd ^ hyp.base.p)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp [hyp.base.p_prime.ne_zero]
  map_mul' x y := by
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    apply Multiplicative.toAdd.injective
    exact (OddOrder.BG.AppC.NormSet.add_pow_p
      hyp.base.p hyp.base.q x.toAdd y.toAdd).symm

/-- The concrete `p`-power Frobenius on the norm-one complement. -/
noncomputable def fieldNormalizerNormOneFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerNormOneUnits hyp →* fieldNormalizerNormOneUnits hyp where
  toFun u := u ^ hyp.base.p
  map_one' := by simp
  map_mul' u v := by
    rw [mul_pow]

/-- The concrete `p`-power Frobenius of BG's semidirect product
`P ⋊ U`: it sends `(x,u)` to `(x^p,u^p)`. -/
noncomputable def fieldNormalizerFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerFrobeniusGroup hyp :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  SemidirectProduct.map
    (fieldNormalizerAdditiveFrobeniusHom (G := G) hyp)
    (fieldNormalizerNormOneFrobeniusHom (G := G) hyp)
    (by
      intro u
      ext x
      apply Multiplicative.toAdd.injective
      change (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) * x) ^ hyp.base.p =
            (((u ^ hyp.base.p : fieldNormalizerNormOneUnits hyp) :
                  (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * x ^ hyp.base.p
      simpa [map_pow] using
        (mul_pow (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q)) x hyp.base.p))

@[simp]
theorem fieldNormalizerFrobeniusHom_inl (hyp : Hypothesis (G := G))
    (x : fieldNormalizerAdditiveGroup hyp) :
    fieldNormalizerFrobeniusHom hyp (SemidirectProduct.inl x) =
      SemidirectProduct.inl (Multiplicative.ofAdd (x.toAdd ^ hyp.base.p)) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerFrobeniusHom, fieldNormalizerAdditiveFrobeniusHom]

@[simp]
theorem fieldNormalizerFrobeniusHom_inr (hyp : Hypothesis (G := G))
    (u : fieldNormalizerNormOneUnits hyp) :
    fieldNormalizerFrobeniusHom hyp
        (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) =
      SemidirectProduct.inr (u ^ hyp.base.p) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerFrobeniusHom, fieldNormalizerNormOneFrobeniusHom]

/-- The concrete Frobenius fixes the prime-field line pointwise. -/
theorem fieldNormalizerFrobeniusHom_primeLineElement (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) :
    fieldNormalizerFrobeniusHom hyp (fieldNormalizerPrimeLineElement hyp c) =
      fieldNormalizerPrimeLineElement hyp c := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rw [fieldNormalizerPrimeLineElement, fieldNormalizerFrobeniusHom_inl,
    SemidirectProduct.inl_inj]
  change (algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c) ^
      hyp.base.p = algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c
  rw [← map_pow, ZMod.pow_card]

/-- The concrete Frobenius fixes the distinguished prime-line generator. -/
theorem fieldNormalizerFrobeniusHom_primeLineGenerator (hyp : Hypothesis (G := G)) :
    fieldNormalizerFrobeniusHom hyp (fieldNormalizerPrimeLineGenerator hyp) =
      fieldNormalizerPrimeLineGenerator hyp := by
  simpa [fieldNormalizerPrimeLineElement_one] using
    fieldNormalizerFrobeniusHom_primeLineElement (G := G) hyp 1

/-- The concrete Frobenius fixes every integer power of the distinguished
prime-line generator. -/
theorem fieldNormalizerFrobeniusHom_primeLineGenerator_zpow
    (hyp : Hypothesis (G := G)) (n : ℤ) :
    fieldNormalizerFrobeniusHom hyp ((fieldNormalizerPrimeLineGenerator hyp) ^ n) =
      (fieldNormalizerPrimeLineGenerator hyp) ^ n := by
  rw [map_zpow, fieldNormalizerFrobeniusHom_primeLineGenerator]

/-- The two conclusions of **Peterfalvi (14.2)**, packaged in the form consumed
by BG Appendix C.  The finite-field model is now carried as a concrete
monomorphism from BG's Frobenius group `H = P \rtimes U` into `G`, together with
its image identifications. -/
structure FieldNormalizerData (hyp : Hypothesis (G := G)) where
  sigma : fieldNormalizerFrobeniusGroup hyp →* G
  sigma_injective : Function.Injective sigma
  sigma_P_eq_P : (fieldNormalizerKernel hyp).map sigma = hyp.base.P
  sigma_P0_eq_W2 : (fieldNormalizerPrimeLine hyp).map sigma = hyp.base.W2
  sigma_U_eq_U : (fieldNormalizerComplement hyp).map sigma = hyp.base.U
  cyclotomic_coprime :
    Nat.Coprime
      ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
      (hyp.base.p - 1)
  Q_elementaryAbelian : IsElementaryAbelian hyp.base.q ↥hyp.base.Q
  W2_normalizes_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G)
  y : G
  y_mem_Q : y ∈ hyp.base.Q
  W2_conj_y_normalizes_U :
    MulAut.conj y • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)
  appC_twisted_normOne_step : appCNormSetTwistedNormOneStep hyp

namespace FieldNormalizerData

/-- The BG element `s ∈ P₀#`, transported to `G` through the concrete
field-normalizer monomorphism. -/
noncomputable def s {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) : G :=
  data.sigma (fieldNormalizerPrimeLineGenerator hyp)

/-- The transported element `s` lies in Peterfalvi's subgroup `W₂ = σ(P₀)`. -/
theorem s_mem_W2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ∈ hyp.base.W2 := by
  rw [← data.sigma_P0_eq_W2]
  exact ⟨fieldNormalizerPrimeLineGenerator hyp,
    fieldNormalizerPrimeLineGenerator_mem hyp, rfl⟩

/-- The transported element `s` lies in the transported additive kernel `P`. -/
theorem s_mem_P {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ∈ hyp.base.P := by
  rw [← data.sigma_P_eq_P]
  refine ⟨fieldNormalizerPrimeLineGenerator hyp, ?_, rfl⟩
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [fieldNormalizerPrimeLineGenerator, fieldNormalizerKernel]
  exact ⟨Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q), rfl⟩

/-- Integer powers of `s` remain in `P`. -/
theorem s_zpow_mem_P {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℤ) :
    data.s ^ n ∈ hyp.base.P :=
  hyp.base.P.zpow_mem data.s_mem_P n

/-- Integer powers of `s` lie in `PU`. -/
theorem s_zpow_mem_P_sup_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℤ) :
    data.s ^ n ∈ hyp.base.P ⊔ hyp.base.U :=
  (le_sup_left : hyp.base.P ≤ hyp.base.P ⊔ hyp.base.U) (data.s_zpow_mem_P n)

/-- The `s^{-2}` factor in BG C.3 Step 4 is the `-2` point of the concrete
prime-field line after transport by `σ`. -/
theorem s_zpow_neg_two_eq_primeLineElement_neg_two
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ^ (-2 : ℤ) =
      data.sigma (fieldNormalizerPrimeLineElement hyp (-2 : ZMod hyp.base.p)) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [s, fieldNormalizerPrimeLineElement, fieldNormalizerPrimeLineGenerator]
  let F := GaloisField hyp.base.p hyp.base.q
  let H := fieldNormalizerFrobeniusGroup hyp
  have hpow_two :
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) ^ 2 =
        SemidirectProduct.inl (Multiplicative.ofAdd (2 : F)) := by
    rw [pow_two, ← map_mul (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →* H)]
    congr
    apply Multiplicative.toAdd.injective
    change (1 : F) + 1 = 2
    ring
  have hneg_two :
      (algebraMap (ZMod hyp.base.p) F (-2 : ZMod hyp.base.p)) = -(2 : F) := by
    simp only [map_neg, map_ofNat]
  rw [← map_zpow]
  congr
  rw [zpow_neg, hneg_two]
  change ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) ^ 2)⁻¹ =
    SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))
  have hpow_two_inv := congrArg Inv.inv hpow_two
  exact hpow_two_inv.trans (by simp [F])

/-- The transported element `s` is nontrivial. -/
theorem s_ne_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ≠ 1 := by
  intro hs
  exact fieldNormalizerPrimeLineGenerator_ne_one hyp
    (data.sigma_injective (by simpa [s] using hs))

/-- The transported prime-line generator has `p`-th power equal to `1`. -/
theorem s_pow_p_eq_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ^ hyp.base.p = 1 := by
  simpa [s] using congrArg data.sigma (fieldNormalizerPrimeLineGenerator_pow_p hyp)

/-- The transported prime-line generator normalizes `Q`. -/
theorem s_normalizes_Q {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ∈ Subgroup.normalizer (hyp.base.Q : Set G) :=
  data.W2_normalizes_Q data.s_mem_W2

/-- The concrete norm-one complement transported through `σ` onto Peterfalvi's
subgroup `U`. -/
noncomputable def normOneUnitsToU {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : fieldNormalizerNormOneUnits hyp →* hyp.base.U :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  { toFun := fun u =>
      ⟨data.sigma (SemidirectProduct.inr u), by
        rw [← data.sigma_U_eq_U]
        exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩⟩
    map_one' := by
      ext
      simp
    map_mul' := by
      intro u v
      ext
      simp }

/-- The transported norm-one complement map is injective. -/
theorem normOneUnitsToU_injective {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : Function.Injective data.normOneUnitsToU := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro u v h
  have hsig : data.sigma (SemidirectProduct.inr u) = data.sigma (SemidirectProduct.inr v) :=
    congrArg Subtype.val h
  exact SemidirectProduct.inr_injective (data.sigma_injective hsig)

/-- The transported norm-one complement map is onto Peterfalvi's `U`. -/
theorem normOneUnitsToU_surjective {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : Function.Surjective data.normOneUnitsToU := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro u
  have hu : (u : G) ∈ (fieldNormalizerComplement hyp).map data.sigma := by
    rw [data.sigma_U_eq_U]
    exact u.property
  rcases hu with ⟨x, hxU, hx⟩
  rcases hxU with ⟨u0, rfl⟩
  refine ⟨u0, ?_⟩
  ext
  exact hx

/-- The concrete norm-one unit group is isomorphic to Peterfalvi's subgroup `U`
through the field-normalizer embedding. -/
noncomputable def normOneUnitsEquivU {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : fieldNormalizerNormOneUnits hyp ≃* hyp.base.U :=
  MulEquiv.ofBijective data.normOneUnitsToU
    ⟨data.normOneUnitsToU_injective, data.normOneUnitsToU_surjective⟩

/-- The transported additive kernel `P` and complement `U` meet trivially in
`G`.  This is the S16-facing form of the `U ∩ P = 1` input used when BG
Appendix C, Lemma C.3 Step 4 reads equations modulo `P`. -/
theorem P_inf_U_eq_bot {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.P ⊓ hyp.base.U = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxP : x ∈ (fieldNormalizerKernel hyp).map data.sigma := by
    rw [data.sigma_P_eq_P]
    exact hx.1
  have hxU : x ∈ (fieldNormalizerComplement hyp).map data.sigma := by
    rw [data.sigma_U_eq_U]
    exact hx.2
  rcases hxP with ⟨p, hpP, hp⟩
  rcases hxU with ⟨u, huU, hu⟩
  have hpu : p = u := data.sigma_injective (by
    rw [hp, hu])
  have hp_inter : p ∈ fieldNormalizerKernel hyp ⊓ fieldNormalizerComplement hyp := by
    exact ⟨hpP, by rwa [hpu]⟩
  have hp_one : p = 1 := by
    have hp_bot : p ∈ (⊥ : Subgroup (fieldNormalizerFrobeniusGroup hyp)) := by
      rw [← fieldNormalizerKernel_inf_complement_eq_bot hyp]
      exact hp_inter
    simpa [Subgroup.mem_bot] using hp_bot
  rw [Subgroup.mem_bot]
  rw [← hp, hp_one, map_one]

/-- The image of the concrete Frobenius group is the subgroup generated by the
transported additive kernel `P` and complement `U`. -/
theorem P_sup_U_eq_sigma_top {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.P ⊔ hyp.base.U =
      (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by
  calc
    hyp.base.P ⊔ hyp.base.U =
        (fieldNormalizerKernel hyp).map data.sigma ⊔
          (fieldNormalizerComplement hyp).map data.sigma := by
      rw [data.sigma_P_eq_P, data.sigma_U_eq_U]
    _ = (fieldNormalizerKernel hyp ⊔ fieldNormalizerComplement hyp).map data.sigma := by
      rw [Subgroup.map_sup]
    _ = (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by
      rw [fieldNormalizerKernel_sup_complement_eq_top hyp]

/-- BG Appendix C, Lemma C.3 Step 3 irreducibility bridge: any subgroup of
`PU` that contains `U` is either `U` or all of `PU`.  This transports the
concrete irreducibility theorem for `P⋊U` through `σ`. -/
theorem subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) {X : Subgroup G}
    (hUle : hyp.base.U ≤ X) (hXle : X ≤ hyp.base.P ⊔ hyp.base.U)
    (hne : X ≠ hyp.base.U) :
    X = hyp.base.P ⊔ hyp.base.U := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  let XH : Subgroup (fieldNormalizerFrobeniusGroup hyp) := X.comap data.sigma
  have hXrange : X ≤ data.sigma.range := by
    intro x hx
    have hxPU : x ∈ hyp.base.P ⊔ hyp.base.U := hXle hx
    rw [data.P_sup_U_eq_sigma_top] at hxPU
    simpa using hxPU
  have hUleH : fieldNormalizerComplement hyp ≤ XH := by
    intro g hg
    have hgU : data.sigma g ∈ hyp.base.U := by
      rw [← data.sigma_U_eq_U]
      exact ⟨g, hg, rfl⟩
    exact hUle hgU
  have hUleH' :
      (SemidirectProduct.inr : fieldNormalizerNormOneUnits hyp →*
        fieldNormalizerFrobeniusGroup hyp).range ≤ XH := by
    simpa [fieldNormalizerComplement] using hUleH
  have hneH : XH ≠ fieldNormalizerComplement hyp := by
    intro hXH
    apply hne
    have hmapX : XH.map data.sigma = X := Subgroup.map_comap_eq_self hXrange
    calc
      X = XH.map data.sigma := hmapX.symm
      _ = (fieldNormalizerComplement hyp).map data.sigma := by rw [hXH]
      _ = hyp.base.U := data.sigma_U_eq_U
  have htopH : XH = ⊤ :=
    OddOrder.BG.AppC.NormSet.normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime data.cyclotomic_coprime
      XH hUleH' (by simpa [fieldNormalizerComplement] using hneH)
  have hmapX : XH.map data.sigma = X := Subgroup.map_comap_eq_self hXrange
  calc
    X = XH.map data.sigma := hmapX.symm
    _ = (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by rw [htopH]
    _ = hyp.base.P ⊔ hyp.base.U := data.P_sup_U_eq_sigma_top.symm

/-- BG Appendix C, Lemma C.3 Step 1 inside the concrete `P⋊U`: every element is
`u s₁ v` with `u,v∈U` and `s₁∈P₀`. -/
theorem exists_normOne_primeLine_normOne {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (g : fieldNormalizerFrobeniusGroup hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u v : fieldNormalizerNormOneUnits hyp,
      g = (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simpa [fieldNormalizerPrimeLineElement] using
    OddOrder.BG.AppC.NormSet.normOneFrobenius_exists_inr_primeLine_inr
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime data.cyclotomic_coprime
      (s := (1 : GaloisField hyp.base.p hyp.base.q)) one_ne_zero g

/-- BG Appendix C, Lemma C.3 Step 1 transported to `G`: every element of `PU`
can be written as the `σ`-image of `u s₁ v`. -/
theorem exists_sigma_normOne_primeLine_normOne_of_mem_PU
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : G} (hx : x ∈ hyp.base.P ⊔ hyp.base.U) :
    ∃ c : ZMod hyp.base.p, ∃ u v : fieldNormalizerNormOneUnits hyp,
      x = data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp) := by
  have hxmap : x ∈ (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by
    rw [← data.P_sup_U_eq_sigma_top]
    exact hx
  rcases hxmap with ⟨g, _hg_top, hg⟩
  rcases data.exists_normOne_primeLine_normOne g with ⟨c, u, v, hgdec⟩
  refine ⟨c, u, v, ?_⟩
  calc
    x = data.sigma g := hg.symm
    _ = data.sigma ((SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v) := by
      rw [hgdec]
    _ = data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp) := by
      simp [map_mul]

/-- BG Appendix C, Lemma C.3 Step 2 inside concrete `P⋊U`: if
`s₁ u s₂` lies in the complement, then either both prime-line factors are
trivial or the complement factor is trivial and the prime-line factors cancel. -/
theorem generatorRelation_step2_primeLine {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {c d : ZMod hyp.base.p}
    (u : fieldNormalizerNormOneUnits hyp)
    (hmem : (fieldNormalizerPrimeLineElement hyp c *
        (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          fieldNormalizerPrimeLineElement hyp d) ∈ fieldNormalizerComplement hyp) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hmem_original :
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd
            ((algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c) *
              (1 : GaloisField hyp.base.p hyp.base.q))) : fieldNormalizerFrobeniusGroup hyp) *
        SemidirectProduct.inr u *
          SemidirectProduct.inl
            (Multiplicative.ofAdd
              ((algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) d) *
                (1 : GaloisField hyp.base.p hyp.base.q)))) ∈
        (SemidirectProduct.inr : fieldNormalizerNormOneUnits hyp →*
          fieldNormalizerFrobeniusGroup hyp).range := by
    simpa [fieldNormalizerPrimeLineElement, fieldNormalizerComplement] using hmem
  exact
    OddOrder.BG.AppC.NormSet.normOneFrobenius_generatorRelation_step2_primeLine
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime data.cyclotomic_coprime
      (s := (1 : GaloisField hyp.base.p hyp.base.q)) one_ne_zero
      (c := c) (d := d) u hmem_original

/-- BG Appendix C, Lemma C.3 Step 2 transported to `G`: the same alternative can
be read from membership of the transported product in `U`. -/
theorem generatorRelation_step2_primeLine_of_sigma_mem_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {c d : ZMod hyp.base.p} (u : fieldNormalizerNormOneUnits hyp)
    (hmem : data.sigma (fieldNormalizerPrimeLineElement hyp c) *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp d) ∈ hyp.base.U) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  have hmem_map : data.sigma (fieldNormalizerPrimeLineElement hyp c) *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp d) ∈
      (fieldNormalizerComplement hyp).map data.sigma := by
    rwa [data.sigma_U_eq_U]
  rcases hmem_map with ⟨g, hgU, hg⟩
  let prodH : fieldNormalizerFrobeniusGroup hyp :=
    fieldNormalizerPrimeLineElement hyp c *
      (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp d
  have hprod_sigma : data.sigma prodH =
      data.sigma (fieldNormalizerPrimeLineElement hyp c) *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp d) := by
    simp [prodH, map_mul]
  have hg_eq : g = prodH := data.sigma_injective (by
    rw [hg, hprod_sigma])
  have hmemH : prodH ∈ fieldNormalizerComplement hyp := by
    simpa [← hg_eq] using hgU
  exact data.generatorRelation_step2_primeLine u hmemH

/-- The chosen nonidentity element `s ∈ P₀` cannot normalize `U`.  Otherwise a
nontrivial norm-one unit `u` would give `s u s⁻¹ ∈ U`, and BG Appendix C,
Lemma C.3 Step 2 forces `u = 1`. -/
theorem s_not_normalizes_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.s ∉ Subgroup.normalizer (hyp.base.U : Set G) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro hsN
  rcases exists_fieldNormalizerNormOneUnit_ne_one hyp with ⟨u, hu_ne⟩
  have huU :
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  have hconjU :
      data.s *
          data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
            data.s⁻¹ ∈ hyp.base.U :=
    (Subgroup.mem_normalizer_iff.mp hsN
      (data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp))).mp huU
  have hsigma_inv :
      data.sigma (fieldNormalizerPrimeLineElement hyp (-1)) = data.s⁻¹ := by
    rw [fieldNormalizerPrimeLineElement_neg hyp (1 : ZMod hyp.base.p)]
    simp [s, fieldNormalizerPrimeLineElement_one]
  have hmem_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp 1) *
          data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp (-1)) ∈ hyp.base.U := by
    simpa [s, fieldNormalizerPrimeLineElement_one, hsigma_inv] using hconjU
  have hstep :=
    data.generatorRelation_step2_primeLine_of_sigma_mem_U
      (c := (1 : ZMod hyp.base.p)) (d := (-1 : ZMod hyp.base.p)) u hmem_step
  rcases hstep with hzero | hone
  · have h1_ne_zero : (1 : ZMod hyp.base.p) ≠ 0 := one_ne_zero
    exact h1_ne_zero hzero.1
  · exact hu_ne hone.1

/-- Consequently the transported prime line `W₂ = P₀` is not contained in
`N_G(U)`.  This is the Step 3 obstruction BG uses after forcing
`P₁ = P₀`. -/
theorem W2_not_le_normalizer_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    ¬ hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G) := by
  intro hW2
  exact data.s_not_normalizes_U (hW2 data.s_mem_W2)

/-- Applying the norm-one/unit equivalence is just `σ` on the concrete
semidirect-product complement. -/
theorem normOneUnitsEquivU_apply_coe {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (u : fieldNormalizerNormOneUnits hyp) :
    (data.normOneUnitsEquivU u : G) = data.sigma (SemidirectProduct.inr u) := by
  rfl

/-- Equality of `σ`-images reflects the additive-kernel coordinate in the
concrete semidirect product. -/
theorem sigma_eq_left_eq {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {g h : fieldNormalizerFrobeniusGroup hyp} (heq : data.sigma g = data.sigma h) :
    g.left = h.left :=
  congrArg (fun x : fieldNormalizerFrobeniusGroup hyp => x.left)
    (data.sigma_injective heq)

/-- Equality of `σ`-images reflects the norm-one complement coordinate in the
concrete semidirect product.  This is the precise "mod `P`" reading used in BG
Appendix C, Lemma C.3 Step 4. -/
theorem sigma_eq_right_eq {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {g h : fieldNormalizerFrobeniusGroup hyp} (heq : data.sigma g = data.sigma h) :
    g.right = h.right :=
  congrArg (fun x : fieldNormalizerFrobeniusGroup hyp => x.right)
    (data.sigma_injective heq)

/-- Semidirect normal forms remain unique after applying the field-normalizer
embedding `σ`. -/
theorem sigma_eq_iff_left_right_eq {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {g h : fieldNormalizerFrobeniusGroup hyp} :
    data.sigma g = data.sigma h ↔ g.left = h.left ∧ g.right = h.right := by
  constructor
  · intro heq
    exact ⟨data.sigma_eq_left_eq heq, data.sigma_eq_right_eq heq⟩
  · rintro ⟨hleft, hright⟩
    apply congrArg data.sigma
    apply SemidirectProduct.ext
    · exact hleft
    · exact hright

/-- The conjugate prime-line subgroup `P₁` used in BG Appendix C, expressed
with Lean left-conjugation convention. -/
noncomputable def P1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    Subgroup G :=
  MulAut.conj data.y • hyp.base.W2

/-- The BG element `t`, the `y`-conjugate of `s` in Lean convention. -/
noncomputable def t {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) : G :=
  MulAut.conj data.y data.s

/-- The transported conjugate generator lies in `P₁`. -/
theorem t_mem_P1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ∈ data.P1 := by
  dsimp [P1, t]
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  convert data.s_mem_W2 using 1
  simp
  group

/-- The conjugate generator `t` is nontrivial. -/
theorem t_ne_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ≠ 1 := by
  intro ht
  exact data.s_ne_one ((MulAut.conj data.y).injective (by simpa [t] using ht))

/-- The conjugate generator `t` has `p`-th power equal to `1`. -/
theorem t_pow_p_eq_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ^ hyp.base.p = 1 := by
  simpa [t, map_pow] using congrArg (MulAut.conj data.y) data.s_pow_p_eq_one

/-- `P₁` normalizes Peterfalvi subgroup `U`, as required in BG C.3 Step 3. -/
theorem P1_normalizes_U {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.P1 ≤ Subgroup.normalizer (hyp.base.U : Set G) := by
  simpa [P1] using data.W2_conj_y_normalizes_U

/-- BG Appendix C, Lemma C.3 Step 3 contradiction endpoint: the conjugate
prime line `P₁` cannot equal the original prime line `P₀ = W₂`, because `P₁`
normalizes `U` while `W₂` cannot be contained in `N_G(U)`. -/
theorem P1_ne_W2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.P1 ≠ hyp.base.W2 := by
  intro hP1
  exact data.W2_not_le_normalizer_U (by
    intro x hxW2
    exact data.P1_normalizes_U (by simpa [hP1] using hxW2))

/-- The symmetric form of `P1_ne_W2`, useful when BG has derived `P₀ = P₁`. -/
theorem W2_ne_P1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.W2 ≠ data.P1 := by
  intro hW2
  exact data.P1_ne_W2 hW2.symm

/-- The conjugate generator `t` normalizes `U`. -/
theorem t_normalizes_U {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
  data.P1_normalizes_U data.t_mem_P1

/-- Powers of the conjugate generator `t` normalize `U`. -/
theorem t_pow_normalizes_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℕ) :
    data.t ^ n ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
  pow_mem data.t_normalizes_U n

/-- Integer powers of the conjugate generator `t` normalize `U`. -/
theorem t_zpow_normalizes_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℤ) :
    data.t ^ n ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
  (Subgroup.normalizer (hyp.base.U : Set G)).zpow_mem data.t_normalizes_U n

/-- Conjugating a concrete norm-one complement element by any integer power of
`t` remains in the transported subgroup `U`. -/
theorem t_zpow_conj_sigma_inr_mem_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℤ) (u : fieldNormalizerNormOneUnits hyp) :
    data.t ^ n * data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        (data.t ^ n)⁻¹ ∈ hyp.base.U := by
  have huU :
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (data.t_zpow_normalizes_U n)
    (data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp))).mp huU

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` membership bridge: any expression
`s^m (u)^{t^n} s^r` with `u ∈ U` lies in `PU`. -/
theorem s_zpow_mul_t_zpow_conj_sigma_inr_mul_s_zpow_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m n r : ℤ) (u : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          (data.t ^ n *
            data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
              (data.t ^ n)⁻¹) *
        data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := by
  have hm : data.s ^ m ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U m
  have hmid :
      data.t ^ n * data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          (data.t ^ n)⁻¹ ∈ hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U)
      (data.t_zpow_conj_sigma_inr_mem_U n u)
  have hr : data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U r
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hm hmid) hr

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` decomposition bridge: expressions
of the form `s^m (u)^{t^n} s^r` admit the Step 1 `u₁ s₁ v₁` normal form. -/
theorem exists_step4_decomposition_of_zpow_tConj_normOne
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m n r : ℤ) (u : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s ^ m *
            (data.t ^ n *
              data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
                (data.t ^ n)⁻¹) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_t_zpow_conj_sigma_inr_mul_s_zpow_mem_P_sup_U m n r u)


/-- BG Appendix C, Lemma C.3 Step 3 intersection dichotomy before the final
contradiction: if `g` normalizes `U`, then `(PU) ∩ (PU)^g` is either `U` or
all of `PU`. -/
theorem P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) {g : G}
    (hgU : g ∈ Subgroup.normalizer (hyp.base.U : Set G)) :
    (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj g • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.U ∨
      (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj g • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.P ⊔ hyp.base.U := by
  let X : Subgroup G :=
    (hyp.base.P ⊔ hyp.base.U) ⊓ (MulAut.conj g • (hyp.base.P ⊔ hyp.base.U))
  have hUle : hyp.base.U ≤ X := by
    intro u hu
    refine ⟨(le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hu, ?_⟩
    have hU_image : MulAut.conj g '' (hyp.base.U : Set G) = hyp.base.U :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp hgU
    have hu_image : u ∈ MulAut.conj g '' (hyp.base.U : Set G) := by
      rw [hU_image]
      exact hu
    rcases hu_image with ⟨u0, hu0, hu0_eq⟩
    have hu0_PU : u0 ∈ hyp.base.P ⊔ hyp.base.U :=
      (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hu0
    rw [← hu0_eq]
    exact Set.smul_mem_smul_set hu0_PU
  by_cases hX : X = hyp.base.U
  · left
    exact hX
  · right
    exact data.subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U hUle inf_le_left hX

/-- The same Step 3 intersection dichotomy for powers of the chosen conjugate
generator `t`. -/
theorem P_sup_U_inf_conj_t_pow_eq_U_or_eq_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) (n : ℕ) :
    (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj (data.t ^ n) • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.U ∨
      (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj (data.t ^ n) • (hyp.base.P ⊔ hyp.base.U)) =
          hyp.base.P ⊔ hyp.base.U :=
  data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
    (data.t_pow_normalizes_U n)

/-- Conjugation by `t` as an automorphism of Peterfalvi's subgroup `U`. -/
noncomputable def tConjUAut {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : MulAut hyp.base.U :=
  hyp.base.U.normalizerMonoidHom ⟨data.t, data.t_normalizes_U⟩

/-- The subgroup automorphism `tConjUAut` is ambient conjugation by `t`. -/
theorem tConjUAut_apply_coe {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (u : hyp.base.U) :
    (data.tConjUAut u : G) = data.t * (u : G) * data.t⁻¹ := by
  rfl

/-- The `t`-conjugation automorphism of `U` has `p`-th power equal to `1`. -/
theorem tConjUAut_pow_p_eq_one {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : data.tConjUAut ^ hyp.base.p = 1 := by
  have ht_norm :
      (⟨data.t, data.t_normalizes_U⟩ : Subgroup.normalizer (hyp.base.U : Set G)) ^
          hyp.base.p = 1 := by
    ext
    exact data.t_pow_p_eq_one
  rw [tConjUAut, ← map_pow, ht_norm, map_one]

/-- Conjugation by `t`, transported back to the concrete norm-one unit group. -/
noncomputable def tConjNormOneUnitsAut {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : MulAut (fieldNormalizerNormOneUnits hyp) :=
  (MulAut.congr data.normOneUnitsEquivU).symm data.tConjUAut

/-- The transported `t`-conjugation automorphism has `p`-th power equal to `1`. -/
theorem tConjNormOneUnitsAut_pow_p_eq_one {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : data.tConjNormOneUnitsAut ^ hyp.base.p = 1 := by
  rw [tConjNormOneUnitsAut,
    ← map_pow ((MulAut.congr data.normOneUnitsEquivU).symm) data.tConjUAut hyp.base.p,
    data.tConjUAut_pow_p_eq_one, map_one]

/-- The transported automorphism agrees with conjugation by `t` after applying
`σ` to the concrete complement. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (u : fieldNormalizerNormOneUnits hyp) :
    data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) =
      data.tConjUAut (data.normOneUnitsEquivU u) := by
  simp [tConjNormOneUnitsAut]

/-- After transporting back to the concrete complement, the `t`-automorphism is
ambient conjugation of `σ(inr u)`. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) :
    (data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) : G) =
      data.t * data.sigma (SemidirectProduct.inr u) * data.t⁻¹ := by
  calc
    (data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) : G) =
        (data.tConjUAut (data.normOneUnitsEquivU u) : G) := by
      rw [data.normOneUnitsEquivU_tConjNormOneUnitsAut]
    _ = data.t * (data.normOneUnitsEquivU u : G) * data.t⁻¹ :=
      data.tConjUAut_apply_coe (data.normOneUnitsEquivU u)
    _ = data.t * data.sigma (SemidirectProduct.inr u) * data.t⁻¹ := by
      rw [data.normOneUnitsEquivU_apply_coe]

/-- Iterating the transported `t`-automorphism agrees with conjugation by
the corresponding natural power of `t` after applying `σ` to the concrete
complement. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut_pow_apply_coe
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ n) u) : G) =
      data.t ^ n * data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        (data.t ^ n)⁻¹ := by
  induction n with
  | zero =>
      simp [data.normOneUnitsEquivU_apply_coe]
  | succ n ih =>
      calc
        (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ (n + 1)) u) : G) =
            data.t *
                (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ n) u) : G) *
              data.t⁻¹ := by
          rw [pow_succ']
          exact data.normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe
            ((data.tConjNormOneUnitsAut ^ n) u)
        _ = data.t *
              (data.t ^ n *
                data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
                  (data.t ^ n)⁻¹) *
            data.t⁻¹ := by
          rw [ih]
        _ = data.t ^ (n + 1) *
              data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
                (data.t ^ (n + 1))⁻¹ := by
          group

/-- The natural-power conjugate of a concrete complement element is the `σ`
image of the corresponding power of the transported norm-one automorphism. -/
theorem t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    data.t ^ n * data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        (data.t ^ n)⁻¹ =
      data.sigma
        (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
          fieldNormalizerFrobeniusGroup hyp) := by
  rw [← data.normOneUnitsEquivU_apply_coe ((data.tConjNormOneUnitsAut ^ n) u)]
  exact (data.normOneUnitsEquivU_tConjNormOneUnitsAut_pow_apply_coe n u).symm

/-- Natural-power form of the Step 4 conjugation rewrite: the middle
`(u)^{t^n}` term can be read as the concrete norm-one unit obtained by iterating
`tConjNormOneUnitsAut`. -/
theorem s_zpow_mul_t_pow_conj_sigma_inr_mul_s_zpow_eq_sigma_inr_tConjNormOneUnitsAut_pow
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          (data.t ^ n *
            data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
              (data.t ^ n)⁻¹) *
        data.s ^ r =
      data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r := by
  rw [data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow n u]

/-- Natural-power variant of the Step 4 `(C.5)` membership bridge, with the
middle term already expressed in the concrete norm-one complement. -/
theorem s_zpow_mul_sigma_inr_tConjNormOneUnitsAut_pow_mul_s_zpow_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := by
  have hm : data.s ^ m ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U m
  have hmidU :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u),
      ⟨(data.tConjNormOneUnitsAut ^ n) u, rfl⟩, rfl⟩
  have hmid :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hmidU
  have hr : data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U r
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hm hmid) hr

/-- Natural-power variant of the Step 4 `(C.5)` decomposition bridge: after
rewriting `(u)^{t^n}` as a concrete iterate of `tConjNormOneUnitsAut`, the term
still admits Step 1 `u₁ s₁ v₁` normal form. -/
theorem exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s ^ m *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_sigma_inr_tConjNormOneUnitsAut_pow_mul_s_zpow_mem_P_sup_U m r n u)


/-- BG Appendix C, Lemma C.3 Step 4 "mod `P`" bridge: once a natural-power
`(C.5)` term is written in Step 1 normal form, applying the right projection of
the concrete semidirect product reads off the complement equation. -/
theorem right_component_of_step4_tConjNormOneUnitsAut_pow_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (n : ℕ) (u u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (c : ZMod hyp.base.p)
    (hdec : data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    (data.tConjNormOneUnitsAut ^ n) u = u₁ * v₁ := by
  have hmP : data.s ^ m ∈ hyp.base.P := data.s_zpow_mem_P m
  rw [← data.sigma_P_eq_P] at hmP
  rcases hmP with ⟨pm, hpmP, hpm⟩
  have hrP : data.s ^ r ∈ hyp.base.P := data.s_zpow_mem_P r
  rw [← data.sigma_P_eq_P] at hrP
  rcases hrP with ⟨pr, hprP, hpr⟩
  have hpm_right : SemidirectProduct.rightHom pm = 1 := by
    rcases hpmP with ⟨x, rfl⟩
    simp
  have hpr_right : SemidirectProduct.rightHom pr = 1 := by
    rcases hprP with ⟨x, rfl⟩
    simp
  have hline_right :
      SemidirectProduct.rightHom (fieldNormalizerPrimeLineElement hyp c) = 1 := by
    simp [fieldNormalizerPrimeLineElement]
  have hσ :
      data.sigma
          (pm *
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) * pr) =
        data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
    calc
      data.sigma
          (pm *
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) * pr) =
          data.s ^ m *
              data.sigma
                (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
                  fieldNormalizerFrobeniusGroup hyp) *
            data.s ^ r := by
        simp [map_mul, hpm, hpr]
      _ = data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp c) *
              data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
        simp [map_mul]
  have hH := data.sigma_injective hσ
  have hright := congrArg (SemidirectProduct.rightHom :
      fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerNormOneUnits hyp) hH
  simpa [map_mul, hpm_right, hpr_right, hline_right, mul_assoc] using hright

/-- BG Appendix C, Lemma C.3 Step 4 final specialization: the first equation of
`(C.5)` at `k = 3` has a Step 1 normal form.  This is the entry point for the
final paragraph, where `u` is instantiated with the norm-one unit represented by
`a ∈ E`. -/
theorem exists_step4_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s *
            data.sigma
              (SemidirectProduct.inr
                ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
  simpa using
    data.exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow
      (m := (1 : ℤ)) (r := (-2 : ℤ)) (n := 3) (u := u⁻¹)

/-- The `mod P` reading of the `k = 3` first `(C.5)` equation: the middle term
`u^{-1}` conjugated by `t^3` has complement component `u₁ * v₁`. -/
theorem right_component_of_step4_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u u₁ v₁ : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    (data.tConjNormOneUnitsAut ^ 3) u⁻¹ = u₁ * v₁ := by
  have hdec' : data.s ^ (1 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
    simpa using hdec
  simpa using
    data.right_component_of_step4_tConjNormOneUnitsAut_pow_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ)) (n := 3) (u := u⁻¹)
      (u₁ := u₁) (v₁ := v₁) (c := c) hdec'

/-- BG Appendix C, Lemma C.3 Step 4 final paragraph, finite-field reading:
if a first `k = 3` normal form has middle prime-line factor `s^{-1}`,
then its additive coordinate gives `N(2*w-1)=1` for the middle complement
element `w`. -/
theorem normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (w u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (hdec : data.s *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
      ((2 : GaloisField hyp.base.p hyp.base.q) *
          (((w : fieldNormalizerNormOneUnits hyp) :
              (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) - 1) = 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  let F := GaloisField hyp.base.p hyp.base.q
  let H := fieldNormalizerFrobeniusGroup hyp
  have hline_neg_one :
      fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) : H) := by
    simp [fieldNormalizerPrimeLineElement, F]
  have hline_neg_two :
      fieldNormalizerPrimeLineElement hyp (-2 : ZMod hyp.base.p) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F))) : H) := by
    simp [fieldNormalizerPrimeLineElement, F, map_neg, map_ofNat]
  have hσ :
      data.sigma
          ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) *
              SemidirectProduct.inr w *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))) =
        data.sigma
          ((SemidirectProduct.inr u₁ : H) *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) *
              SemidirectProduct.inr v₁) := by
    calc
      data.sigma
          ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) *
              SemidirectProduct.inr w *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))) =
          data.s * data.sigma (SemidirectProduct.inr w : H) * data.s ^ (-2 : ℤ) := by
        have hs :
            data.s =
              data.sigma
                (SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) := by
          simp [s, fieldNormalizerPrimeLineGenerator, F]
        have hsneg_two :
            data.s ^ (-2 : ℤ) =
              data.sigma
                (SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F))) : H) := by
          simpa [hline_neg_two] using data.s_zpow_neg_two_eq_primeLineElement_neg_two
        rw [map_mul, map_mul, hsneg_two, hs]
      _ = data.sigma (SemidirectProduct.inr u₁ : H) *
            data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
              data.sigma (SemidirectProduct.inr v₁ : H) := by
        exact hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : H) *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) *
              SemidirectProduct.inr v₁) := by
        simp [map_mul, hline_neg_one]
  have hH := data.sigma_injective hσ
  simpa [F] using
    OddOrder.BG.AppC.NormSet.normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.ne_zero w u₁ v₁ hH

/-- BG Appendix C, Lemma C.3 Step 4 final paragraph, finite-field reading:
if the first `k = 3` equation of `(C.5)` has middle prime-line factor `s^{-1}`,
then its additive coordinate gives `N(2*w-1)=1` for
`w = (tConjNormOneUnitsAut^3)(u^{-1})`. -/
theorem normN_two_mul_sub_one_of_step4_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
      ((2 : GaloisField hyp.base.p hyp.base.q) *
          ((((data.tConjNormOneUnitsAut ^ 3) u⁻¹ : fieldNormalizerNormOneUnits hyp) :
              (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) - 1) = 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simpa using
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
      ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) u₁ v₁ hdec

/-- A first `k = 3` coordinate step for every element of `E` implies the
AppC generator relation.  This is the exact S16-facing target left after the
BG C.3 Step 4 argument has shown that the middle prime-line factor in the
relevant normal form is `s^{-1}`. -/
theorem appC_normSet_generator_relation_of_first_k_three_coordinate
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hstep :
      letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
      ∀ w : fieldNormalizerNormOneUnits hyp,
        (((w : fieldNormalizerNormOneUnits hyp) :
            (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) ∈
          OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
          ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
            data.s *
                data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
              data.s ^ (-2 : ℤ) =
            data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
              data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
                data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    appCNormSetGeneratorRelation hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro a ha
  let w : fieldNormalizerNormOneUnits hyp :=
    OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE
      hyp.base.p hyp.base.q hyp.base.q_prime.pos ha
  have hwE :
      (((w : fieldNormalizerNormOneUnits hyp) :
          (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q) ∈
        OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
    simpa [w] using ha
  rcases hstep w hwE with ⟨u₁, v₁, hdec⟩
  have hnorm :=
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition w u₁ v₁ hdec
  simpa [w] using hnorm

/-- The `twistedInv` operation in the norm-one C.3 interface is ambient
conjugation by `t` applied to the inverse complement element. -/
theorem normOneUnitsEquivU_twistedInv_tConjNormOneUnitsAut_apply_coe
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) :
    (data.normOneUnitsEquivU
        (OddOrder.BG.AppC.NormSet.twistedInv data.tConjNormOneUnitsAut u) : G) =
      data.t * data.sigma (SemidirectProduct.inr u⁻¹) * data.t⁻¹ := by
  simpa [OddOrder.BG.AppC.NormSet.twistedInv] using
    data.normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe u⁻¹

/-- To produce the S16 AppC C.3 interface it is enough to prove the norm-set
step for the concrete automorphism induced by conjugation with `t`. -/
theorem appC_twisted_normOne_step_of_tConjNormOneUnitsAut
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    OddOrder.BG.AppC.NormSet.normSetETwistedNormOneStep
        (p := hyp.base.p) (q := hyp.base.q) data.tConjNormOneUnitsAut →
      appCNormSetTwistedNormOneStep hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro hstep
  exact ⟨data.tConjNormOneUnitsAut, data.tConjNormOneUnitsAut_pow_p_eq_one, hstep⟩

/-- The conjugate generator `t` also normalizes `Q`. -/
theorem t_normalizes_Q {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ∈ Subgroup.normalizer (hyp.base.Q : Set G) := by
  have hyN : data.y ∈ Subgroup.normalizer (hyp.base.Q : Set G) :=
    Subgroup.le_normalizer data.y_mem_Q
  dsimp [t]
  exact mul_mem (mul_mem hyN data.s_normalizes_Q) (inv_mem hyN)

/-- The first BG commutator factor `s⁻¹t` lies in `Q`. -/
theorem s_inv_mul_t_mem_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.s⁻¹ * data.t ∈ hyp.base.Q := by
  have hsN_inv : data.s⁻¹ ∈ Subgroup.normalizer (hyp.base.Q : Set G) :=
    inv_mem data.s_normalizes_Q
  have hconj_y : data.s⁻¹ * data.y * data.s ∈ hyp.base.Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp hsN_inv data.y).mp data.y_mem_Q
  have hy_inv : data.y⁻¹ ∈ hyp.base.Q := inv_mem data.y_mem_Q
  dsimp [t]
  simpa [mul_assoc] using mul_mem hconj_y hy_inv

private theorem inv_pow_mul_pow_mem_of_inv_mul_mem {H : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (H : Set G)) (hrel : a⁻¹ * b ∈ H) :
    ∀ n : ℕ, (a⁻¹) ^ n * b ^ n ∈ H := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have haN_inv : a⁻¹ ∈ Subgroup.normalizer (H : Set G) := inv_mem haN
      have hconj : a⁻¹ * ((a⁻¹) ^ n * b ^ n) * a ∈ H := by
        simpa using (Subgroup.mem_normalizer_iff.mp haN_inv ((a⁻¹) ^ n * b ^ n)).mp ih
      have hprod : (a⁻¹ * ((a⁻¹) ^ n * b ^ n) * a) * (a⁻¹ * b) ∈ H :=
        mul_mem hconj hrel
      convert hprod using 1
      group

/-- The BG commutator factors `(s⁻¹)^n t^n` lie in `Q`. -/
theorem s_inv_pow_mul_t_pow_mem_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℕ) :
    (data.s⁻¹) ^ n * data.t ^ n ∈ hyp.base.Q :=
  inv_pow_mul_pow_mem_of_inv_mul_mem data.s_normalizes_Q data.s_inv_mul_t_mem_Q n

/-- Elements of the transported `Q` commute.  This is the S16-facing form of
BG Appendix C Remark (B)/(X) used in Lemma C.3 Step 4 when rewriting (C.3) to
(C.4). -/
theorem Q_mul_comm {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x y : G} (hx : x ∈ hyp.base.Q) (hy : y ∈ hyp.base.Q) :
    x * y = y * x := by
  simpa using congrArg Subtype.val
    (data.Q_elementaryAbelian.comm ⟨x, hx⟩ ⟨y, hy⟩)

/-- Elements of the transported prime line `W₂ = σ(P₀)` have `p`-th power
`1`.  This is the ambient `G` form needed when reading BG Appendix C Step 4
modulo `Q`. -/
theorem W2_pow_p_eq_one {hyp : Hypothesis (G := G)} (_data : FieldNormalizerData hyp)
    {x : G} (hx : x ∈ hyp.base.W2) :
    x ^ hyp.base.p = 1 := by
  haveI : Finite hyp.base.W2 := Nat.finite_of_card_ne_zero (by
    rw [← hyp.base.p_eq_card_W2]
    exact hyp.base.p_prime.ne_zero)
  have hxpow := pow_card_eq_one' (G := hyp.base.W2) (x := (⟨x, hx⟩ : hyp.base.W2))
  have hxpow_coe := congrArg Subtype.val hxpow
  simpa [← hyp.base.p_eq_card_W2] using hxpow_coe

/-- Elements of the transported elementary abelian subgroup `Q` have `q`-th
power `1`, in ambient `G` form. -/
theorem Q_pow_q_eq_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : G} (hx : x ∈ hyp.base.Q) :
    x ^ hyp.base.q = 1 := by
  simpa using congrArg Subtype.val
    (data.Q_elementaryAbelian.pow_eq_one (⟨x, hx⟩ : hyp.base.Q))

/-- The transported prime line and the transported elementary abelian `Q` meet
trivially.  This is the BG Appendix C Step 4 `P₀ ∩ Q = 1` input after
identifying `P₀` with `W₂ = σ(P₀)`. -/
theorem W2_inf_Q_eq_bot {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.W2 ⊓ hyp.base.Q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxW2 : x ∈ hyp.base.W2 := hx.1
  have hxQ : x ∈ hyp.base.Q := hx.2
  have hxp : x ^ hyp.base.p = 1 := data.W2_pow_p_eq_one hxW2
  have hxq : x ^ hyp.base.q = 1 := data.Q_pow_q_eq_one hxQ
  have horder_p : orderOf x ∣ hyp.base.p := orderOf_dvd_of_pow_eq_one hxp
  have horder_q : orderOf x ∣ hyp.base.q := orderOf_dvd_of_pow_eq_one hxq
  have hpq : Nat.Coprime hyp.base.p hyp.base.q :=
    (Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hpq horder_p horder_q
  simpa [Subgroup.mem_bot] using orderOf_eq_one_iff.mp horder_one

/-- The orders of `W₂ = σ(P₀)` and `Q` are coprime: `|W₂| = p` is prime, `|Q|`
is a power of `q`, and `p ≠ q`.  This is the coprimality input to BG Appendix C
Remark (X)'s coprime decomposition `Q = C_Q(P₀) × ⁅Q, P₀⁆` (Isaacs Thm 4.34 /
BG Prop 1.6(d)), used in the Lemma C.3 Step 4 kernel argument. -/
theorem W2_card_coprime_Q_card [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    Nat.Coprime (Nat.card ↥hyp.base.W2) (Nat.card ↥hyp.base.Q) := by
  haveI : Fact hyp.base.q.Prime := ⟨hyp.base.q_prime⟩
  have hW2 : Nat.card ↥hyp.base.W2 = hyp.base.p := hyp.base.p_eq_card_W2.symm
  obtain ⟨k, hQ⟩ : ∃ k, Nat.card ↥hyp.base.Q = hyp.base.q ^ k :=
    ⟨_, data.Q_elementaryAbelian.card_eq_pow_finrank⟩
  rw [hW2, hQ]
  exact ((Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q).pow_right k

/-- The conjugation action of `W₂ = σ(P₀)` on the normal elementary abelian
subgroup `Q`, restricted to `↥Q`.  This is the coprime action used to
instantiate BG Appendix C Remark (X)'s decomposition `Q = C_Q(P₀) × ⁅Q, P₀⁆`
(Isaacs Thm 4.34 / BG Prop 1.6(d)) in the Lemma C.3 Step 4 kernel argument. -/
noncomputable def w2ConjQAut {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    ↥hyp.base.W2 →* MulAut ↥hyp.base.Q :=
  (Subgroup.normalizerMonoidHom (H := hyp.base.Q)).comp
    (Subgroup.inclusion data.W2_normalizes_Q)

/-- **BG Appendix C, Remark (X)** (Isaacs Thm 4.34 / BG Prop 1.6(d)): under the
coprime conjugation action of `W₂` on the elementary abelian `Q`, the fixed
points `C_Q(W₂)` and the action commutator `⁅Q, W₂⁆` meet trivially.  This is the
fixed-point-free input to the BG Lemma C.3 Step 4 kernel argument: an element of
`⁅Q, W₂⁆` fixed by `W₂` (equivalently, centralizing the prime line) is trivial. -/
theorem w2ConjQAut_fixedPoints_inf_actionCommutator_eq_bot [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    Subgroup.fixedPointsOfMulAut data.w2ConjQAut ⊓
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut = ⊥ := by
  letI : CommGroup ↥hyp.base.Q :=
    { (inferInstance : Group ↥hyp.base.Q) with
      mul_comm := data.Q_elementaryAbelian.comm }
  exact OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian
    data.w2ConjQAut data.W2_card_coprime_Q_card

/-- **BG Appendix C, Lemma C.3 Step 4 fixed-point-free input**: an element of the
action commutator `⁅Q, W₂⁆` fixed by the whole `W₂`-action is trivial.  Since
`W₂` is generated by `s`, this is BG's statement that `s` acts without nonzero
fixed points on `⁅Q, P₀⁆`, the key to inverting `(s⁻¹ - 1)` in the kernel step. -/
theorem w2ConjQAut_eq_one_of_mem_actionCommutator_of_fixed [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : ↥hyp.base.Q}
    (hx : x ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut)
    (hfix : ∀ w : ↥hyp.base.W2, data.w2ConjQAut w x = x) :
    x = 1 := by
  have hmem : x ∈ Subgroup.fixedPointsOfMulAut data.w2ConjQAut ⊓
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut :=
    ⟨Subgroup.mem_fixedPointsOfMulAut.mpr hfix, hx⟩
  rw [data.w2ConjQAut_fixedPoints_inf_actionCommutator_eq_bot] at hmem
  simpa using hmem

/-- The `W₂`-conjugation action on `Q`, read in the ambient group `G`: it is
genuine conjugation `w x w⁻¹`. -/
theorem w2ConjQAut_apply_coe {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (w : ↥hyp.base.W2) (x : ↥hyp.base.Q) :
    ((data.w2ConjQAut w x : ↥hyp.base.Q) : G) = (w : G) * (x : G) * (w : G)⁻¹ := rfl

/-- **BG Appendix C, Remark (XI)**: we may assume `y ∈ ⁅Q, P₀⁆`.  Writing the
coprime decomposition `Q = ⁅Q,W₂⁆ · C_Q(W₂)`, the centralizer component `yC` of
`y` commutes with `s ∈ W₂`, so the conjugate generator `t = y s y⁻¹` is already
produced by the action-commutator component `yD ∈ ⁅Q, W₂⁆`: `t = yD s yD⁻¹`. -/
theorem exists_yD_mem_actionCommutator_conj_s_eq_t [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    ∃ yD : ↥hyp.base.Q,
      yD ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ∧
        MulAut.conj (yD : G) data.s = data.t := by
  letI : CommGroup ↥hyp.base.Q :=
    { (inferInstance : Group ↥hyp.base.Q) with
      mul_comm := data.Q_elementaryAbelian.comm }
  have hsup : OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ⊔
      Subgroup.fixedPointsOfMulAut data.w2ConjQAut = ⊤ := by
    rw [sup_comm]
    exact OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      data.W2_card_coprime_Q_card (Or.inr inferInstance)
  have hmem : (⟨data.y, data.y_mem_Q⟩ : ↥hyp.base.Q) ∈
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ⊔
        Subgroup.fixedPointsOfMulAut data.w2ConjQAut := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨yD, hyD, yC, hyC, hyDyC⟩ := hmem
  refine ⟨yD, hyD, ?_⟩
  have hyC_s : (yC : G) * data.s = data.s * (yC : G) := by
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hyC ⟨data.s, data.s_mem_W2⟩
    have hcoe := congrArg (Subtype.val) hfix
    rw [data.w2ConjQAut_apply_coe] at hcoe
    exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
  have hconj_raw : (yC : G) * data.s * (yC : G)⁻¹ = data.s := by
    rw [hyC_s]; group
  have hy_coe : (data.y : G) = (yD : G) * (yC : G) := by
    have h := congrArg (Subtype.val) hyDyC
    simpa using h.symm
  show MulAut.conj (yD : G) data.s = MulAut.conj data.y data.s
  rw [MulAut.conj_apply, MulAut.conj_apply, hy_coe, mul_inv_rev,
    show (yD : G) * (yC : G) * data.s * ((yC : G)⁻¹ * (yD : G)⁻¹)
        = (yD : G) * ((yC : G) * data.s * (yC : G)⁻¹) * (yD : G)⁻¹ by group,
    hconj_raw]

/-- **BG Appendix C, Lemma C.3 Step 4, the `s^a` notation**: conjugating the
prime-line generator `s` by `σ(inr a)` (`a ∈ U`) acts as scalar multiplication by
`a⁻¹` on the additive line, i.e. `σ(inr a)⁻¹ s σ(inr a) = σ(inl (a⁻¹ · 1))`.  This
is the concrete reading of BG's relation `as + bs = 2s ⟹ s^a s^b = s²`. -/
theorem sigma_inr_inv_mul_s_mul_sigma_inr {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (a : fieldNormalizerNormOneUnits hyp) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    (data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
        data.sigma (SemidirectProduct.inr a) =
      data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd
        (((((a⁻¹ : fieldNormalizerNormOneUnits hyp) :
            (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q)) *
          (1 : GaloisField hyp.base.p hyp.base.q)))) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rw [s, fieldNormalizerPrimeLineGenerator, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv]
  have h := OddOrder.BG.AppC.NormSet.normOneFrobenius_conj_inl
    (p := hyp.base.p) (q := hyp.base.q) a⁻¹
    (1 : GaloisField hyp.base.p hyp.base.q)
  rw [inv_inv] at h
  exact h

/-- The BG factors `(s⁻¹)^m t^m` and `(s⁻¹)^n t^n` commute because both lie
in `Q`. -/
theorem s_inv_pow_mul_t_pow_mul_comm {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (m n : ℕ) :
    ((data.s⁻¹) ^ m * data.t ^ m) * ((data.s⁻¹) ^ n * data.t ^ n) =
      ((data.s⁻¹) ^ n * data.t ^ n) * ((data.s⁻¹) ^ m * data.t ^ m) :=
  data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q m) (data.s_inv_pow_mul_t_pow_mem_Q n)

/-- The opposite first commutator factor `t⁻¹s` lies in `Q`. -/
theorem t_inv_mul_s_mem_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.t⁻¹ * data.s ∈ hyp.base.Q := by
  simpa using inv_mem data.s_inv_mul_t_mem_Q

/-- The opposite BG commutator factors `(t⁻¹)^n s^n` lie in `Q`. -/
theorem t_inv_pow_mul_s_pow_mem_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℕ) :
    (data.t⁻¹) ^ n * data.s ^ n ∈ hyp.base.Q :=
  inv_pow_mul_pow_mem_of_inv_mul_mem data.t_normalizes_Q data.t_inv_mul_s_mem_Q n

/-- The opposite BG factors `(t⁻¹)^m s^m` and `(t⁻¹)^n s^n` commute because
both lie in `Q`. -/
theorem t_inv_pow_mul_s_pow_mul_comm {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (m n : ℕ) :
    ((data.t⁻¹) ^ m * data.s ^ m) * ((data.t⁻¹) ^ n * data.s ^ n) =
      ((data.t⁻¹) ^ n * data.s ^ n) * ((data.t⁻¹) ^ m * data.s ^ m) :=
  data.Q_mul_comm (data.t_inv_pow_mul_s_pow_mem_Q m) (data.t_inv_pow_mul_s_pow_mem_Q n)

/-- The two BG commutator-factor families commute with each other inside `Q`. -/
theorem s_inv_pow_mul_t_pow_mul_comm_t_inv_pow_mul_s_pow
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) (m n : ℕ) :
    ((data.s⁻¹) ^ m * data.t ^ m) * ((data.t⁻¹) ^ n * data.s ^ n) =
      ((data.t⁻¹) ^ n * data.s ^ n) * ((data.s⁻¹) ^ m * data.t ^ m) :=
  data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q m) (data.t_inv_pow_mul_s_pow_mem_Q n)

/-- The C.3 generator-relation interface consumed by BG Appendix C, derived from
BG's norm-one twisted-inverse output stored in `FieldNormalizerData`. -/
theorem appC_normSet_generator_relation {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    appCNormSetGeneratorRelation hyp :=
  appCNormSetGeneratorRelation_of_twisted_normOne_step hyp data.appC_twisted_normOne_step

/-! ### BG Appendix C, Lemma C.3 Step 4: the generator relation `s₁ = s⁻¹`

The remaining mathematical gap of BG Appendix C (mmd L4994–5095): the central
prime-line factor of the relevant `k = 3` normal form is `s⁻¹`.  The argument is
the group-relation chain (C.2)–(C.10), a kernel/fixed-point-free step inside
`End ⁅Q, P₀⁆`, and a final contradiction via Steps 2–3.

We work throughout with the prime-field-line scalar `s^x := σ(inl(ofAdd x))` for a
field scalar `x ∈ 𝔽_{p^q}`; conjugating by `σ(inr a)` (`a ∈ U`) scales by `↑a⁻¹`. -/

section Step4

/-- Local `Fact` instance for the Step 4 development, so that
`GaloisField hyp.base.p hyp.base.q` elaborates in signatures with a field scalar
argument.  Scoped to the section; downstream callers supply their own. -/
local instance factPPrimeStep4 {hyp : Hypothesis (G := G)} : Fact hyp.base.p.Prime :=
  ⟨hyp.base.p_prime⟩

/-- BG Appendix C prime-field-line scalar `s^x`: the additive-line element
`σ(inl(ofAdd x))` for a field scalar `x ∈ 𝔽_{p^q}`.  The distinguished generator is
`s = s^1`, and `s^x · s^y = s^{x+y}`. -/
noncomputable def sScalar {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x : GaloisField hyp.base.p hyp.base.q) : G :=
  data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd x))

/-- The prime-field-line scalars are additive in the exponent: `s^x · s^y = s^{x+y}`. -/
theorem sScalar_mul {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x y : GaloisField hyp.base.p hyp.base.q) :
    data.sScalar x * data.sScalar y = data.sScalar (x + y) := by
  rw [sScalar, sScalar, sScalar, ← map_mul data.sigma,
    ← map_mul (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp),
    ← ofAdd_add]

/-- The trivial scalar `s^0 = 1`. -/
theorem sScalar_zero {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.sScalar 0 = 1 := by
  rw [sScalar, ofAdd_zero, map_one, map_one]

/-- The distinguished generator is the scalar `s = s^1`. -/
theorem s_eq_sScalar_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s = data.sScalar 1 := by
  rw [sScalar, s, fieldNormalizerPrimeLineGenerator]

/-- The field value `↑a ∈ 𝔽_{p^q}` of a norm-one unit `a ∈ U`. -/
def unitVal {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    GaloisField hyp.base.p hyp.base.q :=
  ((a : (GaloisField hyp.base.p hyp.base.q)ˣ) : GaloisField hyp.base.p hyp.base.q)

/-- The field value of an inverse unit is the inverse field value. -/
theorem unitVal_inv {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    unitVal a⁻¹ = (unitVal a)⁻¹ := by
  simp [unitVal]

/-- The field value of a norm-one unit is nonzero. -/
theorem unitVal_ne_zero {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    unitVal a ≠ 0 := by
  simpa [unitVal] using (a : (GaloisField hyp.base.p hyp.base.q)ˣ).ne_zero

/-- Conjugating the prime-line scalar `s^x` by `σ(inr a)` scales the exponent by
`↑a⁻¹`: `σ(inr a)⁻¹ · s^x · σ(inr a) = s^{(↑a⁻¹)·x}`.  This is BG's `s^a` notation. -/
theorem sScalar_conj {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) (x : GaloisField hyp.base.p hyp.base.q) :
    (data.sigma (SemidirectProduct.inr a))⁻¹ * data.sScalar x *
        data.sigma (SemidirectProduct.inr a) =
      data.sScalar (unitVal a⁻¹ * x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv]
  have h := OddOrder.BG.AppC.NormSet.normOneFrobenius_conj_inl
    (p := hyp.base.p) (q := hyp.base.q) a⁻¹ x
  rw [inv_inv] at h
  exact h

/-- Inversion of a prime-line scalar negates the exponent: `(s^x)⁻¹ = s^{-x}`. -/
theorem sScalar_inv {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x : GaloisField hyp.base.p hyp.base.q) :
    (data.sScalar x)⁻¹ = data.sScalar (-x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_inv, ← ofAdd_neg]

/-- `s⁻¹ = s^{-1}` as a prime-line scalar. -/
theorem s_inv_eq_sScalar_neg_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s⁻¹ = data.sScalar (-1) := by
  rw [s_eq_sScalar_one, sScalar_inv]

/-- `s² = s^2` as a prime-line scalar. -/
theorem s_sq_eq_sScalar_two {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ^ 2 = data.sScalar 2 := by
  rw [s_eq_sScalar_one, pow_two, sScalar_mul]
  congr 1
  norm_num

/-- The transported prime-line element `σ(P₀ c)` is the scalar `s^{algebraMap c}`. -/
theorem sigma_primeLineElement_eq_sScalar {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c : ZMod hyp.base.p) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c) =
      data.sScalar
        (algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c) := by
  rw [sScalar, fieldNormalizerPrimeLineElement]

/-- The central prime-line scalar `s^{-1}` equals `σ(P₀ (-1))`, the middle factor
of the target normal form. -/
theorem sScalar_neg_one_eq_sigma_primeLineElement {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.sScalar (-1) =
      data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) := by
  rw [sigma_primeLineElement_eq_sScalar]
  congr 1
  push_cast
  ring

/-- **BG Appendix C, Lemma C.3 Step 4 base relation** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`, BG's identity `s^a · s^b = s²`, where the BG
conjugate `s^a = σ(inr a)⁻¹ · s · σ(inr a) = s^{↑a⁻¹}`. -/
theorem sBGConj_mul_sBGConj {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    ((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
          data.sigma (SemidirectProduct.inr a)) *
        ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
          data.sigma (SemidirectProduct.inr b)) =
      data.s ^ 2 := by
  have ha : (data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
      data.sigma (SemidirectProduct.inr a) = data.sScalar (unitVal a⁻¹) := by
    rw [s_eq_sScalar_one, sScalar_conj, mul_one]
  have hb : (data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
      data.sigma (SemidirectProduct.inr b) = data.sScalar (unitVal b⁻¹) := by
    rw [s_eq_sScalar_one, sScalar_conj, mul_one]
  rw [ha, hb, sScalar_mul, hab, s_sq_eq_sScalar_two]

/-- **BG Appendix C, Lemma C.3 Step 4 relation (C.2)** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`,
`s⁻² · (σ(inr a)⁻¹ s σ(inr a)) · (σ(inr b)⁻¹ s σ(inr b)) = 1`. -/
theorem relationC2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    data.s ^ (-2 : ℤ) *
        (((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
            data.sigma (SemidirectProduct.inr a)) *
          ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
            data.sigma (SemidirectProduct.inr b))) = 1 := by
  rw [data.sBGConj_mul_sBGConj a b hab, zpow_neg, zpow_two, ← pow_two,
    inv_mul_cancel]

/-- **BG Appendix C, Lemma C.3 Step 4 companion** (mmd L4994): for a norm-one unit
`a` whose inverse field value lies in `E`, BG's companion element `b ∈ E` with
`a + b = 2` exists as a norm-one unit.  Concretely, `↑b⁻¹ = 2 - ↑a⁻¹` (so the base
relation `↑a⁻¹ + ↑b⁻¹ = 2` of `sBGConj_mul_sBGConj` holds), and `↑b⁻¹` again lies in
`E`. -/
theorem exists_companion_of_unitVal_inv_mem_normSetE {hyp : Hypothesis (G := G)}
    (_data : FieldNormalizerData hyp) {a : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q) :
    ∃ b : fieldNormalizerNormOneUnits hyp,
      unitVal a⁻¹ + unitVal b⁻¹ = 2 ∧
        unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hq : 0 < hyp.base.q := hyp.base.q_prime.pos
  have ha2 : (2 - unitVal a⁻¹) ∈
      OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q :=
    OddOrder.BG.AppC.NormSet.two_sub_mem_normSetE hyp.base.p hyp.base.q ha
  have hval : unitVal
      ((OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE
        hyp.base.p hyp.base.q hq ha2)⁻¹)⁻¹ = 2 - unitVal a⁻¹ := by
    rw [inv_inv]
    simp only [unitVal]
    exact OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE_coe
      hyp.base.p hyp.base.q hq ha2
  refine ⟨(OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE
      hyp.base.p hyp.base.q hq ha2)⁻¹, ?_, ?_⟩
  · rw [hval]; ring
  · rw [hval]; exact ha2

/-- **BG Appendix C, Lemma C.3 Step 4 E-membership extraction** (mmd L5090–5094):
if the `k = 3` normal form of `s · σ(inr W) · s⁻²` has central prime-line factor
`s⁻¹`, then the inverse field value `(↑W)⁻¹` lies in the norm set `E`.  This is BG's
final paragraph `v₁ = 2 - W ⟹ N(2 - W) = N(v₁) = 1 ⟹ W ∈ E`, read in the repo's
(inverse) convention so that it is `(↑W)⁻¹` that enters `E`. -/
theorem unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (W u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (hdec : data.s * data.sigma (SemidirectProduct.inr W) * data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
          data.sigma (SemidirectProduct.inr v₁)) :
    (unitVal W)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
  have hN :
      OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
        ((2 : GaloisField hyp.base.p hyp.base.q) * unitVal W - 1) = 1 :=
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition W u₁ v₁ hdec
  have hWnorm :
      OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q (unitVal W) = 1 :=
    (OddOrder.BG.AppC.NormSet.mem_normOneUnits_iff_normN hyp.base.p hyp.base.q
      hyp.base.q_prime.ne_zero (W : (GaloisField hyp.base.p hyp.base.q)ˣ)).mp W.property
  have hW0 : unitVal W ≠ 0 := unitVal_ne_zero W
  refine ⟨?_, ?_⟩
  · rw [OddOrder.BG.AppC.NormSet.normN_inv, hWnorm, inv_one]
  · have hcalc :
        (2 : GaloisField hyp.base.p hyp.base.q) - (unitVal W)⁻¹ =
          (unitVal W)⁻¹ * ((2 : GaloisField hyp.base.p hyp.base.q) * unitVal W - 1) := by
      field_simp
    rw [hcalc, OddOrder.BG.AppC.NormSet.normN_mul,
      OddOrder.BG.AppC.NormSet.normN_inv, hWnorm, inv_one, one_mul, hN]

/-- **Backward conjugation rewrite**: `(t^n)⁻¹ · σ(inr u) · t^n = σ(inr ((tConj^n)⁻¹ u))`.
This is the inverse-direction companion of
`t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow` (S16), giving BG's
right-conjugation `(u)^{t^n} = t⁻ⁿ u tⁿ` directly.  It lets the BG (C.4) connector
`q`-swap telescoping be carried out on the backward `tConj⁻³` form of `M₁`. -/
theorem t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    (data.t ^ n)⁻¹ *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.t ^ n =
      data.sigma
        (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) :
          fieldNormalizerFrobeniusGroup hyp) := by
  have hself : (data.tConjNormOneUnitsAut ^ n) ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) = u := by
    simp
  have h := data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow n
    ((data.tConjNormOneUnitsAut ^ n)⁻¹ u)
  rw [hself] at h
  rw [← h]; group

/-- **Backward `k = 3` first `(C.5)` decomposition** (the entry point for the
capstone proof): for any norm-one unit `a`, the backward form
`s · σ(inr ((tConj³)⁻¹ a⁻¹)) · s⁻²` (BG's `s · (a⁻¹)^{t³} · s⁻²`) admits a Step 1
normal form `σ(inr u₁) · σ(P₀ c) · σ(inr v₁)`.  BG's Lemma C.3 Step 4 pins `c = -1`;
that is the content of `Step4Capstone`. -/
theorem exists_step4_first_k_three_inv_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
  apply data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
  have hs : data.s ∈ hyp.base.P ⊔ hyp.base.U := by
    rw [← zpow_one data.s]; exact data.s_zpow_mem_P_sup_U 1
  have hmidU :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹),
      ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹, rfl⟩, rfl⟩
  have hmid :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hmidU
  have hr : data.s ^ (-2 : ℤ) ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U (-2)
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hs hmid) hr

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` membership bridge in a neutral form:
any word `s^m · σ(inr w) · s^r`, with the middle term already a concrete
norm-one complement element, lies in `PU`. -/
theorem s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := by
  have hm : data.s ^ m ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U m
  have hmidU :
      data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr w, ⟨w, rfl⟩, rfl⟩
  have hmid :
      data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hmidU
  have hr : data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U r
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hm hmid) hr

/-- Neutral Step 4 `(C.5)` decomposition bridge: every word
`s^m · σ(inr w) · s^r` admits Step 1 normal form
`σ(inr u) · σ(P₀ c) · σ(inr v)`. -/
theorem exists_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u v : fieldNormalizerNormOneUnits hyp,
      data.s ^ m *
            data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U m r w)

/-- BG Appendix C, Lemma C.3 Step 4 "mod `P`" bridge in a neutral form: if a
word `s^m · σ(inr w) · s^r` is written in Step 1 normal form `u₁ s₁ v₁`, then the
right component is `w = u₁ v₁`.  This is the reusable right-projection step behind
both the forward and backward `k = 3` `(C.5)` equations. -/
theorem right_component_of_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w u₁ v₁ : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    w = u₁ * v₁ := by
  have hmP : data.s ^ m ∈ hyp.base.P := data.s_zpow_mem_P m
  rw [← data.sigma_P_eq_P] at hmP
  rcases hmP with ⟨pm, hpmP, hpm⟩
  have hrP : data.s ^ r ∈ hyp.base.P := data.s_zpow_mem_P r
  rw [← data.sigma_P_eq_P] at hrP
  rcases hrP with ⟨pr, hprP, hpr⟩
  have hpm_right : SemidirectProduct.rightHom pm = 1 := by
    rcases hpmP with ⟨x, rfl⟩
    simp
  have hpr_right : SemidirectProduct.rightHom pr = 1 := by
    rcases hprP with ⟨x, rfl⟩
    simp
  have hline_right :
      SemidirectProduct.rightHom (fieldNormalizerPrimeLineElement hyp c) = 1 := by
    simp [fieldNormalizerPrimeLineElement]
  have hσ :
      data.sigma (pm * (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) * pr) =
        data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
    calc
      data.sigma (pm * (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) * pr) =
          data.s ^ m *
              data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
            data.s ^ r := by
        simp [map_mul, hpm, hpr]
      _ = data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp c) *
              data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
        simp [map_mul]
  have hH := data.sigma_injective hσ
  have hright := congrArg (SemidirectProduct.rightHom :
      fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerNormOneUnits hyp) hH
  simpa [map_mul, hpm_right, hpr_right, hline_right, mul_assoc] using hright

/-- BG Appendix C `(C.8)` normal-form transport in neutral form: applying the
concrete `p`-power Frobenius to a `(C.5)` equation keeps the prime-line factor
fixed and raises the three complement terms to their `p`-th powers. -/
theorem frobenius_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w u v : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp)) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  let g := fieldNormalizerPrimeLineGenerator hyp
  let W : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr w
  let U : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr u
  let V : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr v
  let S : fieldNormalizerFrobeniusGroup hyp := fieldNormalizerPrimeLineElement hyp c
  have hleft_sigma :
      data.sigma (g ^ m * W * g ^ r) =
        data.s ^ m * data.sigma W * data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_sigma :
      data.sigma (U * S * V) = data.sigma U * data.sigma S * data.sigma V := by
    rw [map_mul, map_mul]
  have hH : g ^ m * W * g ^ r = U * S * V := by
    apply data.sigma_injective
    calc
      data.sigma (g ^ m * W * g ^ r) =
          data.s ^ m * data.sigma W * data.s ^ r := hleft_sigma
      _ = data.sigma U * data.sigma S * data.sigma V := hdec
      _ = data.sigma (U * S * V) := hright_sigma.symm
  have hpowH := congrArg (fieldNormalizerFrobeniusHom hyp) hH
  have hpowH' :
      g ^ m * (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          g ^ r =
        (SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          fieldNormalizerPrimeLineElement hyp c *
            (SemidirectProduct.inr (v ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) := by
    simpa [W, U, V, S, g, map_mul, map_pow,
      fieldNormalizerFrobeniusHom_primeLineGenerator,
      fieldNormalizerFrobeniusHom_inr,
      fieldNormalizerFrobeniusHom_primeLineElement] using hpowH
  have hleft_pow_sigma :
      data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
              g ^ r) =
        data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
            data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_pow_sigma :
      data.sigma
          ((SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c *
              (SemidirectProduct.inr (v ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)) =
        data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
              fieldNormalizerFrobeniusGroup hyp) := by
    rw [map_mul, map_mul]
  calc
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
        data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
              g ^ r) := hleft_pow_sigma.symm
    _ = data.sigma
          ((SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c *
              (SemidirectProduct.inr (v ^ hyp.base.p) :
                fieldNormalizerFrobeniusGroup hyp)) := by
      rw [hpowH']
    _ = data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := hright_pow_sigma

/-- The `mod P` reading of the backward `k = 3` first `(C.5)` equation: BG's
middle term `(a⁻¹)^{t^3}` has complement component `u₁ * v₁`. -/
theorem right_component_of_step4_first_k_three_inv_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a u₁ v₁ : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u₁ * v₁ := by
  have hdec' : data.s ^ (1 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
    simpa using hdec
  simpa using
    data.right_component_of_step4_sigma_inr_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
      (u₁ := u₁) (v₁ := v₁) (c := c) hdec'

/-- BG Appendix C, Lemma C.3 Step 4 first `(C.5)` factor
`M₁ = s · (a⁻¹)^{t^3} · s⁻²`, in BG's backward conjugation convention. -/
noncomputable def step4M1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) : G :=
  data.s *
      ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
    (data.s⁻¹) ^ 2

/-- BG Appendix C, Lemma C.3 Step 4 second `(C.5)` factor
`M₂ = s³ · (ab⁻¹)^{t^2} · s⁻¹`. -/
noncomputable def step4M2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) : G :=
  data.s ^ 3 *
      ((data.t⁻¹) ^ 2 *
        (data.sigma (SemidirectProduct.inr a) *
          (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
    data.s⁻¹

/-- BG Appendix C, Lemma C.3 Step 4 third `(C.5)` factor
`M₃ = s² · b^t · s⁻³`. -/
noncomputable def step4M3 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (b : fieldNormalizerNormOneUnits hyp) : G :=
  data.s ^ 2 *
      (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
    (data.s⁻¹) ^ 3

/-! ### BG Appendix C (C.4) connector `q`-swaps

The three connector words appearing between the conjugated factors in the BG (C.4)
relation are single `Q`-commutator swaps `qᵢ qⱼ = qⱼ qᵢ` (`qᵢ = (s⁻¹)ⁱ tⁱ ∈ Q`,
`Q` abelian).  Each rewrites a connector to a form whose `t`-powers telescope with
the neighbouring conjugates. -/

/-- BG (C.4) connector 1: `s⁻³ t² s = t⁻¹ s⁻² t³`, by commuting `(s⁻¹)³t³` and
`t⁻¹s` inside the abelian `Q`. -/
theorem connectorC4_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.s =
      data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3 :=
  calc
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.s
        = ((data.s⁻¹) ^ 3 * data.t ^ 3) * (data.t⁻¹ * data.s) := by group
    _ = (data.t⁻¹ * data.s) * ((data.s⁻¹) ^ 3 * data.t ^ 3) :=
          data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q 3) data.t_inv_mul_s_mem_Q
    _ = data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3 := by group

/-- BG (C.4) connector 2: `s⁻² t⁻¹ s³ = t⁻³ s t²`, by commuting `(s⁻¹)²t²` and
`(t⁻¹)³s³` inside the abelian `Q`. -/
theorem connectorC4_two {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    (data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3 =
      (data.t⁻¹) ^ 3 * data.s * data.t ^ 2 :=
  calc
    (data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3
        = ((data.s⁻¹) ^ 2 * data.t ^ 2) * ((data.t⁻¹) ^ 3 * data.s ^ 3) := by group
    _ = ((data.t⁻¹) ^ 3 * data.s ^ 3) * ((data.s⁻¹) ^ 2 * data.t ^ 2) :=
          data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q 2)
            (data.t_inv_pow_mul_s_pow_mem_Q 3)
    _ = (data.t⁻¹) ^ 3 * data.s * data.t ^ 2 := by group

/-- BG (C.4) connector 3: `s⁻¹ t⁻¹ s² = t⁻² s t`, by commuting `s⁻¹t` and
`(t⁻¹)²s²` inside the abelian `Q`. -/
theorem connectorC4_three {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s⁻¹ * data.t⁻¹ * data.s ^ 2 =
      (data.t⁻¹) ^ 2 * data.s * data.t :=
  calc
    data.s⁻¹ * data.t⁻¹ * data.s ^ 2
        = (data.s⁻¹ * data.t) * ((data.t⁻¹) ^ 2 * data.s ^ 2) := by group
    _ = ((data.t⁻¹) ^ 2 * data.s ^ 2) * (data.s⁻¹ * data.t) :=
          data.Q_mul_comm data.s_inv_mul_t_mem_Q (data.t_inv_pow_mul_s_pow_mem_Q 2)
    _ = (data.t⁻¹) ^ 2 * data.s * data.t := by group

/-- **BG Appendix C, Lemma C.3 relation (C.4)** (mmd L4994, PDF p.150): the
backward conjugated `k = 3` relation
`s⁻³ t² M₁ t⁻¹ M₂ t⁻¹ M₃ s³ = 1`, where
`M₁ = s · (t⁻³ σ(inr a)⁻¹ t³) · s⁻²`, `M₂ = s³ · (t⁻² σ(inr (a b⁻¹)) t²) · s⁻¹`,
`M₃ = s² · (t⁻¹ σ(inr b) t) · s⁻³` are BG's `s^{k-2}(a⁻¹)^{t^k}s^{-k+1}` etc.  The
connector words between the conjugated factors `q`-swap (Connectors 1–3) and the
`t`-powers then telescope to `t⁻¹ · (C.2) · t = 1`. -/
theorem relationC4 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 *
        (data.s *
            ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
          (data.s⁻¹) ^ 2) *
      data.t⁻¹ *
        (data.s ^ 3 *
            ((data.t⁻¹) ^ 2 *
              (data.sigma (SemidirectProduct.inr a) *
                (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
          data.s⁻¹) *
      data.t⁻¹ *
        (data.s ^ 2 *
            (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
          (data.s⁻¹) ^ 3) *
      data.s ^ 3 = 1 := by
  have hC2 := data.relationC2 a b hab
  calc
    (data.s⁻¹) ^ 3 * data.t ^ 2 *
          (data.s *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
            (data.s⁻¹) ^ 2) *
        data.t⁻¹ *
          (data.s ^ 3 *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
            data.s⁻¹) *
        data.t⁻¹ *
          (data.s ^ 2 *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
            (data.s⁻¹) ^ 3) *
        data.s ^ 3
        = ((data.s⁻¹) ^ 3 * data.t ^ 2 * data.s) *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
              ((data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3) *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
              (data.s⁻¹ * data.t⁻¹ * data.s ^ 2) *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) := by
        group
    _ = (data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3) *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
              ((data.t⁻¹) ^ 3 * data.s * data.t ^ 2) *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
              ((data.t⁻¹) ^ 2 * data.s * data.t) *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) := by
        rw [data.connectorC4_one, data.connectorC4_two, data.connectorC4_three]
    _ = data.t⁻¹ *
          (data.s ^ (-2 : ℤ) *
            (((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
                data.sigma (SemidirectProduct.inr a)) *
              ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
                data.sigma (SemidirectProduct.inr b)))) *
          data.t := by
        group
    _ = data.t⁻¹ * 1 * data.t := by rw [hC2]
    _ = 1 := by group

/-- The first BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^3)⁻¹ a⁻¹`. -/
theorem step4M1_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) :
    data.step4M1 a =
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) := by
  unfold step4M1
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    3 a⁻¹]
  simp [map_inv]
  group

/-- The second BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^2)⁻¹ (a b⁻¹)`. -/
theorem step4M2_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) :
    data.step4M2 a b =
      data.s ^ (3 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-1 : ℤ) := by
  unfold step4M2
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    2 (a * b⁻¹)]
  simp [map_mul, map_inv]
  group

/-- The third BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = tConj⁻¹ b`. -/
theorem step4M3_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (b : fieldNormalizerNormOneUnits hyp) :
    data.step4M3 b =
      data.s ^ (2 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-3 : ℤ) := by
  unfold step4M3
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 b]
  group

/-- Relation `(C.4)` restated using the named BG `(C.5)` factors. -/
theorem relationC4_step4M {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.step4M1 a *
      data.t⁻¹ * data.step4M2 a b * data.t⁻¹ * data.step4M3 b *
        data.s ^ 3 = 1 := by
  simpa [step4M1, step4M2, step4M3] using data.relationC4 a b hab

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` normal-form package for the three
terms appearing in the already-proved relation `(C.4)`.  The `hM*` fields state
the Step 1 normal forms of BG's named factors, and the `right*` fields record the
corresponding mod-`P` complement readings. -/
structure Step4C5NormalForms {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (a b : fieldNormalizerNormOneUnits hyp) where
  c1 : ZMod hyp.base.p
  c2 : ZMod hyp.base.p
  c3 : ZMod hyp.base.p
  u1 : fieldNormalizerNormOneUnits hyp
  v1 : fieldNormalizerNormOneUnits hyp
  u2 : fieldNormalizerNormOneUnits hyp
  v2 : fieldNormalizerNormOneUnits hyp
  u3 : fieldNormalizerNormOneUnits hyp
  v3 : fieldNormalizerNormOneUnits hyp
  hM1 :
    data.step4M1 a =
      data.sigma (SemidirectProduct.inr u1 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
          data.sigma (SemidirectProduct.inr v1 : fieldNormalizerFrobeniusGroup hyp)
  hM2 :
    data.step4M2 a b =
      data.sigma (SemidirectProduct.inr u2 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.sigma (SemidirectProduct.inr v2 : fieldNormalizerFrobeniusGroup hyp)
  hM3 :
    data.step4M3 b =
      data.sigma (SemidirectProduct.inr u3 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c3) *
          data.sigma (SemidirectProduct.inr v3 : fieldNormalizerFrobeniusGroup hyp)
  right1 : (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u1 * v1
  right2 : (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹) = u2 * v2
  right3 : (data.tConjNormOneUnitsAut ^ 1)⁻¹ b = u3 * v3

/-- The three BG `(C.5)` factors in relation `(C.4)` admit compatible Step 1
normal forms and mod-`P` complement readings. -/
theorem exists_step4C5NormalForms
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) :
    Nonempty (Step4C5NormalForms data a b) := by
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) with
    ⟨c1, u1, v1, h1⟩
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (3 : ℤ)) (r := (-1 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) with
    ⟨c2, u2, v2, h2⟩
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (2 : ℤ)) (r := (-3 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b) with
    ⟨c3, u3, v3, h3⟩
  exact ⟨{
    c1 := c1
    c2 := c2
    c3 := c3
    u1 := u1
    v1 := v1
    u2 := u2
    v2 := v2
    u3 := u3
    v3 := v3
    hM1 := by
      rw [data.step4M1_eq_sigma_inr]
      simpa using h1
    hM2 := by
      rw [data.step4M2_eq_sigma_inr]
      simpa using h2
    hM3 := by
      rw [data.step4M3_eq_sigma_inr]
      simpa using h3
    right1 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (1 : ℤ)) (r := (-2 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
        (u₁ := u1) (v₁ := v1) (c := c1) h1
    right2 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (3 : ℤ)) (r := (-1 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹))
        (u₁ := u2) (v₁ := v2) (c := c2) h2
    right3 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (2 : ℤ)) (r := (-3 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b)
        (u₁ := u3) (v₁ := v3) (c := c3) h3
  }⟩

namespace Step4C5NormalForms

/-- The first normal-form factor `u₁ s₁ v₁` from `(C.5)`. -/
noncomputable def factor1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
      data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp)

/-- The second normal-form factor `u₂ s₂ v₂` from `(C.5)`. -/
noncomputable def factor2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
      data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp)

/-- The third normal-form factor `u₃ s₃ v₃` from `(C.5)`. -/
noncomputable def factor3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
      data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp)

/-- BG Appendix C `(C.8)` applied to the first `(C.5)` normal form. -/
theorem hM1_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M1 (a ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u1 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma (SemidirectProduct.inr (forms.v1 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (1 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
            data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM1
    rw [data.step4M1_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (1 : ℤ)) (r := (-2 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
    (u := forms.u1) (v := forms.v1) (c := forms.c1) hneutral
  rw [data.step4M1_eq_sigma_inr]
  simpa [map_pow, map_inv] using hpow

/-- BG Appendix C `(C.8)` applied to the second `(C.5)` normal form. -/
theorem hM2_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M2 (a ^ hyp.base.p) (b ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u2 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.sigma (SemidirectProduct.inr (forms.v2 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (3 : ℤ) *
            data.sigma
              (SemidirectProduct.inr
                ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-1 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
            data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM2
    rw [data.step4M2_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (3 : ℤ)) (r := (-1 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹))
    (u := forms.u2) (v := forms.v2) (c := forms.c2) hneutral
  rw [data.step4M2_eq_sigma_inr]
  simpa [map_pow, map_mul, map_inv, mul_pow] using hpow

/-- BG Appendix C `(C.8)` applied to the third `(C.5)` normal form. -/
theorem hM3_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M3 (b ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u3 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
          data.sigma (SemidirectProduct.inr (forms.v3 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (2 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-3 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
            data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM3
    rw [data.step4M3_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (2 : ℤ)) (r := (-3 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b)
    (u := forms.u3) (v := forms.v3) (c := forms.c3) hneutral
  rw [data.step4M3_eq_sigma_inr]
  simpa [map_pow] using hpow

/-- BG Appendix C `(C.8)` as closure of the whole `(C.5)` normal-form package
under the concrete `p`-power Frobenius. -/
noncomputable def frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    Step4C5NormalForms data (a ^ hyp.base.p) (b ^ hyp.base.p) where
  c1 := forms.c1
  c2 := forms.c2
  c3 := forms.c3
  u1 := forms.u1 ^ hyp.base.p
  v1 := forms.v1 ^ hyp.base.p
  u2 := forms.u2 ^ hyp.base.p
  v2 := forms.v2 ^ hyp.base.p
  u3 := forms.u3 ^ hyp.base.p
  v3 := forms.v3 ^ hyp.base.p
  hM1 := forms.hM1_frobenius
  hM2 := forms.hM2_frobenius
  hM3 := forms.hM3_frobenius
  right1 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right1
    simpa [map_pow, map_inv, mul_pow] using h
  right2 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right2
    simpa [map_pow, map_mul, map_inv, mul_pow] using h
  right3 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right3
    simpa [map_pow, mul_pow] using h

end Step4C5NormalForms

/-- Relation `(C.4)` after substituting the three `(C.5)` normal forms. -/
theorem relationC4_step4C5NormalForms
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * forms.factor1 *
      data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 * data.s ^ 3 = 1 := by
  have h := data.relationC4_step4M a b hab
  rw [forms.hM1, forms.hM2, forms.hM3] at h
  simpa [Step4C5NormalForms.factor1, Step4C5NormalForms.factor2,
    Step4C5NormalForms.factor3] using h

/-- The first rearranged relation on the way to BG `(C.7)`: multiply `(C.4)` by
`s^3` on the left and `s^{-3}` on the right after substituting `(C.5)`. -/
theorem relationC7_seed
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 =
      1 := by
  have h := data.relationC4_step4C5NormalForms hab forms
  calc
    data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 =
        data.s ^ 3 *
          ((data.s⁻¹) ^ 3 * data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 *
            data.t⁻¹ * forms.factor3 * data.s ^ 3) * (data.s ^ 3)⁻¹ := by
      group
    _ = data.s ^ 3 * 1 * (data.s ^ 3)⁻¹ := by rw [h]
    _ = 1 := by group


namespace Step4C5NormalForms

/-- BG `w₁ = v₂^{t⁻¹} u₃` from the rearrangement leading to `(C.7)`. -/
noncomputable def w1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  data.tConjNormOneUnitsAut forms.v2 * forms.u3

/-- BG `w₂ = v₃ u₁^{t⁻²}` from the rearrangement leading to `(C.7)`. -/
noncomputable def w2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  forms.v3 * (data.tConjNormOneUnitsAut ^ 2) forms.u1

/-- BG `w₃ = v₁ u₂^t` from the rearrangement leading to `(C.7)`. -/
noncomputable def w3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  forms.v1 * (data.tConjNormOneUnitsAut ^ 1)⁻¹ forms.u2

/-- Under `(C.8)`, the first `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w1
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w1 = forms.w1 ^ hyp.base.p := by
  simp [frobenius, w1, map_pow, mul_pow]

/-- Under `(C.8)`, the second `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w2
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w2 = forms.w2 ^ hyp.base.p := by
  simp [frobenius, w2, map_pow, mul_pow]

/-- Under `(C.8)`, the third `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w3
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w3 = forms.w3 ^ hyp.base.p := by
  simp [frobenius, w3, map_pow, mul_pow]

/-- The ambient reading of `w₁`: `σ(w₁) = t σ(v₂) t⁻¹ σ(u₃)`. -/
theorem sigma_inr_w1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) =
      data.t * data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) *
        data.t⁻¹ *
          data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) := by
  unfold Step4C5NormalForms.w1
  simp only [map_mul]
  have hφ :
      data.sigma
          (SemidirectProduct.inr (data.tConjNormOneUnitsAut forms.v2) :
            fieldNormalizerFrobeniusGroup hyp) =
        data.t * data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) *
          data.t⁻¹ := by
    simpa using
      (data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 1 forms.v2).symm
  rw [hφ]

/-- The ambient reading of `w₂`: `σ(w₂) = σ(v₃) t² σ(u₁) t⁻²`. -/
theorem sigma_inr_w2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) =
      data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp) *
        data.t ^ 2 *
          data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
            (data.t ^ 2)⁻¹ := by
  unfold Step4C5NormalForms.w2
  simp only [map_mul]
  rw [← data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 2 forms.u1]
  group

/-- The ambient reading of `w₃`: `σ(w₃) = σ(v₁) t⁻¹ σ(u₂) t`. -/
theorem sigma_inr_w3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp) =
      data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp) *
        data.t⁻¹ * data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
          data.t := by
  unfold Step4C5NormalForms.w3
  simp only [map_mul]
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 forms.u2]
  group

/-- The three BG `(C.7)` words are elements of `U`, expressed after applying `σ`. -/
theorem sigma_inr_w_mem_U {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U ∧
      data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U ∧
        data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp) ∈
          hyp.base.U := by
  constructor
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w1, ⟨forms.w1, rfl⟩, rfl⟩
  constructor
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w2, ⟨forms.w2, rfl⟩, rfl⟩
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w3, ⟨forms.w3, rfl⟩, rfl⟩

end Step4C5NormalForms

/-- BG Appendix C `(C.7)`, obtained by rearranging the `(C.5)` substitution relation and
absorbing the conjugated complement terms into `w₁`, `w₂`, and `w₃`. -/
theorem relationC7
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) * data.t⁻¹ =
      (data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
          data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) *
            data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
              data.sigma
                (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp))⁻¹ := by
  let U1 := data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp)
  let V1 := data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp)
  let U2 := data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp)
  let V2 := data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp)
  let U3 := data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp)
  let V3 := data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp)
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  have hseed :
      data.t ^ 2 * U1 * S1 * V1 * data.t⁻¹ * U2 * S2 * V2 * data.t⁻¹ * U3 * S3 * V3 =
        1 := by
    have h := data.relationC7_seed hab forms
    simpa [Step4C5NormalForms.factor1, Step4C5NormalForms.factor2,
      Step4C5NormalForms.factor3, U1, V1, U2, V2, U3, V3, S1, S2, S3, mul_assoc]
      using h
  have hw1_t : data.t⁻¹ * W1 = V2 * data.t⁻¹ * U3 := by
    dsimp [W1, V2, U3]
    rw [forms.sigma_inr_w1]
    group
  have hw2_t : W2 * data.t ^ 2 = V3 * data.t ^ 2 * U1 := by
    dsimp [W2, V3, U1]
    rw [forms.sigma_inr_w2]
    group
  have hw3_t : W3 * data.t⁻¹ = V1 * data.t⁻¹ * U2 := by
    dsimp [W3, V1, U2]
    rw [forms.sigma_inr_w3]
    group
  have hword :
      data.t ^ 2 * U1 * S1 * W3 * (data.t⁻¹ * S2 * data.t⁻¹) * W1 * S3 * V3 =
        1 := by
    calc
      data.t ^ 2 * U1 * S1 * W3 * (data.t⁻¹ * S2 * data.t⁻¹) * W1 * S3 * V3 =
          data.t ^ 2 * U1 * S1 * (W3 * data.t⁻¹) * S2 *
            (data.t⁻¹ * W1) * S3 * V3 := by
        group
      _ = data.t ^ 2 * U1 * S1 * (V1 * data.t⁻¹ * U2) * S2 *
            (V2 * data.t⁻¹ * U3) * S3 * V3 := by
        rw [hw3_t, hw1_t]
      _ = data.t ^ 2 * U1 * S1 * V1 * data.t⁻¹ * U2 * S2 * V2 * data.t⁻¹ * U3 * S3 * V3 := by
        group
      _ = 1 := hseed
  have hwordPrime :
      (data.t ^ 2 * U1 * S1 * W3) * (data.t⁻¹ * S2 * data.t⁻¹) *
          (W1 * S3 * V3) = 1 := by
    simpa [mul_assoc] using hword
  have hmain : data.t⁻¹ * S2 * data.t⁻¹ =
      (W1 * S3 * W2 * data.t ^ 2 * S1 * W3)⁻¹ := by
    calc
      data.t⁻¹ * S2 * data.t⁻¹ =
          (data.t ^ 2 * U1 * S1 * W3)⁻¹ *
            ((data.t ^ 2 * U1 * S1 * W3) * (data.t⁻¹ * S2 * data.t⁻¹) *
              (W1 * S3 * V3)) * (W1 * S3 * V3)⁻¹ := by
        group
      _ = (data.t ^ 2 * U1 * S1 * W3)⁻¹ * 1 * (W1 * S3 * V3)⁻¹ := by
        rw [hwordPrime]
      _ = ((W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3))⁻¹ := by
        group
      _ = (W1 * S3 * W2 * data.t ^ 2 * S1 * W3)⁻¹ := by
        have hD : W1 * S3 * W2 * data.t ^ 2 * S1 * W3 =
            (W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3) := by
          calc
            W1 * S3 * W2 * data.t ^ 2 * S1 * W3 =
                W1 * S3 * (W2 * data.t ^ 2) * S1 * W3 := by
              group
            _ = W1 * S3 * (V3 * data.t ^ 2 * U1) * S1 * W3 := by
              rw [hw2_t]
            _ = (W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3) := by
              group
        rw [← hD]
  simpa [S1, S2, S3, W1, W2, W3, mul_assoc] using hmain


/-- BG Appendix C `(C.8)` Frobenius entry: if the inverse field values of `a` and
`b` lie in `E` and satisfy the companion equation, then the inverse field values of
`a^p` and `b^p` again lie in `E` and satisfy the same companion equation. -/
theorem unitVal_inv_frobenius_pair
    {hyp : Hypothesis (G := G)} {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    unitVal (a ^ hyp.base.p)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q ∧
      unitVal (b ^ hyp.base.p)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q ∧
        unitVal (a ^ hyp.base.p)⁻¹ + unitVal (b ^ hyp.base.p)⁻¹ = 2 := by
  have hpair := OddOrder.BG.AppC.NormSet.normSetE_frobenius_pair
    hyp.base.p hyp.base.q hyp.base.q_prime.ne_zero ha hb hab
  simpa [unitVal, map_pow] using hpair

/-- BG Appendix C `(C.9)` for the third word: comparing `(C.7)` for `(a,b)`
with `(C.7)` for `(a^p,b^p)` shows that
`S₁ W₃^(p-1) S₁⁻¹` lies in `PU` and its `t²`-conjugate also lies in `PU`. -/
theorem relationC9_w3_mem_P_sup_U_and_conj
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
        fieldNormalizerFrobeniusGroup hyp)
    S1 * W3pow * S1⁻¹ ∈ hyp.base.P ⊔ hyp.base.U ∧
      data.t ^ 2 * (S1 * W3pow * S1⁻¹) * (data.t ^ 2)⁻¹ ∈
        hyp.base.P ⊔ hyp.base.U := by
  classical
  dsimp only
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair ha hb hab
  have hC7 := data.relationC7 hab forms
  have hC7p := data.relationC7 hpow_pair.2.2 forms.frobenius
  have hC7' :
      data.t⁻¹ * S2 * data.t⁻¹ = (A * data.t ^ 2 * S1 * W3)⁻¹ := by
    simpa [A, S1, S2, S3, W1, W2, W3, mul_assoc] using hC7
  have hC7p' :
      data.t⁻¹ * S2 * data.t⁻¹ = (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := by
    have hC7p0 := hC7p
    rw [forms.frobenius_w1, forms.frobenius_w2, forms.frobenius_w3] at hC7p0
    simpa [Ap, S1, S2, S3, W1p, W2p, W3p,
      Step4C5NormalForms.frobenius, mul_assoc] using hC7p0
  have hword : A * data.t ^ 2 * S1 * W3 = Ap * data.t ^ 2 * S1 * W3p := by
    have hinv : (A * data.t ^ 2 * S1 * W3)⁻¹ =
        (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := hC7'.symm.trans hC7p'
    exact inv_inj.mp hinv
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hp_eq : hyp.base.p = hyp.base.p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ hyp.base.p * W3⁻¹ = W3 ^ (hyp.base.p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ hyp.base.p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (hyp.base.p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ hyp.base.p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (hyp.base.p - 1) := hW3_pow_mul_inv
      _ = W3pow := hW3pow_eq.symm
  have hApA : Ap⁻¹ * A = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
    calc
      Ap⁻¹ * A = Ap⁻¹ * (A * data.t ^ 2 * S1 * W3) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = Ap⁻¹ * (Ap * data.t ^ 2 * S1 * W3p) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        rw [hword]
      _ = data.t ^ 2 * S1 * (W3p * W3⁻¹) * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = data.t ^ 2 * S1 * W3pow * S1⁻¹ * (data.t ^ 2)⁻¹ := by
        rw [hW3p_mul_inv]
      _ = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
        simp [X]
        group
  have hA_mem : A ∈ PU := by
    change A ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨(SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp forms.c3 * SemidirectProduct.inr forms.w2,
      trivial, ?_⟩
    simp [A, W1, W2, S3, map_mul]
  have hAp_mem : Ap ∈ PU := by
    change Ap ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨(SemidirectProduct.inr (forms.w1 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp forms.c3 *
          SemidirectProduct.inr (forms.w2 ^ hyp.base.p), trivial, ?_⟩
    simp [Ap, W1p, W2p, S3, map_mul]
  have hX_mem : X ∈ PU := by
    change X ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨fieldNormalizerPrimeLineElement hyp forms.c1 *
        (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
          fieldNormalizerFrobeniusGroup hyp) *
          (fieldNormalizerPrimeLineElement hyp forms.c1)⁻¹, trivial, ?_⟩
    simp [X, S1, W3pow, map_mul, map_inv]
  have hconj_mem : data.t ^ 2 * X * (data.t ^ 2)⁻¹ ∈ PU := by
    have hleft : Ap⁻¹ * A ∈ PU := PU.mul_mem (PU.inv_mem hAp_mem) hA_mem
    rwa [hApA] at hleft
  exact ⟨by simpa [PU, X, S1, W3pow] using hX_mem,
    by simpa [PU, X, S1, W3pow] using hconj_mem⟩


/-- BG Appendix C exact `(C.9)` word equation.  This is the equality displayed
just before `(C.9)`: after comparing `(C.7)` for `(a,b)` with the Frobenius-powered
`(C.7)`, the remaining `w₁/w₂` word is a `t²`-conjugate of
`S₁ W₃^(p-1) S₁⁻¹`. -/
theorem relationC9_w3_word
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
    let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
    let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
    let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
    let W1p := data.sigma
      (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
    let W2p := data.sigma
      (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
        fieldNormalizerFrobeniusGroup hyp)
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) * data.t ^ 2 =
      S1 * W3pow * S1⁻¹ := by
  classical
  dsimp only
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair ha hb hab
  have hC7 := data.relationC7 hab forms
  have hC7p := data.relationC7 hpow_pair.2.2 forms.frobenius
  have hC7' :
      data.t⁻¹ * S2 * data.t⁻¹ = (A * data.t ^ 2 * S1 * W3)⁻¹ := by
    simpa [A, S1, S2, S3, W1, W2, W3, mul_assoc] using hC7
  have hC7p' :
      data.t⁻¹ * S2 * data.t⁻¹ = (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := by
    have hC7p0 := hC7p
    rw [forms.frobenius_w1, forms.frobenius_w2, forms.frobenius_w3] at hC7p0
    simpa [Ap, S1, S2, S3, W1p, W2p, W3p,
      Step4C5NormalForms.frobenius, mul_assoc] using hC7p0
  have hword : A * data.t ^ 2 * S1 * W3 = Ap * data.t ^ 2 * S1 * W3p := by
    have hinv : (A * data.t ^ 2 * S1 * W3)⁻¹ =
        (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := hC7'.symm.trans hC7p'
    exact inv_inj.mp hinv
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hp_eq : hyp.base.p = hyp.base.p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ hyp.base.p * W3⁻¹ = W3 ^ (hyp.base.p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ hyp.base.p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (hyp.base.p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ hyp.base.p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (hyp.base.p - 1) := hW3_pow_mul_inv
      _ = W3pow := hW3pow_eq.symm
  have hApA : Ap⁻¹ * A = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
    calc
      Ap⁻¹ * A = Ap⁻¹ * (A * data.t ^ 2 * S1 * W3) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = Ap⁻¹ * (Ap * data.t ^ 2 * S1 * W3p) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        rw [hword]
      _ = data.t ^ 2 * S1 * (W3p * W3⁻¹) * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = data.t ^ 2 * S1 * W3pow * S1⁻¹ * (data.t ^ 2)⁻¹ := by
        rw [hW3p_mul_inv]
      _ = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
        simp [X]
        group
  have hleft : W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2 = Ap⁻¹ * A := by
    simp [A, Ap]
    group
  calc
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) *
        data.t ^ 2 =
        (data.t ^ 2)⁻¹ * (Ap⁻¹ * A) * data.t ^ 2 := by
      rw [hleft]
    _ = X := by
      rw [hApA]
      group

/-- After the third word has been killed, exact `(C.9)` and Step 2 force the
remaining two words to satisfy condition `(A)`.  The nontriviality of the third
prime-line factor is the `(C.6)` input, kept explicit here because the global
`C.6` theorem is a separate frontier. -/
theorem relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc3 : forms.c3 ≠ 0) (hw3 : forms.w3 = 1) :
    forms.w1 ^ (hyp.base.p - 1) = 1 ∧ forms.w2 ^ (hyp.base.p - 1) = 1 := by
  classical
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let U1 := (forms.w1 ^ hyp.base.p)⁻¹ * forms.w1
  let L := W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2
  have hC9 := data.relationC9_w3_word ha hb hab forms
  have hC9' : (data.t ^ 2)⁻¹ * L * data.t ^ 2 = S1 * W3pow * S1⁻¹ := by
    simpa [S1, S3, W1, W2, W1p, W2p, W3pow, L, mul_assoc] using hC9
  have hW3pow_one : W3pow = 1 := by
    simp [W3pow, hw3]
  have hL_one : L = 1 := by
    have hconj : (data.t ^ 2)⁻¹ * L * data.t ^ 2 = 1 := by
      simpa [hW3pow_one] using hC9'
    calc
      L = data.t ^ 2 * ((data.t ^ 2)⁻¹ * L * data.t ^ 2) * (data.t ^ 2)⁻¹ := by
        group
      _ = 1 := by
        rw [hconj]
        group
  have hU1_sigma : data.sigma (SemidirectProduct.inr U1 : fieldNormalizerFrobeniusGroup hyp) =
      W1p⁻¹ * W1 := by
    simp [U1, W1p, W1, map_mul, map_inv]
  have hS3_inv : data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) = S3⁻¹ := by
    calc
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) =
          data.sigma ((fieldNormalizerPrimeLineElement hyp forms.c3)⁻¹) := by
        rw [fieldNormalizerPrimeLineElement_neg]
      _ = S3⁻¹ := by
        simp [S3]
  have hW2p_mem : W2p ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr (forms.w2 ^ hyp.base.p),
      ⟨forms.w2 ^ hyp.base.p, rfl⟩, rfl⟩
  have hW2_mem : W2 ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w2, ⟨forms.w2, rfl⟩, rfl⟩
  have hW2_ratio_mem : W2p * W2⁻¹ ∈ hyp.base.U :=
    hyp.base.U.mul_mem hW2p_mem (hyp.base.U.inv_mem hW2_mem)
  have hL' : W2p⁻¹ * (S3⁻¹ * W1p⁻¹ * W1 * S3) * W2 = 1 := by
    simpa [L, mul_assoc] using hL_one
  have hmid_eq : S3⁻¹ * W1p⁻¹ * W1 * S3 = W2p * W2⁻¹ := by
    calc
      S3⁻¹ * W1p⁻¹ * W1 * S3 =
          W2p * (W2p⁻¹ * (S3⁻¹ * W1p⁻¹ * W1 * S3) * W2) * W2⁻¹ := by
        group
      _ = W2p * 1 * W2⁻¹ := by
        rw [hL']
      _ = W2p * W2⁻¹ := by
        group
  have hmid_mem : S3⁻¹ * W1p⁻¹ * W1 * S3 ∈ hyp.base.U := by
    rw [hmid_eq]
    exact hW2_ratio_mem
  have hmem_step : data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) *
        data.sigma (SemidirectProduct.inr U1 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) ∈ hyp.base.U := by
    simpa [hS3_inv, hU1_sigma, S3, mul_assoc] using hmid_mem
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := -forms.c3) (d := forms.c3) U1 hmem_step
  have hU1_one : U1 = 1 := by
    rcases hstep with hzero | hone
    · have hc3_zero : forms.c3 = 0 := by
        simpa using (neg_eq_zero.mp hzero.1)
      exact False.elim (hc3 hc3_zero)
    · exact hone.1
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hU1_one' : (forms.w1 ^ hyp.base.p)⁻¹ * forms.w1 = 1 := by
    simpa [U1] using hU1_one
  have hw1p_eq : forms.w1 ^ hyp.base.p = forms.w1 := by
    calc
      forms.w1 ^ hyp.base.p = forms.w1 ^ hyp.base.p * 1 := by simp
      _ = forms.w1 ^ hyp.base.p * ((forms.w1 ^ hyp.base.p)⁻¹ * forms.w1) := by
        rw [hU1_one']
      _ = forms.w1 := by
        group
  have hw1 : forms.w1 ^ (hyp.base.p - 1) = 1 := by
    have hpow : forms.w1 ^ (hyp.base.p - 1) * forms.w1 = forms.w1 ^ hyp.base.p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hp_pos)]
    calc
      forms.w1 ^ (hyp.base.p - 1) =
          (forms.w1 ^ (hyp.base.p - 1) * forms.w1) * forms.w1⁻¹ := by
        group
      _ = forms.w1 ^ hyp.base.p * forms.w1⁻¹ := by
        rw [hpow]
      _ = forms.w1 * forms.w1⁻¹ := by
        rw [hw1p_eq]
      _ = 1 := by
        group
  have hW1_ratio_one : W1p⁻¹ * W1 = 1 := by
    rw [← hU1_sigma, hU1_one]
    simp
  have hW2_ratio_one : W2p⁻¹ * W2 = 1 := by
    calc
      W2p⁻¹ * W2 = W2p⁻¹ * S3⁻¹ * (W1p⁻¹ * W1) * S3 * W2 := by
        rw [hW1_ratio_one]
        group
      _ = 1 := by
        simpa [L, mul_assoc] using hL_one
  have hW2p_eq : W2p = W2 := by
    calc
      W2p = W2p * 1 := by simp
      _ = W2p * (W2p⁻¹ * W2) := by
        rw [hW2_ratio_one]
      _ = W2 := by
        group
  have hw2p_eq : forms.w2 ^ hyp.base.p = forms.w2 := by
    have hinr : (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) = SemidirectProduct.inr forms.w2 :=
      data.sigma_injective (by simpa [W2p, W2] using hW2p_eq)
    exact (SemidirectProduct.inr_inj.mp hinr)
  have hw2 : forms.w2 ^ (hyp.base.p - 1) = 1 := by
    have hpow : forms.w2 ^ (hyp.base.p - 1) * forms.w2 = forms.w2 ^ hyp.base.p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hp_pos)]
    calc
      forms.w2 ^ (hyp.base.p - 1) =
          (forms.w2 ^ (hyp.base.p - 1) * forms.w2) * forms.w2⁻¹ := by
        group
      _ = forms.w2 ^ hyp.base.p * forms.w2⁻¹ := by
        rw [hpow]
      _ = forms.w2 * forms.w2⁻¹ := by
        rw [hw2p_eq]
      _ = 1 := by
        group
  exact ⟨hw1, hw2⟩


/-- BG Appendix C condition `(A)` in S16 form: a norm-one unit with
`(p - 1)`-st power equal to `1` is trivial. -/
theorem normOneUnit_eq_one_of_pow_sub_one_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) (hu : u ^ (hyp.base.p - 1) = 1) :
    u = 1 :=
  OddOrder.BG.AppC.NormSet.normOneUnits_eq_one_of_pow_sub_one_eq_one
    hyp.base.p hyp.base.q hyp.base.q_prime data.cyclotomic_coprime u hu

namespace Step4C5NormalForms

/-- The post-`(C.9)` condition `(A)` step for the three BG words. -/
theorem w_eq_one_of_pow_sub_one_eq_one
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 ^ (hyp.base.p - 1) = 1)
    (hw2 : forms.w2 ^ (hyp.base.p - 1) = 1)
    (hw3 : forms.w3 ^ (hyp.base.p - 1) = 1) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 :=
  ⟨data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w1 hw1,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w2 hw2,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3⟩

end Step4C5NormalForms


/-- BG Appendix C `(C.10)`: once `(C.9)` and condition `(A)` have forced
`w₁ = w₂ = w₃ = 1`, relation `(C.7)` collapses to
`t² s₁ t⁻¹ s₂ t⁻¹ s₃ = 1`. -/
theorem relationC10_of_w_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 = 1) (hw2 : forms.w2 = 1) (hw3 : forms.w3 = 1) :
    data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  have hC7 := data.relationC7 hab forms
  rw [hw1, hw2, hw3] at hC7
  simp only [map_one, one_mul, mul_one] at hC7
  calc
    data.t ^ 2 * S1 * data.t⁻¹ * S2 * data.t⁻¹ * S3 =
        data.t ^ 2 * S1 * (data.t⁻¹ * S2 * data.t⁻¹) * S3 := by
      group
    _ = data.t ^ 2 * S1 * (S3 * data.t ^ 2 * S1)⁻¹ * S3 := by
      rw [hC7]
    _ = 1 := by group

/-- BG Appendix C Step 4 after Step 3: once Step 3 supplies the membership
`s₁ w₃^(p-1) s₁⁻¹ ∈ U`, Step 2 and condition `(A)` force
`w₁ = w₂ = w₃ = 1`, and hence `(C.10)`.

The two nonzero hypotheses are the `(C.6)` inputs for the first and third
prime-line factors.  The remaining frontier is to produce the displayed
`U`-membership from the Step 3 intersection theorem. -/
theorem relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hw3U :
      data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma
            (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
              fieldNormalizerFrobeniusGroup hyp) *
            (data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1))⁻¹ ∈ hyp.base.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  classical
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let U3 := forms.w3 ^ (hyp.base.p - 1)
  have hS1_inv :
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) = S1⁻¹ := by
    calc
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) =
          data.sigma ((fieldNormalizerPrimeLineElement hyp forms.c1)⁻¹) := by
        rw [fieldNormalizerPrimeLineElement_neg]
      _ = S1⁻¹ := by
        simp [S1]
  have hU3_sigma :
      data.sigma (SemidirectProduct.inr U3 : fieldNormalizerFrobeniusGroup hyp) =
        W3pow := by
    simp [U3, W3pow]
  have hmem_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma (SemidirectProduct.inr U3 : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) ∈ hyp.base.U := by
    simpa [S1, W3pow, U3, hS1_inv, hU3_sigma, mul_assoc] using hw3U
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := forms.c1) (d := -forms.c1) U3 hmem_step
  have hU3_one : U3 = 1 := by
    rcases hstep with hzero | hone
    · exact False.elim (hc1 hzero.1)
    · exact hone.1
  have hw3_pow : forms.w3 ^ (hyp.base.p - 1) = 1 := by
    simpa [U3] using hU3_one
  have hw3 : forms.w3 = 1 :=
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3_pow
  have h12 :=
    data.relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one ha hb hab forms hc3 hw3
  have hwords := forms.w_eq_one_of_pow_sub_one_eq_one h12.1 h12.2 hw3_pow
  have hC10 := data.relationC10_of_w_eq_one hab forms hwords.1 hwords.2.1 hwords.2.2
  exact ⟨hwords.1, hwords.2.1, hwords.2.2, hC10⟩

/-- BG Appendix C Step 4, Step 3 producer in the `U` branch: the concrete `(C.9)`
membership places `S₁ W₃^(p-1) S₁⁻¹` in `PU` and, after applying the inverse Lean
conjugation convention, in `(PU)^{t^{-2}}`.  If Step 3 identifies that
intersection with `U`, the already-landed `(C.9)` collapse gives `w₁=w₂=w₃=1`
and hence `(C.10)`.

This theorem isolates the remaining Step 3 obstruction: after this point the only
missing part of the producer is ruling out the alternative intersection `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_of_w3_step3_inf_eq_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hstep3 :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let X := S1 * W3pow * S1⁻¹
  have hC9 := data.relationC9_w3_mem_P_sup_U_and_conj ha hb hab forms
  have hX_PU : X ∈ PU := by
    simpa [PU, X, S1, W3pow] using hC9.1
  have hX_conj_PU : data.t ^ 2 * X * (data.t ^ 2)⁻¹ ∈ PU := by
    simpa [PU, X, S1, W3pow] using hC9.2
  have hX_smul : X ∈ MulAut.conj ((data.t ^ 2)⁻¹) • PU := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsmul : ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • X) =
        data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
      rw [show ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • X) =
          (MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ X from rfl,
        MulAut.conj_inv_apply]
      group
    rwa [hsmul]
  have hX_inf : X ∈ PU ⊓ (MulAut.conj ((data.t ^ 2)⁻¹) • PU) := ⟨hX_PU, hX_smul⟩
  have hX_U : X ∈ hyp.base.U := by
    have hX_inf' : X ∈ (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) := by
      simpa [PU] using hX_inf
    rwa [hstep3] at hX_inf'
  exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    ha hb hab forms hc1 hc3 (by simpa [X, S1, W3pow] using hX_U)

/-- BG Appendix C Step 4 after applying Step 3 to the `(C.9)` element: either
`(C.10)` has already been forced, or the only remaining Step 3 obstruction is
the bad branch where the relevant intersection is all of `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    (forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1) ∨
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U := by
  classical
  have ht2_norm : data.t ^ 2 ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
    data.t_pow_normalizes_U 2
  have ht2_inv_norm : (data.t ^ 2)⁻¹ ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
    (Subgroup.normalizer (hyp.base.U : Set G)).inv_mem ht2_norm
  have hstep3 := data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U ht2_inv_norm
  rcases hstep3 with hU | hPU
  · left
    exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_inf_eq_U
      ha hb hab forms hc1 hc3 hU
  · right
    exact hPU

/-- **BG Appendix C, Lemma C.3 Step 4 capstone `s₁ = s⁻¹`**, as a statement: for
every norm-one unit `a` whose inverse field value `↑a⁻¹` lies in `E` (so that BG's
companion `b = 2 - ↑a⁻¹` is again a norm-one value), the `k = 3` first normal form
of `s · σ(inr ((tConj⁻³)(a⁻¹))) · s⁻²` has central prime-line factor `s⁻¹`.  This is
the remaining mathematical content; it follows from the (C.2)–(C.10) chain and the
kernel/fixed-point-free argument inside `End ⁅Q, P₀⁆`.

We use the **backward** conjugation `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`, so that
`σ(inr ((tConj⁻³)(a⁻¹))) = t⁻³ σ(inr a⁻¹) t³` matches BG's `(a⁻¹)^{t³}` exactly (BG's
right-conjugation convention `x^{t^k} = t⁻ᵏ x tᵏ`).  This makes the BG (C.4) connector
`q`-swap telescoping (`qⱼ = s⁻ʲtʲ ∈ Q`) port directly; the downstream
`normSetE_eq_inv_of_twisted_normOne_step` is `φ`-agnostic (it only needs `φ^p = 1`,
and `((tConj^3)⁻¹)^p = 1`). -/
def Step4Capstone {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) : Prop :=
  ∀ a : fieldNormalizerNormOneUnits hyp,
    unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
      ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
        data.s *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr u₁) *
          data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
            data.sigma (SemidirectProduct.inr v₁)

/-- The Step 4 capstone yields BG's one-step twisted-inverse output for the
backward conjugation automorphism `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`:
`a ∈ E ⟹ (a⁻¹)^{t³} ∈ E` (BG's right-conjugation).  We apply the capstone at
`a = u⁻¹` so that its hypothesis `↑(u⁻¹)⁻¹ = ↑u ∈ E` is exactly the input, and the
E-extraction `(↑W)⁻¹ ∈ E` (with `W = (tConj⁻³)(u)`) reads as `↑((tConj⁻³)(u⁻¹)) ∈ E`. -/
theorem normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hcap : data.Step4Capstone) :
    OddOrder.BG.AppC.NormSet.normSetETwistedNormOneStep
      (p := hyp.base.p) (q := hyp.base.q) (data.tConjNormOneUnitsAut ^ 3)⁻¹ := by
  intro u hu
  have hcond : unitVal (u⁻¹)⁻¹ ∈
      OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
    rw [inv_inv]; exact hu
  obtain ⟨u₁, v₁, hdec⟩ := hcap u⁻¹ hcond
  have hext := data.unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    ((data.tConjNormOneUnitsAut ^ 3)⁻¹ (u⁻¹)⁻¹) u₁ v₁ hdec
  rw [inv_inv, ← unitVal_inv, ← map_inv] at hext
  rw [OddOrder.BG.AppC.NormSet.twistedInv]
  exact hext

/-- The Step 4 capstone supplies the AppC norm-one twisted-inverse output. -/
theorem appCNormSetTwistedNormOneStep_of_capstone {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (hcap : data.Step4Capstone) :
    appCNormSetTwistedNormOneStep hyp := by
  refine ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹, ?_,
    data.normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone hcap⟩
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul, data.tConjNormOneUnitsAut_pow_p_eq_one,
    one_pow, inv_one]

/-- The Step 4 capstone supplies the AppC generator relation `∀ a ∈ E, N(2a-1)=1`,
**without** the `FieldNormalizerData.appC_twisted_normOne_step` field.  Once the
capstone is proved, this replaces the field-based
`appC_normSet_generator_relation`. -/
theorem appC_normSet_generator_relation_of_capstone {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (hcap : data.Step4Capstone) :
    appCNormSetGeneratorRelation hyp :=
  appCNormSetGeneratorRelation_of_twisted_normOne_step hyp
    (data.appCNormSetTwistedNormOneStep_of_capstone hcap)

end Step4

end FieldNormalizerData

/-! ## (14.3)--(14.7): the subgroup `L` over `N_G(U)` -/

/-- **Peterfalvi (14.3)**: the type-I maximal subgroup `L` containing `N_G(U)`,
its Fitting kernel `H`, the Dade extension, and the three virtual characters
`beta_S`, `beta_T`, and `beta_L`. -/
structure LHypothesis (hyp : Hypothesis (G := G)) where
  L : Subgroup G
  H : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  normalizer_U_le_L : Subgroup.normalizer (hyp.base.U : Set G) ≤ L
  H_eq_LF : H = maxNilpotentNormalHall L
  Lset : Set (ClassFunction ↥L ℂ)
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  phi : ClassFunction ↥L ℂ
  e : ℕ
  e_eq_index : Prop
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaS : ClassFunction G ℂ
  betaT : ClassFunction G ℂ
  betaL : ClassFunction G ℂ
  betaS_formula : Prop
  betaS_formula_holds : betaS_formula
  betaT_formula : Prop
  betaT_formula_holds : betaT_formula
  betaL_formula : Prop
  betaL_formula_holds : betaL_formula
  L_semidirect_formula : G → Prop
  U_characteristic_in_H : Prop
  typeI_data : OddOrder.Peterfalvi.S15.TypeIOverNormalizerData hyp.base

/-- Carrier for the case-(9.7.b) conclusion applied to `T` in Peterfalvi
(14.4). -/
structure CaseBForTData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  D_eq_bot : hyp.base.D = ⊥
  v_eq : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)

namespace CaseBForTData

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
odd. -/
theorem v_odd {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    Odd hyp.base.v := by
  rw [data.v_eq]
  exact hyp.tSide_cyclotomic_quotient_odd

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
positive. -/
theorem v_pos {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    0 < hyp.base.v :=
  Odd.pos data.v_odd

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
nonzero. -/
theorem v_ne_zero {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    hyp.base.v ≠ 0 :=
  ne_of_gt data.v_pos

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
coprime to `q - 1`. -/
theorem v_coprime_q_sub_one {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    Nat.Coprime hyp.base.v (hyp.base.q - 1) := by
  rw [data.v_eq]
  exact hyp.tSide_cyclotomic_quotient_coprime

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, every
positive divisor of `v` is `1 mod p`. -/
theorem divisor_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    ∀ x : ℕ, x ≠ 0 → x ∣ hyp.base.v → x ≡ 1 [MOD hyp.base.p] := by
  intro x hx hxdvd
  apply hyp.tSide_cyclotomic_quotient_divisor_modEq_one x hx
  rw [data.v_eq] at hxdvd
  exact hxdvd

end CaseBForTData

/-- **Peterfalvi (14.4)**: case (9.7.b) holds for `T`, and
`v = (q^p - 1) / (q - 1)`. -/
theorem caseB_for_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧
        hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
  sorry

/-- **Peterfalvi (14.5)**: after conjugating `W_2` by some element of `Q`,
`L` splits as `H semidirect (W_1 W_2^y)`. -/
theorem exists_y_L_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ y : G, y ∈ hyp.base.Q ∧ Ldata.L_semidirect_formula y := by
  sorry

/-- Carrier for the case-(9.7.b) conclusion applied to `S` in Peterfalvi
(14.6). -/
structure CaseBForSData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  order : OddOrder.Peterfalvi.S15.CaseBOrderUData hyp.base caseB_formula
  U_rank_obstruction : Prop
  U_rank_obstruction_holds : U_rank_obstruction

namespace CaseBForSData

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
`p ≡ 1 mod q` branch gives the divided cyclotomic value of `u`. -/
theorem u_eq_of_p_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) :=
  data.order.u_eq_of_p_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
non-`p ≡ 1 mod q` branch gives the full cyclotomic value of `u`. -/
theorem u_eq_of_not_modEq_one {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  data.order.u_eq_of_not_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, `u` is at
most the full cyclotomic quotient.  The `p ≡ 1 mod q` branch divides that
quotient by the additional factor `q`; the other branch is equality. -/
theorem u_le_full_cyclotomic {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hp1_pos : 0 < hyp.base.p - 1 := by
      have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
      omega
    have hden_le : hyp.base.p - 1 ≤ hyp.base.q * (hyp.base.p - 1) := by
      have hqpos : 1 ≤ hyp.base.q := hyp.base.q_prime.one_le
      nlinarith [Nat.mul_le_mul_right (hyp.base.p - 1) hqpos]
    exact Nat.div_le_div_left hden_le hp1_pos
  · rw [data.u_eq_of_not_modEq_one hmod]

end CaseBForSData

/-- **Peterfalvi (14.6)**: case (9.7.b) holds for `S`. -/
theorem caseB_for_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ data : CaseBForSData hyp, data.caseB_formula := by
  sorry

/-- **Peterfalvi (14.7)**: if `U` is characteristic in `H`, then the final
field-normalizer configuration (14.2) holds. -/
theorem field_normalizer_of_U_characteristic [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (hchar : Ldata.U_characteristic_in_H) :
    Nonempty (FieldNormalizerData hyp) := by
  sorry

/-! ## (14.8)--(14.9): the key inequality and `T` is type II -/

/-- A small explicit upper bound for `e`, used to keep Peterfalvi (14.8.a)
inside elementary arithmetic/log estimates. -/
private theorem real_exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h :=
    Complex.exp_bound_sq (0 : ℂ) ((1 : ℝ) : ℂ) (by norm_num : ‖((1 : ℝ) : ℂ)‖ ≤ 1)
  rw [Complex.exp_zero] at h
  norm_num at h
  change ‖Complex.exp (((1 : ℝ) : ℂ)) - 1 - 1‖ ≤ (1 : ℝ) at h
  have hsq : ‖Complex.exp (((1 : ℝ) : ℂ)) - 1 - 1‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
  simp [Complex.exp_re, Complex.exp_im] at hsq
  have hupper : Real.exp 1 - 2 ≤ 1 := by nlinarith
  linarith

/-- Taylor's quadratic upper bound for `exp` on `[0,1]`, in the weak form
needed for Peterfalvi (14.8.a). -/
private theorem real_exp_le_quadratic {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hxnorm : ‖((x : ℝ) : ℂ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have h := Complex.exp_bound_sq (0 : ℂ) ((x : ℝ) : ℂ) hxnorm
  rw [Complex.exp_zero] at h
  have hnorm : ‖Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ)‖ ≤ x ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0, pow_two] using h
  have hre := Complex.re_le_norm (Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ))
  have hre_eq :
      (Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ)).re = Real.exp x - 1 - x := by
    simp [Complex.exp_re]
  have hdiff : Real.exp x - 1 - x ≤ x ^ 2 := by
    rw [← hre_eq]
    exact hre.trans hnorm
  linarith

private theorem one_add_inv_le_log_of_five_le {q : ℕ} (hq : 5 ≤ q) :
    1 + (1 / (q : ℝ)) ≤ Real.log q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  rw [Real.le_log_iff_exp_le hqpos]
  have hqge : (5 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    Real.exp (1 + 1 / (q : ℝ)) = Real.exp 1 * Real.exp (1 / (q : ℝ)) := by
      rw [Real.exp_add]
    _ ≤ 3 * (1 + 1 / (q : ℝ) + (1 / (q : ℝ)) ^ 2) := by
      have hsmall : Real.exp (1 / (q : ℝ)) ≤
          1 + 1 / (q : ℝ) + (1 / (q : ℝ)) ^ 2 :=
        real_exp_le_quadratic (by positivity) (by
          field_simp [hqpos.ne']
          exact_mod_cast (le_trans (by norm_num : 1 ≤ 5) hq))
      exact mul_le_mul real_exp_one_le_three hsmall (Real.exp_nonneg _) (by norm_num)
    _ ≤ q := by
      have hs : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
      have hcube : 5 * (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by nlinarith [hqge, hs]
      have hquad : 3 * ((q : ℝ) * ((q : ℝ) + 1) + 1) ≤ 5 * (q : ℝ) ^ 2 := by
        nlinarith [hqge, hs]
      field_simp [hqpos.ne']
      nlinarith [hcube, hquad]

private theorem log_div_succ_lt_of_five_le {p q : ℕ} (hq : 5 ≤ q) (hqp : q < p) :
    Real.log (p : ℝ) / ((p : ℝ) + 1) < Real.log (q : ℝ) / ((q : ℝ) + 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  have hppos : (0 : ℝ) < p := hqpos.trans (by exact_mod_cast hqp)
  have hdenp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hdenq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  rw [div_lt_div_iff₀ hdenp hdenq]
  have hratio_pos : (0 : ℝ) < (p : ℝ) / (q : ℝ) := div_pos hppos hqpos
  have hratio_ne : (p : ℝ) / (q : ℝ) ≠ 1 := by
    intro h
    field_simp [hqpos.ne'] at h
    have hpq : p = q := by exact_mod_cast h
    omega
  have hlog_ratio := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
  have hlog_div := Real.log_div hppos.ne' hqpos.ne'
  have hlogp_bound : Real.log (p : ℝ) < Real.log (q : ℝ) + ((p : ℝ) / (q : ℝ) - 1) := by
    nlinarith [hlog_ratio, hlog_div]
  have hmul := mul_lt_mul_of_pos_right hlogp_bound hdenq
  have hlogq_lower : ((q : ℝ) + 1) / (q : ℝ) ≤ Real.log (q : ℝ) := by
    have h := one_add_inv_le_log_of_five_le hq
    field_simp [hqpos.ne'] at h ⊢
    exact h
  have hupper :
      (Real.log (q : ℝ) + ((p : ℝ) / (q : ℝ) - 1)) * ((q : ℝ) + 1) ≤
        Real.log (q : ℝ) * ((p : ℝ) + 1) := by
    have hpq_nonneg : 0 ≤ (p : ℝ) - (q : ℝ) := by
      have hpqle : (q : ℝ) ≤ p := by exact_mod_cast (le_of_lt hqp)
      linarith
    have hlogq_lower' : (q : ℝ) + 1 ≤ Real.log (q : ℝ) * (q : ℝ) := by
      rwa [div_le_iff₀ hqpos] at hlogq_lower
    have hmul_nonneg :
        ((p : ℝ) - (q : ℝ)) * ((q : ℝ) + 1) ≤
          ((p : ℝ) - (q : ℝ)) * (Real.log (q : ℝ) * (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogq_lower' hpq_nonneg
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  exact hmul.trans_le hupper

private theorem q_pow_gt_p_pow_of_five_le {p q : ℕ} (hq : 5 ≤ q) (hqp : q < p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  have hppos : (0 : ℝ) < p := hqpos.trans (by exact_mod_cast hqp)
  have hdenp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hdenq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hfrac := log_div_succ_lt_of_five_le (p := p) (q := q) hq hqp
  rw [div_lt_div_iff₀ hdenp hdenq] at hfrac
  have hlogpow : Real.log (((p : ℝ) ^ (q + 1))) < Real.log (((q : ℝ) ^ (p + 1))) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    nlinarith [hfrac]
  have hreal : ((p : ℝ) ^ (q + 1)) < ((q : ℝ) ^ (p + 1)) :=
    (Real.log_lt_log_iff (pow_pos hppos _) (pow_pos hqpos _)).mp hlogpow
  exact_mod_cast hreal

private theorem fourth_lt_three_pow_succ {p : ℕ} (hp : 5 ≤ p) :
    p ^ 4 < 3 ^ (p + 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hstep : (p + 1) ^ 4 < 3 * p ^ 4 := by
        have hpz : (5 : ℤ) ≤ p := by exact_mod_cast hp
        have hz : ((p + 1 : ℤ) ^ 4 < 3 * (p : ℤ) ^ 4) := by
          nlinarith [hpz, sq_nonneg ((p : ℤ) - 5), sq_nonneg ((p : ℤ) - 4),
            sq_nonneg ((p : ℤ) - 3), sq_nonneg ((p : ℤ) - 2),
            sq_nonneg ((p : ℤ) - 1), sq_nonneg (p : ℤ)]
        exact_mod_cast hz
      calc
        (p + 1) ^ 4 < 3 * p ^ 4 := hstep
        _ < 3 * 3 ^ (p + 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 3 ^ (p + 2) := by
          rw [show p + 2 = p + 1 + 1 by omega, pow_succ]
          ring

private theorem q_pow_gt_p_pow_of_q_eq_three {p q : ℕ} (hq : q = 3) (hp : 5 ≤ p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  subst q
  simpa using fourth_lt_three_pow_succ hp

/-- **Peterfalvi (14.8.a)**: for odd prime parameters with `q < p`,
`q^(p+1)` strictly dominates `p^(q+1)`. -/
theorem q_pow_gt_p_pow {p q : ℕ} (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hqp : q < p) :
    q ^ (p + 1) > p ^ (q + 1) := by
  by_cases hq3 : q = 3
  · have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := by
        intro hp4
        subst p
        rcases hpodd with ⟨k, hk⟩
        omega
      omega
    exact q_pow_gt_p_pow_of_q_eq_three hq3 hp5
  · have hq_ne_two : q ≠ 2 := by
      intro hq2
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    have hq_three : 3 ≤ q := by
      have htwo : 2 ≤ q := hq.two_le
      omega
    have hq_ne_four : q ≠ 4 := by
      intro hq4
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    have hq5 : 5 ≤ q := by omega
    exact q_pow_gt_p_pow_of_five_le hq5 hqp

namespace Hypothesis

/-- The arithmetic part of **Peterfalvi (14.8)** under the Section 16
hypothesis bundle. -/
theorem q_pow_gt_p_pow (hyp : Hypothesis (G := G)) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) :=
  OddOrder.Peterfalvi.S16.q_pow_gt_p_pow hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p

end Hypothesis

private theorem cyclotomic_quotient_sub_one_ge_pow_pred {q p : ℕ}
    (hq2 : 2 ≤ q) (hp2 : 2 ≤ p) :
    ((q ^ (p - 1) : ℕ) : ℚ) ≤ (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) := by
  have hsum_eq : ∑ k ∈ Finset.range p, q ^ k = (q ^ p - 1) / (q - 1) :=
    Nat.geomSum_eq hq2 p
  have hle_rest : q ^ (p - 1) ≤ ∑ k ∈ Finset.range (p - 1), q ^ (k + 1) := by
    have hlast_mem : p - 2 ∈ Finset.range (p - 1) := by
      simp
      omega
    have hnonneg : ∀ k ∈ Finset.range (p - 1), 0 ≤ q ^ (k + 1) := by
      intro k _hk
      exact Nat.zero_le _
    have hsingle := Finset.single_le_sum hnonneg hlast_mem
    simpa [show p - 2 + 1 = p - 1 by omega] using hsingle
  have hsum_succ : ∑ k ∈ Finset.range p, q ^ k =
      (∑ k ∈ Finset.range (p - 1), q ^ (k + 1)) + 1 := by
    rw [show p = (p - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    simp
  have hle_sum : q ^ (p - 1) + 1 ≤ ∑ k ∈ Finset.range p, q ^ k := by
    rw [hsum_succ]
    omega
  have hnat : q ^ (p - 1) ≤ (q ^ p - 1) / (q - 1) - 1 := by
    rw [← hsum_eq]
    omega
  exact_mod_cast hnat

private theorem cyclotomic_quotient_sub_one_lt_div {p q : ℕ} (hp2 : 2 ≤ p) :
    (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) <
      (p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp2
  have hp1_pos_nat : 0 < p - 1 := by omega
  have hden_pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by exact_mod_cast hp1_pos_nat
  have hdiv : p - 1 ∣ p ^ q - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow p 1 q
  have hcast_div : (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) =
      ((p ^ q - 1 : ℕ) : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
    exact Nat.cast_div hdiv (ne_of_gt hden_pos)
  have hsub_le : (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) ≤
      (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le ((p ^ q - 1) / (p - 1)) 1
  have hnum_nat : p ^ q - 1 < p ^ q := by
    have hpq_pos : 0 < p ^ q := pow_pos hp_pos q
    omega
  have hnum : ((p ^ q - 1 : ℕ) : ℚ) < (p ^ q : ℚ) := by exact_mod_cast hnum_nat
  have hquot_lt : (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) <
      (p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
    rw [hcast_div]
    exact div_lt_div_of_pos_right hnum hden_pos
  exact lt_of_le_of_lt hsub_le hquot_lt

private theorem mul_pred_lt_three_pow_pred {p : ℕ} (hp : 5 ≤ p) :
    p * (p - 1) < 3 ^ (p - 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hstep : (p + 1) * p < 3 * (p * (p - 1)) := by
        have hfactor : p + 1 < 3 * (p - 1) := by omega
        have hmul := Nat.mul_lt_mul_of_pos_right hfactor (by omega : 0 < p)
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      calc
        (p + 1) * ((p + 1) - 1) = (p + 1) * p := by rw [Nat.add_sub_cancel_right]
        _ < 3 * (p * (p - 1)) := hstep
        _ < 3 * 3 ^ (p - 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 3 ^ p := by
          calc
            3 * 3 ^ (p - 1) = 3 ^ (p - 1) * 3 := by rw [mul_comm]
            _ = 3 ^ ((p - 1) + 1) := by rw [pow_succ]
            _ = 3 ^ p := by rw [show (p - 1) + 1 = p by omega]

private theorem p_mul_q_lt_q_pow_pred_of_five_le {p q : ℕ}
    (hp5 : 5 ≤ p) (hq3 : 3 ≤ q) (hqp : q < p) :
    p * q < q ^ (p - 1) := by
  have hq_le_pred : q ≤ p - 1 := by omega
  have hpq_le : p * q ≤ p * (p - 1) := Nat.mul_le_mul_left p hq_le_pred
  have hpq_lt_three : p * q < 3 ^ (p - 1) :=
    lt_of_le_of_lt hpq_le (mul_pred_lt_three_pow_pred hp5)
  have hthree_le_qpow : 3 ^ (p - 1) ≤ q ^ (p - 1) :=
    Nat.pow_le_pow_left hq3 (p - 1)
  exact lt_of_lt_of_le hpq_lt_three hthree_le_qpow

private theorem two_mul_sq_lt_pow_pred_of_odd_lt {p q : ℕ}
    (hpodd : Odd p) (hqodd : Odd q) (hq3 : 3 ≤ q) (hqp : q < p) :
    2 * q * q < p ^ (q - 1) := by
  by_cases hq_three : q = 3
  · subst q
    have hp_gt_three : 3 < p := by simpa using hqp
    have hp5 : 5 ≤ p := by
      have hp_ne_four : p ≠ 4 := by
        intro hp4
        have hodd : Odd 4 := by simpa [hp4] using hpodd
        rcases hodd with ⟨k, hk⟩
        omega
      omega
    have hpow2 : 2 * 3 * 3 < p ^ 2 := by
      nlinarith
    simpa using hpow2
  · have hq5 : 5 ≤ q := by
      have hq_ne_four : q ≠ 4 := by
        intro hq4
        have hodd : Odd 4 := by simpa [hq4] using hqodd
        rcases hodd with ⟨k, hk⟩
        omega
      omega
    have hq_pos : 0 < q := by omega
    have hq_sq_pos : 0 < q * q := Nat.mul_pos hq_pos hq_pos
    have htwo_lt_qsq : 2 < q * q := by nlinarith
    have hlt_q4 : 2 * (q * q) < (q * q) * (q * q) :=
      Nat.mul_lt_mul_of_pos_right htwo_lt_qsq hq_sq_pos
    have hq4_le_p4 : q ^ 4 ≤ p ^ 4 :=
      Nat.pow_le_pow_left (Nat.le_of_lt hqp) 4
    have hp_pos : 0 < p := by omega
    have hp4_le : p ^ 4 ≤ p ^ (q - 1) :=
      Nat.pow_le_pow_right hp_pos (by omega : 4 ≤ q - 1)
    calc
      2 * q * q = 2 * (q * q) := by ring
      _ < (q * q) * (q * q) := hlt_q4
      _ = q ^ 4 := by ring
      _ ≤ p ^ 4 := hq4_le_p4
      _ ≤ p ^ (q - 1) := hp4_le

namespace CaseBForTData

/-- The T-side case-(9.7.b) cyclotomic value in **Peterfalvi (14.4)** is already
larger than `p q`.  This is the cyclotomic lower consequence consumed by the
norm-cascade contradiction in (14.11.4). -/
theorem pq_lt_v {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    hyp.base.p * hyp.base.q < hyp.base.v := by
  have hpow : hyp.base.p * hyp.base.q < hyp.base.q ^ (hyp.base.p - 1) :=
    p_mul_q_lt_q_pow_pred_of_five_le hyp.five_le_p hyp.base.three_le_q hyp.q_lt_p
  have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
    (q := hyp.base.q) (p := hyp.base.p) hyp.base.q_prime.two_le hyp.base.p_prime.two_le
  have hle : hyp.base.q ^ (hyp.base.p - 1) ≤
      (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) - 1 := by
    exact_mod_cast hleQ
  rw [data.v_eq]
  exact lt_of_lt_of_le (lt_of_lt_of_le hpow hle)
    (Nat.sub_le ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)) 1)

/-- The T-side case-(9.7.b) lower bound also gives the size hypothesis
`v > 2 p` needed in the (14.11.4) norm cascade. -/
theorem two_p_lt_v {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    2 * hyp.base.p < hyp.base.v := by
  have hq_gt_two : 2 < hyp.base.q := by
    have hq3 : 3 ≤ hyp.base.q := hyp.base.three_le_q
    omega
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hmul : hyp.base.p * 2 < hyp.base.p * hyp.base.q :=
    Nat.mul_lt_mul_of_pos_left hq_gt_two hp_pos
  have h2p_lt_pq : 2 * hyp.base.p < hyp.base.p * hyp.base.q := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact lt_trans h2p_lt_pq data.pq_lt_v

end CaseBForTData

namespace CaseBForSData

/-- The S-side case-(9.7.b) cyclotomic value in **Peterfalvi (14.6)** is larger
than `2 q`.  This is the S-side size input consumed by the norm-cascade
contradiction in (14.11.4), including the additional division by `q` in the
`p ≡ 1 mod q` branch. -/
theorem two_q_lt_u {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    2 * hyp.base.q < hyp.base.u := by
  have hpow_sq :
      2 * hyp.base.q * hyp.base.q < hyp.base.p ^ (hyp.base.q - 1) :=
    two_mul_sq_lt_pow_pred_of_odd_lt hyp.base.p_odd hyp.base.q_odd
      hyp.base.three_le_q hyp.q_lt_p
  have hq_gt_one : 1 < hyp.base.q := hyp.base.q_prime.one_lt
  have htwoq_pos : 0 < 2 * hyp.base.q :=
    Nat.mul_pos (by norm_num) hyp.base.q_prime.pos
  have htwoq_lt_twoqq : 2 * hyp.base.q < 2 * hyp.base.q * hyp.base.q := by
    have hmul := Nat.mul_lt_mul_of_pos_left hq_gt_one htwoq_pos
    simpa [mul_assoc] using hmul
  have hpow : 2 * hyp.base.q < hyp.base.p ^ (hyp.base.q - 1) :=
    lt_trans htwoq_lt_twoqq hpow_sq
  have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
    (q := hyp.base.p) (p := hyp.base.q) hyp.base.p_prime.two_le hyp.base.q_prime.two_le
  have hle : hyp.base.p ^ (hyp.base.q - 1) ≤
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 := by
    exact_mod_cast hleQ
  have hfull_gt_twoq :
      2 * hyp.base.q < (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hpow hle)
      (Nat.sub_le ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) 1)
  have hfull_gt_twoqq :
      2 * hyp.base.q * hyp.base.q <
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hpow_sq hle)
      (Nat.sub_le ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) 1)
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hdvd : hyp.base.q ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
        hyp.base.p_prime hmod
    have hlt_div :
        2 * hyp.base.q <
          (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q := by
      rw [Nat.lt_div_iff_mul_lt' hdvd]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfull_gt_twoqq
    rw [show (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q by
      rw [Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm]]
    exact hlt_div
  · rw [data.u_eq_of_not_modEq_one hmod]
    exact hfull_gt_twoq

end CaseBForSData

/-- Arithmetic bridge for **Peterfalvi (14.8)**: under the Section 16 prime
ordering `q < p`, the T-side full cyclotomic quotient gives a strictly larger
`(v - 1) / p` ratio than the S-side full cyclotomic quotient gives for
`(u - 1) / q`. -/
theorem cyclotomic_ratio_gt_of_q_lt_p {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p) :
    (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) >
      (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ) := by
  have hpow : q ^ (p + 1) > p ^ (q + 1) :=
    OddOrder.Peterfalvi.S16.q_pow_gt_p_pow hq hpodd hqodd hqp
  have hq2 : 2 ≤ q := hq.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have hqpos_nat : 0 < q := hq.pos
  have hppos_nat : 0 < p := hp.pos
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hp1_pos_nat : 0 < p - 1 := by omega
  have hp1pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by exact_mod_cast hp1_pos_nat
  have hp_pred_ge_q : q ≤ p - 1 := by omega
  have hmain_nat : p ^ (q + 1) < (p - 1) * q ^ p := by
    have hmul : q ^ (p + 1) ≤ (p - 1) * q ^ p := by
      rw [pow_succ, mul_comm (q ^ p) q]
      exact Nat.mul_le_mul_right (q ^ p) hp_pred_ge_q
    exact lt_of_lt_of_le hpow hmul
  have hmain : (p : ℚ) ^ (q + 1) < (((p - 1 : ℕ) : ℚ)) * (q : ℚ) ^ p := by
    exact_mod_cast hmain_nat
  have hmain' : (p ^ q : ℚ) * (p : ℚ) <
      (q ^ (p - 1) : ℚ) * ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) := by
    have hp_pow : (p : ℚ) ^ (q + 1) = (p : ℚ) ^ q * (p : ℚ) := by
      rw [pow_succ]
    have hq_pow : (q : ℚ) ^ p = (q : ℚ) ^ (p - 1) * (q : ℚ) := by
      calc
        (q : ℚ) ^ p = (q : ℚ) ^ ((p - 1) + 1) := by
          exact congrArg (fun n : ℕ => (q : ℚ) ^ n) (by omega : p = (p - 1) + 1)
        _ = (q : ℚ) ^ (p - 1) * (q : ℚ) := by rw [pow_succ]
    norm_num [Nat.cast_pow] at hmain ⊢
    nlinarith
  have hleft_lower := cyclotomic_quotient_sub_one_ge_pow_pred (q := q) (p := p) hq2 hp2
  have hright_upper := cyclotomic_quotient_sub_one_lt_div (p := p) (q := q) hp2
  have hcompare_core : (p ^ q : ℚ) / ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) <
      (q ^ (p - 1) : ℚ) / (p : ℚ) := by
    rw [div_lt_div_iff₀]
    · simpa [Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hmain'
    · positivity
    · exact hppos
  calc
    (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ)
        < ((p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ))) / (q : ℚ) :=
          div_lt_div_of_pos_right hright_upper hqpos
    _ = (p ^ q : ℚ) / ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) := by
          field_simp [hqpos.ne', hp1pos.ne']
    _ < (q ^ (p - 1) : ℚ) / (p : ℚ) := hcompare_core
    _ ≤ (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) := by
          exact div_le_div_of_nonneg_right (by simpa [Nat.cast_pow] using hleft_lower)
            (le_of_lt hppos)

/-- The ratio comparison in **Peterfalvi (14.8)** from the two case-(9.7.b)
cyclotomic order conclusions. -/
theorem key_ratio_inequality_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) :
    (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  have hqpos : (0 : ℚ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right Sdata.u_le_full_cyclotomic 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  rw [Tdata.v_eq]
  exact lt_of_le_of_lt hu_div hratio

/-- **Peterfalvi (14.8)** from materialized case-(9.7.b) data on both sides.
This is the proven consumer form of `key_inequality`: once Sections (14.4) and
(14.6) provide the T- and S-side `CaseB` data, the remaining comparison is pure
arithmetic. -/
theorem key_inequality_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  exact ⟨hyp.q_pow_gt_p_pow, key_ratio_inequality_of_caseB_data Tdata Sdata⟩

/-- **Peterfalvi (14.8)** consumer form for the exact output shapes of
`caseB_for_T` and `caseB_for_S`.  This keeps the future proof of
`key_inequality` focused on constructing the structural `CaseB` data. -/
theorem key_inequality_of_caseB_outputs {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact key_inequality_of_caseB_data Tdata Sdata

/-- **Peterfalvi (14.8)**: the strict exponential inequality and its
character-theoretic corollary comparing `(v - 1) / p` and `(u - 1) / q`. -/
theorem key_inequality [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  refine ⟨hyp.q_pow_gt_p_pow, ?_⟩
  sorry

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II. -/
theorem T_typeII [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T := by
  sorry

/-! ## (14.10)--(14.11): the subgroup `M` over `N_G(V)` -/

/-- **Peterfalvi (14.10)**: the type-I maximal subgroup `M` containing
`N_G(V)`, its Fitting kernel `K`, the Dade extension, and `beta_M`. -/
structure MHypothesis (hyp : Hypothesis (G := G)) where
  M : Subgroup G
  K : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  normalizer_V_le_M : Subgroup.normalizer (hyp.base.V : Set G) ≤ M
  K_eq_MF : K = maxNilpotentNormalHall M
  Mset : Set (ClassFunction ↥M ℂ)
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  psi : ClassFunction ↥M ℂ
  e : ℕ
  k : ℕ
  e_eq_index : Prop
  k_eq_card_K : k = Nat.card ↥K
  psi_mem : psi ∈ Mset
  psi_degree_eq_e : psi 1 = (e : ℂ)
  betaM : ClassFunction G ℂ
  betaM_formula : Prop
  betaM_formula_holds : betaM_formula
  G0 : Set G
  generic_bound_formula : G → Prop
  betaM_expansion_formula : Prop
  final_norm_contradiction : Prop

/-- The displayed rational inequality produced by the norm calculation in
**Peterfalvi (14.11.4)**, after substituting `e = p q`.  It is kept concrete so
future character-theoretic producers can target the exact arithmetic consumer
without adding another opaque proposition. -/
def normCascadeBound (hyp : Hypothesis (G := G)) (k : ℕ) : Prop :=
  (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
    ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
      2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)

/-- Pure arithmetic estimate used in **Peterfalvi (14.11.4)**.  Once the
norm calculation reduces the error terms to `2 / (p q) + 1 / (u q) + 1 / (v p)`,
the Section 16 size assumptions `u > 2q`, `v > 2p`, and `q < p` bound that error
strictly by `1 / q`. -/
theorem norm_error_terms_lt_inv_q {p q u v : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v) :
    (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
        1 / ((v * p : ℕ) : ℚ) < 1 / (q : ℚ) := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hupos_nat : 0 < u := by omega
  have hvpos_nat : 0 < v := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hupos : (0 : ℚ) < u := by exact_mod_cast hupos_nat
  have hvpos : (0 : ℚ) < v := by exact_mod_cast hvpos_nat
  have hq3q : (3 : ℚ) ≤ q := by exact_mod_cast hq3
  have hqpq : (q : ℚ) < p := by exact_mod_cast hqp
  have huq : (2 : ℚ) * q < u := by exact_mod_cast hu
  have hvp : (2 : ℚ) * p < v := by exact_mod_cast hv
  have hterm1 : (2 : ℚ) / ((p * q : ℕ) : ℚ) < 2 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    exact div_lt_div_of_pos_left (by norm_num) (mul_pos hqpos hqpos)
      (mul_lt_mul_of_pos_right hqpq hqpos)
  have hterm2 : (1 : ℚ) / ((u * q : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hden : (2 : ℚ) * q * q < u * q := by nlinarith [huq, hqpos]
    have hcore : (1 : ℚ) / (u * q) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hterm3 : (1 : ℚ) / ((v * p : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hsq : (q : ℚ) * q < p * p := by nlinarith [hqpq, hqpos, hppos]
    have hden : (2 : ℚ) * q * q < v * p := by nlinarith [hsq, hvp, hppos]
    have hcore : (1 : ℚ) / (v * p) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hsum :
      (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ) <
        2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) := by
    nlinarith [hterm1, hterm2, hterm3]
  have hsum_eq :
      2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) = 3 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    field_simp [hqpos.ne']
    ring
  have hthree_le : (3 : ℚ) / ((q * q : ℕ) : ℚ) ≤ 1 / (q : ℚ) := by
    norm_num [Nat.cast_mul]
    have hmul_nonneg : 0 ≤ (q : ℚ) * ((q : ℚ) - 3) :=
      mul_nonneg (le_of_lt hqpos) (sub_nonneg.mpr hq3q)
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  nlinarith [hsum, hsum_eq, hthree_le]

/-- Arithmetic endpoint for **Peterfalvi (14.11.4)**.  If the norm calculation
has already yielded the displayed bound from the text, then the lower bound
`k > 2 p v` and the cyclotomic lower consequence `p q < v` are contradictory. -/
theorem norm_cascade_contradiction {p q u v k : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v)
    (hk : 2 * p * v < k) (hvlarge : p * q < v)
    (hbound :
      (1 : ℚ) / (p : ℚ) + 1 / (q : ℚ) ≤
        ((p * q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((p * q : ℕ) : ℚ) +
          1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ)) :
    False := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hvpos_nat : 0 < v := by omega
  have hkpos_nat : 0 < k := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hkpos : (0 : ℚ) < k := by exact_mod_cast hkpos_nat
  have hsmall := norm_error_terms_lt_inv_q (p := p) (q := q) (u := u) (v := v)
    hq3 hqp hu hv
  have hpinv_lt : (1 : ℚ) / (p : ℚ) < ((p * q : ℕ) : ℚ) / (k : ℚ) := by
    nlinarith [hbound, hsmall]
  have hk_lt : (k : ℚ) < (p : ℚ) * (p : ℚ) * (q : ℚ) := by
    field_simp [Nat.cast_mul, hppos.ne', hqpos.ne', hkpos.ne'] at hpinv_lt
    norm_num [Nat.cast_mul] at hpinv_lt
    nlinarith [hpinv_lt]
  have hk_gt : ((2 * p * v : ℕ) : ℚ) < k := by exact_mod_cast hk
  have hvlargeq : ((p * q : ℕ) : ℚ) < v := by exact_mod_cast hvlarge
  norm_num [Nat.cast_mul] at hk_gt hvlargeq
  nlinarith [hk_lt, hk_gt, hvlargeq, hppos]

/-- **Peterfalvi (14.11.4)** arithmetic consumer with the T-side case-(9.7.b)
data already materialized.  The T-side data supplies both `p q < v` and
`2 p < v`, so the remaining inputs are exactly the S-side lower bound on `u`,
the `k > 2 p v` lower bound, and the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_T_caseB {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (hu : 2 * hyp.base.q < hyp.base.u) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction hyp.base.three_le_q hyp.q_lt_p hu
    Tdata.two_p_lt_v hk Tdata.pq_lt_v hbound

/-- **Peterfalvi (14.11.4)** arithmetic consumer with both case-(9.7.b) data
packages materialized.  The S-side data supplies `2 q < u`; the T-side data
supplies `2 p < v` and `p q < v`. -/
theorem norm_cascade_contradiction_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction_of_T_caseB Tdata Sdata.two_q_lt_u hk hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T` and `caseB_for_S`.  It leaves only the lower bound on `k` and the
concrete displayed norm inequality as inputs. -/
theorem norm_cascade_contradiction_of_caseB_outputs {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k) (hbound : normCascadeBound hyp k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hk hbound

/-- **Peterfalvi (14.11.4)** consumer after the first numerical output of
`main_size_bounds` has supplied `k > 2 p v`.  The remaining non-arithmetic work
is precisely to produce the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_main_size_bound {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v)
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hsize hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact three-part numerical output
of **Peterfalvi (14.11.1)**.  Only the first component, `k > 2 p v`, is needed
by the norm-cascade contradiction; the remaining components stay available to
match the theorem output without weakening its shape. -/
theorem norm_cascade_contradiction_of_caseB_data_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_main_size_bound Tdata Sdata Mdata hsize.1 hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T`, `caseB_for_S`, and `main_size_bounds`. -/
theorem norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data_main_size_bounds Tdata Sdata Mdata
    hsize hbound

/-- **Peterfalvi (14.11.1)**: if `K != V`, then `k` is large and the quotient
bound dominates `(v - 1) / p`. -/
theorem main_size_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  sorry

/-- **Peterfalvi (14.11.2)**: under `K != V`, `e = p q`, and
`beta_M^tau` is a signed sum of the `eta_ij` with one character removed. -/
theorem betaM_expansion [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.e = hyp.base.p * hyp.base.q ∧ Mdata.betaM_expansion_formula := by
  sorry

/-- **Peterfalvi (14.11.3)**: on the generic set `G_0`, the extended character
`psi^tau_1` has absolute value at least one. -/
theorem generic_character_bound [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) :
    ∀ g : G, g ∈ Mdata.G0 → Mdata.generic_bound_formula g := by
  sorry

/-- **Peterfalvi (14.11.2)+(14.11.3) ⇒ (14.11.4)**: the character-theoretic norm
calculation.  Combining the `beta_M^tau` expansion (14.11.2) with the generic
lower bound `|psi^tau_1| ≥ 1` (14.11.3) and the Frobenius inner-product formula
(7.5) yields the displayed rational inequality `normCascadeBound hyp k`.  This is
the *sole* genuinely character-theoretic input to the (14.11.4) contradiction;
everything downstream of it is the arithmetic cascade already discharged in
`norm_cascade_contradiction`. -/
theorem normCascadeBound_of_charData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    normCascadeBound hyp Mdata.k := by
  -- (14.11.2): `e = p q` together with the signed `eta_ij` expansion of `beta_M^tau`.
  have _hbeta := betaM_expansion _hG hyp Mdata hne
  -- (14.11.3): the generic lower bound `|psi^tau_1(g)| ≥ 1` on `G_0`.
  have _hgen := generic_character_bound _hG hyp Mdata
  sorry

/-- **Peterfalvi (14.11.4)**: the norm inequality cascade contradicts `K != V`.

This is now a transparent composition rather than an opaque obligation: the
case-(9.7.b) outputs of `caseB_for_T` (14.4) and `caseB_for_S` (14.6) supply the
T-side/S-side cyclotomic size data, `main_size_bounds` (14.11.1) supplies
`k > 2 p v`, and `normCascadeBound_of_charData` (14.11.2)--(14.11.3) supplies the
displayed norm inequality.  The arithmetic consumer
`norm_cascade_contradiction_of_caseB_outputs_main_size_bounds` then closes the
cascade.  The only remaining genuine `sorry`s are the named producers above. -/
theorem contradiction_of_K_ne_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    False :=
  norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    (caseB_for_T _hG hyp) (caseB_for_S _hG hyp Ldata) Mdata
    (main_size_bounds _hG hyp Mdata hne)
    (normCascadeBound_of_charData _hG hyp Mdata hne)

/-- **Peterfalvi (14.11)**: `K = V` and `|M : K| = p q`.

The `K = V` half is now a genuine consequence of the (14.11.1)--(14.11.4)
contradiction: assuming `K ≠ V` invokes `contradiction_of_K_ne_V`.  The index
computation `|M : K| = p q` (here `Mdata.e = p q`) is the remaining genuine
obligation; note `betaM_expansion`'s `e = p q` is unavailable here because it
is conditioned on `K ≠ V`, so the equal-index value under `K = V` needs the
type-I structure of `M` directly. -/
theorem K_eq_V_index_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp) :
    Mdata.K = hyp.base.V ∧ Mdata.e = hyp.base.p * hyp.base.q := by
  refine ⟨?_, ?_⟩
  · -- (14.11.1)--(14.11.4): `K ≠ V` is contradictory.
    by_contra hne
    exact contradiction_of_K_ne_V _hG hyp Ldata Mdata hne
  · -- `|M : K| = p q` from the type-I structure of `M` (still to be supplied).
    sorry

/-! ## (14.12)--(14.16): comparing `L` and `M` -/

/-- **Peterfalvi (14.12)**: if `L` is conjugate to `M`, then the final
field-normalizer configuration (14.2) holds. -/
theorem field_normalizer_of_L_conj_M [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M) :
    Nonempty (FieldNormalizerData hyp) := by
  sorry

/-- **Peterfalvi (14.13)**: the final comparison case assumes `L` and `M` are
not conjugate and sets `h = |H|`. -/
structure NonConjugateHypothesis (hyp : Hypothesis (G := G)) where
  Ldata : LHypothesis hyp
  Mdata : MHypothesis hyp
  not_conj : ¬ ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
  h : ℕ
  h_eq_card_H : h = Nat.card ↥Ldata.H

/-- The two alternatives of **Peterfalvi (14.14)**. -/
structure OrthogonalitySwitchData {hyp : Hypothesis (G := G)}
    (nc : NonConjugateHypothesis hyp) where
  caseA : Prop
  caseA_bound :
    caseA →
      (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))
  caseB : Prop
  caseB_params : caseB → hyp.base.q = 3 ∧ hyp.base.p = 5

/-- **Peterfalvi (14.14)**: either the `beta_M`--`phi` pairing is nonzero and
`(h - 1) / p q <= p q - 1`, or the `beta_L`--`psi` pairing is nonzero and
`(q,p) = (3,5)`. -/
theorem orthogonality_switch [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    ∃ data : OrthogonalitySwitchData nc, data.caseA ∨ data.caseB := by
  sorry

/-- **Peterfalvi (14.15)**: `u` has the full cyclotomic value
`(p^q - 1) / (p - 1)`. -/
theorem u_final_value [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  sorry

/-- **Peterfalvi (14.16)**: in the non-conjugate case, the kernel `H` is
exactly `U`. -/
theorem H_eq_U [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    nc.Ldata.H = hyp.base.U := by
  sorry

/-- **Peterfalvi (14.2)**: the field-normalizer configuration follows from the
Section 16 hypotheses. -/
theorem field_normalizer_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (FieldNormalizerData hyp) := by
  sorry

/-- **Peterfalvi Section 16 + BG Appendix C**: BG Appendix C turns the
field-normalizer configuration into `p <= q`, contradicting (14.1). -/
theorem nonexistence_of_G [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (bgAppendixC : FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q) :
    False := by
  rcases field_normalizer_structure hG hyp with ⟨data⟩
  exact (not_lt_of_ge (bgAppendixC data)) hyp.q_lt_p

end OddOrder.Peterfalvi.S16
