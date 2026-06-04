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

/-- The concrete norm-one unit group used as BG's complement before transport
through the field-normalizer embedding. -/
abbrev fieldNormalizerNormOneUnits (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q

/-- The distinguished nonidentity element of the prime-field line `P₀`,
corresponding to `1 : F_{p^q}` in BG Appendix C. -/
noncomputable def fieldNormalizerPrimeLineGenerator (hyp : Hypothesis (G := G)) :
    fieldNormalizerFrobeniusGroup hyp :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  SemidirectProduct.inl
    (Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q))

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

/-- The conjugate generator `t` normalizes `U`. -/
theorem t_normalizes_U {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
  data.P1_normalizes_U data.t_mem_P1

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

/-- **Peterfalvi (14.11.4)**: the norm inequality cascade contradicts
`K != V`. -/
theorem contradiction_of_K_ne_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    False := by
  sorry

/-- **Peterfalvi (14.11)**: `K = V` and `|M : K| = p q`. -/
theorem K_eq_V_index_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) :
    Mdata.K = hyp.base.V ∧ Mdata.e = hyp.base.p * hyp.base.q := by
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
