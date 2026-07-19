/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki.RootSubgroupStructure
import OddOrder.GroupTheory.SpecificGroups.Suzuki.Simplicity
import OddOrder.GroupTheory.SpecificGroups.Suzuki2Group.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The standard Suzuki root as a Sylow subgroup and a Suzuki 2-group

For the nondegenerate parameter `0 < m`, this file completes the structural
identification of the concrete root group of `Sz(2^(2m+1))`:

* the standard root subgroup is a Sylow `2`-subgroup of the standard
  permutation group;
* the multiplicative defining field gives a cyclic subgroup of root-group
  automorphisms;
* this subgroup acts regularly on the nonidentity involutions; and
* consequently the coordinate root group satisfies Peterfalvi Appendix III,
  Definition 1 without a proposition-valued carrier.

The multiplication is the explicit type-A central extension attached to the
quadratic map `x |-> x * theta(x)` from Appendix III, Definition 2.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.Suzuki

noncomputable section

open OddOrder.GroupTheory.Suzuki2Group

section Sylow

/-- The odd cofactor in the order of the standard Suzuki group. -/
def standardRootOddCofactor (m : ℕ) : ℕ :=
  (2 ^ (2 * (2 * m + 1)) + 1) * (2 ^ (2 * m + 1) - 1)

theorem standardRootOddCofactor_odd (m : ℕ) :
    Odd (standardRootOddCofactor m) := by
  apply Odd.mul
  · exact (even_two.pow_of_ne_zero (by omega)).add_one
  · exact Nat.Even.sub_odd (one_le_pow₀ one_le_two)
      (even_two.pow_of_ne_zero (by omega)) odd_one

/-- The index of the standard root is the odd factor in the standard group
order. -/
theorem standardRootSubgroup_index (m : ℕ) :
    (standardRootSubgroup m).index = standardRootOddCofactor m := by
  have hcard := (standardRootSubgroup m).card_mul_index
  rw [natCard_standardRootSubgroup, natCard_standardPermGroup] at hcard
  apply Nat.eq_of_mul_eq_mul_left
    (pow_pos (by omega : 0 < 2) (2 * (2 * m + 1)))
  simpa [standardRootOddCofactor, mul_assoc] using hcard

/-- The standard root has odd index in the standard Suzuki group. -/
theorem standardRootSubgroup_index_odd (m : ℕ) :
    Odd (standardRootSubgroup m).index := by
  rw [standardRootSubgroup_index]
  exact standardRootOddCofactor_odd m

/-- **Peterfalvi Part II, Ch. I, Proposition 1(c), Suzuki case.**
The standard root subgroup is a Sylow `2`-subgroup of the standard Suzuki
permutation group. -/
noncomputable def standardRootSylow (m : ℕ) : Sylow 2 (standardPermGroup m) :=
  ((RootGroup.isPGroup m).of_equiv (rootEquivStandardRoot m)).toSylow
    (by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr (standardRootSubgroup_index_odd m))

@[simp] theorem coe_standardRootSylow (m : ℕ) :
    (standardRootSylow m : Subgroup (standardPermGroup m)) =
      standardRootSubgroup m := by
  rfl

end Sylow

section RegularTorus

/-- The torus weight, regarded as a unit of the defining field. -/
noncomputable def torusWeightUnit (m : ℕ) :
    TorusParameter m →* TorusParameter m where
  toFun c := Units.mk0 (torusWeight c) (torusWeight_ne_zero c)
  map_one' := by ext; exact torusWeight_one m
  map_mul' c d := by ext; exact torusWeight_mul c d

@[simp] theorem coe_torusWeightUnit {m : ℕ} (c : TorusParameter m) :
    ((torusWeightUnit m c : TorusParameter m) : Field m) = torusWeight c :=
  rfl

/-- The weight `c |-> c * theta(c)` is injective on the multiplicative field. -/
theorem torusWeightUnit_injective (m : ℕ) :
    Function.Injective (torusWeightUnit m) := by
  intro c d h
  have hker : torusWeightUnit m (c * d⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hweight : torusWeight (c * d⁻¹) = 1 := by
    exact Units.ext_iff.mp hker
  have hcd : c * d⁻¹ = 1 := (torusWeight_eq_one_iff _).mp hweight
  exact mul_inv_eq_one.mp hcd

/-- The weight `c |-> c * theta(c)` permutes the nonzero field elements. -/
theorem torusWeightUnit_surjective (m : ℕ) :
    Function.Surjective (torusWeightUnit m) :=
  Finite.surjective_of_injective (torusWeightUnit_injective m)

/-- The standard cyclic torus inside the automorphism group of the root. -/
noncomputable def standardRootTorus (m : ℕ) :
    Subgroup (MulAut (RootGroup m)) :=
  (torusScaleHom m).range

/-- The standard root torus is cyclic. -/
theorem standardRootTorus_isCyclic (m : ℕ) :
    IsCyclic ↥(standardRootTorus m) := by
  letI : IsCyclic (TorusParameter m) := inferInstance
  exact isCyclic_of_surjective (torusScaleHom m).rangeRestrict
    (torusScaleHom m).rangeRestrict_surjective

/-- The torus action on the root group is faithful. -/
theorem torusScaleHom_injective (m : ℕ) :
    Function.Injective (torusScaleHom m) := by
  intro c d h
  have hfst := congrArg
    (fun e : MulAut (RootGroup m) =>
      (e (RootGroup.mk 1 0)).fst) h
  apply Units.ext
  apply inv_injective
  simpa only [torusScaleHom_apply, torusScale_fst, one_div] using hfst

/-- The standard torus acts regularly on the nonidentity involutions of the
coordinate root group. -/
theorem standardRootTorus_actsRegularlyOnInvolutions (m : ℕ) :
    ActsRegularlyOnInvolutions (standardRootTorus m) := by
  intro x hx y hy
  rcases hx with ⟨hx2, hx1⟩
  rcases hy with ⟨hy2, hy1⟩
  have hxfst : x.fst = 0 := (RootGroup.sq_eq_one_iff x).mp hx2
  have hyfst : y.fst = 0 := (RootGroup.sq_eq_one_iff y).mp hy2
  have hxsnd : x.snd ≠ 0 := by
    intro h
    apply hx1
    ext
    · simpa only [RootGroup.fst_one] using hxfst
    · simpa only [RootGroup.snd_one] using h
  have hysnd : y.snd ≠ 0 := by
    intro h
    apply hy1
    ext
    · simpa only [RootGroup.fst_one] using hyfst
    · simpa only [RootGroup.snd_one] using h
  let xu : TorusParameter m := Units.mk0 x.snd hxsnd
  let yu : TorusParameter m := Units.mk0 y.snd hysnd
  obtain ⟨c, hc⟩ := torusWeightUnit_surjective m (xu * yu⁻¹)
  have hcval : torusWeight c = x.snd / y.snd := by
    have h := congrArg (fun z : TorusParameter m => (z : Field m)) hc
    simpa only [coe_torusWeightUnit, xu, yu, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_mul_inv] using h
  let a : ↥(standardRootTorus m) :=
    ⟨torusScaleHom m c, ⟨c, rfl⟩⟩
  refine ⟨a, ?_, ?_⟩
  · change torusScale c x = y
    ext
    · simp [hxfst, hyfst]
    · simp only [torusScale_snd]
      rw [hcval]
      field_simp
  · intro b hb
    rcases b.2 with ⟨d, hd⟩
    have hbd : torusScale d x = y := by
      change (b : MulAut (RootGroup m)) x = y at hb
      rw [← hd] at hb
      exact hb
    have hdval : torusWeight d = x.snd / y.snd := by
      have hsnd := congrArg RootGroup.snd hbd
      simp only [torusScale_snd] at hsnd
      have h' := (div_eq_iff (torusWeight_ne_zero d)).mp hsnd
      apply (eq_div_iff hysnd).mpr
      exact (mul_comm _ _).trans h'.symm
    have hdc : d = c := by
      apply torusWeightUnit_injective m
      apply Units.ext
      exact hdval.trans hcval.symm
    apply Subtype.ext
    change b.1 = torusScaleHom m c
    rw [← hd, hdc]

end RegularTorus

section TypeA

/-- One full odd field period kills the Tits twist. -/
theorem titsTwist_pow_period (m : ℕ) :
    titsTwist m ^ (2 * m + 1) = 1 := by
  have hfrob :
      frobeniusEquiv (Field m) 2 ^ (2 * m + 1) = 1 := by
    rw [← iterateFrobeniusEquiv_eq_pow]
    ext x
    exact iterateFrobeniusEquiv_period m x
  rw [titsTwist, iterateFrobeniusEquiv_eq_pow]
  calc
    (frobeniusEquiv (Field m) 2 ^ (m + 1)) ^ (2 * m + 1) =
        frobeniusEquiv (Field m) 2 ^ ((m + 1) * (2 * m + 1)) := by
      rw [← pow_mul]
    _ = frobeniusEquiv (Field m) 2 ^ ((2 * m + 1) * (m + 1)) := by
      rw [Nat.mul_comm (m + 1) (2 * m + 1)]
    _ = (frobeniusEquiv (Field m) 2 ^ (2 * m + 1)) ^ (m + 1) := by
      rw [pow_mul]
    _ = 1 := by rw [hfrob, one_pow]

/-- The Tits twist has odd order. -/
theorem titsTwist_orderOf_odd (m : ℕ) : Odd (orderOf (titsTwist m)) := by
  exact (odd_two_mul_add_one m).of_dvd_nat
    (orderOf_dvd_of_pow_eq_one (titsTwist_pow_period m))

private theorem frobeniusEquiv_ne_one_of_pos (m : ℕ) (hm : 0 < m) :
    frobeniusEquiv (Field m) 2 ≠ 1 := by
  intro hfrob
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic
    (ZMod 2) (Field m)
  have hσ : σ = 1 := by
    ext x
    have hx := DFunLike.congr_fun hfrob x
    change x ^ 2 = x at hx
    change x ^ Fintype.card (ZMod 2) = x
    simpa only [ZMod.card] using hx
  have hord : orderOf σ = 2 * m + 1 := by
    dsimp only [σ]
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      GaloisField.finrank 2 (by omega)]
  rw [hσ, orderOf_one] at hord
  omega

/-- For a nondegenerate Suzuki parameter, the Tits twist is nontrivial. -/
theorem titsTwist_ne_one_of_pos (m : ℕ) (hm : 0 < m) :
    titsTwist m ≠ 1 := by
  intro h
  apply frobeniusEquiv_ne_one_of_pos m hm
  rw [← titsTwist_sq, h, one_pow]

/-- A positive-parameter Suzuki root group is noncommutative. -/
theorem RootGroup.not_isMulCommutative (m : ℕ) (hm : 0 < m) :
    ¬ IsMulCommutative (RootGroup m) := by
  have hex : ∃ a : Field m, titsTwist m a ≠ a := by
    by_contra h
    push Not at h
    apply titsTwist_ne_one_of_pos m hm
    ext a
    simpa using h a
  obtain ⟨a, ha⟩ := hex
  intro hcomm
  let x : RootGroup m := RootGroup.mk a 0
  let y : RootGroup m := RootGroup.mk 1 0
  have hxy := congrArg RootGroup.snd (isMulCommutative_iff.mp hcomm x y)
  apply ha
  simpa only [RootGroup.snd_mul, x, y, map_one, one_mul, mul_one,
    zero_add, add_zero] using hxy

/-- Constructive data for the standard type-A family of Appendix III,
Definition 2.  Unlike `SuzukiTypeData.typeA`, this contains an actual group
equivalence to the central extension for `x |-> x * theta(x)`. -/
structure StandardTypeAData (P : Type*) [Group P] where
  parameter : ℕ
  parameter_pos : 0 < parameter
  equivRootGroup : P ≃* RootGroup parameter

namespace StandardTypeAData

variable {P : Type*} [Group P] (data : StandardTypeAData P)

/-- The field automorphism in an honest standard type-A model is nontrivial. -/
theorem twist_ne_one : titsTwist data.parameter ≠ 1 :=
  titsTwist_ne_one_of_pos data.parameter data.parameter_pos

/-- The field automorphism in an honest standard type-A model has odd order,
as required in Appendix III, Definition 2. -/
theorem twist_orderOf_odd : Odd (orderOf (titsTwist data.parameter)) :=
  titsTwist_orderOf_odd data.parameter

/-- Under the model equivalence, squaring is the quadratic map
`x |-> x * theta(x)` into the central coordinate line. -/
theorem map_sq (x : P) :
    data.equivRootGroup (x ^ 2) =
      RootGroup.mk 0
        ((data.equivRootGroup x).fst *
          titsTwist data.parameter (data.equivRootGroup x).fst) := by
  rw [map_pow, RootGroup.sq_eq]

end StandardTypeAData

/-- The coordinate root group is the standard honest type-A model. -/
noncomputable def RootGroup.standardTypeAData (m : ℕ) (hm : 0 < m) :
    StandardTypeAData (RootGroup m) where
  parameter := m
  parameter_pos := hm
  equivRootGroup := MulEquiv.refl _

/-- The standard Sylow root subgroup carries the same honest type-A model as
the coordinate root group. -/
noncomputable def standardRootSubgroupTypeAData (m : ℕ) (hm : 0 < m) :
    StandardTypeAData ↥(standardRootSubgroup m) where
  parameter := m
  parameter_pos := hm
  equivRootGroup := (rootEquivStandardRoot m).symm

private theorem exists_two_rootGroup_involutions (m : ℕ) (hm : 0 < m) :
    ∃ x y : RootGroup m,
      x ∈ involutions (RootGroup m) ∧
      y ∈ involutions (RootGroup m) ∧ x ≠ y := by
  have hcard : 1 < Nat.card (TorusParameter m) := by
    rw [Nat.card_units, natCard_field]
    have hpow : 2 ^ 3 ≤ 2 ^ (2 * m + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hpow ⊢
    omega
  letI : Nontrivial (TorusParameter m) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨c, hc⟩ := exists_ne (1 : TorusParameter m)
  let x : RootGroup m := RootGroup.mk 0 1
  let y : RootGroup m := RootGroup.mk 0 (c : Field m)
  refine ⟨x, y, ⟨(RootGroup.sq_eq_one_iff x).2 rfl, ?_⟩,
    ⟨(RootGroup.sq_eq_one_iff y).2 rfl, ?_⟩, ?_⟩
  · intro hx
    have h : (1 : Field m) = 0 := congrArg RootGroup.snd hx
    exact one_ne_zero h
  · intro hy
    exact Units.ne_zero c (by
      have h := congrArg RootGroup.snd hy
      simpa only [y, RootGroup.snd_one] using h)
  · intro hxy
    apply hc
    apply Units.ext
    simpa only [x, y, Units.val_one] using
      (congrArg RootGroup.snd hxy).symm

/-- **Peterfalvi Appendix III, Definition 1.**  The positive-parameter
coordinate root group is an honest Suzuki `2`-group, witnessed by its standard
cyclic torus acting regularly on involutions. -/
theorem RootGroup.isSuzuki2Group (m : ℕ) (hm : 0 < m) :
    IsSuzuki2Group (RootGroup m) := by
  refine ⟨RootGroup.isPGroup m, RootGroup.not_isMulCommutative m hm,
    exists_two_rootGroup_involutions m hm, standardRootTorus m,
    standardRootTorus_isCyclic m,
    standardRootTorus_actsRegularlyOnInvolutions m⟩

private theorem map_mem_involutions
    {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) {x : P}
    (hx : x ∈ involutions P) : e x ∈ involutions Q := by
  rcases hx with ⟨hx2, hx1⟩
  constructor
  · rw [← map_pow, hx2, map_one]
  · intro hex
    apply hx1
    apply e.injective
    simpa only [map_one] using hex

private theorem mulAut_congr_apply
    {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) (a : MulAut P) (x : Q) :
    MulAut.congr e a x = e (a (e.symm x)) :=
  rfl

/-- The honest Suzuki `2`-group structure is invariant under group
equivalence.  The acting cyclic automorphism subgroup and its regular action
are transported by conjugating automorphisms with the equivalence. -/
theorem IsSuzuki2Group.of_equiv
    {P Q : Type*} [Group P] [Group Q]
    (hP : IsSuzuki2Group P) (e : P ≃* Q) : IsSuzuki2Group Q := by
  rcases hP with ⟨hp, hnoncomm, htwo, A, hcyclic, hregular⟩
  have hnoncommQ : ¬ IsMulCommutative Q := by
    intro hcommQ
    apply hnoncomm
    rw [isMulCommutative_iff] at hcommQ ⊢
    intro x y
    apply e.injective
    simpa only [map_mul] using hcommQ (e x) (e y)
  rcases htwo with ⟨x, y, hx, hy, hxy⟩
  have htwoQ :
      ∃ x y : Q, x ∈ involutions Q ∧
        y ∈ involutions Q ∧ x ≠ y :=
    ⟨e x, e y, map_mem_involutions e hx, map_mem_involutions e hy,
      fun heq ↦ hxy (e.injective heq)⟩
  let autEquiv : MulAut P ≃* MulAut Q := MulAut.congr e
  let B : Subgroup (MulAut Q) := A.map autEquiv.toMonoidHom
  have hcyclicB : IsCyclic ↥B := by
    exact (autEquiv.subgroupMap A).isCyclic.mp hcyclic
  have hregularB : ActsRegularlyOnInvolutions B := by
    intro u hu v hv
    have huP : e.symm u ∈ involutions P :=
      map_mem_involutions e.symm hu
    have hvP : e.symm v ∈ involutions P :=
      map_mem_involutions e.symm hv
    obtain ⟨a, ha, ha_unique⟩ := hregular (e.symm u) huP (e.symm v) hvP
    let mapA : A ≃* B := autEquiv.subgroupMap A
    let b : B := mapA a
    refine ⟨b, ?_, ?_⟩
    · change autEquiv a u = v
      rw [mulAut_congr_apply, ha, e.apply_symm_apply]
    · intro c hc
      let cpre : A := mapA.symm c
      have hcpre_map : mapA cpre = c := mapA.apply_symm_apply c
      have hcpre_map_val :
          autEquiv (cpre : MulAut P) = (c : MulAut Q) := by
        exact congrArg Subtype.val hcpre_map
      have hcpre_act :
          (cpre : MulAut P) (e.symm u) = e.symm v := by
        apply e.injective
        calc
          e ((cpre : MulAut P) (e.symm u)) =
              autEquiv (cpre : MulAut P) u :=
            (mulAut_congr_apply e (cpre : MulAut P) u).symm
          _ = (c : MulAut Q) u := by rw [hcpre_map_val]
          _ = v := hc
          _ = e (e.symm v) := (e.apply_symm_apply v).symm
      have hcpre_eq : cpre = a := ha_unique cpre hcpre_act
      calc
        c = mapA cpre := hcpre_map.symm
        _ = b := by
          change mapA cpre = mapA a
          exact congrArg mapA hcpre_eq
  exact ⟨hp.of_equiv e, hnoncommQ, htwoQ, B, hcyclicB, hregularB⟩

/-- The standard Sylow root subgroup is itself an honest Suzuki `2`-group;
all Definition 1 data are transported from the coordinate root group. -/
theorem standardRootSubgroup_isSuzuki2Group (m : ℕ) (hm : 0 < m) :
    IsSuzuki2Group ↥(standardRootSubgroup m) :=
  IsSuzuki2Group.of_equiv (RootGroup.isSuzuki2Group m hm)
    (rootEquivStandardRoot m)

end TypeA

end


end OddOrder.GroupTheory.SpecificGroups.Suzuki
